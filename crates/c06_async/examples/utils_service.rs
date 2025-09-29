//! 运行方式：
//! BIND_ADDR=127.0.0.1:8088 METRICS_ADDR=127.0.0.1:9899 cargo run -p c06_async --example utils_service
//! 可选：CONFIG_PATH=./configs/strategy.json 指定策略配置（JSON）
//!
//! 端点：
//! - GET /health           → 健康检查
//! - POST /work {n:u32}    → 触发一次受策略控制的后端调用（重试/超时/熔断/限速）
//! - /metrics              → Prometheus 指标（由 utils::metrics 暴露在 METRICS_ADDR）

use std::fs;
use std::net::SocketAddr;

use axum::{routing::{get, post}, Json, Router};
use serde::{Deserialize, Serialize};
use tracing::{info, info_span, Instrument};
use tracing_subscriber::{fmt, EnvFilter};
use tracing_subscriber::prelude::*; // for .with()

#[derive(Debug, Deserialize, Serialize)]
struct WorkReq { n: u32 }

#[derive(Debug, Deserialize, Serialize)]
struct WorkResp { ok: bool, message: String }

async fn run() -> anyhow::Result<()> {
    // 1) 初始化 tracing：结构化 JSON 日志，支持 RUST_LOG 覆盖
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));
    // 改为易读的文本格式（pretty）。如需更紧凑可改为 `.compact()`
    let fmt_layer = fmt::layer().with_target(true).pretty();
    tracing_subscriber::registry().with(filter).with(fmt_layer).init();

    // 2) 加载服务端口与策略配置
    let bind_addr: String = std::env::var("BIND_ADDR").unwrap_or_else(|_| "127.0.0.1:8088".to_string());
    let metrics_addr: String = std::env::var("METRICS_ADDR").unwrap_or_else(|_| "127.0.0.1:9899".to_string());
    let cfg_path = std::env::var("CONFIG_PATH").ok();

    let strategy_cfg: c06_async::utils::StrategyConfig = if let Some(path) = cfg_path.as_ref() {
        let raw = fs::read_to_string(path)?;
        serde_json::from_str(&raw)?
    } else {
        // 合理的默认策略
        serde_json::from_value(serde_json::json!({
            "concurrency": 4u32,
            "max_attempts": 4u32,
            "start_delay_ms": 50u64,
            "timeout_ms": 1000u64,
            "enable_breaker": true,
            "breaker_threshold": 5u32,
            "breaker_window_ms": 30000u64,
            "breaker_half_open_max_calls": 3u32,
            "token_bucket": {"capacity": 10u32, "refill_per_sec": 5u32}
        }))?
    };

    let builder = c06_async::utils::ExecStrategyBuilder::from_config(&strategy_cfg);
    let runner = builder.build();

    // 3) 指标服务（后台）
    let registry = prometheus::Registry::new();
    let _ = registry.register(Box::new(prometheus::IntCounter::with_opts(
        prometheus::Opts::new("service_requests_total", "服务请求数")
    )?));
    let reg_for_srv = registry.clone();
    let metrics_addr_clone = metrics_addr.clone();
    tokio::spawn(async move {
        let _ = c06_async::utils::metrics::serve_metrics(reg_for_srv, metrics_addr_clone.as_str()).await;
    });

    // 4) Axum 路由
    let runner = std::sync::Arc::new(runner);
    let app = Router::new()
        .route("/health", get(|| async { axum::http::StatusCode::OK }))
        .route("/work", post({
            let runner = runner.clone();
            move |Json(req): Json<WorkReq>| {
                let runner = runner.clone();
                async move {
                    let request_id = uuid::Uuid::new_v4();
                    let req_span = info_span!("work_request", %request_id, n = %req.n);
                    let _enter = req_span.enter();
                    // 模拟“可能失败”的后端：依据 n 与 attempt 控制成功/失败
                    async fn flaky(n: u32, attempt: u32) -> Result<String, anyhow::Error> {
                        if (n + attempt) % 5 < 2 { Err(anyhow::anyhow!("temporary backend error")) } else { Ok(format!("ok:{}@{}", n, attempt)) }
                    }

                    let n = req.n;
                    let res = runner
                        .run(
                            move |attempt| {
                                let att_span = info_span!("attempt", %request_id, attempt = %attempt);
                                async move { flaky(n, attempt).await }.instrument(att_span)
                            },
                            None::<fn(&anyhow::Error)->bool>,
                        )
                        .await;
                    match res {
                        Ok(Some(msg)) => (axum::http::StatusCode::OK, Json(WorkResp{ ok: true, message: msg })),
                        Ok(None) => (axum::http::StatusCode::REQUEST_TIMEOUT, Json(WorkResp{ ok: false, message: "timeout/deadline".to_string() })),
                        Err(e) => (axum::http::StatusCode::BAD_GATEWAY, Json(WorkResp{ ok: false, message: format!("error: {}", e) })),
                    }
                }
            }
        }));

    let addr: SocketAddr = bind_addr.parse()?;
    info!(%addr, %metrics_addr, "utils_service starting");
    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app.into_make_service()).await?;
    Ok(())
}

fn main() -> anyhow::Result<()> {
    let runtime = tokio::runtime::Builder::new_multi_thread()
        .enable_all()
        .build()?;
    runtime.block_on(run())
}


