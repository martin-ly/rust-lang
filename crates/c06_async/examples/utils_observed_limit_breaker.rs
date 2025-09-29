//! 运行方式：
//! cargo run -p c06_async --example utils_observed_limit_breaker
//!
//! 功能：
//! - 使用 `SimpleTokenBucket` 进行限速
//! - 使用 `CircuitBreaker` 进行熔断（含半开探测）
//! - 使用 `ExecStrategyBuilder` 组合重试/退避/超时策略
//! - 暴露 Prometheus 指标：`/metrics`（默认 127.0.0.1:9899）

use std::sync::Arc;
use std::time::Duration;

use prometheus::{IntCounter, Histogram, HistogramOpts, Opts, Registry};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 1) 指标注册与 HTTP 暴露
    let registry = Registry::new();
    static REQUESTS_TOTAL: once_cell::sync::Lazy<IntCounter> = once_cell::sync::Lazy::new(|| IntCounter::with_opts(Opts::new("requests_total", "总请求数")).unwrap());
    static REQUESTS_FAIL:  once_cell::sync::Lazy<IntCounter> = once_cell::sync::Lazy::new(|| IntCounter::with_opts(Opts::new("requests_fail_total", "失败请求数")).unwrap());
    static REQUEST_LATENCY: once_cell::sync::Lazy<Histogram> = once_cell::sync::Lazy::new(|| Histogram::with_opts(HistogramOpts::new("request_seconds", "请求耗时(秒)")).unwrap());
    let _ = registry.register(Box::new(REQUESTS_TOTAL.clone()));
    let _ = registry.register(Box::new(REQUESTS_FAIL.clone()));
    let _ = registry.register(Box::new(REQUEST_LATENCY.clone()));

    // 在后台启动 metrics server
    let reg_for_srv = registry.clone();
    tokio::spawn(async move {
        let _ = c06_async::utils::metrics::serve_metrics(reg_for_srv, "127.0.0.1:9899").await;
    });

    // 2) 构造熔断器与令牌桶
    let breaker = c06_async::utils::circuit_breaker::CircuitBreaker::new_with_half_open_max(5, Duration::from_secs(30), 3);
    let bucket = c06_async::utils::SimpleTokenBucket::new(10, 5); // 容量10，每秒回填5

    // 3) 构造策略执行器（含熔断、限速、重试）
    let runner = c06_async::utils::ExecStrategyBuilder::new()
        .concurrency(4)
        .attempts(4)
        .start_delay(Duration::from_millis(50))
        .timeout(Duration::from_secs(1))
        .breaker(breaker.clone())
        .token_bucket(bucket.clone())
        .build();
    let runner = Arc::new(runner);

    // 4) 模拟一个“易失败”的下游调用
    async fn flaky_backend(input: u32) -> Result<String, anyhow::Error> {
        // 让前 2 次调用失败，之后成功
        if input % 5 < 2 { Err(anyhow::anyhow!("backend temporary error")) } else { Ok(format!("ok: {}", input)) }
    }

    // 5) 执行若干请求，观测熔断/限速/指标
    let mut tasks = Vec::new();
    for i in 0..20u32 {
        let runner = runner.clone();
        tasks.push(tokio::spawn(async move {
            let t = std::time::Instant::now();
            REQUESTS_TOTAL.inc();
            let base = i;
            let res = runner.run(move |attempt| flaky_backend(base + attempt), None::<fn(&anyhow::Error)->bool>).await;
            match res {
                Ok(Some(v)) => {
                    REQUEST_LATENCY.observe(t.elapsed().as_secs_f64());
                    Ok::<_, anyhow::Error>(v)
                }
                Ok(None) => {
                    REQUESTS_FAIL.inc();
                    REQUEST_LATENCY.observe(t.elapsed().as_secs_f64());
                    Err(anyhow::anyhow!("timeout/deadline reached"))
                }
                Err(e) => {
                    REQUESTS_FAIL.inc();
                    REQUEST_LATENCY.observe(t.elapsed().as_secs_f64());
                    Err(anyhow::anyhow!(e))
                }
            }
        }));
    }

    // 等待完成
    let mut ok = 0usize;
    for t in tasks { if t.await??.starts_with("ok:") { ok += 1; } }
    println!("completed_ok = {} (metrics at http://127.0.0.1:9899/metrics)", ok);

    Ok(())
}


