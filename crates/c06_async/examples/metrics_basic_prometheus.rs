//! metrics + metrics-exporter-prometheus 指标记录与导出示例
//!
//! 启动一个 Prometheus scrape endpoint（默认 `0.0.0.0:9090`），
//! 可通过 `METRICS_ADDR` 环境变量覆盖。
//! 循环生成 counter / gauge / histogram 三类指标，用于演示 metrics facade 的用法。

use metrics::{counter, describe_counter, gauge, histogram};
use std::net::SocketAddr;
use std::time::Duration;
use tokio::time::interval;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let addr: SocketAddr = std::env::var("METRICS_ADDR")
        .unwrap_or_else(|_| "0.0.0.0:9090".into())
        .parse()?;

    metrics_exporter_prometheus::PrometheusBuilder::new()
        .with_http_listener(addr)
        .install()?;

    describe_counter!("demo_requests_total", "Total number of demo requests");

    let mut ticker = interval(Duration::from_secs(1));
    for i in 0..10 {
        ticker.tick().await;
        counter!("demo_requests_total", "method" => "GET").increment(1);
        gauge!("demo_active_tasks").set(i as f64);
        histogram!("demo_request_duration_seconds").record(i as f64 * 0.01);
    }

    // 给 scraper 留出窗口后退出
    tokio::time::sleep(Duration::from_secs(1)).await;
    Ok(())
}
