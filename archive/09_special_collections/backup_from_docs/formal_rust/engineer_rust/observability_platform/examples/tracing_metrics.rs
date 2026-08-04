// 可观测性平台：tracing与metrics采集示例
// Observability Platform: Tracing & Metrics Example
use tracing::info;
use metrics::{counter, describe_counter};

fn main() {
    tracing_subscriber::fmt::init();
    describe_counter!("requests_total", "Total number of requests");
    counter!("requests_total", 1);
    info!("service started");
} 