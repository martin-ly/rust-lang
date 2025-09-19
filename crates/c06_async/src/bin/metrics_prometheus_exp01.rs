// Prometheus 指标集成示例

use prometheus::{Histogram, Registry, TextEncoder, Encoder, CounterVec, HistogramOpts, Opts};
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let _ = tracing_subscriber::fmt::try_init();
    
    // 创建指标注册表
    let registry = Registry::new();
    
    // 定义指标
    let request_counter = CounterVec::new(
        Opts::new("http_requests_total", "Total HTTP requests"),
        &["method", "endpoint"]
    )?;
    
    let request_duration = Histogram::with_opts(
        HistogramOpts::new("http_request_duration_seconds", "HTTP request duration")
            .buckets(vec![0.001, 0.01, 0.1, 0.5, 1.0, 2.0, 5.0])
    )?;
    
    let error_counter = CounterVec::new(
        Opts::new("http_errors_total", "Total HTTP errors"),
        &["status_code"]
    )?;
    
    // 注册指标
    registry.register(Box::new(request_counter.clone()))?;
    registry.register(Box::new(request_duration.clone()))?;
    registry.register(Box::new(error_counter.clone()))?;
    
    println!("开始模拟请求并收集指标...");
    
    // 模拟一些请求
    for i in 0..10 {
        let start = std::time::Instant::now();
        
        // 模拟请求
        request_counter.with_label_values(&["GET", "/api/data"]).inc();
        
        // 模拟不同的响应时间
        let delay = if i % 3 == 0 { 100 } else if i % 3 == 1 { 500 } else { 50 };
        sleep(Duration::from_millis(delay)).await;
        
        let duration = start.elapsed();
        request_duration.observe(duration.as_secs_f64());
        
        // 模拟一些错误
        if i % 4 == 0 {
            error_counter.with_label_values(&["500"]).inc();
        }
        
        println!("请求 {} 完成，耗时: {:?}", i + 1, duration);
    }
    
    // 输出 Prometheus 格式的指标
    println!("\n=== Prometheus 指标 ===");
    let metric_families = registry.gather();
    let encoder = TextEncoder::new();
    let mut buffer = Vec::new();
    encoder.encode(&metric_families, &mut buffer)?;
    println!("{}", String::from_utf8(buffer)?);
    
    Ok(())
}
