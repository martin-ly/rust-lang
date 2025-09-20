//! # OTLP综合使用示例
//! 
//! 展示基于Rust 1.90的OTLP客户端库的各种使用场景和最佳实践。

use c21_otlp::{
    OtlpClient, OtlpConfig, TelemetryData,
    data::{LogSeverity, StatusCode, MetricType},
    config::{TransportProtocol, Compression, BatchConfig, RetryConfig},
};
use std::time::Duration;
use tokio::time::{sleep, interval};
use futures::future::join_all;

/// 基础使用示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 OTLP Rust 1.90 综合使用示例");
    
    // 运行各种示例
    basic_usage_example().await?;
    advanced_configuration_example().await?;
    batch_processing_example().await?;
    concurrent_processing_example().await?;
    error_handling_example().await?;
    monitoring_example().await?;
    
    println!("✅ 所有示例执行完成！");
    Ok(())
}

/// 基础使用示例
async fn basic_usage_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📋 基础使用示例");
    
    // 创建基础配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("basic-example", "1.0.0")
        .with_request_timeout(Duration::from_secs(5));
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送追踪数据
    let trace_result = client.send_trace("user-authentication").await?
        .with_attribute("user.id", "12345")
        .with_attribute("user.email", "user@example.com")
        .with_attribute("auth.method", "oauth2")
        .with_numeric_attribute("auth.duration", 250.0)
        .with_bool_attribute("auth.success", true)
        .with_status(StatusCode::Ok, Some("认证成功".to_string()))
        .finish()
        .await?;
    
    println!("  📊 追踪数据发送: 成功 {} 条", trace_result.success_count);
    
    // 发送指标数据
    let metric_result = client.send_metric("http_requests_total", 1.0).await?
        .with_label("method", "POST")
        .with_label("endpoint", "/api/auth")
        .with_label("status", "200")
        .with_description("HTTP请求总数")
        .with_unit("count")
        .send()
        .await?;
    
    println!("  📈 指标数据发送: 成功 {} 条", metric_result.success_count);
    
    // 发送日志数据
    let log_result = client.send_log("用户认证成功", LogSeverity::Info).await?
        .with_attribute("user_id", "12345")
        .with_attribute("ip_address", "192.168.1.100")
        .with_attribute("user_agent", "Mozilla/5.0 (Windows NT 10.0; Win64; x64)")
        .with_trace_context("trace-123", "span-456")
        .send()
        .await?;
    
    println!("  📝 日志数据发送: 成功 {} 条", log_result.success_count);
    
    client.shutdown().await?;
    Ok(())
}

/// 高级配置示例
async fn advanced_configuration_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n⚙️ 高级配置示例");
    
    // 批处理配置
    let batch_config = BatchConfig {
        max_export_batch_size: 256,
        export_timeout: Duration::from_secs(10),
        max_queue_size: 1024,
        scheduled_delay: Duration::from_millis(2000),
    };
    
    // 重试配置
    let retry_config = RetryConfig {
        max_retries: 3,
        initial_retry_delay: Duration::from_millis(500),
        max_retry_delay: Duration::from_secs(5),
        retry_delay_multiplier: 2.0,
        randomize_retry_delay: true,
    };
    
    // 高级配置
    let config = OtlpConfig::default()
        .with_endpoint("https://api.example.com/otlp")
        .with_protocol(TransportProtocol::Grpc)
        .with_compression(Compression::Gzip)
        .with_service("advanced-example", "2.0.0")
        .with_sampling_ratio(0.1)
        .with_tls(true)
        .with_api_key("your-api-key-here")
        .with_batch_config(batch_config)
        .with_retry_config(retry_config)
        .with_resource_attribute("environment", "production")
        .with_resource_attribute("region", "us-west-2")
        .with_resource_attribute("datacenter", "dc1")
        .with_debug(true);
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送带有高级配置的数据
    let result = client.send_trace("advanced-operation").await?
        .with_attribute("operation.type", "critical")
        .with_attribute("operation.priority", "high")
        .with_numeric_attribute("operation.complexity", 8.5)
        .with_status(StatusCode::Ok, Some("高级操作完成".to_string()))
        .finish()
        .await?;
    
    println!("  🔧 高级配置数据发送: 成功 {} 条", result.success_count);
    
    client.shutdown().await?;
    Ok(())
}

/// 批量处理示例
async fn batch_processing_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📦 批量处理示例");
    
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http)
        .with_service("batch-example", "1.0.0");
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 创建批量数据
    let mut batch_data = Vec::new();
    
    for i in 0..50 {
        let trace_data = TelemetryData::trace(format!("batch-operation-{}", i))
            .with_attribute("batch_id", "batch-001")
            .with_attribute("operation_index", i.to_string())
            .with_attribute("operation_type", "data_processing")
            .with_numeric_attribute("processing_time", (i * 5) as f64)
            .with_bool_attribute("success", i % 10 != 0); // 90% 成功率
        
        batch_data.push(trace_data);
    }
    
    // 批量发送
    let result = client.send_batch(batch_data).await?;
    println!("  📦 批量数据发送: 成功 {} 条", result.success_count);
    
    // 分批处理示例
    let mut all_data = Vec::new();
    for i in 0..200 {
        let data = TelemetryData::metric(format!("metric_{}", i), MetricType::Gauge)
            .with_attribute("metric_type", "performance")
            .with_attribute("metric_index", i.to_string());
        all_data.push(data);
    }
    
    // 分批发送（每批50条）
    let batch_size = 50;
    for chunk in all_data.chunks(batch_size) {
        let result = client.send_batch(chunk.to_vec()).await?;
        println!("  📊 分批发送: 成功 {} 条", result.success_count);
        sleep(Duration::from_millis(100)).await; // 避免过快发送
    }
    
    client.shutdown().await?;
    Ok(())
}

/// 并发处理示例
async fn concurrent_processing_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🔄 并发处理示例");
    
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("concurrent-example", "1.0.0");
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 并发发送追踪数据
    let mut futures = Vec::new();
    
    for i in 0..20 {
        let client_clone = client.clone();
        let future = tokio::spawn(async move {
            let result = client_clone.send_trace(format!("concurrent-operation-{}", i)).await?
                .with_attribute("concurrent", "true")
                .with_attribute("worker_id", i.to_string())
                .with_attribute("operation_type", "concurrent_processing")
                .with_numeric_attribute("worker_load", (i * 10) as f64)
                .finish()
                .await?;
            
            Ok::<_, Box<dyn std::error::Error + Send + Sync>>(result)
        });
        futures.push(future);
    }
    
    // 等待所有并发操作完成
    let results = join_all(futures).await;
    let mut total_success = 0;
    
    for result in results {
        match result {
            Ok(Ok(export_result)) => {
                total_success += export_result.success_count;
                println!("  🔄 并发操作完成: 成功 {} 条", export_result.success_count);
            }
            Ok(Err(e)) => println!("  ❌ 并发操作失败: {}", e),
            Err(e) => println!("  ❌ 任务执行失败: {}", e),
        }
    }
    
    println!("  📊 并发处理总计: 成功 {} 条", total_success);
    
    // 异步流处理示例
    let mut interval = interval(Duration::from_millis(500));
    for i in 0..10 {
        interval.tick().await;
        
        let result = client.send_metric("stream_metric", i as f64).await?
            .with_label("stream_id", "stream-001")
            .with_label("iteration", i.to_string())
            .with_description("流式指标")
            .with_unit("count")
            .send()
            .await?;
        
        println!("  🌊 流式处理: 第{}次, 成功 {} 条", i + 1, result.success_count);
    }
    
    client.shutdown().await?;
    Ok(())
}

/// 错误处理示例
async fn error_handling_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n⚠️ 错误处理示例");
    
    // 配置错误处理
    let config = OtlpConfig::default()
        .with_endpoint("http://invalid-endpoint:9999") // 故意使用无效端点
        .with_protocol(TransportProtocol::Http)
        .with_service("error-example", "1.0.0")
        .with_request_timeout(Duration::from_secs(1)); // 短超时
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 尝试发送数据（预期会失败）
    match client.send_trace("error-test").await {
        Ok(trace_builder) => {
            match trace_builder
                .with_attribute("test", "error_handling")
                .finish()
                .await
            {
                Ok(result) => println!("  ✅ 意外成功: {} 条", result.success_count),
                Err(e) => println!("  ❌ 预期错误: {}", e),
            }
        }
        Err(e) => println!("  ❌ 客户端错误: {}", e),
    }
    
    // 使用有效配置重试
    let valid_config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("error-recovery", "1.0.0");
    
    let valid_client = OtlpClient::new(valid_config).await?;
    valid_client.initialize().await?;
    
    // 成功发送数据
    let result = valid_client.send_trace("recovery-test").await?
        .with_attribute("recovery", "successful")
        .with_status(StatusCode::Ok, Some("错误恢复成功".to_string()))
        .finish()
        .await?;
    
    println!("  🔄 错误恢复: 成功 {} 条", result.success_count);
    
    valid_client.shutdown().await?;
    Ok(())
}

/// 监控示例
async fn monitoring_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n📊 监控示例");
    
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("monitoring-example", "1.0.0");
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送一些数据以产生指标
    for i in 0..10 {
        let result = client.send_trace(format!("monitoring-operation-{}", i)).await?
            .with_attribute("monitoring", "true")
            .with_numeric_attribute("operation_count", i as f64)
            .finish()
            .await?;
        
        println!("  📈 监控数据发送 {}: 成功 {} 条", i + 1, result.success_count);
        sleep(Duration::from_millis(100)).await;
    }
    
    // 获取并显示客户端指标
    let metrics = client.get_metrics().await;
    
    println!("\n  📊 客户端指标:");
    println!("    - 总发送数据量: {}", metrics.total_data_sent);
    println!("    - 总接收数据量: {}", metrics.total_data_received);
    println!("    - 活跃连接数: {}", metrics.active_connections);
    println!("    - 运行时间: {:?}", metrics.uptime);
    
    println!("\n  📈 导出器指标:");
    println!("    - 总导出次数: {}", metrics.exporter_metrics.total_exports);
    println!("    - 成功导出次数: {}", metrics.exporter_metrics.successful_exports);
    println!("    - 失败导出次数: {}", metrics.exporter_metrics.failed_exports);
    println!("    - 平均导出延迟: {:?}", metrics.exporter_metrics.average_export_latency);
    println!("    - 最大导出延迟: {:?}", metrics.exporter_metrics.max_export_latency);
    
    if metrics.exporter_metrics.total_exports > 0 {
        let success_rate = (metrics.exporter_metrics.successful_exports as f64 / 
                           metrics.exporter_metrics.total_exports as f64) * 100.0;
        println!("    - 导出成功率: {:.2}%", success_rate);
    }
    
    println!("\n  🔧 处理器指标:");
    println!("    - 处理的数据量: {}", metrics.processor_metrics.total_processed);
    println!("    - 批处理次数: {}", metrics.processor_metrics.batch_count);
    println!("    - 平均批处理大小: {:.2}", metrics.processor_metrics.average_batch_size);
    println!("    - 过滤的数据量: {}", metrics.processor_metrics.total_filtered);
    
    client.shutdown().await?;
    Ok(())
}
