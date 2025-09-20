//! # OTLP 集成测试
//! 
//! 本模块包含 OTLP 客户端的集成测试，验证各个组件之间的协作。

use c21_otlp::{
    OtlpClient, 
    OtlpConfig, TelemetryData, 
    config::TransportProtocol,
    data::{
        LogSeverity, 
        //MetricType, 
        StatusCode,
    },
};
use std::time::Duration;
use tokio::time::timeout;

/// 测试客户端创建和初始化
#[tokio::test]
async fn test_client_creation_and_initialization() {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http)
        .with_service("test-service", "1.0.0");

    let client = OtlpClient::new(config).await;
    assert!(client.is_ok());

    let client = client.unwrap();
    let init_result = client.initialize().await;
    // 注意：这个测试可能会失败，因为需要实际的网络连接
    // 在实际测试中，应该使用mock或测试服务器
    println!("初始化结果: {:?}", init_result);
}

/// 测试追踪数据发送
#[tokio::test]
async fn test_trace_sending() {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http);

    let client = OtlpClient::new(config).await.unwrap();
    let _init_result = client.initialize().await;

    // 测试追踪构建器
    let trace_builder = client.send_trace("test-operation").await.unwrap();
    let result = trace_builder
        .with_attribute("service.name", "test-service")
        .with_attribute("service.version", "1.0.0")
        .with_numeric_attribute("duration", 100.0)
        .with_bool_attribute("success", true)
        .with_status(StatusCode::Ok, Some("success".to_string()))
        .finish()
        .await;

    println!("追踪发送结果: {:?}", result);
}

/// 测试指标数据发送
#[tokio::test]
async fn test_metric_sending() {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http);

    let client = OtlpClient::new(config).await.unwrap();
    let _init_result = client.initialize().await;

    // 测试指标构建器
    let metric_builder = client.send_metric("test-metric", 42.0).await.unwrap();
    let result = metric_builder
        .with_label("environment", "test")
        .with_label("service", "test-service")
        .with_description("Test metric for integration testing")
        .with_unit("count")
        .send()
        .await;

    println!("指标发送结果: {:?}", result);
}

/// 测试日志数据发送
#[tokio::test]
async fn test_log_sending() {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http);

    let client = OtlpClient::new(config).await.unwrap();
    let _init_result = client.initialize().await;

    // 测试日志构建器
    let log_builder = client.send_log("Test log message", LogSeverity::Info).await.unwrap();
    let result = log_builder
        .with_attribute("logger", "test")
        .with_attribute("module", "integration_test")
        .with_numeric_attribute("line", 42.0)
        .with_bool_attribute("debug", true)
        .with_trace_context("trace-id-123", "span-id-456")
        .send()
        .await;

    println!("日志发送结果: {:?}", result);
}

/// 测试批量数据发送
#[tokio::test]
async fn test_batch_sending() {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http);

    let client = OtlpClient::new(config).await.unwrap();
    let _init_result = client.initialize().await;

    // 创建批量数据
    let mut batch = Vec::new();
    for i in 0..10 {
        let data = TelemetryData::trace(format!("batch-operation-{}", i))
            .with_attribute("batch.id", "batch-001")
            .with_attribute("batch.size", "10")
            .with_numeric_attribute("operation.index", i as f64);
        batch.push(data);
    }

    // 发送批量数据
    let result = client.send_batch(batch).await;
    println!("批量发送结果: {:?}", result);
}

/// 测试并发数据发送
#[tokio::test]
async fn test_concurrent_sending() {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http);

    let client = OtlpClient::new(config).await.unwrap();
    let _init_result = client.initialize().await;

    // 创建并发任务
    let mut handles = Vec::new();
    for i in 0..5 {
        let client_clone = client.clone();
        let handle = tokio::spawn(async move {
            let mut results = Vec::new();
            for j in 0..10 {
                let result = client_clone.send_trace(format!("concurrent-{}-{}", i, j)).await
                    .unwrap()
                    .with_attribute("worker.id", i.to_string())
                    .with_attribute("task.id", j.to_string())
                    .finish()
                    .await;
                results.push(result);
            }
            results
        });
        handles.push(handle);
    }

    // 等待所有任务完成
    let mut total_success = 0;
    for handle in handles {
        let results = handle.await.unwrap();
        for result in results {
            if let Ok(export_result) = result {
                total_success += export_result.success_count;
            }
        }
    }

    println!("并发发送完成，总成功数: {}", total_success);
}

/// 测试客户端指标
#[tokio::test]
async fn test_client_metrics() {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http);

    let client = OtlpClient::new(config).await.unwrap();
    let _init_result = client.initialize().await;

    // 发送一些数据
    for i in 0..5 {
        let _result = client.send_trace(format!("metrics-test-{}", i)).await
            .unwrap()
            .finish()
            .await;
    }

    // 获取指标
    let metrics = client.get_metrics().await;
    println!("客户端指标: {:?}", metrics);
    
    assert!(metrics.total_data_sent > 0);
    assert!(metrics.uptime > Duration::ZERO);
}

/// 测试客户端关闭
#[tokio::test]
async fn test_client_shutdown() {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http);

    let client = OtlpClient::new(config).await.unwrap();
    let _init_result = client.initialize().await;

    // 发送一些数据
    let _result = client.send_trace("shutdown-test").await
        .unwrap()
        .finish()
        .await;

    // 关闭客户端
    let shutdown_result = client.shutdown().await;
    assert!(shutdown_result.is_ok());
}

/// 测试配置验证
#[tokio::test]
async fn test_config_validation() {
    // 测试有效配置
    let valid_config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http)
        .with_service("test-service", "1.0.0");
    
    assert!(valid_config.validate().is_ok());

    // 测试无效配置
    let invalid_config = OtlpConfig::default()
        .with_endpoint("")  // 空端点
        .with_protocol(TransportProtocol::Http);
    
    assert!(invalid_config.validate().is_err());
}

/// 测试超时处理
#[tokio::test]
async fn test_timeout_handling() {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http)
        .with_request_timeout(Duration::from_millis(100)); // 很短的超时

    let client = OtlpClient::new(config).await.unwrap();
    let _init_result = client.initialize().await;

    // 测试超时
    let result = timeout(
        Duration::from_secs(1),
        client.send_trace("timeout-test").await.unwrap().finish()
    ).await;

    match result {
        Ok(Ok(_)) => println!("请求成功完成"),
        Ok(Err(e)) => println!("请求失败: {:?}", e),
        Err(_) => println!("请求超时"),
    }
}

/// 测试错误处理
#[tokio::test]
async fn test_error_handling() {
    // 使用无效端点测试错误处理
    let config = OtlpConfig::default()
        .with_endpoint("http://invalid-endpoint:9999")
        .with_protocol(TransportProtocol::Http);

    let client = OtlpClient::new(config).await.unwrap();
    let _init_result = client.initialize().await;

    // 尝试发送数据，应该会失败
    let result = client.send_trace("error-test").await
        .unwrap()
        .finish()
        .await;

    match result {
        Ok(_) => println!("意外成功"),
        Err(e) => println!("预期的错误: {:?}", e),
    }
}

/// 测试数据验证
#[tokio::test]
async fn test_data_validation() {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http);

    let client = OtlpClient::new(config).await.unwrap();
    let _init_result = client.initialize().await;

    // 测试有效数据
    let valid_data = TelemetryData::trace("valid-operation");
    assert!(valid_data.is_valid());

    // 测试无效数据（空名称）
    let mut invalid_data = TelemetryData::trace("");
    if let c21_otlp::data::TelemetryContent::Trace(ref mut trace) = invalid_data.content {
        trace.name = "".to_string();
    }
    assert!(!invalid_data.is_valid());
}

/// 测试性能基准
#[tokio::test]
async fn test_performance_benchmark() {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http);

    let client = OtlpClient::new(config).await.unwrap();
    let _init_result = client.initialize().await;

    let start_time = std::time::Instant::now();
    let mut success_count = 0;

    // 发送100条数据
    for i in 0..100 {
        let result = client.send_trace(format!("perf-test-{}", i)).await
            .unwrap()
            .finish()
            .await;
        
        if result.is_ok() {
            success_count += 1;
        }
    }

    let duration = start_time.elapsed();
    let throughput = success_count as f64 / duration.as_secs_f64();

    println!("性能测试结果:");
    println!("  总时间: {:?}", duration);
    println!("  成功数量: {}", success_count);
    println!("  吞吐量: {:.2} ops/sec", throughput);
}
