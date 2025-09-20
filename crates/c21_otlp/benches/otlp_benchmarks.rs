//! # OTLP 性能基准测试
//! 
//! 本模块包含 OTLP 客户端的性能基准测试，用于评估不同场景下的性能表现。

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use c21_otlp::{
    OtlpClient, OtlpConfig, TelemetryData,
    config::TransportProtocol,
    data::{LogSeverity, MetricType, StatusCode},
};
use std::time::Duration;
use tokio::runtime::Runtime;

/// 创建测试客户端
fn create_test_client() -> OtlpClient {
    let rt = Runtime::new().unwrap();
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Http)
        .with_service("benchmark-service", "1.0.0");

    rt.block_on(async {
        let client = OtlpClient::new(config).await.unwrap();
        let _ = client.initialize().await; // 忽略初始化错误
        client
    })
}

/// 创建测试数据
fn create_test_trace_data(count: usize) -> Vec<TelemetryData> {
    (0..count)
        .map(|i| {
            TelemetryData::trace(format!("benchmark-operation-{}", i))
                .with_attribute("service.name", "benchmark-service")
                .with_attribute("service.version", "1.0.0")
                .with_numeric_attribute("duration", (i * 10) as f64)
                .with_bool_attribute("success", i % 2 == 0)
                .with_status(StatusCode::Ok, Some("success".to_string()))
        })
        .collect()
}

fn create_test_metric_data(count: usize) -> Vec<TelemetryData> {
    (0..count)
        .map(|i| {
            TelemetryData::metric(format!("benchmark-metric-{}", i), MetricType::Counter)
                .with_attribute("environment", "benchmark")
                .with_attribute("service", "benchmark-service")
        })
        .collect()
}

fn create_test_log_data(count: usize) -> Vec<TelemetryData> {
    (0..count)
        .map(|i| {
            TelemetryData::log(
                format!("Benchmark log message {}", i),
                LogSeverity::Info
            )
            .with_attribute("logger", "benchmark")
            .with_attribute("module", "benchmark_test")
            .with_numeric_attribute("line", i as f64)
        })
        .collect()
}

/// 基准测试：单个追踪数据发送
fn benchmark_single_trace_send(c: &mut Criterion) {
    let client = create_test_client();
    let rt = Runtime::new().unwrap();

    c.bench_function("single_trace_send", |b| {
        b.iter(|| {
            rt.block_on(async {
                let result = client.send_trace("benchmark-operation").await
                    .unwrap()
                    .with_attribute("service.name", "benchmark-service")
                    .with_numeric_attribute("duration", 100.0)
                    .finish()
                    .await;
                black_box(result)
            })
        })
    });
}

/// 基准测试：批量追踪数据发送
fn benchmark_batch_trace_send(c: &mut Criterion) {
    let client = create_test_client();
    let rt = Runtime::new().unwrap();

    let mut group = c.benchmark_group("batch_trace_send");
    
    for size in [10, 50, 100, 500, 1000].iter() {
        let data = create_test_trace_data(*size);
        
        group.bench_with_input(BenchmarkId::new("size", size), size, |b, _| {
            b.iter(|| {
                rt.block_on(async {
                    let result = client.send_batch(data.clone()).await;
                    black_box(result)
                })
            })
        });
    }
    
    group.finish();
}

/// 基准测试：并发追踪数据发送
fn benchmark_concurrent_trace_send(c: &mut Criterion) {
    let client = create_test_client();
    let rt = Runtime::new().unwrap();

    let mut group = c.benchmark_group("concurrent_trace_send");
    
    for concurrency in [1, 5, 10, 20, 50].iter() {
        group.bench_with_input(BenchmarkId::new("concurrency", concurrency), concurrency, |b, &concurrency| {
            b.iter(|| {
                rt.block_on(async {
                    let mut handles = Vec::new();
                    
                    for i in 0..concurrency {
                        let client_clone = client.clone();
                        let handle = tokio::spawn(async move {
                            let result = client_clone.send_trace(format!("concurrent-{}", i)).await
                                .unwrap()
                                .with_attribute("worker.id", i.to_string())
                                .finish()
                                .await;
                            result
                        });
                        handles.push(handle);
                    }
                    
                    let mut results = Vec::new();
                    for handle in handles {
                        let result = handle.await.unwrap();
                        results.push(result);
                    }
                    
                    black_box(results)
                })
            })
        });
    }
    
    group.finish();
}

/// 基准测试：数据创建性能
fn benchmark_data_creation(c: &mut Criterion) {
    let mut group = c.benchmark_group("data_creation");
    
    // 追踪数据创建
    group.bench_function("trace_creation", |b| {
        b.iter(|| {
            let data = TelemetryData::trace("benchmark-operation")
                .with_attribute("service.name", "benchmark-service")
                .with_numeric_attribute("duration", 100.0)
                .with_bool_attribute("success", true)
                .with_status(StatusCode::Ok, Some("success".to_string()));
            black_box(data)
        })
    });
    
    // 指标数据创建
    group.bench_function("metric_creation", |b| {
        b.iter(|| {
            let data = TelemetryData::metric("benchmark-metric", MetricType::Counter)
                .with_attribute("environment", "benchmark")
                .with_attribute("service", "benchmark-service");
            black_box(data)
        })
    });
    
    // 日志数据创建
    group.bench_function("log_creation", |b| {
        b.iter(|| {
            let data = TelemetryData::log("Benchmark log message", LogSeverity::Info)
                .with_attribute("logger", "benchmark")
                .with_numeric_attribute("line", 42.0);
            black_box(data)
        })
    });
    
    group.finish();
}

/// 基准测试：数据序列化性能
fn benchmark_data_serialization(c: &mut Criterion) {
    let mut group = c.benchmark_group("data_serialization");
    
    let trace_data = create_test_trace_data(100);
    let metric_data = create_test_metric_data(100);
    let log_data = create_test_log_data(100);
    
    // JSON序列化
    group.bench_function("json_serialization_trace", |b| {
        b.iter(|| {
            let json = serde_json::to_vec(&trace_data).unwrap();
            black_box(json)
        })
    });
    
    group.bench_function("json_serialization_metric", |b| {
        b.iter(|| {
            let json = serde_json::to_vec(&metric_data).unwrap();
            black_box(json)
        })
    });
    
    group.bench_function("json_serialization_log", |b| {
        b.iter(|| {
            let json = serde_json::to_vec(&log_data).unwrap();
            black_box(json)
        })
    });
    
    group.finish();
}

/// 基准测试：配置验证性能
fn benchmark_config_validation(c: &mut Criterion) {
    c.bench_function("config_validation", |b| {
        b.iter(|| {
            let config = OtlpConfig::default()
                .with_endpoint("http://localhost:4317")
                .with_protocol(TransportProtocol::Http)
                .with_service("benchmark-service", "1.0.0")
                .with_request_timeout(Duration::from_secs(30))
                .with_sampling_ratio(0.1);
            
            let result = config.validate();
            black_box(result)
        })
    });
}

/// 基准测试：客户端创建性能
fn benchmark_client_creation(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    c.bench_function("client_creation", |b| {
        b.iter(|| {
            rt.block_on(async {
                let config = OtlpConfig::default()
                    .with_endpoint("http://localhost:4317")
                    .with_protocol(TransportProtocol::Http)
                    .with_service("benchmark-service", "1.0.0");
                
                let client = OtlpClient::new(config).await.unwrap();
                black_box(client)
            })
        })
    });
}

/// 基准测试：内存使用
fn benchmark_memory_usage(c: &mut Criterion) {
    let mut group = c.benchmark_group("memory_usage");
    
    for size in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("data_size", size), size, |b, &size| {
            b.iter(|| {
                let data = create_test_trace_data(size);
                let total_size: usize = data.iter().map(|d| d.size()).sum();
                black_box(total_size)
            })
        });
    }
    
    group.finish();
}

/// 基准测试：错误处理性能
fn benchmark_error_handling(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    
    c.bench_function("error_handling", |b| {
        b.iter(|| {
            rt.block_on(async {
                // 使用无效配置测试错误处理性能
                let config = OtlpConfig::default()
                    .with_endpoint("")  // 无效端点
                    .with_protocol(TransportProtocol::Http);
                
                let result = config.validate();
                black_box(result)
            })
        })
    });
}

/// 基准测试：指标收集性能
fn benchmark_metrics_collection(c: &mut Criterion) {
    let client = create_test_client();
    let rt = Runtime::new().unwrap();
    
    // 先发送一些数据
    rt.block_on(async {
        for i in 0..100 {
            let _ = client.send_trace(format!("metrics-test-{}", i)).await
                .unwrap()
                .finish()
                .await;
        }
    });
    
    c.bench_function("metrics_collection", |b| {
        b.iter(|| {
            rt.block_on(async {
                let metrics = client.get_metrics().await;
                black_box(metrics)
            })
        })
    });
}

/// 基准测试：不同协议性能对比
fn benchmark_protocol_comparison(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();
    let data = create_test_trace_data(100);
    
    let mut group = c.benchmark_group("protocol_comparison");
    
    // HTTP协议
    group.bench_function("http_protocol", |b| {
        b.iter(|| {
            rt.block_on(async {
                let config = OtlpConfig::default()
                    .with_endpoint("http://localhost:4317")
                    .with_protocol(TransportProtocol::Http);
                
                let client = OtlpClient::new(config).await.unwrap();
                let _ = client.initialize().await;
                let result = client.send_batch(data.clone()).await;
                black_box(result)
            })
        })
    });
    
    // gRPC协议
    group.bench_function("grpc_protocol", |b| {
        b.iter(|| {
            rt.block_on(async {
                let config = OtlpConfig::default()
                    .with_endpoint("http://localhost:4317")
                    .with_protocol(TransportProtocol::Grpc);
                
                let client = OtlpClient::new(config).await.unwrap();
                let _ = client.initialize().await;
                let result = client.send_batch(data.clone()).await;
                black_box(result)
            })
        })
    });
    
    group.finish();
}

criterion_group!(
    benches,
    benchmark_single_trace_send,
    benchmark_batch_trace_send,
    benchmark_concurrent_trace_send,
    benchmark_data_creation,
    benchmark_data_serialization,
    benchmark_config_validation,
    benchmark_client_creation,
    benchmark_memory_usage,
    benchmark_error_handling,
    benchmark_metrics_collection,
    benchmark_protocol_comparison
);

criterion_main!(benches);
