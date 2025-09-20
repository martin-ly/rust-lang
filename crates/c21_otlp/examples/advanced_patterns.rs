//! # OTLP高级设计模式示例
//! 
//! 展示基于Rust 1.90的同步异步结合OTLP设计模式的最佳实践。

use c21_otlp::{
    OtlpClient, OtlpConfig, TelemetryData,
    data::{
        //LogSeverity, 
        StatusCode, 
        //MetricType, 
        SpanKind,
    },
    config::{TransportProtocol, Compression, BatchConfig, RetryConfig},
};
use std::time::Duration;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{RwLock, Semaphore};
use tokio::time::{
    sleep, 
    //interval, 
    //timeout,
};
use futures::future::{
    join_all, 
    //try_join_all,
};
//use serde::{Serialize, Deserialize};

/// 高级设计模式示例
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🎯 OTLP高级设计模式示例");
    
    // 运行各种高级模式示例
    builder_pattern_example().await?;
    strategy_pattern_example().await?;
    observer_pattern_example().await?;
    factory_pattern_example().await?;
    pool_pattern_example().await?;
    circuit_breaker_pattern_example().await?;
    
    println!("✅ 所有高级模式示例执行完成！");
    Ok(())
}

/// 建造者模式示例
async fn builder_pattern_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🏗️ 建造者模式示例");
    
    // 使用建造者模式创建复杂配置
    let config = OtlpConfigBuilder::new()
        .endpoint("http://localhost:4317")
        .protocol(TransportProtocol::Grpc)
        .compression(Compression::Gzip)
        .service("builder-example", "1.0.0")
        .request_timeout(Duration::from_secs(10))
        .auth("api-key-123")
        .tls(true)
        .batch_size(256)
        .retry_count(3)
        .build()?;
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 使用建造者模式创建复杂数据
    let trace_data = TelemetryDataBuilder::trace("complex-operation")
        .with_span_kind(SpanKind::Server)
        .with_attribute("service.name", "builder-service")
        .with_attribute("service.version", "1.0.0")
        .with_numeric_attribute("request.size", 1024.0)
        .with_bool_attribute("cache.hit", false)
        .with_status(StatusCode::Ok, Some("操作成功".to_string()))
        .with_event("request.received", HashMap::new())
        .with_event("response.sent", HashMap::new())
        .build();
    
    let result = client.send(trace_data).await?;
    println!("  🏗️ 建造者模式数据发送: 成功 {} 条", result.success_count);
    
    client.shutdown().await?;
    Ok(())
}

/// 策略模式示例
async fn strategy_pattern_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🎯 策略模式示例");
    
    // 不同的传输策略
    let strategies = vec![
        ("gRPC策略", TransportProtocol::Grpc),
        ("HTTP策略", TransportProtocol::Http),
    ];
    
    for (name, protocol) in strategies {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(protocol)
            .with_service("strategy-example", "1.0.0");
        
        let client = OtlpClient::new(config).await?;
        client.initialize().await?;
        
        let result = client.send_trace(format!("{}-operation", name)).await?
            .with_attribute("strategy", name)
            .with_attribute("protocol", format!("{:?}", protocol))
            .finish()
            .await?;
        
        println!("  🎯 {}数据发送: 成功 {} 条", name, result.success_count);
        
        client.shutdown().await?;
    }
    
    // 不同的压缩策略
    let compression_strategies = vec![
        ("无压缩", Compression::None),
        ("Gzip压缩", Compression::Gzip),
        ("Brotli压缩", Compression::Brotli),
    ];
    
    for (name, compression) in compression_strategies {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(TransportProtocol::Http)
            .with_compression(compression)
            .with_service("compression-example", "1.0.0");
        
        let client = OtlpClient::new(config).await?;
        client.initialize().await?;
        
        let result = client.send_trace(format!("{}-operation", name)).await?
            .with_attribute("compression", name)
            .finish()
            .await?;
        
        println!("  🗜️ {}数据发送: 成功 {} 条", name, result.success_count);
        
        client.shutdown().await?;
    }
    
    Ok(())
}

/// 观察者模式示例
async fn observer_pattern_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n👁️ 观察者模式示例");
    
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("observer-example", "1.0.0");
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 创建指标观察者
    let metrics_observer = MetricsObserver::new();
    let metrics_observer = Arc::new(metrics_observer);
    
    // 模拟数据发送并观察指标变化
    for i in 0..5 {
        let result = client.send_trace(format!("observed-operation-{}", i)).await?
            .with_attribute("observation", "true")
            .with_numeric_attribute("iteration", i as f64)
            .finish()
            .await?;
        
        // 通知观察者
        metrics_observer.notify_operation_completed(result.success_count as usize).await;
        
        // 获取当前指标
        let current_metrics = metrics_observer.get_metrics().await;
        println!("  👁️ 观察指标 - 总操作数: {}, 成功率: {:.2}%", 
                current_metrics.total_operations,
                current_metrics.success_rate);
        
        sleep(Duration::from_millis(200)).await;
    }
    
    client.shutdown().await?;
    Ok(())
}

/// 工厂模式示例
async fn factory_pattern_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🏭 工厂模式示例");
    
    // 使用工厂创建不同类型的客户端
    let client_types = vec![
        ("高性能客户端", ClientType::HighPerformance),
        ("标准客户端", ClientType::Standard),
        ("轻量级客户端", ClientType::Lightweight),
    ];
    
    for (name, client_type) in client_types {
        let client = ClientFactory::create_client(client_type, "factory-example", "1.0.0").await?;
        
        let result = client.send_trace(format!("{}-operation", name)).await?
            .with_attribute("client_type", name)
            .with_attribute("factory_created", "true")
            .finish()
            .await?;
        
        println!("  🏭 {}数据发送: 成功 {} 条", name, result.success_count);
        
        client.shutdown().await?;
    }
    
    Ok(())
}

/// 连接池模式示例
async fn pool_pattern_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n🏊 连接池模式示例");
    
    // 创建连接池
    let pool = ConnectionPool::new(3, "pool-example", "1.0.0").await?;
    
    // 并发使用连接池
    let mut tasks = Vec::new();
    
    for i in 0..10 {
        let pool_clone = pool.clone();
        let task = tokio::spawn(async move {
            let client = pool_clone.get_client().await;
            let result = client.send_trace(format!("pool-operation-{}", i)).await?
                .with_attribute("pool_id", "pool-001")
                .with_attribute("operation_id", i.to_string())
                .finish()
                .await?;
            
            Ok::<_, Box<dyn std::error::Error + Send + Sync>>(result)
        });
        tasks.push(task);
    }
    
    // 等待所有任务完成
    let results = join_all(tasks).await;
    let mut total_success = 0;
    
    for result in results {
        match result {
            Ok(Ok(export_result)) => {
                total_success += export_result.success_count;
            }
            Ok(Err(e)) => println!("  ❌ 池操作失败: {}", e),
            Err(e) => println!("  ❌ 任务执行失败: {}", e),
        }
    }
    
    println!("  🏊 连接池处理总计: 成功 {} 条", total_success);
    
    pool.shutdown().await?;
    Ok(())
}

/// 熔断器模式示例
async fn circuit_breaker_pattern_example() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n⚡ 熔断器模式示例");
    
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("circuit-breaker-example", "1.0.0");
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 创建熔断器
    let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(10));
    
    // 模拟正常操作
    for i in 0..3 {
        match circuit_breaker.execute(|| {
            let client = client.clone();
            async move {
                client.send_trace(format!("normal-operation-{}", i)).await?
                    .with_attribute("circuit_breaker", "normal")
                    .finish()
                    .await
            }
        }).await {
            Ok(result) => println!("  ✅ 正常操作 {}: 成功 {} 条", i + 1, result.success_count),
            Err(e) => println!("  ❌ 正常操作 {} 失败: {}", i + 1, e),
        }
    }
    
    // 模拟失败操作（触发熔断器）
    for i in 0..7 {
        match circuit_breaker.execute(|| {
            async move {
                // 故意使用无效配置来模拟失败
                let invalid_config = OtlpConfig::default()
                    .with_endpoint("http://invalid-endpoint:9999")
                    .with_request_timeout(Duration::from_millis(100));
                
                let invalid_client = OtlpClient::new(invalid_config).await?;
                invalid_client.send_trace(format!("failing-operation-{}", i)).await?
                    .finish()
                    .await
            }
        }).await {
            Ok(result) => println!("  ✅ 失败操作 {}: 意外成功 {} 条", i + 1, result.success_count),
            Err(e) => println!("  ❌ 失败操作 {}: {}", i + 1, e),
        }
    }
    
    // 等待熔断器恢复
    println!("  ⏳ 等待熔断器恢复...");
    sleep(Duration::from_secs(2)).await;
    
    // 尝试恢复操作
    match circuit_breaker.execute(|| {
        let client = client.clone();
        async move {
            client.send_trace("recovery-operation").await?
                .with_attribute("circuit_breaker", "recovery")
                .finish()
                .await
        }
    }).await {
        Ok(result) => println!("  🔄 恢复操作: 成功 {} 条", result.success_count),
        Err(e) => println!("  ❌ 恢复操作失败: {}", e),
    }
    
    client.shutdown().await?;
    Ok(())
}

// 辅助结构和实现

/// 配置建造者
struct OtlpConfigBuilder {
    config: OtlpConfig,
}

impl OtlpConfigBuilder {
    fn new() -> Self {
        Self {
            config: OtlpConfig::default(),
        }
    }
    
    fn endpoint(mut self, endpoint: &str) -> Self {
        self.config = self.config.with_endpoint(endpoint);
        self
    }
    
    fn protocol(mut self, protocol: TransportProtocol) -> Self {
        self.config = self.config.with_protocol(protocol);
        self
    }
    
    fn compression(mut self, compression: Compression) -> Self {
        self.config = self.config.with_compression(compression);
        self
    }
    
    fn service(mut self, name: &str, version: &str) -> Self {
        self.config = self.config.with_service(name, version);
        self
    }
    
    fn request_timeout(mut self, timeout: Duration) -> Self {
        self.config = self.config.with_request_timeout(timeout);
        self
    }
    
    fn auth(mut self, api_key: &str) -> Self {
        self.config = self.config.with_api_key(api_key);
        self
    }
    
    fn tls(mut self, enabled: bool) -> Self {
        self.config = self.config.with_tls(enabled);
        self
    }
    
    fn batch_size(mut self, size: usize) -> Self {
        let batch_config = BatchConfig {
            max_export_batch_size: size,
            export_timeout: Duration::from_secs(30),
            max_queue_size: size * 4,
            scheduled_delay: Duration::from_millis(5000),
        };
        self.config = self.config.with_batch_config(batch_config);
        self
    }
    
    fn retry_count(mut self, count: usize) -> Self {
        let retry_config = RetryConfig {
            max_retries: count,
            initial_retry_delay: Duration::from_millis(1000),
            max_retry_delay: Duration::from_secs(30),
            retry_delay_multiplier: 2.0,
            randomize_retry_delay: true,
        };
        self.config = self.config.with_retry_config(retry_config);
        self
    }
    
    fn build(self) -> Result<OtlpConfig, Box<dyn std::error::Error>> {
        self.config.validate()?;
        Ok(self.config)
    }
}

/// 数据建造者
struct TelemetryDataBuilder {
    data: TelemetryData,
}

impl TelemetryDataBuilder {
    fn trace(name: &str) -> Self {
        Self {
            data: TelemetryData::trace(name),
        }
    }
    
    fn with_span_kind(mut self, kind: SpanKind) -> Self {
        if let c21_otlp::data::TelemetryContent::Trace(ref mut trace_data) = self.data.content {
            trace_data.span_kind = kind;
        }
        self
    }
    
    fn with_attribute(mut self, key: &str, value: &str) -> Self {
        self.data = self.data.with_attribute(key, value);
        self
    }
    
    fn with_numeric_attribute(mut self, key: &str, value: f64) -> Self {
        self.data = self.data.with_numeric_attribute(key, value);
        self
    }
    
    fn with_bool_attribute(mut self, key: &str, value: bool) -> Self {
        self.data = self.data.with_bool_attribute(key, value);
        self
    }
    
    fn with_status(mut self, code: StatusCode, message: Option<String>) -> Self {
        self.data = self.data.with_status(code, message);
        self
    }
    
    fn with_event(mut self, name: &str, attributes: HashMap<String, c21_otlp::data::AttributeValue>) -> Self {
        self.data = self.data.with_event(name, attributes);
        self
    }
    
    fn build(self) -> TelemetryData {
        self.data
    }
}

/// 指标观察者
#[derive(Debug)]
struct MetricsObserver {
    total_operations: u64,
    successful_operations: u64,
    failed_operations: u64,
}

impl MetricsObserver {
    fn new() -> Self {
        Self {
            total_operations: 0,
            successful_operations: 0,
            failed_operations: 0,
        }
    }
    
    async fn notify_operation_completed(&self, success_count: usize) {
        // 在实际实现中，这里会更新指标
        println!("    📊 操作完成通知: 成功 {} 条", success_count);
    }
    
    async fn get_metrics(&self) -> ObserverMetrics {
        ObserverMetrics {
            total_operations: self.total_operations,
            successful_operations: self.successful_operations,
            failed_operations: self.failed_operations,
            success_rate: if self.total_operations > 0 {
                (self.successful_operations as f64 / self.total_operations as f64) * 100.0
            } else {
                0.0
            },
        }
    }
}

#[allow(dead_code)]
#[derive(Debug)]
struct ObserverMetrics {
    total_operations: u64,
    successful_operations: u64,
    failed_operations: u64,
    success_rate: f64,
}

/// 客户端类型
#[allow(dead_code)]
#[derive(Debug, Clone)]
enum ClientType {
    HighPerformance,
    Standard,
    Lightweight,
}

/// 客户端工厂
#[allow(dead_code)]
struct ClientFactory;

impl ClientFactory {
    async fn create_client(
        client_type: ClientType,
        service_name: &str,
        service_version: &str,
    ) -> Result<OtlpClient, Box<dyn std::error::Error>> {
        let config = match client_type {
            ClientType::HighPerformance => {
                OtlpConfig::default()
                    .with_endpoint("http://localhost:4317")
                    .with_protocol(TransportProtocol::Grpc)
                    .with_compression(Compression::Gzip)
                    .with_service(service_name, service_version)
                    .with_batch_config(BatchConfig {
                        max_export_batch_size: 1024,
                        export_timeout: Duration::from_secs(5),
                        max_queue_size: 4096,
                        scheduled_delay: Duration::from_millis(1000),
                    })
            }
            ClientType::Standard => {
                OtlpConfig::default()
                    .with_endpoint("http://localhost:4317")
                    .with_protocol(TransportProtocol::Grpc)
                    .with_service(service_name, service_version)
            }
            ClientType::Lightweight => {
                OtlpConfig::default()
                    .with_endpoint("http://localhost:4317")
                    .with_protocol(TransportProtocol::Http)
                    .with_service(service_name, service_version)
                    .with_batch_config(BatchConfig {
                        max_export_batch_size: 64,
                        export_timeout: Duration::from_secs(30),
                        max_queue_size: 256,
                        scheduled_delay: Duration::from_millis(10000),
                    })
            }
        };
        
        let client = OtlpClient::new(config).await?;
        client.initialize().await?;
        Ok(client)
    }
}

/// 连接池
#[allow(dead_code)]
#[derive(Clone)]
struct ConnectionPool {
    clients: Arc<RwLock<Vec<OtlpClient>>>,
    semaphore: Arc<Semaphore>,
}

impl ConnectionPool {
    async fn new(pool_size: usize, service_name: &str, service_version: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let mut clients = Vec::new();
        
        for _ in 0..pool_size {
            let config = OtlpConfig::default()
                .with_endpoint("http://localhost:4317")
                .with_protocol(TransportProtocol::Grpc)
                .with_service(service_name, service_version);
            
            let client = OtlpClient::new(config).await?;
            client.initialize().await?;
            clients.push(client);
        }
        
        Ok(Self {
            clients: Arc::new(RwLock::new(clients)),
            semaphore: Arc::new(Semaphore::new(pool_size)),
        })
    }
    
    async fn get_client(&self) -> OtlpClient {
        let _permit = self.semaphore.acquire().await.unwrap();
        let clients = self.clients.read().await;
        clients[0].clone() // 简化实现，实际应该使用轮询或随机选择
    }
    
    async fn shutdown(&self) -> Result<(), Box<dyn std::error::Error>> {
        let clients = self.clients.read().await;
        for client in clients.iter() {
            client.shutdown().await?;
        }
        Ok(())
    }
}

/// 熔断器
struct CircuitBreaker {
    failure_threshold: usize,
    timeout: Duration,
    failure_count: Arc<RwLock<usize>>,
    last_failure_time: Arc<RwLock<Option<std::time::Instant>>>,
    state: Arc<RwLock<CircuitState>>,
}

#[derive(Debug, Clone)]
enum CircuitState {
    Closed,
    Open,
    HalfOpen,
}

impl CircuitBreaker {
    fn new(failure_threshold: usize, timeout: Duration) -> Self {
        Self {
            failure_threshold,
            timeout,
            failure_count: Arc::new(RwLock::new(0)),
            last_failure_time: Arc::new(RwLock::new(None)),
            state: Arc::new(RwLock::new(CircuitState::Closed)),
        }
    }
    
    async fn execute<F, Fut, T>(&self, operation: F) -> Result<T, Box<dyn std::error::Error>>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = Result<T, c21_otlp::error::OtlpError>>,
    {
        let state = self.state.read().await;
        match *state {
            CircuitState::Open => {
                let last_failure = self.last_failure_time.read().await;
                if let Some(last_failure_time) = *last_failure {
                    if last_failure_time.elapsed() >= self.timeout {
                        drop(state);
                        drop(last_failure);
                        *self.state.write().await = CircuitState::HalfOpen;
                        return Box::pin(self.execute(operation)).await;
                    }
                }
                return Err("熔断器开启，拒绝请求".into());
            }
            CircuitState::HalfOpen => {
                drop(state);
                match operation().await {
                    Ok(result) => {
                        self.reset().await;
                        Ok(result)
                    }
                    Err(e) => {
                        self.record_failure().await;
                        Err(Box::new(e))
                    }
                }
            }
            CircuitState::Closed => {
                drop(state);
                match operation().await {
                    Ok(result) => {
                        self.reset().await;
                        Ok(result)
                    }
                    Err(e) => {
                        self.record_failure().await;
                        Err(Box::new(e))
                    }
                }
            }
        }
    }
    
    async fn record_failure(&self) {
        let mut failure_count = self.failure_count.write().await;
        *failure_count += 1;
        
        if *failure_count >= self.failure_threshold {
            *self.state.write().await = CircuitState::Open;
            *self.last_failure_time.write().await = Some(std::time::Instant::now());
        }
    }
    
    async fn reset(&self) {
        *self.failure_count.write().await = 0;
        *self.last_failure_time.write().await = None;
        *self.state.write().await = CircuitState::Closed;
    }
}
