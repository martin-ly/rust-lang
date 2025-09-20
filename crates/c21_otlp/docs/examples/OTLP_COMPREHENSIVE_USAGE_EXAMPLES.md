# OTLP 详细使用解释与示例

## 概述

本文档提供OpenTelemetry Protocol (OTLP)在Rust 1.90环境下的详细使用解释和完整示例，涵盖从基础使用到高级应用的各种场景。

## 1. 基础使用示例

### 1.1 环境配置

```rust
// Cargo.toml 依赖配置
[dependencies]
c21_otlp = "0.1.0"
tokio = { version = "1.0", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
chrono = { version = "0.4", features = ["serde"] }
uuid = { version = "1.0", features = ["v4"] }
```

### 1.2 基本客户端初始化

```rust
use c21_otlp::{OtlpClient, OtlpConfig, TelemetryData};
use c21_otlp::data::{LogSeverity, StatusCode};
use c21_otlp::transport::TransportProtocol;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建OTLP配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("example-service", "1.0.0")
        .with_timeout(Duration::from_secs(10))
        .with_debug(true);
    
    // 创建并初始化客户端
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    println!("OTLP客户端初始化成功");
    
    // 关闭客户端
    client.shutdown().await?;
    
    Ok(())
}
```

### 1.3 发送追踪数据

```rust
use c21_otlp::{OtlpClient, OtlpConfig};
use c21_otlp::data::StatusCode;
use std::time::Duration;

async fn send_trace_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送基本追踪数据
    let result = client.send_trace("user_login").await?
        .with_attribute("user.id", "12345")
        .with_attribute("user.email", "user@example.com")
        .with_attribute("login.method", "oauth")
        .with_numeric_attribute("login.duration_ms", 150.0)
        .with_status(StatusCode::Ok, Some("登录成功".to_string()))
        .finish()
        .await?;
    
    println!("追踪数据发送结果: 成功 {} 条", result.success_count);
    println!("追踪ID: {}", result.trace_id);
    println!("跨度ID: {}", result.span_id);
    
    client.shutdown().await?;
    Ok(())
}
```

### 1.4 发送指标数据

```rust
use c21_otlp::{OtlpClient, OtlpConfig};
use std::collections::HashMap;

async fn send_metrics_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送计数器指标
    let result = client.send_metric("http_requests_total", 1.0).await?
        .with_label("method", "GET")
        .with_label("endpoint", "/api/users")
        .with_label("status_code", "200")
        .with_description("HTTP请求总数")
        .with_unit("count")
        .send()
        .await?;
    
    println!("指标数据发送结果: 成功 {} 条", result.success_count);
    
    // 发送直方图指标
    let histogram_result = client.send_histogram("request_duration_seconds", 0.5).await?
        .with_label("service", "user-service")
        .with_label("operation", "get_user")
        .with_bucket(0.1, 10)
        .with_bucket(0.5, 5)
        .with_bucket(1.0, 2)
        .with_bucket(5.0, 1)
        .with_description("请求持续时间")
        .with_unit("seconds")
        .send()
        .await?;
    
    println!("直方图指标发送结果: 成功 {} 条", histogram_result.success_count);
    
    client.shutdown().await?;
    Ok(())
}
```

### 1.5 发送日志数据

```rust
use c21_otlp::{OtlpClient, OtlpConfig};
use c21_otlp::data::LogSeverity;

async fn send_logs_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 发送信息日志
    let info_result = client.send_log("用户登录成功", LogSeverity::Info).await?
        .with_attribute("user.id", "12345")
        .with_attribute("user.email", "user@example.com")
        .with_attribute("login.method", "oauth")
        .with_attribute("ip.address", "192.168.1.100")
        .with_trace_context("trace-123", "span-456")
        .send()
        .await?;
    
    println!("信息日志发送结果: 成功 {} 条", info_result.success_count);
    
    // 发送错误日志
    let error_result = client.send_log("数据库连接失败", LogSeverity::Error).await?
        .with_attribute("error.code", "DB_CONNECTION_FAILED")
        .with_attribute("error.message", "无法连接到数据库服务器")
        .with_attribute("database.host", "db.example.com")
        .with_attribute("database.port", "5432")
        .with_trace_context("trace-789", "span-012")
        .send()
        .await?;
    
    println!("错误日志发送结果: 成功 {} 条", error_result.success_count);
    
    client.shutdown().await?;
    Ok(())
}
```

## 2. 高级使用示例

### 2.1 批量数据处理

```rust
use c21_otlp::{OtlpClient, OtlpConfig, TelemetryData};
use std::time::Duration;

async fn batch_processing_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_batch_config(BatchConfig {
            max_export_batch_size: 100,
            export_timeout: Duration::from_secs(5),
            max_queue_size: 1000,
            scheduled_delay: Duration::from_millis(1000),
        });
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 创建批量数据
    let mut batch_data = Vec::new();
    
    for i in 0..100 {
        let trace_data = TelemetryData::trace(format!("batch_operation_{}", i))
            .with_attribute("batch_id", "batch-001")
            .with_attribute("operation_index", i.to_string())
            .with_attribute("service.name", "batch-service")
            .with_attribute("service.version", "1.0.0");
        
        batch_data.push(trace_data);
    }
    
    // 批量发送
    let result = client.send_batch(batch_data).await?;
    println!("批量发送结果: 成功 {} 条", result.success_count);
    
    client.shutdown().await?;
    Ok(())
}
```

### 2.2 异步并发处理

```rust
use c21_otlp::{OtlpClient, OtlpConfig};
use tokio::task;
use std::time::Duration;

async fn async_concurrent_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 创建多个异步任务
    let mut handles = Vec::new();
    
    for i in 0..10 {
        let client_clone = client.clone();
        let handle = task::spawn(async move {
            // 模拟异步操作
            tokio::time::sleep(Duration::from_millis(100)).await;
            
            let result = client_clone.send_trace(format!("async_operation_{}", i)).await?
                .with_attribute("async", "true")
                .with_attribute("task_id", i.to_string())
                .with_attribute("service.name", "async-service")
                .finish()
                .await?;
            
            Ok::<_, Box<dyn std::error::Error>>(result)
        });
        
        handles.push(handle);
    }
    
    // 等待所有任务完成
    let mut total_success = 0;
    for handle in handles {
        match handle.await? {
            Ok(result) => {
                total_success += result.success_count;
                println!("异步任务完成: 成功 {} 条", result.success_count);
            }
            Err(e) => {
                eprintln!("异步任务失败: {}", e);
            }
        }
    }
    
    println!("总成功数: {}", total_success);
    
    client.shutdown().await?;
    Ok(())
}
```

### 2.3 自定义数据处理器

```rust
use c21_otlp::{OtlpClient, OtlpConfig, TelemetryData};
use c21_otlp::processor::{DataProcessor, ProcessingResult};

// 自定义数据处理器
pub struct CustomDataProcessor {
    name: String,
    config: ProcessorConfig,
}

#[derive(Debug, Clone)]
pub struct ProcessorConfig {
    pub enable_compression: bool,
    pub max_attribute_count: usize,
    pub filter_patterns: Vec<String>,
}

impl CustomDataProcessor {
    pub fn new(name: String, config: ProcessorConfig) -> Self {
        Self { name, config }
    }
}

impl DataProcessor for CustomDataProcessor {
    fn process(&self, data: TelemetryData) -> Result<ProcessingResult, OtlpError> {
        let mut processed_data = data;
        
        // 应用过滤器
        if !self.config.filter_patterns.is_empty() {
            processed_data = self.apply_filters(processed_data)?;
        }
        
        // 限制属性数量
        if processed_data.attributes.len() > self.config.max_attribute_count {
            processed_data = self.limit_attributes(processed_data)?;
        }
        
        // 应用压缩
        if self.config.enable_compression {
            processed_data = self.compress_data(processed_data)?;
        }
        
        Ok(ProcessingResult {
            data: processed_data,
            processing_time: Duration::from_millis(10),
            processor_name: self.name.clone(),
        })
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
}

impl CustomDataProcessor {
    fn apply_filters(&self, mut data: TelemetryData) -> Result<TelemetryData, OtlpError> {
        // 实现过滤逻辑
        data.attributes.retain(|key, _| {
            self.config.filter_patterns.iter().any(|pattern| {
                key.contains(pattern)
            })
        });
        
        Ok(data)
    }
    
    fn limit_attributes(&self, mut data: TelemetryData) -> Result<TelemetryData, OtlpError> {
        if data.attributes.len() > self.config.max_attribute_count {
            let mut attributes: Vec<_> = data.attributes.into_iter().collect();
            attributes.sort_by_key(|(_, _)| std::cmp::Reverse(attributes.len()));
            attributes.truncate(self.config.max_attribute_count);
            data.attributes = attributes.into_iter().collect();
        }
        
        Ok(data)
    }
    
    fn compress_data(&self, data: TelemetryData) -> Result<TelemetryData, OtlpError> {
        // 实现数据压缩逻辑
        // 这里简化处理，实际应该使用压缩算法
        Ok(data)
    }
}

async fn custom_processor_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc);
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 创建自定义处理器
    let processor_config = ProcessorConfig {
        enable_compression: true,
        max_attribute_count: 50,
        filter_patterns: vec!["user.".to_string(), "service.".to_string()],
    };
    
    let processor = CustomDataProcessor::new("custom_processor".to_string(), processor_config);
    
    // 创建测试数据
    let mut test_data = TelemetryData::trace("test_operation")
        .with_attribute("user.id", "12345")
        .with_attribute("user.email", "user@example.com")
        .with_attribute("service.name", "test-service")
        .with_attribute("service.version", "1.0.0")
        .with_attribute("temp.attribute1", "value1")
        .with_attribute("temp.attribute2", "value2");
    
    // 处理数据
    let result = processor.process(test_data)?;
    println!("处理结果: {:?}", result);
    
    client.shutdown().await?;
    Ok(())
}
```

### 2.4 错误处理和重试机制

```rust
use c21_otlp::{OtlpClient, OtlpConfig, OtlpError};
use std::time::Duration;

async fn error_handling_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_retry_config(RetryConfig {
            max_retries: 3,
            initial_retry_delay: Duration::from_millis(1000),
            max_retry_delay: Duration::from_secs(30),
            retry_delay_multiplier: 2.0,
            randomize_retry_delay: true,
        });
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 尝试发送数据，处理可能的错误
    match client.send_trace("error_handling_test").await {
        Ok(trace_builder) => {
            match trace_builder
                .with_attribute("test", "error_handling")
                .finish()
                .await
            {
                Ok(result) => {
                    println!("数据发送成功: {}", result.success_count);
                }
                Err(e) => {
                    match e {
                        OtlpError::NetworkError(msg) => {
                            eprintln!("网络错误: {}", msg);
                        }
                        OtlpError::SerializationError(msg) => {
                            eprintln!("序列化错误: {}", msg);
                        }
                        OtlpError::AuthenticationError(msg) => {
                            eprintln!("认证错误: {}", msg);
                        }
                        OtlpError::Backpressure(msg) => {
                            eprintln!("背压错误: {}", msg);
                        }
                        _ => {
                            eprintln!("其他错误: {}", e);
                        }
                    }
                }
            }
        }
        Err(e) => {
            eprintln!("客户端错误: {}", e);
        }
    }
    
    client.shutdown().await?;
    Ok(())
}
```

## 3. 实际应用场景示例

### 3.1 Web应用监控

```rust
use c21_otlp::{OtlpClient, OtlpConfig};
use std::collections::HashMap;
use std::time::Instant;

// Web应用监控示例
pub struct WebAppMonitor {
    client: OtlpClient,
    request_counter: AtomicU64,
    error_counter: AtomicU64,
}

impl WebAppMonitor {
    pub async fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(TransportProtocol::Grpc)
            .with_service("web-app", "1.0.0")
            .with_resource_attribute("environment", "production")
            .with_resource_attribute("region", "us-west-2");
        
        let client = OtlpClient::new(config).await?;
        client.initialize().await?;
        
        Ok(Self {
            client,
            request_counter: AtomicU64::new(0),
            error_counter: AtomicU64::new(0),
        })
    }
    
    pub async fn monitor_request(
        &self,
        method: &str,
        path: &str,
        status_code: u16,
        duration: Duration,
        user_id: Option<String>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let request_id = self.request_counter.fetch_add(1, Ordering::Relaxed);
        
        // 发送追踪数据
        let trace_result = self.client.send_trace("http_request").await?
            .with_attribute("http.method", method)
            .with_attribute("http.url", path)
            .with_attribute("http.status_code", status_code.to_string())
            .with_attribute("request.id", request_id.to_string())
            .with_numeric_attribute("request.duration_ms", duration.as_millis() as f64)
            .finish()
            .await?;
        
        // 发送指标数据
        let metric_result = self.client.send_metric("http_requests_total", 1.0).await?
            .with_label("method", method)
            .with_label("path", path)
            .with_label("status_code", status_code.to_string())
            .with_description("HTTP请求总数")
            .with_unit("count")
            .send()
            .await?;
        
        // 发送延迟指标
        let latency_result = self.client.send_histogram("http_request_duration_seconds", duration.as_secs_f64()).await?
            .with_label("method", method)
            .with_label("path", path)
            .with_description("HTTP请求延迟")
            .with_unit("seconds")
            .send()
            .await?;
        
        // 如果有用户ID，记录用户相关指标
        if let Some(uid) = user_id {
            let _ = self.client.send_metric("user_requests_total", 1.0).await?
                .with_label("user_id", &uid)
                .with_label("method", method)
                .with_description("用户请求总数")
                .with_unit("count")
                .send()
                .await?;
        }
        
        // 记录错误
        if status_code >= 400 {
            self.error_counter.fetch_add(1, Ordering::Relaxed);
            
            let _ = self.client.send_log(
                format!("HTTP请求失败: {} {}", method, path),
                LogSeverity::Error,
            ).await?
                .with_attribute("http.method", method)
                .with_attribute("http.url", path)
                .with_attribute("http.status_code", status_code.to_string())
                .with_attribute("request.id", request_id.to_string())
                .with_trace_context(&trace_result.trace_id, &trace_result.span_id)
                .send()
                .await?;
        }
        
        Ok(())
    }
    
    pub async fn monitor_database_query(
        &self,
        query_type: &str,
        table_name: &str,
        duration: Duration,
        row_count: Option<u64>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 发送数据库查询追踪
        let _ = self.client.send_trace("database_query").await?
            .with_attribute("db.operation", query_type)
            .with_attribute("db.table", table_name)
            .with_numeric_attribute("db.duration_ms", duration.as_millis() as f64)
            .finish()
            .await?;
        
        // 发送数据库查询指标
        let _ = self.client.send_metric("database_queries_total", 1.0).await?
            .with_label("operation", query_type)
            .with_label("table", table_name)
            .with_description("数据库查询总数")
            .with_unit("count")
            .send()
            .await?;
        
        // 发送查询延迟指标
        let _ = self.client.send_histogram("database_query_duration_seconds", duration.as_secs_f64()).await?
            .with_label("operation", query_type)
            .with_label("table", table_name)
            .with_description("数据库查询延迟")
            .with_unit("seconds")
            .send()
            .await?;
        
        // 如果有行数，记录行数指标
        if let Some(count) = row_count {
            let _ = self.client.send_metric("database_rows_affected", count as f64).await?
                .with_label("operation", query_type)
                .with_label("table", table_name)
                .with_description("数据库影响行数")
                .with_unit("rows")
                .send()
                .await?;
        }
        
        Ok(())
    }
    
    pub async fn shutdown(&self) -> Result<(), Box<dyn std::error::Error>> {
        self.client.shutdown().await?;
        Ok(())
    }
}

// 使用示例
async fn web_app_monitoring_example() -> Result<(), Box<dyn std::error::Error>> {
    let monitor = WebAppMonitor::new().await?;
    
    // 模拟HTTP请求
    let start_time = Instant::now();
    tokio::time::sleep(Duration::from_millis(100)).await;
    let duration = start_time.elapsed();
    
    monitor.monitor_request(
        "GET",
        "/api/users",
        200,
        duration,
        Some("user123".to_string()),
    ).await?;
    
    // 模拟数据库查询
    let start_time = Instant::now();
    tokio::time::sleep(Duration::from_millis(50)).await;
    let duration = start_time.elapsed();
    
    monitor.monitor_database_query(
        "SELECT",
        "users",
        duration,
        Some(10),
    ).await?;
    
    monitor.shutdown().await?;
    Ok(())
}
```

### 3.2 微服务间通信监控

```rust
use c21_otlp::{OtlpClient, OtlpConfig};
use std::sync::Arc;

// 微服务间通信监控
pub struct MicroserviceCommunicationMonitor {
    client: OtlpClient,
    service_name: String,
    service_version: String,
}

impl MicroserviceCommunicationMonitor {
    pub async fn new(service_name: String, service_version: String) -> Result<Self, Box<dyn std::error::Error>> {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(TransportProtocol::Grpc)
            .with_service(&service_name, &service_version)
            .with_resource_attribute("service.name", &service_name)
            .with_resource_attribute("service.version", &service_version);
        
        let client = OtlpClient::new(config).await?;
        client.initialize().await?;
        
        Ok(Self {
            client,
            service_name,
            service_version,
        })
    }
    
    pub async fn monitor_service_call(
        &self,
        target_service: &str,
        operation: &str,
        duration: Duration,
        success: bool,
        error_message: Option<String>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 发送服务调用追踪
        let trace_result = self.client.send_trace("service_call").await?
            .with_attribute("service.name", &self.service_name)
            .with_attribute("service.version", &self.service_version)
            .with_attribute("target.service", target_service)
            .with_attribute("operation.name", operation)
            .with_attribute("call.success", success.to_string())
            .with_numeric_attribute("call.duration_ms", duration.as_millis() as f64)
            .finish()
            .await?;
        
        // 发送服务调用指标
        let _ = self.client.send_metric("service_calls_total", 1.0).await?
            .with_label("source_service", &self.service_name)
            .with_label("target_service", target_service)
            .with_label("operation", operation)
            .with_label("success", success.to_string())
            .with_description("服务调用总数")
            .with_unit("count")
            .send()
            .await?;
        
        // 发送服务调用延迟指标
        let _ = self.client.send_histogram("service_call_duration_seconds", duration.as_secs_f64()).await?
            .with_label("source_service", &self.service_name)
            .with_label("target_service", target_service)
            .with_label("operation", operation)
            .with_description("服务调用延迟")
            .with_unit("seconds")
            .send()
            .await?;
        
        // 如果调用失败，记录错误日志
        if !success {
            let _ = self.client.send_log(
                format!("服务调用失败: {} -> {}:{}", self.service_name, target_service, operation),
                LogSeverity::Error,
            ).await?
                .with_attribute("source_service", &self.service_name)
                .with_attribute("target_service", target_service)
                .with_attribute("operation", operation)
                .with_attribute("error.message", error_message.unwrap_or_default())
                .with_trace_context(&trace_result.trace_id, &trace_result.span_id)
                .send()
                .await?;
        }
        
        Ok(())
    }
    
    pub async fn monitor_message_queue(
        &self,
        queue_name: &str,
        message_type: &str,
        processing_time: Duration,
        success: bool,
    ) -> Result<(), Box<dyn std::error::Error>> {
        // 发送消息队列追踪
        let _ = self.client.send_trace("message_queue_processing").await?
            .with_attribute("queue.name", queue_name)
            .with_attribute("message.type", message_type)
            .with_attribute("processing.success", success.to_string())
            .with_numeric_attribute("processing.duration_ms", processing_time.as_millis() as f64)
            .finish()
            .await?;
        
        // 发送消息队列指标
        let _ = self.client.send_metric("message_queue_messages_total", 1.0).await?
            .with_label("queue", queue_name)
            .with_label("message_type", message_type)
            .with_label("success", success.to_string())
            .with_description("消息队列消息总数")
            .with_unit("count")
            .send()
            .await?;
        
        Ok(())
    }
    
    pub async fn shutdown(&self) -> Result<(), Box<dyn std::error::Error>> {
        self.client.shutdown().await?;
        Ok(())
    }
}

// 使用示例
async fn microservice_communication_example() -> Result<(), Box<dyn std::error::Error>> {
    let monitor = MicroserviceCommunicationMonitor::new(
        "user-service".to_string(),
        "1.0.0".to_string(),
    ).await?;
    
    // 模拟服务调用
    let start_time = Instant::now();
    tokio::time::sleep(Duration::from_millis(200)).await;
    let duration = start_time.elapsed();
    
    monitor.monitor_service_call(
        "auth-service",
        "validate_token",
        duration,
        true,
        None,
    ).await?;
    
    // 模拟消息队列处理
    let start_time = Instant::now();
    tokio::time::sleep(Duration::from_millis(50)).await;
    let duration = start_time.elapsed();
    
    monitor.monitor_message_queue(
        "user-events",
        "user_created",
        duration,
        true,
    ).await?;
    
    monitor.shutdown().await?;
    Ok(())
}
```

### 3.3 性能监控和告警

```rust
use c21_otlp::{OtlpClient, OtlpConfig};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

// 性能监控和告警系统
pub struct PerformanceMonitor {
    client: OtlpClient,
    request_count: AtomicU64,
    error_count: AtomicU64,
    total_latency: AtomicU64,
    last_alert_time: AtomicU64,
}

impl PerformanceMonitor {
    pub async fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_protocol(TransportProtocol::Grpc)
            .with_service("performance-monitor", "1.0.0");
        
        let client = OtlpClient::new(config).await?;
        client.initialize().await?;
        
        Ok(Self {
            client,
            request_count: AtomicU64::new(0),
            error_count: AtomicU64::new(0),
            total_latency: AtomicU64::new(0),
            last_alert_time: AtomicU64::new(0),
        })
    }
    
    pub async fn record_request(&self, duration: Duration, success: bool) -> Result<(), Box<dyn std::error::Error>> {
        let request_count = self.request_count.fetch_add(1, Ordering::Relaxed);
        let latency_ms = duration.as_millis() as u64;
        self.total_latency.fetch_add(latency_ms, Ordering::Relaxed);
        
        if !success {
            self.error_count.fetch_add(1, Ordering::Relaxed);
        }
        
        // 计算当前指标
        let current_time = Instant::now();
        let avg_latency = if request_count > 0 {
            self.total_latency.load(Ordering::Relaxed) / request_count
        } else {
            0
        };
        
        let error_rate = if request_count > 0 {
            self.error_count.load(Ordering::Relaxed) as f64 / request_count as f64
        } else {
            0.0
        };
        
        // 发送性能指标
        let _ = self.client.send_metric("request_latency_ms", avg_latency as f64).await?
            .with_description("平均请求延迟")
            .with_unit("milliseconds")
            .send()
            .await?;
        
        let _ = self.client.send_metric("error_rate", error_rate).await?
            .with_description("错误率")
            .with_unit("ratio")
            .send()
            .await?;
        
        let _ = self.client.send_metric("requests_per_second", 1.0).await?
            .with_description("每秒请求数")
            .with_unit("requests/second")
            .send()
            .await?;
        
        // 检查告警条件
        self.check_alerts(avg_latency, error_rate).await?;
        
        Ok(())
    }
    
    async fn check_alerts(&self, avg_latency: u64, error_rate: f64) -> Result<(), Box<dyn std::error::Error>> {
        let current_time = Instant::now();
        let last_alert = self.last_alert_time.load(Ordering::Relaxed);
        let time_since_last_alert = current_time.duration_since(Instant::now() - Duration::from_secs(last_alert as u64));
        
        // 避免频繁告警，至少间隔5分钟
        if time_since_last_alert < Duration::from_secs(300) {
            return Ok(());
        }
        
        let mut alert_triggered = false;
        let mut alert_message = String::new();
        
        // 延迟告警
        if avg_latency > 1000 {
            alert_message.push_str(&format!("高延迟告警: 平均延迟 {}ms", avg_latency));
            alert_triggered = true;
        }
        
        // 错误率告警
        if error_rate > 0.05 {
            alert_message.push_str(&format!("高错误率告警: 错误率 {:.2}%", error_rate * 100.0));
            alert_triggered = true;
        }
        
        if alert_triggered {
            // 发送告警日志
            let _ = self.client.send_log(alert_message, LogSeverity::Warn).await?
                .with_attribute("alert.type", "performance")
                .with_attribute("avg_latency_ms", avg_latency.to_string())
                .with_attribute("error_rate", error_rate.to_string())
                .send()
                .await?;
            
            // 更新最后告警时间
            self.last_alert_time.store(current_time.elapsed().as_secs(), Ordering::Relaxed);
        }
        
        Ok(())
    }
    
    pub async fn shutdown(&self) -> Result<(), Box<dyn std::error::Error>> {
        self.client.shutdown().await?;
        Ok(())
    }
}

// 使用示例
async fn performance_monitoring_example() -> Result<(), Box<dyn std::error::Error>> {
    let monitor = PerformanceMonitor::new().await?;
    
    // 模拟一些请求
    for i in 0..100 {
        let start_time = Instant::now();
        
        // 模拟请求处理
        if i % 10 == 0 {
            // 模拟错误
            tokio::time::sleep(Duration::from_millis(1500)).await;
            monitor.record_request(start_time.elapsed(), false).await?;
        } else {
            // 正常请求
            tokio::time::sleep(Duration::from_millis(100)).await;
            monitor.record_request(start_time.elapsed(), true).await?;
        }
    }
    
    monitor.shutdown().await?;
    Ok(())
}
```

## 4. 最佳实践

### 4.1 配置管理

```rust
use serde::{Deserialize, Serialize};
use std::env;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OtlpConfig {
    pub endpoint: String,
    pub protocol: String,
    pub service_name: String,
    pub service_version: String,
    pub timeout_seconds: u64,
    pub batch_size: usize,
    pub max_retries: u32,
    pub debug: bool,
}

impl Default for OtlpConfig {
    fn default() -> Self {
        Self {
            endpoint: env::var("OTLP_ENDPOINT").unwrap_or_else(|_| "http://localhost:4317".to_string()),
            protocol: env::var("OTLP_PROTOCOL").unwrap_or_else(|_| "grpc".to_string()),
            service_name: env::var("SERVICE_NAME").unwrap_or_else(|_| "unknown-service".to_string()),
            service_version: env::var("SERVICE_VERSION").unwrap_or_else(|_| "1.0.0".to_string()),
            timeout_seconds: env::var("OTLP_TIMEOUT").unwrap_or_else(|_| "10".to_string()).parse().unwrap_or(10),
            batch_size: env::var("OTLP_BATCH_SIZE").unwrap_or_else(|_| "100".to_string()).parse().unwrap_or(100),
            max_retries: env::var("OTLP_MAX_RETRIES").unwrap_or_else(|_| "3".to_string()).parse().unwrap_or(3),
            debug: env::var("OTLP_DEBUG").unwrap_or_else(|_| "false".to_string()).parse().unwrap_or(false),
        }
    }
}

impl OtlpConfig {
    pub fn from_file(path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let content = std::fs::read_to_string(path)?;
        let config: OtlpConfig = serde_json::from_str(&content)?;
        Ok(config)
    }
    
    pub fn to_file(&self, path: &str) -> Result<(), Box<dyn std::error::Error>> {
        let content = serde_json::to_string_pretty(self)?;
        std::fs::write(path, content)?;
        Ok(())
    }
}
```

### 4.2 错误处理策略

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum OtlpError {
    #[error("网络错误: {0}")]
    NetworkError(String),
    
    #[error("序列化错误: {0}")]
    SerializationError(String),
    
    #[error("认证错误: {0}")]
    AuthenticationError(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("背压错误: {0}")]
    BackpressureError(String),
    
    #[error("超时错误: {0}")]
    TimeoutError(String),
    
    #[error("未知错误: {0}")]
    UnknownError(String),
}

impl OtlpError {
    pub fn is_retryable(&self) -> bool {
        match self {
            OtlpError::NetworkError(_) => true,
            OtlpError::TimeoutError(_) => true,
            OtlpError::BackpressureError(_) => true,
            _ => false,
        }
    }
    
    pub fn get_retry_delay(&self) -> Duration {
        match self {
            OtlpError::NetworkError(_) => Duration::from_secs(1),
            OtlpError::TimeoutError(_) => Duration::from_secs(2),
            OtlpError::BackpressureError(_) => Duration::from_secs(5),
            _ => Duration::from_secs(1),
        }
    }
}
```

### 4.3 性能优化建议

```rust
// 性能优化建议
pub struct PerformanceOptimization {
    // 使用连接池
    connection_pool_size: usize,
    
    // 批量处理
    batch_size: usize,
    batch_timeout: Duration,
    
    // 异步处理
    async_processing: bool,
    max_concurrent_requests: usize,
    
    // 压缩
    enable_compression: bool,
    compression_algorithm: String,
    
    // 缓存
    enable_caching: bool,
    cache_size: usize,
    cache_ttl: Duration,
}

impl PerformanceOptimization {
    pub fn new() -> Self {
        Self {
            connection_pool_size: 10,
            batch_size: 100,
            batch_timeout: Duration::from_secs(5),
            async_processing: true,
            max_concurrent_requests: 100,
            enable_compression: true,
            compression_algorithm: "gzip".to_string(),
            enable_caching: true,
            cache_size: 1000,
            cache_ttl: Duration::from_secs(300),
        }
    }
    
    pub fn optimize_for_high_throughput(&mut self) {
        self.batch_size = 1000;
        self.batch_timeout = Duration::from_secs(1);
        self.max_concurrent_requests = 1000;
        self.connection_pool_size = 50;
    }
    
    pub fn optimize_for_low_latency(&mut self) {
        self.batch_size = 10;
        self.batch_timeout = Duration::from_millis(100);
        self.max_concurrent_requests = 10;
        self.connection_pool_size = 5;
    }
    
    pub fn optimize_for_memory_usage(&mut self) {
        self.batch_size = 50;
        self.cache_size = 100;
        self.connection_pool_size = 5;
    }
}
```

## 5. 总结

本文档提供了OTLP在Rust 1.90环境下的详细使用解释和完整示例，包括：

1. **基础使用**: 客户端初始化、基本数据发送
2. **高级功能**: 批量处理、异步并发、自定义处理器
3. **实际应用**: Web应用监控、微服务通信、性能监控
4. **最佳实践**: 配置管理、错误处理、性能优化

这些示例展示了如何充分利用Rust 1.90的语言特性，构建高性能、可扩展的OTLP应用，为实际项目开发提供了全面的参考。

---

*本文档为OTLP的详细使用提供了全面的示例和最佳实践指导，适用于各种实际应用场景。*
