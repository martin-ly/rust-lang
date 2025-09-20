# OTLP综合使用示例和详细解释 - 2025年

## 概述

本文档提供了OpenTelemetry Protocol (OTLP)的全面使用示例，包括基础用法、高级特性、最佳实践和实际应用场景，帮助开发者快速掌握OTLP的使用方法。

## 1. 基础使用示例

### 1.1 简单客户端初始化

```rust
use c21_otlp::{OtlpClient, OtlpConfig, TelemetryData};
use c21_otlp::data::{LogSeverity, StatusCode};
use c21_otlp::transport::TransportProtocol;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建基础配置
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_protocol(TransportProtocol::Grpc)
        .with_service("my-service", "1.0.0")
        .with_timeout(Duration::from_secs(10));
    
    // 创建并初始化客户端
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    println!("OTLP客户端初始化成功");
    
    // 关闭客户端
    client.shutdown().await?;
    
    Ok(())
}
```

### 1.2 发送追踪数据

```rust
async fn send_trace_example(client: &OtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    // 创建追踪数据
    let trace_result = client.send_trace("user-login").await?
        .with_attribute("user.id", "12345")
        .with_attribute("user.email", "user@example.com")
        .with_attribute("service.name", "auth-service")
        .with_numeric_attribute("response.time", 150.0)
        .with_status(StatusCode::Ok, Some("登录成功".to_string()))
        .finish()
        .await?;
    
    println!("追踪数据发送成功: {} 条", trace_result.success_count);
    Ok(())
}
```

### 1.3 发送指标数据

```rust
async fn send_metric_example(client: &OtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    // 发送计数器指标
    let counter_result = client.send_metric("request_count", 1.0).await?
        .with_label("method", "GET")
        .with_label("endpoint", "/api/users")
        .with_label("status", "200")
        .with_description("HTTP请求计数")
        .with_unit("count")
        .send()
        .await?;
    
    println!("计数器指标发送成功: {} 条", counter_result.success_count);
    
    // 发送直方图指标
    let histogram_result = client.send_metric("response_duration", 0.15).await?
        .with_label("method", "GET")
        .with_label("endpoint", "/api/users")
        .with_description("响应时间分布")
        .with_unit("seconds")
        .send()
        .await?;
    
    println!("直方图指标发送成功: {} 条", histogram_result.success_count);
    
    Ok(())
}
```

### 1.4 发送日志数据

```rust
async fn send_log_example(client: &OtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    // 发送信息日志
    let info_log_result = client.send_log("用户登录成功", LogSeverity::Info).await?
        .with_attribute("user_id", "12345")
        .with_attribute("ip_address", "192.168.1.100")
        .with_attribute("user_agent", "Mozilla/5.0...")
        .with_trace_context("trace-123", "span-456")
        .send()
        .await?;
    
    println!("信息日志发送成功: {} 条", info_log_result.success_count);
    
    // 发送错误日志
    let error_log_result = client.send_log("数据库连接失败", LogSeverity::Error).await?
        .with_attribute("error_code", "DB_CONNECTION_ERROR")
        .with_attribute("database", "user_db")
        .with_attribute("retry_count", "3")
        .with_trace_context("trace-789", "span-012")
        .send()
        .await?;
    
    println!("错误日志发送成功: {} 条", error_log_result.success_count);
    
    Ok(())
}
```

## 2. 高级配置示例

### 2.1 生产环境配置

```rust
async fn production_config_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfig::default()
        .with_endpoint("https://api.honeycomb.io:443")
        .with_protocol(TransportProtocol::Grpc)
        .with_compression(Compression::Gzip)
        .with_api_key("your-api-key")
        .with_tls(true)
        .with_sampling_ratio(0.1)
        .with_batch_config(BatchConfig {
            max_export_batch_size: 512,
            export_timeout: Duration::from_millis(5000),
            max_queue_size: 2048,
            scheduled_delay: Duration::from_millis(5000),
        })
        .with_retry_config(RetryConfig {
            max_retries: 5,
            initial_retry_delay: Duration::from_millis(1000),
            max_retry_delay: Duration::from_secs(30),
            retry_delay_multiplier: 2.0,
            randomize_retry_delay: true,
        })
        .with_resource_attribute("service.name", "my-service")
        .with_resource_attribute("service.version", "1.0.0")
        .with_resource_attribute("deployment.environment", "production")
        .with_resource_attribute("region", "us-west-2")
        .with_resource_attribute("instance.id", "instance-001");
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    println!("生产环境OTLP客户端配置完成");
    
    Ok(())
}
```

### 2.2 自定义处理器配置

```rust
async fn custom_processor_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_processor(ProcessorConfig {
            processor_type: ProcessorType::Batch,
            batch_size: 100,
            timeout: Duration::from_millis(1000),
        })
        .with_processor(ProcessorConfig {
            processor_type: ProcessorType::MemoryLimiter,
            memory_limit_mb: 512,
        })
        .with_processor(ProcessorConfig {
            processor_type: ProcessorType::Sampler,
            sampling_ratio: 0.1,
        });
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    println!("自定义处理器配置完成");
    
    Ok(())
}
```

## 3. 批量处理示例

### 3.1 批量发送数据

```rust
async fn batch_send_example(client: &OtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    let mut batch_data = Vec::new();
    
    // 创建批量追踪数据
    for i in 0..100 {
        let trace_data = TelemetryData::trace(format!("batch-operation-{}", i))
            .with_attribute("batch_id", "batch-001")
            .with_attribute("operation_index", i.to_string())
            .with_attribute("service.name", "batch-service")
            .with_numeric_attribute("duration", (i as f64) * 0.1);
        
        batch_data.push(trace_data);
    }
    
    // 批量发送
    let result = client.send_batch(batch_data).await?;
    println!("批量发送结果: 成功 {} 条", result.success_count);
    
    Ok(())
}
```

### 3.2 异步批量处理

```rust
async fn async_batch_example(client: &OtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    let mut futures = Vec::new();
    
    // 创建多个异步批量任务
    for batch_id in 0..10 {
        let client_clone = client.clone();
        let future = tokio::spawn(async move {
            let mut batch_data = Vec::new();
            
            for i in 0..50 {
                let trace_data = TelemetryData::trace(format!("async-batch-{}-{}", batch_id, i))
                    .with_attribute("batch_id", format!("batch-{}", batch_id))
                    .with_attribute("operation_index", i.to_string());
                
                batch_data.push(trace_data);
            }
            
            client_clone.send_batch(batch_data).await
        });
        
        futures.push(future);
    }
    
    // 等待所有异步任务完成
    let results = futures::future::join_all(futures).await;
    
    let mut total_success = 0;
    for result in results {
        let batch_result = result??;
        total_success += batch_result.success_count;
    }
    
    println!("异步批量处理完成，总计成功: {} 条", total_success);
    
    Ok(())
}
```

## 4. 高级特性示例

### 4.1 自定义采样策略

```rust
async fn custom_sampling_example(client: &OtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    // 创建自定义采样策略
    let sampling_strategy = CustomSamplingStrategy::new()
        .with_rule(SamplingRule::new("high_priority", "高优先级采样")
            .with_condition(RuleCondition::LogLevel(LogLevel::Error))
            .with_decision(SamplingDecision::RecordAndSample)
            .with_priority(1))
        .with_rule(SamplingRule::new("low_priority", "低优先级采样")
            .with_condition(RuleCondition::LogLevel(LogLevel::Debug))
            .with_decision(SamplingDecision::Drop)
            .with_priority(10));
    
    // 应用采样策略
    client.set_sampling_strategy(sampling_strategy).await?;
    
    // 发送不同级别的日志
    let error_log = client.send_log("严重错误", LogSeverity::Error).await?
        .with_attribute("error_type", "critical")
        .send()
        .await?;
    
    let debug_log = client.send_log("调试信息", LogSeverity::Debug).await?
        .with_attribute("debug_info", "detailed")
        .send()
        .await?;
    
    println!("错误日志采样结果: {} 条", error_log.success_count);
    println!("调试日志采样结果: {} 条", debug_log.success_count);
    
    Ok(())
}
```

### 4.2 动态配置调整

```rust
async fn dynamic_config_example(client: &OtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    // 获取当前配置
    let current_config = client.get_config().await?;
    println!("当前采样率: {}", current_config.sampling_ratio);
    
    // 动态调整采样率
    client.adjust_sampling_ratio(0.2).await?;
    println!("采样率已调整为: 0.2");
    
    // 动态调整批处理大小
    client.adjust_batch_size(256).await?;
    println!("批处理大小已调整为: 256");
    
    // 动态调整超时时间
    client.adjust_timeout(Duration::from_secs(15)).await?;
    println!("超时时间已调整为: 15秒");
    
    Ok(())
}
```

## 5. 实际应用场景示例

### 5.1 Web应用监控

```rust
// Web应用监控示例
pub struct WebAppMonitor {
    otlp_client: OtlpClient,
    request_counter: AtomicU64,
    response_time_histogram: Histogram<f64>,
}

impl WebAppMonitor {
    pub async fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_service("web-app", "1.0.0")
            .with_sampling_ratio(0.1);
        
        let client = OtlpClient::new(config).await?;
        client.initialize().await?;
        
        Ok(Self {
            otlp_client: client,
            request_counter: AtomicU64::new(0),
            response_time_histogram: Histogram::new("response_time", "Response time distribution"),
        })
    }
    
    pub async fn monitor_request(&self, request: &HttpRequest) -> Result<(), Box<dyn std::error::Error>> {
        let request_id = self.request_counter.fetch_add(1, Ordering::Relaxed);
        let start_time = Instant::now();
        
        // 创建追踪
        let trace_result = self.otlp_client.send_trace("http_request").await?
            .with_attribute("request.id", request_id.to_string())
            .with_attribute("request.method", request.method.clone())
            .with_attribute("request.path", request.path.clone())
            .with_attribute("request.user_agent", request.user_agent.clone())
            .with_attribute("request.ip", request.ip.clone())
            .finish()
            .await?;
        
        // 记录指标
        let response_time = start_time.elapsed().as_secs_f64();
        self.response_time_histogram.record(response_time);
        
        let metric_result = self.otlp_client.send_metric("request_duration", response_time).await?
            .with_label("method", request.method.clone())
            .with_label("path", request.path.clone())
            .with_label("status", "200")
            .with_unit("seconds")
            .send()
            .await?;
        
        // 记录日志
        let log_result = self.otlp_client.send_log("请求处理完成", LogSeverity::Info).await?
            .with_attribute("request.id", request_id.to_string())
            .with_attribute("response.time", response_time.to_string())
            .with_trace_context("trace-123", "span-456")
            .send()
            .await?;
        
        println!("请求监控完成: 追踪={}, 指标={}, 日志={}", 
                trace_result.success_count, 
                metric_result.success_count, 
                log_result.success_count);
        
        Ok(())
    }
}
```

### 5.2 数据库操作监控

```rust
// 数据库操作监控示例
pub struct DatabaseMonitor {
    otlp_client: OtlpClient,
    query_counter: AtomicU64,
    connection_pool: ConnectionPool,
}

impl DatabaseMonitor {
    pub async fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_service("database-service", "1.0.0")
            .with_sampling_ratio(0.05); // 数据库操作采样率较低
        
        let client = OtlpClient::new(config).await?;
        client.initialize().await?;
        
        Ok(Self {
            otlp_client: client,
            query_counter: AtomicU64::new(0),
            connection_pool: ConnectionPool::new(),
        })
    }
    
    pub async fn monitor_query(&self, query: &str, params: &[String]) -> Result<QueryResult, Box<dyn std::error::Error>> {
        let query_id = self.query_counter.fetch_add(1, Ordering::Relaxed);
        let start_time = Instant::now();
        
        // 创建追踪
        let trace_result = self.otlp_client.send_trace("database_query").await?
            .with_attribute("query.id", query_id.to_string())
            .with_attribute("query.sql", query.to_string())
            .with_attribute("query.params", params.join(","))
            .with_attribute("database.name", "user_db")
            .finish()
            .await?;
        
        // 执行查询
        let result = self.connection_pool.execute_query(query, params).await?;
        let execution_time = start_time.elapsed();
        
        // 记录指标
        let metric_result = self.otlp_client.send_metric("query_duration", execution_time.as_secs_f64()).await?
            .with_label("query_type", self.get_query_type(query))
            .with_label("database", "user_db")
            .with_unit("seconds")
            .send()
            .await?;
        
        // 记录日志
        let log_level = if execution_time > Duration::from_secs(1) {
            LogSeverity::Warn
        } else {
            LogSeverity::Info
        };
        
        let log_result = self.otlp_client.send_log("数据库查询完成", log_level).await?
            .with_attribute("query.id", query_id.to_string())
            .with_attribute("execution.time", execution_time.as_millis().to_string())
            .with_attribute("result.rows", result.row_count.to_string())
            .send()
            .await?;
        
        println!("数据库查询监控完成: 追踪={}, 指标={}, 日志={}", 
                trace_result.success_count, 
                metric_result.success_count, 
                log_result.success_count);
        
        Ok(result)
    }
    
    fn get_query_type(&self, query: &str) -> &'static str {
        let query_upper = query.to_uppercase();
        if query_upper.starts_with("SELECT") {
            "SELECT"
        } else if query_upper.starts_with("INSERT") {
            "INSERT"
        } else if query_upper.starts_with("UPDATE") {
            "UPDATE"
        } else if query_upper.starts_with("DELETE") {
            "DELETE"
        } else {
            "OTHER"
        }
    }
}
```

### 5.3 微服务间通信监控

```rust
// 微服务间通信监控示例
pub struct MicroserviceMonitor {
    otlp_client: OtlpClient,
    service_registry: ServiceRegistry,
    circuit_breaker: CircuitBreaker,
}

impl MicroserviceMonitor {
    pub async fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let config = OtlpConfig::default()
            .with_endpoint("http://localhost:4317")
            .with_service("microservice-gateway", "1.0.0")
            .with_sampling_ratio(0.2);
        
        let client = OtlpClient::new(config).await?;
        client.initialize().await?;
        
        Ok(Self {
            otlp_client: client,
            service_registry: ServiceRegistry::new(),
            circuit_breaker: CircuitBreaker::new(),
        })
    }
    
    pub async fn monitor_service_call(
        &self,
        target_service: &str,
        endpoint: &str,
        request_data: &str
    ) -> Result<ServiceResponse, Box<dyn std::error::Error>> {
        let call_id = Uuid::new_v4().to_string();
        let start_time = Instant::now();
        
        // 创建追踪
        let trace_result = self.otlp_client.send_trace("service_call").await?
            .with_attribute("call.id", call_id.clone())
            .with_attribute("target.service", target_service.to_string())
            .with_attribute("target.endpoint", endpoint.to_string())
            .with_attribute("source.service", "gateway")
            .finish()
            .await?;
        
        // 检查熔断器状态
        if !self.circuit_breaker.is_available(target_service) {
            let error_log = self.otlp_client.send_log("服务熔断", LogSeverity::Error).await?
                .with_attribute("target.service", target_service.to_string())
                .with_attribute("circuit.state", "OPEN")
                .send()
                .await?;
            
            return Err("服务熔断".into());
        }
        
        // 调用目标服务
        let response = match self.service_registry.call_service(target_service, endpoint, request_data).await {
            Ok(response) => {
                let execution_time = start_time.elapsed();
                
                // 记录成功指标
                let metric_result = self.otlp_client.send_metric("service_call_duration", execution_time.as_secs_f64()).await?
                    .with_label("target_service", target_service)
                    .with_label("endpoint", endpoint)
                    .with_label("status", "success")
                    .with_unit("seconds")
                    .send()
                    .await?;
                
                // 记录成功日志
                let log_result = self.otlp_client.send_log("服务调用成功", LogSeverity::Info).await?
                    .with_attribute("call.id", call_id)
                    .with_attribute("target.service", target_service)
                    .with_attribute("response.time", execution_time.as_millis().to_string())
                    .send()
                    .await?;
                
                println!("服务调用监控完成: 追踪={}, 指标={}, 日志={}", 
                        trace_result.success_count, 
                        metric_result.success_count, 
                        log_result.success_count);
                
                response
            }
            Err(error) => {
                // 记录失败指标
                let metric_result = self.otlp_client.send_metric("service_call_errors", 1.0).await?
                    .with_label("target_service", target_service)
                    .with_label("endpoint", endpoint)
                    .with_label("error_type", "service_error")
                    .send()
                    .await?;
                
                // 记录错误日志
                let log_result = self.otlp_client.send_log("服务调用失败", LogSeverity::Error).await?
                    .with_attribute("call.id", call_id)
                    .with_attribute("target.service", target_service)
                    .with_attribute("error.message", error.to_string())
                    .send()
                    .await?;
                
                // 更新熔断器状态
                self.circuit_breaker.record_failure(target_service);
                
                return Err(error);
            }
        };
        
        Ok(response)
    }
}
```

## 6. 错误处理和重试示例

### 6.1 错误处理策略

```rust
async fn error_handling_example(client: &OtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    // 配置错误处理策略
    let error_handler = ErrorHandler::new()
        .with_retry_policy(RetryPolicy {
            max_retries: 3,
            initial_delay: Duration::from_millis(1000),
            max_delay: Duration::from_secs(10),
            backoff_multiplier: 2.0,
        })
        .with_circuit_breaker(CircuitBreakerConfig {
            failure_threshold: 5,
            recovery_timeout: Duration::from_secs(30),
        });
    
    client.set_error_handler(error_handler).await?;
    
    // 发送可能失败的数据
    match client.send_trace("risky-operation").await {
        Ok(trace_builder) => {
            let result = trace_builder
                .with_attribute("risk_level", "high")
                .finish()
                .await?;
            println!("操作成功: {} 条", result.success_count);
        }
        Err(e) => {
            println!("操作失败: {:?}", e);
            // 记录错误到本地日志
            client.send_log("操作失败", LogSeverity::Error).await?
                .with_attribute("error", e.to_string())
                .send()
                .await?;
        }
    }
    
    Ok(())
}
```

### 6.2 重试机制示例

```rust
async fn retry_mechanism_example(client: &OtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    let retry_config = RetryConfig {
        max_retries: 5,
        initial_retry_delay: Duration::from_millis(1000),
        max_retry_delay: Duration::from_secs(30),
        retry_delay_multiplier: 2.0,
        randomize_retry_delay: true,
    };
    
    client.set_retry_config(retry_config).await?;
    
    // 发送数据，自动重试
    let result = client.send_metric("retry_test", 1.0).await?
        .with_label("test", "retry")
        .send()
        .await?;
    
    println!("重试机制测试完成: {} 条", result.success_count);
    
    Ok(())
}
```

## 7. 性能优化示例

### 7.1 连接池优化

```rust
async fn connection_pool_example() -> Result<(), Box<dyn std::error::Error>> {
    let config = OtlpConfig::default()
        .with_endpoint("http://localhost:4317")
        .with_connection_pool(ConnectionPoolConfig {
            max_connections: 10,
            min_connections: 2,
            connection_timeout: Duration::from_secs(5),
            idle_timeout: Duration::from_secs(30),
            max_lifetime: Duration::from_secs(300),
        });
    
    let client = OtlpClient::new(config).await?;
    client.initialize().await?;
    
    // 并发发送大量数据
    let mut tasks = Vec::new();
    for i in 0..1000 {
        let client_clone = client.clone();
        let task = tokio::spawn(async move {
            client_clone.send_metric("concurrent_test", i as f64).await?
                .with_label("task_id", i.to_string())
                .send()
                .await
        });
        tasks.push(task);
    }
    
    let results = futures::future::join_all(tasks).await;
    let mut total_success = 0;
    
    for result in results {
        match result {
            Ok(Ok(metric_result)) => total_success += metric_result.success_count,
            Ok(Err(e)) => println!("任务失败: {:?}", e),
            Err(e) => println!("任务执行失败: {:?}", e),
        }
    }
    
    println!("并发测试完成，总计成功: {} 条", total_success);
    
    Ok(())
}
```

### 7.2 批处理优化

```rust
async fn batch_optimization_example(client: &OtlpClient) -> Result<(), Box<dyn std::error::Error>> {
    // 优化批处理配置
    let batch_config = BatchConfig {
        max_export_batch_size: 1000,
        export_timeout: Duration::from_millis(2000),
        max_queue_size: 5000,
        scheduled_delay: Duration::from_millis(1000),
    };
    
    client.set_batch_config(batch_config).await?;
    
    // 创建大量数据
    let mut batch_data = Vec::new();
    for i in 0..10000 {
        let data = TelemetryData::metric(format!("batch_metric_{}", i), i as f64)
            .with_label("batch_id", "optimization_test")
            .with_label("index", i.to_string());
        batch_data.push(data);
    }
    
    // 批量发送
    let start_time = Instant::now();
    let result = client.send_batch(batch_data).await?;
    let duration = start_time.elapsed();
    
    println!("批处理优化测试完成:");
    println!("  发送数据: {} 条", result.success_count);
    println!("  耗时: {:?}", duration);
    println!("  吞吐量: {:.2} 条/秒", result.success_count as f64 / duration.as_secs_f64());
    
    Ok(())
}
```

## 8. 最佳实践总结

### 8.1 配置最佳实践

1. **生产环境**: 使用适当的采样率和批处理配置
2. **开发环境**: 使用高采样率便于调试
3. **测试环境**: 使用中等采样率平衡性能和覆盖度

### 8.2 性能最佳实践

1. **批处理**: 使用批处理减少网络开销
2. **连接池**: 使用连接池提高连接效率
3. **异步处理**: 使用异步API避免阻塞

### 8.3 监控最佳实践

1. **关键指标**: 监控请求量、响应时间、错误率
2. **业务指标**: 监控业务相关的自定义指标
3. **告警设置**: 设置合理的告警阈值

### 8.4 错误处理最佳实践

1. **重试机制**: 实现指数退避重试
2. **熔断器**: 使用熔断器保护系统
3. **降级策略**: 实现优雅降级

通过以上示例和最佳实践，开发者可以快速掌握OTLP的使用方法，构建高性能、可观测的分布式系统。
