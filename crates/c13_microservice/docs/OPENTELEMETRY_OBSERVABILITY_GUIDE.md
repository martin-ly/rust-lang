# OpenTelemetry 可观测性功能指南

本指南介绍如何使用 c13_microservice 中的 OpenTelemetry 可观测性功能，包括日志记录、指标收集、分布式追踪和系统监控。

## 功能概述

### 1. 日志记录和聚合

- **结构化日志**: 支持 JSON 和文本格式的结构化日志记录
- **日志级别过滤**: 可配置的日志级别过滤
- **异步日志写入**: 高性能的异步日志写入机制
- **日志聚合**: 自动聚合和分析日志数据
- **日志轮转**: 支持日志文件轮转和大小限制

### 2. 指标收集和导出

- **多种指标类型**: 支持计数器、仪表、直方图和计时器
- **标签支持**: 支持带标签的指标记录
- **Prometheus 导出**: 内置 Prometheus 格式导出器
- **指标聚合**: 自动计算统计信息（平均值、分位数等）
- **实时监控**: 支持实时指标监控和告警

### 3. 分布式追踪

- **上下文传播**: 支持 HTTP 头部中的追踪上下文传播
- **采样策略**: 可配置的采样策略（总是、从不、概率、限流）
- **Span 管理**: 完整的 Span 生命周期管理
- **线程本地存储**: 线程安全的追踪上下文存储
- **追踪导出**: 支持追踪数据导出和分析

### 4. 可观测性功能

- **健康检查**: 可扩展的健康检查框架
- **性能监控**: 操作性能监控和告警
- **错误追踪**: 错误记录、分类和统计
- **系统状态报告**: 综合的系统状态报告

## 快速开始

### 1. 基本配置

```rust
use c13_microservice::opentelemetry::{
    OpenTelemetryManager, OpenTelemetryConfig, LogConfig
};
use std::collections::HashMap;

// 创建配置
let mut config = OpenTelemetryConfig {
    jaeger_endpoint: "http://localhost:14268/api/traces".to_string(),
    service_name: "my-service".to_string(),
    service_version: "1.0.0".to_string(),
    tracing_enabled: true,
    metrics_enabled: true,
    logging_enabled: true,
    sampling_ratio: 0.1, // 10% 采样率
    resource_attributes: HashMap::new(),
};

// 创建管理器
let mut otel_manager = OpenTelemetryManager::new(config)?;
otel_manager.init()?;
```

### 2. 日志记录

```rust
use std::collections::HashMap;

// 基本日志记录
otel_manager.logger().info("用户登录成功", None);

// 带字段的结构化日志
let mut fields = HashMap::new();
fields.insert("user_id".to_string(), "123".to_string());
fields.insert("ip_address".to_string(), "192.168.1.1".to_string());

otel_manager.logger().info("用户登录", Some(fields));

// HTTP 请求日志
otel_manager.logger().log_http_request("GET", "/api/users", 200, 150);

// 数据库查询日志
otel_manager.logger().log_database_query(
    "SELECT * FROM users", 
    25, 
    Some(10)
);

// 错误日志
let mut context = HashMap::new();
context.insert("operation".to_string(), "create_user".to_string());
otel_manager.logger().log_error("数据库连接失败", Some(context));
```

### 3. 指标收集

```rust
use std::collections::HashMap;
use std::time::Duration;

// 基本指标
otel_manager.metrics().increment_counter("requests_total", 1);
otel_manager.metrics().set_gauge("cpu_usage", 75.5);
otel_manager.metrics().record_histogram("response_time", 0.1);
otel_manager.metrics().record_timer("operation_duration", Duration::from_millis(100));

// 带标签的指标
let mut labels = HashMap::new();
labels.insert("method".to_string(), "GET".to_string());
labels.insert("endpoint".to_string(), "/api/users".to_string());

otel_manager.metrics().increment_labeled_counter(
    "http_requests_total",
    labels,
    1
);

// 设置 Prometheus 导出器
let prometheus_exporter = Arc::new(PrometheusExporter::new("my_service".to_string()));
otel_manager.metrics().set_exporter(prometheus_exporter);
```

### 4. 分布式追踪

```rust
// 创建根 Span
if let Some(root_span) = otel_manager.tracer().start_root_span("user_registration".to_string()) {
    root_span.add_attribute("user.email".to_string(), "user@example.com".to_string());
    
    // 创建子 Span
    if let Some(child_span) = otel_manager.tracer().start_span("validate_user".to_string()) {
        child_span.add_attribute("validation.rules".to_string(), "email,password".to_string());
        
        // 执行验证逻辑
        // ...
        
        otel_manager.tracer().finish_span(child_span);
    }
    
    otel_manager.tracer().finish_span(root_span);
}

// HTTP 头部传播
let mut headers = HashMap::new();
headers.insert("x-trace-id".to_string(), "abc123".to_string());
headers.insert("x-span-id".to_string(), "def456".to_string());

if let Some(context) = otel_manager.tracer().extract_context_from_headers(&headers) {
    // 使用提取的上下文
    println!("追踪ID: {}", context.trace_id);
}

// 注入上下文到 HTTP 头部
let new_headers = otel_manager.tracer().inject_context_to_headers(&context);
```

### 5. 健康检查

```rust
use c13_microservice::opentelemetry::{
    DatabaseHealthChecker, RedisHealthChecker, SystemResourceHealthChecker
};

// 添加健康检查器
otel_manager.add_health_checker(Box::new(DatabaseHealthChecker::new(
    "main_database".to_string(),
    "postgresql://localhost:5432/mydb".to_string(),
)));

otel_manager.add_health_checker(Box::new(RedisHealthChecker::new(
    "cache_redis".to_string(),
    "redis://localhost:6379".to_string(),
)));

otel_manager.add_health_checker(Box::new(SystemResourceHealthChecker::new(
    "system_resources".to_string(),
    80.0, // CPU 阈值
    85.0, // 内存阈值
)));

// 获取系统健康状态
let health_status = otel_manager.get_system_health();
match health_status {
    HealthStatus::Healthy => println!("系统健康"),
    HealthStatus::Degraded => println!("系统性能下降"),
    HealthStatus::Unhealthy => println!("系统不健康"),
}
```

### 6. 性能监控

```rust
use std::time::{Duration, Instant};

// 记录操作性能
let start_time = Instant::now();
// 执行操作
let duration = start_time.elapsed();

otel_manager.performance_monitor().record_operation(
    "user_lookup",
    duration,
    true, // 成功
);

// 设置性能告警阈值
otel_manager.set_performance_alert_threshold("user_lookup", 1000.0); // 1秒

// 获取性能摘要
let perf_summary = otel_manager.performance_monitor().get_performance_summary();
println!("平均响应时间: {:.2}ms", perf_summary.avg_response_time_ms);
println!("错误率: {:.2}%", perf_summary.error_rate * 100.0);
```

### 7. 错误追踪

```rust
use c13_microservice::opentelemetry::ErrorSeverity;
use std::collections::HashMap;

// 记录错误
let mut context = HashMap::new();
context.insert("user_id".to_string(), "123".to_string());
context.insert("operation".to_string(), "create_user".to_string());

let error_id = otel_manager.error_tracker().record_error(
    "validation_error",
    "用户邮箱格式无效",
    context,
    ErrorSeverity::Medium,
);

// 设置错误告警阈值
otel_manager.set_error_alert_threshold("validation_error", 10);

// 获取错误统计
let error_stats = otel_manager.error_tracker().get_error_statistics();
println!("总错误数: {}", error_stats.total_errors);
println!("严重错误: {}", error_stats.critical_severity);

// 标记错误为已解决
otel_manager.error_tracker().resolve_error(&error_id);
```

### 8. 系统状态报告

```rust
// 生成完整系统报告
let system_report = otel_manager.generate_system_report();

println!("整体健康状态: {:?}", system_report.overall_health);
println!("健康检查数量: {}", system_report.health_checks.len());
println!("性能监控操作数: {}", system_report.performance_summary.monitored_operations);
println!("总错误数: {}", system_report.error_statistics.total_errors);

// 导出所有数据
let exported_data = otel_manager.export_all_data()?;
println!("导出的追踪数据: {}", exported_data.traces);
println!("导出的指标数据: {}", exported_data.metrics);
```

## 高级功能

### 1. 自定义健康检查器

```rust
use c13_microservice::opentelemetry::{HealthChecker, HealthCheck, HealthStatus};
use std::collections::HashMap;

struct CustomHealthChecker {
    name: String,
    check_url: String,
}

impl HealthChecker for CustomHealthChecker {
    fn name(&self) -> &str {
        &self.name
    }
    
    fn check(&self) -> HealthCheck {
        let start_time = std::time::Instant::now();
        let timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        // 执行自定义健康检查逻辑
        let status = HealthStatus::Healthy;
        let message = "自定义检查通过".to_string();
        
        let mut details = HashMap::new();
        details.insert("check_url".to_string(), self.check_url.clone());
        
        HealthCheck {
            name: self.name.clone(),
            status,
            message,
            timestamp,
            duration_ms: start_time.elapsed().as_millis() as u64,
            details,
        }
    }
}

// 使用自定义健康检查器
let custom_checker = Box::new(CustomHealthChecker {
    name: "custom_service".to_string(),
    check_url: "http://localhost:8080/health".to_string(),
});

otel_manager.add_health_checker(custom_checker);
```

### 2. 自定义指标导出器

```rust
use c13_microservice::opentelemetry::{MetricExporter, LabeledMetric};
use anyhow::Result;

struct CustomExporter {
    name: String,
}

impl MetricExporter for CustomExporter {
    fn export(&self, metrics: &[LabeledMetric]) -> Result<()> {
        // 实现自定义导出逻辑
        for metric in metrics {
            println!("导出指标: {} = {:?}", metric.name, metric.value);
        }
        Ok(())
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
}

// 使用自定义导出器
let custom_exporter = Arc::new(CustomExporter {
    name: "custom_exporter".to_string(),
});

otel_manager.metrics().set_exporter(custom_exporter);
```

### 3. 采样策略配置

```rust
use c13_microservice::opentelemetry::SamplingStrategy;

// 总是采样
let always_sampling = SamplingStrategy::Always;

// 从不采样
let never_sampling = SamplingStrategy::Never;

// 概率采样 (10%)
let probability_sampling = SamplingStrategy::Probability(0.1);

// 限流采样 (每秒最多100个)
let rate_limiting_sampling = SamplingStrategy::RateLimiting(100);

// 设置采样策略
otel_manager.tracer().set_sampling_strategy(probability_sampling);
```

## 最佳实践

### 1. 性能优化

- 使用异步日志写入以提高性能
- 合理设置采样率以平衡性能和可观测性
- 定期清理旧的追踪和指标数据
- 使用缓冲区批量处理指标数据

### 2. 错误处理

- 为不同类型的错误设置合适的严重级别
- 配置错误告警阈值
- 定期检查未解决的错误
- 记录足够的上下文信息用于调试

### 3. 监控告警

- 设置合理的性能告警阈值
- 监控关键业务指标
- 建立健康检查机制
- 定期生成系统状态报告

### 4. 数据管理

- 定期导出和备份可观测性数据
- 设置数据保留策略
- 监控存储使用情况
- 实施数据压缩和归档

## 示例项目

查看 `examples/comprehensive_observability_demo.rs` 获取完整的使用示例，该示例展示了所有功能的集成使用。

## 故障排除

### 常见问题

1. **编译错误**: 确保所有依赖项都已正确添加到 Cargo.toml
2. **性能问题**: 检查采样率设置和缓冲区大小
3. **内存泄漏**: 定期清理旧的追踪和指标数据
4. **网络问题**: 检查 Jaeger 端点配置和网络连接

### 调试技巧

1. 启用详细日志记录
2. 使用系统状态报告诊断问题
3. 检查健康检查结果
4. 监控错误统计和模式

## 总结

OpenTelemetry 可观测性功能为微服务提供了全面的监控和调试能力。通过合理配置和使用这些功能，可以大大提高系统的可观测性和可维护性。
