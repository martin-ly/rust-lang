# 使用指南

> **文档定位**: C13 可靠性框架详细使用说明  
> **适用人群**: 所有开发者  
> **相关文档**: [快速开始](../../QUICK_START.md) | [最佳实践](best-practices.md)


## 📊 目录

- [📋 目录](#目录)
- [快速开始](#快速开始)
  - [1. 添加依赖](#1-添加依赖)
  - [2. 基本使用](#2-基本使用)
- [错误处理](#错误处理)
  - [创建统一错误](#创建统一错误)
  - [记录错误](#记录错误)
  - [错误恢复](#错误恢复)
- [容错机制](#容错机制)
  - [断路器](#断路器)
  - [重试策略](#重试策略)
  - [超时控制](#超时控制)
  - [降级机制](#降级机制)
  - [组合使用](#组合使用)
- [运行时监控](#运行时监控)
  - [健康检查](#健康检查)
  - [自定义健康检查](#自定义健康检查)
  - [资源监控](#资源监控)
  - [性能监控](#性能监控)
  - [异常检测](#异常检测)
- [混沌工程](#混沌工程)
  - [故障注入](#故障注入)
  - [混沌场景](#混沌场景)
- [配置管理](#配置管理)
  - [基本配置](#基本配置)
  - [配置文件格式](#配置文件格式)
- [指标收集](#指标收集)
  - [基本使用](#基本使用)
- [工具函数](#工具函数)
  - [持续时间扩展](#持续时间扩展)
  - [性能工具](#性能工具)
  - [配置工具](#配置工具)
- [最佳实践](#最佳实践)
  - [1. 错误处理](#1-错误处理)
  - [2. 容错机制](#2-容错机制)
  - [3. 监控](#3-监控)
  - [4. 配置管理](#4-配置管理)
  - [5. 混沌工程](#5-混沌工程)
- [常见问题](#常见问题)
  - [Q: 如何自定义健康检查？](#q-如何自定义健康检查)
  - [Q: 如何调整容错参数？](#q-如何调整容错参数)
  - [Q: 如何集成到现有项目？](#q-如何集成到现有项目)
  - [Q: 如何监控自定义指标？](#q-如何监控自定义指标)
  - [Q: 如何启用混沌工程？](#q-如何启用混沌工程)


**最后更新**: 2025-10-19  
**文档类型**: 📖 使用指南

---

## 📋 目录

- [使用指南](#使用指南)
  - [📋 目录](#-目录)
  - [快速开始](#快速开始)
    - [1. 添加依赖](#1-添加依赖)
    - [2. 基本使用](#2-基本使用)
  - [错误处理](#错误处理)
    - [创建统一错误](#创建统一错误)
    - [记录错误](#记录错误)
    - [错误恢复](#错误恢复)
  - [容错机制](#容错机制)
    - [断路器](#断路器)
    - [重试策略](#重试策略)
    - [超时控制](#超时控制)
    - [降级机制](#降级机制)
    - [组合使用](#组合使用)
  - [运行时监控](#运行时监控)
    - [健康检查](#健康检查)
    - [自定义健康检查](#自定义健康检查)
    - [资源监控](#资源监控)
    - [性能监控](#性能监控)
    - [异常检测](#异常检测)
  - [混沌工程](#混沌工程)
    - [故障注入](#故障注入)
    - [混沌场景](#混沌场景)
  - [配置管理](#配置管理)
    - [基本配置](#基本配置)
    - [配置文件格式](#配置文件格式)
  - [指标收集](#指标收集)
    - [基本使用](#基本使用)
  - [工具函数](#工具函数)
    - [持续时间扩展](#持续时间扩展)
    - [性能工具](#性能工具)
    - [配置工具](#配置工具)
  - [最佳实践](#最佳实践)
    - [1. 错误处理](#1-错误处理)
    - [2. 容错机制](#2-容错机制)
    - [3. 监控](#3-监控)
    - [4. 配置管理](#4-配置管理)
    - [5. 混沌工程](#5-混沌工程)
  - [常见问题](#常见问题)
    - [Q: 如何自定义健康检查？](#q-如何自定义健康检查)
    - [Q: 如何调整容错参数？](#q-如何调整容错参数)
    - [Q: 如何集成到现有项目？](#q-如何集成到现有项目)
    - [Q: 如何监控自定义指标？](#q-如何监控自定义指标)
    - [Q: 如何启用混沌工程？](#q-如何启用混沌工程)

---

## 快速开始

### 1. 添加依赖

在 `Cargo.toml` 中添加：

```toml
[dependencies]
c13_reliability = "0.1.0"
tokio = { version = "1.0", features = ["full"] }
env_logger = "0.9"
```

### 2. 基本使用

```rust
use c13_reliability::prelude::*;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 初始化可靠性框架
    c13_reliability::init().await?;
    
    // 使用各种可靠性功能
    
    // 关闭可靠性框架
    c13_reliability::shutdown().await?;
    Ok(())
}
```

## 错误处理

### 创建统一错误

```rust
use c13_reliability::error_handling::*;

let error = UnifiedError::new(
    "操作失败",
    ErrorSeverity::Medium,
    "my_service",
    ErrorContext::new(
        "my_service",
        "operation",
        file!(),
        line!(),
        ErrorSeverity::Medium,
        "my_component"
    )
);
```

### 记录错误

```rust
use c13_reliability::error_handling::*;

log_error!(error, "操作上下文");
```

### 错误恢复

```rust
use c13_reliability::error_handling::*;

let recovery_strategy = RecoveryStrategy::Retry {
    max_attempts: 3,
    delay_ms: 1000,
    exponential_backoff: true,
};

let error_handler = ErrorHandler::new(recovery_strategy);
let result = error_handler.execute(|| async {
    // 可能失败的操作
    Ok::<String, UnifiedError>("success".to_string())
}).await;
```

## 容错机制

### 断路器

```rust
use c13_reliability::fault_tolerance::*;

let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(60));

let result = circuit_breaker.execute(|| async {
    // 可能失败的操作
    Ok::<String, UnifiedError>("success".to_string())
}).await;
```

### 重试策略

```rust
use c13_reliability::fault_tolerance::*;

let retry_policy = RetryPolicy::Exponential {
    max_attempts: 3,
    initial_delay_ms: 100,
    factor: 2,
};

let retrier = Retrier::new(retry_policy);
let result = retrier.execute(|| async {
    // 可能失败的操作
    Ok::<String, UnifiedError>("success".to_string())
}).await;
```

### 超时控制

```rust
use c13_reliability::fault_tolerance::*;

let timeout = Timeout::new(Duration::from_secs(5));
let result = timeout.execute(|| async {
    // 可能超时的操作
    Ok::<String, UnifiedError>("success".to_string())
}).await;
```

### 降级机制

```rust
use c13_reliability::fault_tolerance::*;

let fallback = Fallback::new(Some("降级响应".to_string()));
let result = fallback.execute(|| async {
    // 可能失败的操作
    Ok::<String, UnifiedError>("success".to_string())
}).await;
```

### 组合使用

```rust
use c13_reliability::fault_tolerance::*;

let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(60));
let retry_policy = RetryPolicy::Exponential {
    max_attempts: 3,
    initial_delay_ms: 100,
    factor: 2,
};
let retrier = Retrier::new(retry_policy);
let timeout = Timeout::new(Duration::from_secs(5));
let fallback = Fallback::new(Some("降级响应".to_string()));

let result = circuit_breaker
    .with_retry(retrier)
    .with_timeout(timeout)
    .with_fallback(fallback)
    .execute(|| async {
        // 业务逻辑
        Ok::<String, UnifiedError>("success".to_string())
    })
    .await;
```

## 运行时监控

### 健康检查

```rust
use c13_reliability::runtime_monitoring::*;

// 创建健康检查器
let health_checker = HealthChecker::new();

// 添加自定义健康检查
health_checker.add_check(Box::new(MyHealthCheck));

// 执行健康检查
let health_status = health_checker.check_health().await;
println!("健康状态: {:?}", health_status);
```

### 自定义健康检查

```rust
use c13_reliability::runtime_monitoring::*;

struct MyHealthCheck;

#[async_trait]
impl HealthCheck for MyHealthCheck {
    fn name(&self) -> &str {
        "my_service"
    }
    
    async fn check(&self) -> HealthStatus {
        // 实现健康检查逻辑
        HealthStatus::Healthy
    }
}
```

### 资源监控

```rust
use c13_reliability::runtime_monitoring::*;

let resource_monitor = ResourceMonitor::new(Duration::from_secs(10));

// 启动资源监控
let monitor_handle = tokio::spawn(async move {
    resource_monitor.start_monitoring(|usage| {
        println!("CPU: {:.1}%, 内存: {}MB", 
                 usage.cpu_usage_percent, 
                 usage.memory_usage_bytes / 1024 / 1024);
    }).await;
});

// 等待一段时间
tokio::time::sleep(Duration::from_secs(30)).await;

// 停止监控
monitor_handle.abort();
```

### 性能监控

```rust
use c13_reliability::runtime_monitoring::*;

let performance_monitor = PerformanceMonitor::new(Duration::from_secs(10));

// 记录性能指标
let start = std::time::Instant::now();
// 执行操作
let latency = start.elapsed();
performance_monitor.record_request(latency, true);
```

### 异常检测

```rust
use c13_reliability::runtime_monitoring::*;

let anomaly_detector = AnomalyDetector::new(80.0, 1024 * 1024 * 1024, 1000.0, 0.1);

let resource_usage = ResourceUsage {
    timestamp: chrono::Utc::now(),
    cpu_usage_percent: 85.0,
    memory_usage_bytes: 512 * 1024 * 1024,
    disk_usage_bytes: 100 * 1024 * 1024,
    network_io_bytes_total: 1024 * 1024,
};

if let Some(anomaly) = anomaly_detector.detect_resource_anomaly(&resource_usage) {
    println!("检测到异常: {:?}", anomaly);
}
```

## 混沌工程

### 故障注入

```rust
use c13_reliability::chaos_engineering::*;

let fault_injector = FaultInjector::new(FaultInjectionConfig::default());
fault_injector.inject_fault().await?;
```

### 混沌场景

```rust
use c13_reliability::chaos_engineering::*;

let chaos_scenario = ChaosScenario::new(
    "网络延迟测试",
    "模拟网络延迟故障",
    vec![
        ChaosStep::NetworkLatency {
            delay_ms: 1000,
            duration: Duration::from_secs(30),
        },
    ]
);

let chaos_manager = ChaosEngineeringManager::new(ChaosEngineeringConfig::default());
chaos_manager.start().await?;
let test_result = chaos_manager.run_tests().await?;
chaos_manager.stop().await?;
```

## 配置管理

### 基本配置

```rust
use c13_reliability::config::*;

let mut config_manager = ConfigManager::new();

// 从文件加载配置
config_manager.load_from_file("config.toml").await?;

// 获取配置
let config = config_manager.get_config();

// 更新配置
let new_config = ReliabilityConfig::default();
config_manager.update_config(new_config);

// 设置配置值
config_manager.set_value("custom_key", "custom_value")?;

// 获取配置值
if let Some(value) = config_manager.get_value::<String>("custom_key") {
    println!("配置值: {}", value);
}
```

### 配置文件格式

```toml
[global]
app_name = "my_app"
environment = "production"
log_level = "info"
debug_mode = false
config_version = "1.0.0"

[error_handling]
enabled = true
log_level = "info"
max_error_records = 1000
monitoring_interval = "60s"

[fault_tolerance]
enabled = true

[fault_tolerance.circuit_breaker]
failure_threshold = 5
recovery_timeout = "60s"
half_open_max_requests = 3

[fault_tolerance.retry]
max_attempts = 3
initial_delay = "100ms"
delay_factor = 2.0
max_delay = "30s"
enable_jitter = true

[fault_tolerance.timeout]
default_timeout = "30s"
connection_timeout = "10s"
read_timeout = "30s"
write_timeout = "30s"

[fault_tolerance.fallback]
enabled = true
threshold = 0.8
duration = "300s"

[runtime_monitoring]
enabled = true

[runtime_monitoring.health_check]
check_interval = "30s"
timeout = "5s"
enable_global = true

[runtime_monitoring.resource_monitor]
monitor_interval = "60s"
cpu_threshold = 80.0
memory_threshold = 80.0
disk_threshold = 90.0
network_threshold = 70.0

[runtime_monitoring.performance_monitor]
monitor_interval = "60s"
response_time_threshold = "1000ms"
throughput_threshold = 100.0
error_rate_threshold = 0.05
enable_detailed_monitoring = true

[runtime_monitoring.anomaly_detection]
enabled = true
detection_interval = "300s"
anomaly_threshold = 0.8
enable_ml = false

[runtime_monitoring.auto_recovery]
enabled = true
recovery_interval = "300s"
max_recovery_attempts = 3
recovery_timeout = "60s"

[chaos_engineering]
enabled = false

[chaos_engineering.fault_injection]
enabled = false
injection_interval = "60s"
fault_duration = "30s"
fault_probability = 0.1
max_faults = 10

[chaos_engineering.chaos_scenarios]
enabled = false
scenario_interval = "300s"
scenario_duration = "120s"
scenario_probability = 0.05
max_concurrent_scenarios = 3

[chaos_engineering.resilience_testing]
enabled = false
test_interval = "600s"
test_duration = "300s"
max_concurrent_tests = 5

[chaos_engineering.recovery_testing]
enabled = false
test_interval = "900s"
test_duration = "600s"
max_concurrent_tests = 3
```

## 指标收集

### 基本使用

```rust
use c13_reliability::metrics::*;

let metrics_collector = MetricsCollector::new(Duration::from_secs(60));

// 启动指标收集
metrics_collector.start().await?;

// 设置自定义指标
metrics_collector.set_custom_metric("custom_counter".to_string(), MetricValue::Integer(42));
metrics_collector.set_custom_metric("custom_gauge".to_string(), MetricValue::Float(3.14));
metrics_collector.set_custom_metric("custom_label".to_string(), MetricValue::String("test".to_string()));

// 获取当前指标
let current_metrics = metrics_collector.get_current_metrics();
println!("总错误数: {}", current_metrics.error_metrics.total_errors);
println!("错误率: {:.2}%", current_metrics.error_metrics.error_rate * 100.0);
println!("总请求数: {}", current_metrics.performance_metrics.total_requests);
println!("平均响应时间: {:?}", current_metrics.performance_metrics.average_response_time);
println!("CPU使用率: {:.1}%", current_metrics.resource_metrics.cpu_usage);
println!("内存使用率: {:.1}%", current_metrics.resource_metrics.memory_usage);
println!("整体健康状态: {}", current_metrics.health_metrics.overall_health);

// 获取自定义指标
let custom_metrics = metrics_collector.get_all_custom_metrics();
println!("自定义指标: {:?}", custom_metrics);

// 停止指标收集
metrics_collector.stop().await?;
```

## 工具函数

### 持续时间扩展

```rust
use c13_reliability::utils::*;

let duration = Duration::from_secs(3661);
println!("持续时间: {}", duration.human_readable());
```

### 性能工具

```rust
use c13_reliability::utils::*;

let (result, duration) = PerformanceUtils::measure_time(|| {
    // 模拟一些计算
    let mut sum = 0;
    for i in 0..1000000 {
        sum += i;
    }
    sum
});
println!("计算结果: {}, 耗时: {:?}", result, duration);
```

### 配置工具

```rust
use c13_reliability::utils::*;

if let Some(value) = ConfigUtils::get_env_var("TEST_CONFIG") {
    println!("环境变量: {}", value);
}
```

## 最佳实践

### 1. 错误处理

- 使用统一的错误类型
- 记录详细的错误上下文
- 实现适当的错误恢复策略

### 2. 容错机制

- 合理设置断路器参数
- 使用指数退避重试
- 实现降级机制

### 3. 监控

- 定期执行健康检查
- 监控关键性能指标
- 设置异常检测阈值

### 4. 配置管理

- 使用配置文件管理参数
- 支持热重载配置
- 验证配置参数

### 5. 混沌工程

- 在测试环境启用混沌工程
- 定期执行弹性测试
- 验证恢复能力

## 常见问题

### Q: 如何自定义健康检查？

A: 实现 `HealthCheck` trait 并添加到 `HealthChecker` 中。

### Q: 如何调整容错参数？

A: 通过配置文件或 `ConfigManager` 动态调整参数。

### Q: 如何集成到现有项目？

A: 在项目启动时调用 `init()`，在关闭时调用 `shutdown()`。

### Q: 如何监控自定义指标？

A: 使用 `MetricsCollector` 的 `set_custom_metric` 方法。

### Q: 如何启用混沌工程？

A: 在配置文件中设置 `chaos_engineering.enabled = true`。
