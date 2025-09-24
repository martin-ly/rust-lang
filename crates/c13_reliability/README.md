# Rust 统一可靠性框架

一个全面的 Rust 可靠性解决方案，提供企业级的错误处理、容错机制、运行时监控和混沌工程测试功能。

## 特性

- **统一错误处理**：类型安全、上下文丰富的错误处理系统
- **容错机制**：断路器、重试、超时、降级等企业级容错模式
- **运行时监控**：健康检查、性能监控、异常检测
- **自动恢复**：内存泄漏检测、连接池重建、死锁恢复
- **混沌工程**：故障注入、弹性测试、恢复验证
- **配置管理**：灵活的配置系统，支持热重载
- **指标收集**：全面的指标收集和分析
- **工具函数**：丰富的工具函数和扩展
- **多环境支持**：支持操作系统、嵌入式裸机、Docker容器三种运行环境

## 快速开始

### 添加依赖

在 `Cargo.toml` 中添加：

```toml
[dependencies]
c13_reliability = "0.1.0"
tokio = { version = "1.0", features = ["full"] }
env_logger = "0.9"
```

### 基本使用

```rust
use c13_reliability::prelude::*;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), UnifiedError> {
    // 初始化可靠性框架
    c13_reliability::init().await?;
    
    // 创建断路器
    let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(60));
    
    // 创建重试策略
    let retry_policy = RetryPolicy::exponential_backoff(3, Duration::from_millis(100));
    
    // 执行带容错的操作
    let result = circuit_breaker
        .with_retry(retry_policy)
        .execute(|| async {
            // 你的业务逻辑
            Ok::<String, UnifiedError>("success".to_string())
        })
        .await?;
    
    println!("操作结果: {}", result);
    
    // 关闭可靠性框架
    c13_reliability::shutdown().await?;
    Ok(())
}
```

## 核心模块

### 错误处理

提供统一的错误处理系统，包括错误分类、上下文记录和恢复策略。

```rust
use c13_reliability::error_handling::*;

// 创建统一错误
let error = UnifiedError::new(
    "操作失败",
    ErrorSeverity::Medium,
    "service",
    ErrorContext::new("service", "operation", file!(), line!(), ErrorSeverity::Medium, "service")
);

// 记录错误
log_error!(error, "操作上下文");

// 使用错误恢复策略
let recovery_strategy = RecoveryStrategy::Retry {
    max_attempts: 3,
    delay_ms: 1000,
    exponential_backoff: true,
};

let error_handler = ErrorHandler::new(recovery_strategy);
```

### 容错机制

提供断路器、重试、超时、降级等容错模式。

```rust
use c13_reliability::fault_tolerance::*;

// 创建断路器
let circuit_breaker = CircuitBreaker::new(5, Duration::from_secs(60));

// 创建重试策略
let retry_policy = RetryPolicy::Exponential {
    max_attempts: 3,
    initial_delay_ms: 100,
    factor: 2,
};

// 创建超时机制
let timeout = Timeout::new(Duration::from_secs(5));

// 创建降级机制
let fallback = Fallback::new(Some("降级响应".to_string()));

// 组合使用
let result = circuit_breaker
    .with_retry(Retrier::new(retry_policy))
    .with_timeout(timeout)
    .with_fallback(fallback)
    .execute(|| async {
        // 你的业务逻辑
        Ok::<String, UnifiedError>("success".to_string())
    })
    .await;
```

### 运行时监控

提供健康检查、性能监控、异常检测和自动恢复功能。

```rust
use c13_reliability::runtime_monitoring::*;

// 创建健康检查器
let health_checker = HealthChecker::new();

// 添加健康检查项目
health_checker.add_check(Box::new(DatabaseHealthCheck));
health_checker.add_check(Box::new(CacheHealthCheck));

// 执行健康检查
let health_status = health_checker.check_health().await;

// 创建资源监控器
let resource_monitor = ResourceMonitor::new(Duration::from_secs(10));

// 启动资源监控
resource_monitor.start_monitoring(|usage| {
    println!("CPU: {:.1}%, 内存: {}MB", 
             usage.cpu_usage_percent, 
             usage.memory_usage_bytes / 1024 / 1024);
}).await;

// 创建性能监控器
let performance_monitor = PerformanceMonitor::new(Duration::from_secs(10));

// 记录性能指标
performance_monitor.record_request(Duration::from_millis(100), true);

// 创建异常检测器
let anomaly_detector = AnomalyDetector::new(80.0, 1024 * 1024 * 1024, 1000.0, 0.1);

// 检测异常
if let Some(anomaly) = anomaly_detector.detect_resource_anomaly(&resource_usage) {
    println!("检测到异常: {:?}", anomaly);
}

// 创建自动恢复器
let auto_recovery = AutoRecovery::new(AutoRecoveryConfig::default());

// 启动自动恢复
auto_recovery.start().await?;
```

### 混沌工程

提供故障注入、弹性测试和恢复验证功能。

```rust
use c13_reliability::chaos_engineering::*;

// 创建混沌工程管理器
let chaos_manager = ChaosEngineeringManager::new(ChaosEngineeringConfig::default());

// 启动混沌工程测试
chaos_manager.start().await?;

// 执行混沌工程测试
let test_result = chaos_manager.run_tests().await?;

println!("总体评分: {:.2}", test_result.overall_assessment.overall_score);
println!("弹性评分: {:.2}", test_result.overall_assessment.resilience_score);
println!("恢复评分: {:.2}", test_result.overall_assessment.recovery_score);

// 停止混沌工程测试
chaos_manager.stop().await?;
```

### 配置管理

提供灵活的配置系统，支持热重载。

```rust
use c13_reliability::config::*;

// 创建配置管理器
let mut config_manager = ConfigManager::new();

// 从文件加载配置
config_manager.load_from_file("config.toml").await?;

// 获取配置
let config = config_manager.get_config();

// 更新配置
config_manager.update_config(new_config);

// 设置配置值
config_manager.set_value("custom_key", "custom_value")?;

// 获取配置值
if let Some(value) = config_manager.get_value::<String>("custom_key") {
    println!("配置值: {}", value);
}
```

### 指标收集

提供全面的指标收集和分析功能。

```rust
use c13_reliability::metrics::*;

// 创建指标收集器
let metrics_collector = MetricsCollector::new(Duration::from_secs(60));

// 启动指标收集
metrics_collector.start().await?;

// 设置自定义指标
metrics_collector.set_custom_metric("custom_counter".to_string(), MetricValue::Integer(42));
metrics_collector.set_custom_metric("custom_gauge".to_string(), MetricValue::Float(3.14));

// 获取当前指标
let current_metrics = metrics_collector.get_current_metrics();

println!("总错误数: {}", current_metrics.error_metrics.total_errors);
println!("错误率: {:.2}%", current_metrics.error_metrics.error_rate * 100.0);
println!("总请求数: {}", current_metrics.performance_metrics.total_requests);
println!("平均响应时间: {:?}", current_metrics.performance_metrics.average_response_time);
println!("CPU使用率: {:.1}%", current_metrics.resource_metrics.cpu_usage);
println!("内存使用率: {:.1}%", current_metrics.resource_metrics.memory_usage);
println!("整体健康状态: {}", current_metrics.health_metrics.overall_health);

// 停止指标收集
metrics_collector.stop().await?;
```

### 工具函数

提供丰富的工具函数和扩展。

```rust
use c13_reliability::utils::*;

// 持续时间扩展
let duration = Duration::from_secs(3661);
println!("持续时间: {}", duration.human_readable());

// 字符串扩展
let s = "hello world".to_string();
println!("标题格式: {}", s.to_title_case());
println!("蛇形命名: {}", s.to_snake_case());
println!("驼峰命名: {}", s.to_camel_case());

// 数字扩展
let number = 1000000u64;
println!("数字: {}", number.human_readable());
println!("百分比: {:.1}%", number.percentage(2000000));

// 性能工具
let (result, duration) = PerformanceUtils::measure_time(|| {
    // 模拟一些计算
    let mut sum = 0;
    for i in 0..1000000 {
        sum += i;
    }
    sum
});
println!("计算结果: {}, 耗时: {:?}", result, duration);

// 配置工具
if let Some(value) = ConfigUtils::get_env_var("TEST_CONFIG") {
    println!("环境变量: {}", value);
}

// 错误处理工具
let error = UnifiedError::new(
    "测试错误",
    ErrorSeverity::Low,
    "example",
    ErrorContext::new("example", "test", file!(), line!(), ErrorSeverity::Low, "example")
);

ErrorHandler::handle_error(&error, "工具函数示例");
```

## 配置

### 基本配置

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

## 运行时环境支持

本框架支持三种不同的运行时环境：

### 1. 操作系统环境

完整的操作系统支持，包括多进程、多线程、文件系统和网络支持。

```rust
use c13_reliability::prelude::*;

let mut adapter = OSEnvironmentAdapter::new();
adapter.initialize().await?;
let system_info = adapter.get_system_info().await?;
```

### 2. 嵌入式裸机环境

无操作系统环境，直接运行在硬件上，支持中断和定时器。

```rust
use c13_reliability::prelude::*;

let mut adapter = EmbeddedEnvironmentAdapter::with_config(
    2 * 1024 * 1024, // 2MB 内存
    2, // 2个CPU核心
    1 * 1024 * 1024, // 1MB 磁盘
);
adapter.initialize().await?;
```

### 3. Docker容器环境

容器化运行环境，支持资源限制监控和容器健康检查。

```rust
use c13_reliability::prelude::*;

let mut adapter = ContainerEnvironmentAdapter::new();
adapter.initialize().await?;
let health_status = adapter.check_health().await?;
```

详细的环境支持指南请查看 [RUNTIME_ENVIRONMENTS_GUIDE.md](RUNTIME_ENVIRONMENTS_GUIDE.md)。

## 示例

查看 `examples/` 目录中的示例代码：

- `basic_usage.rs` - 基本使用示例
- `advanced_usage.rs` - 高级使用示例
- `integration_example.rs` - 集成示例
- `runtime_environment_example.rs` - 运行时环境示例

## 测试

运行测试：

```bash
cargo test
```

运行示例：

```bash
cargo run --example basic_usage
```

## 贡献

欢迎贡献代码！请查看 `CONTRIBUTING.md` 了解详细信息。

## 许可证

本项目采用 MIT 许可证。查看 `LICENSE` 文件了解详细信息。

## 更新日志

### v0.1.0

- 初始版本
- 统一错误处理系统
- 容错机制（断路器、重试、超时、降级）
- 运行时监控（健康检查、性能监控、异常检测）
- 自动恢复功能
- 混沌工程测试工具
- 配置管理系统
- 指标收集和分析
- 工具函数和扩展
