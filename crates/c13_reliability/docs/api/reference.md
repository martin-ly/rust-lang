# API 参考文档

## 核心模块

### error_handling

#### UnifiedError

统一错误类型，提供类型安全的错误处理。

```rust
pub struct UnifiedError {
    pub message: String,
    pub severity: ErrorSeverity,
    pub service: String,
    pub context: ErrorContext,
}
```

**方法:**

- `new(message: &str, severity: ErrorSeverity, service: &str, context: ErrorContext) -> Self`
- `with_context(mut self, context: ErrorContext) -> Self`
- `with_severity(mut self, severity: ErrorSeverity) -> Self`

#### ErrorSeverity

错误严重程度枚举。

```rust
pub enum ErrorSeverity {
    Low,
    Medium,
    High,
    Critical,
}
```

#### ErrorContext

错误上下文，记录详细的错误信息。

```rust
pub struct ErrorContext {
    pub service: String,
    pub operation: String,
    pub file: String,
    pub line: u32,
    pub severity: ErrorSeverity,
    pub component: String,
}
```

### fault_tolerance

#### CircuitBreaker

断路器模式，防止级联故障。

```rust
pub struct CircuitBreaker {
    failure_threshold: usize,
    recovery_timeout: Duration,
    state: CircuitState,
}
```

**方法:**

- `new(failure_threshold: usize, recovery_timeout: Duration) -> Self`
- `execute<F, Fut, T, E>(&self, operation: F) -> impl Future<Output = Result<T, E>>`
- `with_retry<R>(self, retrier: R) -> CircuitBreakerWithRetry<R>`
- `with_timeout<T>(self, timeout: T) -> CircuitBreakerWithTimeout<T>`
- `with_fallback<F>(self, fallback: F) -> CircuitBreakerWithFallback<F>`

#### RetryPolicy

重试策略枚举。

```rust
pub enum RetryPolicy {
    Fixed {
        max_attempts: usize,
        delay_ms: u64,
    },
    Exponential {
        max_attempts: usize,
        initial_delay_ms: u64,
        factor: f64,
    },
    Linear {
        max_attempts: usize,
        initial_delay_ms: u64,
        increment_ms: u64,
    },
}
```

#### Retrier

重试器，执行重试逻辑。

```rust
pub struct Retrier {
    policy: RetryPolicy,
}
```

**方法:**

- `new(policy: RetryPolicy) -> Self`
- `execute<F, Fut, T, E>(&self, operation: F) -> impl Future<Output = Result<T, E>>`

### runtime_monitoring

#### HealthChecker

健康检查器，监控系统状态。

```rust
pub struct HealthChecker {
    checks: Vec<Box<dyn HealthCheck>>,
}
```

**方法:**

- `new() -> Self`
- `add_check(&mut self, check: Box<dyn HealthCheck>)`
- `check_health(&self) -> impl Future<Output = HealthStatus>`
- `init_global() -> impl Future<Output = Result<(), UnifiedError>>`
- `shutdown_global() -> impl Future<Output = Result<(), UnifiedError>>`

#### HealthCheck

健康检查 trait。

```rust
#[async_trait]
pub trait HealthCheck: Send + Sync {
    fn name(&self) -> &str;
    async fn check(&self) -> HealthStatus;
}
```

#### HealthStatus

健康状态枚举。

```rust
pub enum HealthStatus {
    Healthy,
    Degraded(String),
    Unhealthy(String),
}
```

#### ResourceMonitor

资源监控器，跟踪系统资源使用。

```rust
pub struct ResourceMonitor {
    monitor_interval: Duration,
}
```

**方法:**

- `new(monitor_interval: Duration) -> Self`
- `start_monitoring<F>(&self, callback: F) -> impl Future<Output = ()>`

#### PerformanceMonitor

性能监控器，分析系统性能指标。

```rust
pub struct PerformanceMonitor {
    monitor_interval: Duration,
}
```

**方法:**

- `new(monitor_interval: Duration) -> Self`
- `record_request(&self, latency: Duration, success: bool)`

### chaos_engineering

#### FaultInjector

故障注入器，模拟各种故障场景。

```rust
pub struct FaultInjector {
    config: FaultInjectionConfig,
}
```

**方法:**

- `new(config: FaultInjectionConfig) -> Self`
- `inject_fault(&self) -> impl Future<Output = Result<(), UnifiedError>>`

#### ChaosScenario

混沌场景，定义复杂的故障测试。

```rust
pub struct ChaosScenario {
    name: String,
    description: String,
    steps: Vec<ChaosStep>,
}
```

### config

#### ConfigManager

配置管理器，统一管理配置。

```rust
pub struct ConfigManager {
    config: ReliabilityConfig,
}
```

**方法:**

- `new() -> Self`
- `load_from_file(&mut self, path: &str) -> impl Future<Output = Result<(), UnifiedError>>`
- `get_config(&self) -> &ReliabilityConfig`
- `update_config(&mut self, config: ReliabilityConfig)`
- `set_value<T>(&mut self, key: &str, value: T) -> Result<(), UnifiedError>`
- `get_value<T>(&self, key: &str) -> Option<T>`

#### ReliabilityConfig

可靠性配置结构。

```rust
pub struct ReliabilityConfig {
    pub global: GlobalConfig,
    pub error_handling: ErrorHandlingConfig,
    pub fault_tolerance: FaultToleranceConfig,
    pub runtime_monitoring: RuntimeMonitoringConfig,
    pub chaos_engineering: ChaosEngineeringConfig,
}
```

### metrics

#### MetricsCollector

指标收集器，收集各种指标。

```rust
pub struct MetricsCollector {
    collect_interval: Duration,
}
```

**方法:**

- `new(collect_interval: Duration) -> Self`
- `start(&self) -> impl Future<Output = Result<(), UnifiedError>>`
- `stop(&self) -> impl Future<Output = Result<(), UnifiedError>>`
- `set_custom_metric(&self, name: String, value: MetricValue)`
- `get_current_metrics(&self) -> ReliabilityMetrics`
- `get_all_custom_metrics(&self) -> HashMap<String, MetricValue>`

#### MetricValue

指标值枚举。

```rust
pub enum MetricValue {
    Integer(i64),
    Float(f64),
    String(String),
    Boolean(bool),
}
```

### utils

#### DurationExt

持续时间扩展 trait。

```rust
pub trait DurationExt {
    fn human_readable(&self) -> String;
}
```

**方法:**

- `human_readable(&self) -> String`

#### PerformanceUtils

性能工具结构。

```rust
pub struct PerformanceUtils;
```

**方法:**

- `measure_time<F, T>(operation: F) -> (T, Duration)`

#### ConfigUtils

配置工具结构。

```rust
pub struct ConfigUtils;
```

**方法:**

- `get_env_var(key: &str) -> Option<String>`

## 宏

### log_error

记录错误的宏。

```rust
macro_rules! log_error {
    ($error:expr, $context:expr) => { ... };
}
```

## 全局函数

### init()

初始化可靠性框架。

```rust
pub async fn init() -> Result<(), UnifiedError>
```

### shutdown()

优雅关闭可靠性框架。

```rust
pub async fn shutdown() -> Result<(), UnifiedError>
```

### version()

获取库版本信息。

```rust
pub fn version() -> &'static str
```

### name()

获取库名称。

```rust
pub fn name() -> &'static str
```

## 错误处理

所有函数都返回 `Result<T, UnifiedError>` 类型，其中：

- `Ok(T)` 表示操作成功
- `Err(UnifiedError)` 表示操作失败，包含详细的错误信息

## 异步支持

所有 I/O 操作都是异步的，使用 `async/await` 语法。需要 Tokio 运行时支持。

## 线程安全

所有公共 API 都是线程安全的，可以在多线程环境中安全使用。
