#![recursion_limit = "8192"]
use anyhow::Result;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tokio::time::{sleep, timeout};
use tracing::{info, warn, debug};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 2025年异步错误恢复和重试机制演示
/// 展示最新的异步错误处理和恢复最佳实践

/// 1. 异步重试策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RetryStrategy {
    Fixed(Duration),
    Exponential(Duration, f64),
    Linear(Duration, Duration),
    Custom(Vec<Duration>),
}

#[derive(Debug, Clone)]
pub struct RetryConfig {
    pub max_attempts: u32,
    pub strategy: RetryStrategy,
    pub jitter: bool,
    pub timeout: Option<Duration>,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            strategy: RetryStrategy::Exponential(Duration::from_millis(100), 2.0),
            jitter: true,
            timeout: Some(Duration::from_secs(30)),
        }
    }
}

pub struct AsyncRetryManager {
    config: RetryConfig,
    metrics: Arc<RwLock<RetryMetrics>>,
}

#[derive(Debug, Default)]
pub struct RetryMetrics {
    pub total_attempts: u64,
    pub successful_attempts: u64,
    pub failed_attempts: u64,
    pub total_retry_time: Duration,
}

impl AsyncRetryManager {
    pub fn new(config: RetryConfig) -> Self {
        Self {
            config,
            metrics: Arc::new(RwLock::new(RetryMetrics::default())),
        }
    }

    #[allow(unused_variables)]
    pub async fn execute_with_retry<F, T>(&self, mut operation: F) -> Result<T>
    where
        F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T>> + Send>>,
    {
        let start_time = Instant::now();
        let mut last_error = None;
        let mut attempt = 1;

        while attempt <= self.config.max_attempts {
            let attempt_start = Instant::now();
            
            // 执行操作（带超时）
            let result = if let Some(timeout_duration) = self.config.timeout {
                match timeout(timeout_duration, operation()).await {
                    Ok(Ok(result)) => {
                        self.update_metrics(true, attempt_start.elapsed()).await;
                        info!("操作在第 {} 次尝试后成功", attempt);
                        return Ok(result);
                    }
                    Ok(Err(e)) => {
                        last_error = Some(e);
                        debug!("操作失败，第 {} 次尝试", attempt);
                    }
                    Err(_) => {
                        last_error = Some(anyhow::anyhow!("操作超时"));
                        warn!("操作超时，第 {} 次尝试", attempt);
                    }
                }
            } else {
                match operation().await {
                    Ok(result) => {
                        self.update_metrics(true, attempt_start.elapsed()).await;
                        info!("操作在第 {} 次尝试后成功", attempt);
                        return Ok(result);
                    }
                    Err(e) => {
                        last_error = Some(e);
                        debug!("操作失败，第 {} 次尝试", attempt);
                    }
                }
            };

            // 更新指标
            self.update_metrics(false, attempt_start.elapsed()).await;

            // 如果不是最后一次尝试，计算延迟并等待
            if attempt < self.config.max_attempts {
                let delay = self.calculate_delay(attempt);
                warn!("操作失败，第 {} 次尝试，{}ms 后重试", attempt, delay.as_millis());
                sleep(delay).await;
            }

            attempt += 1;
        }

        let total_time = start_time.elapsed();
        self.update_total_retry_time(total_time).await;
        
        Err(last_error.unwrap())
    }

    fn calculate_delay(&self, attempt: u32) -> Duration {
        let base_delay = match &self.config.strategy {
            RetryStrategy::Fixed(delay) => *delay,
            RetryStrategy::Exponential(base, multiplier) => {
                Duration::from_millis((base.as_millis() as f64 * multiplier.powi(attempt as i32 - 1)) as u64)
            }
            RetryStrategy::Linear(base, increment) => {
                *base + *increment * (attempt - 1)
            }
            RetryStrategy::Custom(delays) => {
                let index = (attempt - 1) as usize;
                delays.get(index).copied().unwrap_or(*delays.last().unwrap())
            }
        };

        if self.config.jitter {
            let jitter_factor = 0.1; // 10% 抖动
            let jitter_range = base_delay.as_nanos() as f64 * jitter_factor;
            let jitter = (rand::random::<f64>() - 0.5) * 2.0 * jitter_range;
            let jittered_nanos = (base_delay.as_nanos() as f64 + jitter).max(0.0) as u64;
            Duration::from_nanos(jittered_nanos)
        } else {
            base_delay
        }
    }

    #[allow(unused_variables)]
    async fn update_metrics(&self, success: bool, duration: Duration) {
        let mut metrics = self.metrics.write().await;
        metrics.total_attempts += 1;
        
        if success {
            metrics.successful_attempts += 1;
        } else {
            metrics.failed_attempts += 1;
        }
    }

    async fn update_total_retry_time(&self, duration: Duration) {
        let mut metrics = self.metrics.write().await;
        metrics.total_retry_time += duration;
    }

    pub async fn get_metrics(&self) -> RetryMetrics {
        self.metrics.read().await.clone()
    }
}

/// 2. 异步熔断器
#[derive(Debug, Clone, PartialEq)]
pub enum CircuitState {
    Closed,    // 正常状态
    Open,      // 熔断状态
    HalfOpen,  // 半开状态
}

pub struct AsyncCircuitBreaker {
    state: Arc<RwLock<CircuitState>>,
    failure_threshold: u32,
    success_threshold: u32,
    timeout: Duration,
    failure_count: Arc<RwLock<u32>>,
    success_count: Arc<RwLock<u32>>,
    last_failure_time: Arc<RwLock<Option<Instant>>>,
    metrics: Arc<RwLock<CircuitBreakerMetrics>>,
}

#[derive(Debug, Default)]
pub struct CircuitBreakerMetrics {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub circuit_open_count: u64,
    pub circuit_half_open_count: u64,
}

impl AsyncCircuitBreaker {
    pub fn new(failure_threshold: u32, success_threshold: u32, timeout: Duration) -> Self {
        Self {
            state: Arc::new(RwLock::new(CircuitState::Closed)),
            failure_threshold,
            success_threshold,
            timeout,
            failure_count: Arc::new(RwLock::new(0)),
            success_count: Arc::new(RwLock::new(0)),
            last_failure_time: Arc::new(RwLock::new(None)),
            metrics: Arc::new(RwLock::new(CircuitBreakerMetrics::default())),
        }
    }

    pub async fn execute<F, T>(&self, operation: F) -> Result<T>
    where
        F: FnOnce() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T>> + Send>>,
    {
        let current_state = self.state.read().await.clone();
        
        match current_state {
            CircuitState::Open => {
                if self.should_attempt_reset().await {
                    self.transition_to_half_open().await;
                } else {
                    return Err(anyhow::anyhow!("熔断器开启，拒绝请求"));
                }
            }
            CircuitState::Closed => {
                // 正常状态，允许请求
            }
            CircuitState::HalfOpen => {
                // 半开状态，允许少量请求测试
            }
        }

        self.update_metrics_total_requests().await;

        match operation().await {
            Ok(result) => {
                self.on_success().await;
                Ok(result)
            }
            Err(e) => {
                self.on_failure().await;
                Err(e)
            }
        }
    }

    async fn should_attempt_reset(&self) -> bool {
        if let Some(last_failure) = *self.last_failure_time.read().await {
            last_failure.elapsed() >= self.timeout
        } else {
            false
        }
    }

    async fn on_success(&self) {
        self.update_metrics_successful_requests().await;
        
        let current_state = self.state.read().await.clone();
        match current_state {
            CircuitState::HalfOpen => {
                let mut success_count = self.success_count.write().await;
                *success_count += 1;
                
                if *success_count >= self.success_threshold {
                    self.transition_to_closed().await;
                }
            }
            CircuitState::Closed => {
                // 重置失败计数
                *self.failure_count.write().await = 0;
            }
            CircuitState::Open => {
                // 不应该发生
            }
        }
    }

    async fn on_failure(&self) {
        self.update_metrics_failed_requests().await;
        
        let mut failure_count = self.failure_count.write().await;
        *failure_count += 1;
        
        *self.last_failure_time.write().await = Some(Instant::now());
        
        if *failure_count >= self.failure_threshold {
            self.transition_to_open().await;
        }
    }

    async fn transition_to_open(&self) {
        *self.state.write().await = CircuitState::Open;
        *self.success_count.write().await = 0;
        self.update_metrics_circuit_open().await;
        warn!("熔断器状态转换为: Open");
    }

    async fn transition_to_half_open(&self) {
        *self.state.write().await = CircuitState::HalfOpen;
        *self.success_count.write().await = 0;
        self.update_metrics_circuit_half_open().await;
        info!("熔断器状态转换为: HalfOpen");
    }

    async fn transition_to_closed(&self) {
        *self.state.write().await = CircuitState::Closed;
        *self.failure_count.write().await = 0;
        info!("熔断器状态转换为: Closed");
    }

    async fn update_metrics_total_requests(&self) {
        self.metrics.write().await.total_requests += 1;
    }

    async fn update_metrics_successful_requests(&self) {
        self.metrics.write().await.successful_requests += 1;
    }

    async fn update_metrics_failed_requests(&self) {
        self.metrics.write().await.failed_requests += 1;
    }

    async fn update_metrics_circuit_open(&self) {
        self.metrics.write().await.circuit_open_count += 1;
    }

    async fn update_metrics_circuit_half_open(&self) {
        self.metrics.write().await.circuit_half_open_count += 1;
    }

    pub async fn get_state(&self) -> CircuitState {
        self.state.read().await.clone()
    }

    pub async fn get_metrics(&self) -> CircuitBreakerMetrics {
        self.metrics.read().await.clone()
    }
}

/// 3. 异步超时管理器
pub struct AsyncTimeoutManager {
    default_timeout: Duration,
    timeouts: Arc<RwLock<HashMap<String, Duration>>>,
    metrics: Arc<RwLock<TimeoutMetrics>>,
}

#[derive(Debug, Default)]
pub struct TimeoutMetrics {
    pub total_operations: u64,
    pub timed_out_operations: u64,
    pub successful_operations: u64,
    pub average_duration: Duration,
}

impl AsyncTimeoutManager {
    pub fn new(default_timeout: Duration) -> Self {
        Self {
            default_timeout,
            timeouts: Arc::new(RwLock::new(HashMap::new())),
            metrics: Arc::new(RwLock::new(TimeoutMetrics::default())),
        }
    }

    pub async fn set_timeout(&self, operation_name: String, timeout: Duration) {
        self.timeouts.write().await.insert(operation_name, timeout);
    }

    pub async fn execute_with_timeout<F, T>(
        &self,
        operation_name: &str,
        mut operation: F,
    ) -> Result<T>
    where
        F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T>> + Send>>,
    {
        let timeout_duration = self.get_timeout_for_operation(operation_name).await;
        let start_time = Instant::now();

        self.update_metrics_total_operations().await;

        match timeout(timeout_duration, operation()).await {
            Ok(Ok(result)) => {
                let duration = start_time.elapsed();
                self.update_metrics_successful_operation(duration).await;
                Ok(result)
            }
            Ok(Err(e)) => {
                let duration = start_time.elapsed();
                self.update_metrics_successful_operation(duration).await;
                Err(e)
            }
            Err(_) => {
                let duration = start_time.elapsed();
                self.update_metrics_timed_out_operation(duration).await;
                Err(anyhow::anyhow!("操作 '{}' 超时 ({:?})", operation_name, timeout_duration))
            }
        }
    }

    async fn get_timeout_for_operation(&self, operation_name: &str) -> Duration {
        self.timeouts
            .read()
            .await
            .get(operation_name)
            .copied()
            .unwrap_or(self.default_timeout)
    }

    async fn update_metrics_total_operations(&self) {
        self.metrics.write().await.total_operations += 1;
    }

    async fn update_metrics_successful_operation(&self, duration: Duration) {
        let mut metrics = self.metrics.write().await;
        metrics.successful_operations += 1;
        
        // 更新平均持续时间
        let total_ops = metrics.total_operations;
        let total_duration = metrics.average_duration.as_nanos() * (total_ops - 1) as u128 + duration.as_nanos();
        metrics.average_duration = Duration::from_nanos((total_duration / total_ops as u128) as u64);
    }

    async fn update_metrics_timed_out_operation(&self, duration: Duration) {
        let mut metrics = self.metrics.write().await;
        metrics.timed_out_operations += 1;
        
        // 更新平均持续时间（包括超时的操作）
        let total_ops = metrics.total_operations;
        let total_duration = metrics.average_duration.as_nanos() * (total_ops - 1) as u128 + duration.as_nanos();
        metrics.average_duration = Duration::from_nanos((total_duration / total_ops as u128) as u64);
    }

    pub async fn get_metrics(&self) -> TimeoutMetrics {
        self.metrics.read().await.clone()
    }
}

/// 4. 异步错误恢复策略
#[derive(Debug, Clone)]
pub enum RecoveryStrategy {
    Retry(RetryConfig),
    CircuitBreaker(u32, u32, Duration),
    Timeout(Duration),
    Fallback(String), // 简化为字符串标识
}

pub struct AsyncErrorRecoveryManager {
    strategies: Arc<RwLock<HashMap<String, RecoveryStrategy>>>,
    recovery_metrics: Arc<RwLock<RecoveryMetrics>>,
}

#[derive(Debug, Default)]
pub struct RecoveryMetrics {
    pub total_recoveries: u64,
    pub successful_recoveries: u64,
    pub failed_recoveries: u64,
    pub recovery_types: HashMap<String, u64>,
}

impl AsyncErrorRecoveryManager {
    pub fn new() -> Self {
        Self {
            strategies: Arc::new(RwLock::new(HashMap::new())),
            recovery_metrics: Arc::new(RwLock::new(RecoveryMetrics::default())),
        }
    }

    pub async fn add_recovery_strategy(&self, operation_name: String, strategy: RecoveryStrategy) {
        self.strategies.write().await.insert(operation_name, strategy);
    }

    pub async fn execute_with_recovery<F, T>(
        &self,
        operation_name: &str,
        mut operation: F,
    ) -> Result<T>
    where
        F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T>> + Send>>,
    {
        let strategies = self.strategies.read().await;
        
        if let Some(strategy) = strategies.get(operation_name) {
            self.apply_recovery_strategy(strategy, operation).await
        } else {
            // 没有恢复策略，直接执行
            operation().await
        }
    }

    async fn apply_recovery_strategy<F, T>(
        &self,
        strategy: &RecoveryStrategy,
        mut operation: F,
    ) -> Result<T>
    where
        F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T>> + Send>>,
    {
        match strategy {
            RecoveryStrategy::Retry(config) => {
                let retry_manager = AsyncRetryManager::new(config.clone());
                retry_manager.execute_with_retry(|| operation()).await
            }
            RecoveryStrategy::CircuitBreaker(failure_threshold, success_threshold, timeout) => {
                let circuit_breaker = AsyncCircuitBreaker::new(*failure_threshold, *success_threshold, *timeout);
                circuit_breaker.execute(|| operation()).await
            }
            RecoveryStrategy::Timeout(duration) => {
                let timeout_manager = AsyncTimeoutManager::new(*duration);
                timeout_manager.execute_with_timeout("operation", || operation()).await
            }
            RecoveryStrategy::Fallback(fallback_msg) => {
                match operation().await {
                    Ok(result) => Ok(result),
                    Err(_) => {
                        self.update_recovery_metrics("fallback", true).await;
                        // 简化：直接返回错误，因为类型转换复杂
                        Err(anyhow::anyhow!("操作失败，回退: {}", fallback_msg))
                    }
                }
            }
        }
    }

    async fn update_recovery_metrics(&self, recovery_type: &str, success: bool) {
        let mut metrics = self.recovery_metrics.write().await;
        metrics.total_recoveries += 1;
        
        if success {
            metrics.successful_recoveries += 1;
        } else {
            metrics.failed_recoveries += 1;
        }
        
        *metrics.recovery_types.entry(recovery_type.to_string()).or_insert(0) += 1;
    }

    pub async fn get_metrics(&self) -> RecoveryMetrics {
        self.recovery_metrics.read().await.clone()
    }
}

/// 演示异步错误恢复和重试机制
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();

    info!("🚀 开始 2025 年异步错误恢复和重试机制演示");

    // 1. 异步重试管理器演示
    demo_async_retry_manager().await?;

    // 2. 异步熔断器演示
    demo_async_circuit_breaker().await?;

    // 3. 异步超时管理器演示
    demo_async_timeout_manager().await?;

    // 4. 异步错误恢复管理器演示
    demo_async_error_recovery_manager().await?;

    info!("✅ 2025 年异步错误恢复和重试机制演示完成!");
    Ok(())
}

async fn demo_async_retry_manager() -> Result<()> {
    info!("🔄 演示异步重试管理器");

    // 指数退避策略
    let retry_config = RetryConfig {
        max_attempts: 5,
        strategy: RetryStrategy::Exponential(Duration::from_millis(100), 2.0),
        jitter: true,
        timeout: Some(Duration::from_secs(1)),
    };

    let retry_manager = AsyncRetryManager::new(retry_config);

    let mut attempt_count = 0;
    let result = retry_manager.execute_with_retry(|| {
        attempt_count += 1;
        Box::pin(async move {
            // 模拟可能失败的操作
            if attempt_count < 4 {
                Err(anyhow::anyhow!("模拟失败 (尝试 {})", attempt_count))
            } else {
                Ok(format!("操作成功 (尝试 {})", attempt_count))
            }
        })
    }).await?;

    info!("重试结果: {}", result);

    let metrics = retry_manager.get_metrics().await;
    info!("重试指标: 总尝试 {}, 成功 {}, 失败 {}", 
          metrics.total_attempts, metrics.successful_attempts, metrics.failed_attempts);

    Ok(())
}

async fn demo_async_circuit_breaker() -> Result<()> {
    info!("⚡ 演示异步熔断器");

    let circuit_breaker = AsyncCircuitBreaker::new(3, 2, Duration::from_millis(500));

    // 模拟一系列操作
    for i in 1..=10 {
        let result = circuit_breaker.execute(|| {
            Box::pin(async move {
                // 前几次操作失败，触发熔断
                if i <= 4 {
                    Err(anyhow::anyhow!("操作失败"))
                } else {
                    Ok(format!("操作成功 {}", i))
                }
            })
        }).await;

        let state = circuit_breaker.get_state().await;
        match result {
            Ok(msg) => info!("操作 {} 成功: {}, 熔断器状态: {:?}", i, msg, state),
            Err(e) => warn!("操作 {} 失败: {}, 熔断器状态: {:?}", i, e, state),
        }

        sleep(Duration::from_millis(100)).await;
    }

    let metrics = circuit_breaker.get_metrics().await;
    info!("熔断器指标: 总请求 {}, 成功 {}, 失败 {}, 开启次数 {}", 
          metrics.total_requests, metrics.successful_requests, 
          metrics.failed_requests, metrics.circuit_open_count);

    Ok(())
}

async fn demo_async_timeout_manager() -> Result<()> {
    info!("⏱️ 演示异步超时管理器");

    let timeout_manager = AsyncTimeoutManager::new(Duration::from_millis(200));

    // 设置不同操作的超时时间
    timeout_manager.set_timeout("fast_operation".to_string(), Duration::from_millis(100)).await;
    timeout_manager.set_timeout("slow_operation".to_string(), Duration::from_millis(500)).await;

    // 快速操作
    let result = timeout_manager.execute_with_timeout("fast_operation", || {
        Box::pin(async move {
            sleep(Duration::from_millis(50)).await;
            Ok("快速操作完成".to_string())
        })
    }).await?;
    info!("快速操作结果: {}", result);

    // 超时操作
    let result = timeout_manager.execute_with_timeout("fast_operation", || {
        Box::pin(async move {
            sleep(Duration::from_millis(300)).await; // 超过超时时间
            Ok("超时操作完成".to_string())
        })
    }).await;
    match result {
        Ok(msg) => info!("超时操作结果: {}", msg),
        Err(e) => warn!("超时操作失败: {}", e),
    }

    let metrics = timeout_manager.get_metrics().await;
    info!("超时管理器指标: 总操作 {}, 成功 {}, 超时 {}, 平均耗时 {:?}", 
          metrics.total_operations, metrics.successful_operations, 
          metrics.timed_out_operations, metrics.average_duration);

    Ok(())
}

async fn demo_async_error_recovery_manager() -> Result<()> {
    info!("🛡️ 演示异步错误恢复管理器");

    let recovery_manager = AsyncErrorRecoveryManager::new();

    // 添加重试策略
    let retry_config = RetryConfig {
        max_attempts: 3,
        strategy: RetryStrategy::Fixed(Duration::from_millis(100)),
        jitter: false,
        timeout: None,
    };
    recovery_manager.add_recovery_strategy(
        "retry_operation".to_string(),
        RecoveryStrategy::Retry(retry_config)
    ).await;

    // 添加熔断器策略
    recovery_manager.add_recovery_strategy(
        "circuit_breaker_operation".to_string(),
        RecoveryStrategy::CircuitBreaker(2, 1, Duration::from_millis(200))
    ).await;

    // 添加回退策略
    recovery_manager.add_recovery_strategy(
        "fallback_operation".to_string(),
        RecoveryStrategy::Fallback("回退操作结果".to_string())
    ).await;

    // 测试重试策略
    let mut attempt_count = 0;
    let result = recovery_manager.execute_with_recovery("retry_operation", || {
        attempt_count += 1;
        Box::pin(async move {
            if attempt_count < 3 {
                Err(anyhow::anyhow!("模拟失败"))
            } else {
                Ok("重试操作成功".to_string())
            }
        })
    }).await?;
    info!("重试策略结果: {}", result);

    // 测试回退策略
    let result: Result<String, _> = recovery_manager.execute_with_recovery("fallback_operation", || {
        Box::pin(async move {
            Err(anyhow::anyhow!("主要操作失败"))
        })
    }).await;
    match result {
        Ok(msg) => info!("回退策略结果: {}", msg),
        Err(e) => info!("回退策略结果: {}", e),
    }

    let metrics = recovery_manager.get_metrics().await;
    info!("错误恢复指标: 总恢复 {}, 成功 {}, 失败 {}", 
          metrics.total_recoveries, metrics.successful_recoveries, metrics.failed_recoveries);

    Ok(())
}

// 为测试添加Clone实现
impl Clone for RetryMetrics {
    fn clone(&self) -> Self {
        Self {
            total_attempts: self.total_attempts,
            successful_attempts: self.successful_attempts,
            failed_attempts: self.failed_attempts,
            total_retry_time: self.total_retry_time,
        }
    }
}

impl Clone for CircuitBreakerMetrics {
    fn clone(&self) -> Self {
        Self {
            total_requests: self.total_requests,
            successful_requests: self.successful_requests,
            failed_requests: self.failed_requests,
            circuit_open_count: self.circuit_open_count,
            circuit_half_open_count: self.circuit_half_open_count,
        }
    }
}

impl Clone for TimeoutMetrics {
    fn clone(&self) -> Self {
        Self {
            total_operations: self.total_operations,
            timed_out_operations: self.timed_out_operations,
            successful_operations: self.successful_operations,
            average_duration: self.average_duration,
        }
    }
}

impl Clone for RecoveryMetrics {
    fn clone(&self) -> Self {
        Self {
            total_recoveries: self.total_recoveries,
            successful_recoveries: self.successful_recoveries,
            failed_recoveries: self.failed_recoveries,
            recovery_types: self.recovery_types.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_retry_manager() {
        let config = RetryConfig {
            max_attempts: 3,
            strategy: RetryStrategy::Fixed(Duration::from_millis(10)),
            jitter: false,
            timeout: None,
        };
        
        let retry_manager = AsyncRetryManager::new(config);
        
        let mut attempt_count = 0;
        let result = retry_manager.execute_with_retry(|| {
            attempt_count += 1;
            Box::pin(async move {
                if attempt_count < 3 {
                    Err(anyhow::anyhow!("模拟失败"))
                } else {
                    Ok("成功".to_string())
                }
            })
        }).await;
        
        assert!(result.is_ok());
        assert_eq!(attempt_count, 3);
    }

    #[tokio::test]
    async fn test_async_circuit_breaker() {
        let circuit_breaker = AsyncCircuitBreaker::new(2, 1, Duration::from_millis(100));
        
        // 触发熔断
        for _ in 0..3 {
            let _ = circuit_breaker.execute(|| {
                Box::pin(async move { Err::<String, _>(anyhow::anyhow!("失败")) })
            }).await;
        }
        
        assert_eq!(circuit_breaker.get_state().await, CircuitState::Open);
    }

    #[tokio::test]
    async fn test_async_timeout_manager() {
        let timeout_manager = AsyncTimeoutManager::new(Duration::from_millis(50));
        
        let result = timeout_manager.execute_with_timeout("test", || {
            Box::pin(async move {
                sleep(Duration::from_millis(100)).await;
                Ok("成功".to_string())
            })
        }).await;
        
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("超时"));
    }
}
