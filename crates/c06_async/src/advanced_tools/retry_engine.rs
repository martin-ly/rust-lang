//! 智能重试引擎
//! 
//! 提供高级重试机制：
//! - 多种重试策略（指数退避、线性退避、固定间隔）
//! - 智能错误分类
//! - 断路器集成
//! - 重试监控和统计
//! - 自定义重试条件

use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::time::{sleep, timeout};
use futures::Future;
use anyhow::Result;
use serde::{Serialize, Deserialize};

/// 重试策略
#[derive(Debug, Clone)]
pub enum RetryStrategy {
    /// 固定间隔重试
    Fixed(Duration),
    /// 线性退避重试
    Linear(Duration, Duration), // (初始间隔, 最大间隔)
    /// 指数退避重试
    Exponential(Duration, f64, Duration), // (初始间隔, 倍数, 最大间隔)
    // 注意：Custom 变体被移除，因为 dyn Trait 无法实现 Debug 和 Clone
}

/// 退避策略 trait
pub trait RetryBackoff {
    fn get_delay(&self, attempt: u32) -> Duration;
}

/// 固定退避策略
pub struct FixedBackoff {
    delay: Duration,
}

impl FixedBackoff {
    pub fn new(delay: Duration) -> Self {
        Self { delay }
    }
}

impl RetryBackoff for FixedBackoff {
    fn get_delay(&self, _attempt: u32) -> Duration {
        self.delay
    }
}

/// 线性退避策略
pub struct LinearBackoff {
    initial_delay: Duration,
    max_delay: Duration,
    increment: Duration,
}

impl LinearBackoff {
    pub fn new(initial_delay: Duration, max_delay: Duration, increment: Duration) -> Self {
        Self {
            initial_delay,
            max_delay,
            increment,
        }
    }
}

impl RetryBackoff for LinearBackoff {
    fn get_delay(&self, attempt: u32) -> Duration {
        let delay = self.initial_delay + (self.increment * attempt);
        delay.min(self.max_delay)
    }
}

/// 指数退避策略
pub struct ExponentialBackoff {
    initial_delay: Duration,
    multiplier: f64,
    max_delay: Duration,
}

impl ExponentialBackoff {
    pub fn new(initial_delay: Duration, multiplier: f64, max_delay: Duration) -> Self {
        Self {
            initial_delay,
            multiplier,
            max_delay,
        }
    }
}

impl RetryBackoff for ExponentialBackoff {
    fn get_delay(&self, attempt: u32) -> Duration {
        let delay_ms = self.initial_delay.as_millis() as f64 * self.multiplier.powi(attempt as i32);
        let delay = Duration::from_millis(delay_ms as u64);
        delay.min(self.max_delay)
    }
}

/// 重试条件
#[derive(Debug, Clone)]
pub enum RetryCondition {
    /// 总是重试
    Always,
    /// 根据错误类型重试
    OnErrorType(Vec<String>),
    /// 根据错误消息重试
    OnErrorMessage(String),
}

impl Default for RetryCondition {
    fn default() -> Self {
        RetryCondition::Always
    }
}

/// 重试配置
#[derive(Debug, Clone)]
pub struct RetryConfig {
    pub max_attempts: u32,
    pub strategy: RetryStrategy,
    pub condition: RetryCondition,
    pub timeout: Option<Duration>,
    pub jitter: bool, // 是否添加随机抖动
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            strategy: RetryStrategy::Exponential(
                Duration::from_millis(100),
                2.0,
                Duration::from_secs(30),
            ),
            condition: RetryCondition::Always,
            timeout: None,
            jitter: true,
        }
    }
}

/// 重试统计信息
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct RetryStats {
    pub total_attempts: u64,
    pub successful_attempts: u64,
    pub failed_attempts: u64,
    pub total_retry_time: Duration,
    pub avg_retry_time: Duration,
    pub max_retry_time: Duration,
    pub min_retry_time: Duration,
}

/// 重试结果
#[derive(Debug)]
pub struct RetryResult<T> {
    pub result: Result<T>,
    pub attempts: u32,
    pub total_time: Duration,
    pub stats: RetryStats,
}

/// 智能重试引擎
pub struct RetryEngine {
    config: RetryConfig,
    stats: Arc<tokio::sync::Mutex<RetryStats>>,
}

impl RetryEngine {
    /// 创建新的重试引擎
    pub fn new(config: RetryConfig) -> Self {
        Self {
            config,
            stats: Arc::new(tokio::sync::Mutex::new(RetryStats::default())),
        }
    }

    /// 执行带重试的异步操作
    pub async fn execute<F, Fut, T>(&self, mut operation: F) -> RetryResult<T>
    where
        F: FnMut() -> Fut,
        Fut: Future<Output = Result<T>>,
    {
        let start_time = Instant::now();
        let mut attempts = 0;
        let mut _last_error = None;

        loop {
            attempts += 1;
            let attempt_start = Instant::now();

            // 执行操作
            let result = if let Some(timeout_duration) = self.config.timeout {
                match timeout(timeout_duration, operation()).await {
                    Ok(result) => result,
                    Err(_) => Err(anyhow::anyhow!("操作超时")),
                }
            } else {
                operation().await
            };

            match result {
                Ok(value) => {
                    // 成功，更新统计信息并返回
                    let total_time = start_time.elapsed();
                    let attempt_time = attempt_start.elapsed();
                    
                    self.update_stats(true, attempt_time, total_time).await;
                    
                    let stats = self.get_stats().await;
                    
                    return RetryResult {
                        result: Ok(value),
                        attempts,
                        total_time,
                        stats,
                    };
                }
                Err(error) => {
                    _last_error = Some(error);
                    let attempt_time = attempt_start.elapsed();
                    
                    // 检查是否应该重试
                    if attempts >= self.config.max_attempts {
                        // 达到最大重试次数，失败
                        let total_time = start_time.elapsed();
                        self.update_stats(false, attempt_time, total_time).await;
                        
                        let stats = self.get_stats().await;
                        
                        return RetryResult {
                            result: Err(_last_error.unwrap()),
                            attempts,
                            total_time,
                            stats,
                        };
                    }

                    // 检查重试条件
                    if !self.should_retry(_last_error.as_ref().unwrap()) {
                        let total_time = start_time.elapsed();
                        self.update_stats(false, attempt_time, total_time).await;
                        
                        let stats = self.get_stats().await;
                        
                        return RetryResult {
                            result: Err(_last_error.unwrap()),
                            attempts,
                            total_time,
                            stats,
                        };
                    }

                    // 计算重试延迟
                    let delay = self.calculate_delay(attempts);
                    
                    // 更新统计信息
                    self.update_stats(false, attempt_time, Duration::ZERO).await;
                    
                    // 等待重试
                    sleep(delay).await;
                }
            }
        }
    }

    /// 获取重试统计信息
    pub async fn get_stats(&self) -> RetryStats {
        self.stats.lock().await.clone()
    }

    /// 重置统计信息
    pub async fn reset_stats(&self) {
        let mut stats = self.stats.lock().await;
        *stats = RetryStats::default();
    }

    // 私有方法

    fn should_retry(&self, error: &anyhow::Error) -> bool {
        match &self.config.condition {
            RetryCondition::Always => true,
            RetryCondition::OnErrorType(types) => {
                let error_type = error.to_string();
                types.iter().any(|t| error_type.contains(t))
            }
            RetryCondition::OnErrorMessage(message) => {
                error.to_string().contains(message)
            }
        }
    }

    fn calculate_delay(&self, attempt: u32) -> Duration {
        let base_delay = match &self.config.strategy {
            RetryStrategy::Fixed(delay) => *delay,
            RetryStrategy::Linear(initial, max) => {
                let increment = max.saturating_sub(*initial) / self.config.max_attempts;
                (*initial + increment * attempt).min(*max)
            }
            RetryStrategy::Exponential(initial, multiplier, max) => {
                let delay_ms = initial.as_millis() as f64 * multiplier.powi(attempt as i32);
                let delay = Duration::from_millis(delay_ms as u64);
                delay.min(*max)
            }
            // 注意：Custom 变体已被移除，这里不再需要默认分支
        };

        if self.config.jitter {
            // 添加随机抖动 (±25%)
            let jitter_range = base_delay.as_millis() as f64 * 0.25;
            let jitter = (rand::random::<f64>() - 0.5) * 2.0 * jitter_range;
            let jittered_ms = (base_delay.as_millis() as f64 + jitter).max(1.0) as u64;
            Duration::from_millis(jittered_ms)
        } else {
            base_delay
        }
    }

    async fn update_stats(&self, success: bool, _attempt_time: Duration, total_time: Duration) {
        let mut stats = self.stats.lock().await;
        
        stats.total_attempts += 1;
        
        if success {
            stats.successful_attempts += 1;
        } else {
            stats.failed_attempts += 1;
        }
        
        stats.total_retry_time += total_time;
        
        if stats.max_retry_time < total_time {
            stats.max_retry_time = total_time;
        }
        
        if stats.min_retry_time == Duration::ZERO || stats.min_retry_time > total_time {
            stats.min_retry_time = total_time;
        }
        
        if stats.successful_attempts > 0 {
            stats.avg_retry_time = Duration::from_nanos(
                stats.total_retry_time.as_nanos() as u64 / stats.successful_attempts as u64
            );
        }
    }
}

/// 重试引擎构建器
pub struct RetryEngineBuilder {
    config: RetryConfig,
}

impl RetryEngineBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: RetryConfig::default(),
        }
    }

    /// 设置最大重试次数
    pub fn max_attempts(mut self, max_attempts: u32) -> Self {
        self.config.max_attempts = max_attempts;
        self
    }

    /// 设置重试策略
    pub fn strategy(mut self, strategy: RetryStrategy) -> Self {
        self.config.strategy = strategy;
        self
    }

    /// 设置重试条件
    pub fn condition(mut self, condition: RetryCondition) -> Self {
        self.config.condition = condition;
        self
    }

    /// 设置超时时间
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.config.timeout = Some(timeout);
        self
    }

    /// 设置是否添加抖动
    pub fn jitter(mut self, jitter: bool) -> Self {
        self.config.jitter = jitter;
        self
    }

    /// 构建重试引擎
    pub fn build(self) -> RetryEngine {
        RetryEngine::new(self.config)
    }
}

impl Default for RetryEngineBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// 便捷宏用于快速创建重试操作
#[macro_export]
macro_rules! retry {
    ($engine:expr, $operation:expr) => {{
        $engine.execute(|| async { $operation }).await
    }};
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;
    use tokio::sync::Mutex;

    #[tokio::test]
    async fn test_fixed_retry_strategy() {
        let config = RetryConfig {
            max_attempts: 3,
            strategy: RetryStrategy::Fixed(Duration::from_millis(100)),
            condition: RetryCondition::Always,
            timeout: None,
            jitter: false,
        };

        let engine = RetryEngine::new(config);
        let attempt_count = Arc::new(Mutex::new(0));

        let attempt_count_clone = Arc::clone(&attempt_count);
        let result: RetryResult<String> = engine.execute(move || {
            let attempt_count = Arc::clone(&attempt_count_clone);
            async move {
                let mut count = attempt_count.lock().await;
                *count += 1;
                if *count < 3 {
                    Err(anyhow::anyhow!("模拟错误"))
                } else {
                    Ok("成功".to_string())
                }
            }
        }).await;

        assert!(result.result.is_ok());
        assert_eq!(result.attempts, 3);
        assert_eq!(*attempt_count.lock().await, 3);
    }

    #[tokio::test]
    async fn test_exponential_backoff() {
        let config = RetryConfig {
            max_attempts: 4,
            strategy: RetryStrategy::Exponential(
                Duration::from_millis(100),
                2.0,
                Duration::from_secs(1),
            ),
            condition: RetryCondition::Always,
            timeout: None,
            jitter: false,
        };

        let engine = RetryEngine::new(config);
        let attempt_count = Arc::new(Mutex::new(0));

        let start = Instant::now();
        let attempt_count_clone = Arc::clone(&attempt_count);
        let result: RetryResult<String> = engine.execute(move || {
            let attempt_count = Arc::clone(&attempt_count_clone);
            async move {
                let mut count = attempt_count.lock().await;
                *count += 1;
                if *count < 4 {
                    Err(anyhow::anyhow!("模拟错误"))
                } else {
                    Ok("成功".to_string())
                }
            }
        }).await;
        let total_time = start.elapsed();

        assert!(result.result.is_ok());
        assert_eq!(result.attempts, 4);
        
        // 验证指数退避：100ms + 200ms + 400ms = 700ms (加上执行时间)
        assert!(total_time >= Duration::from_millis(700));
        assert!(total_time < Duration::from_millis(1000));
    }

    #[tokio::test]
    async fn test_retry_condition() {
        let config = RetryConfig {
            max_attempts: 3,
            strategy: RetryStrategy::Fixed(Duration::from_millis(10)),
            condition: RetryCondition::OnErrorType(vec!["重试".to_string()]),
            timeout: None,
            jitter: false,
        };

        let engine = RetryEngine::new(config);
        let attempt_count = Arc::new(Mutex::new(0));

        // 应该重试的错误
        let attempt_count_clone = Arc::clone(&attempt_count);
        let result1: RetryResult<String> = engine.execute(move || {
            let attempt_count = Arc::clone(&attempt_count_clone);
            async move {
                let mut count = attempt_count.lock().await;
                *count += 1;
                Err(anyhow::anyhow!("这是一个可重试的错误"))
            }
        }).await;

        assert!(result1.result.is_err());
        assert_eq!(result1.attempts, 3); // 应该重试3次

        // 重置计数器
        *attempt_count.lock().await = 0;

        // 不应该重试的错误
        let attempt_count_clone2 = Arc::clone(&attempt_count);
        let result2: RetryResult<String> = engine.execute(move || {
            let attempt_count = Arc::clone(&attempt_count_clone2);
            async move {
                let mut count = attempt_count.lock().await;
                *count += 1;
                Err(anyhow::anyhow!("这是一个不可重试的错误"))
            }
        }).await;

        assert!(result2.result.is_err());
        assert_eq!(result2.attempts, 1); // 只尝试1次
    }
}
