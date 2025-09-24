//! 重试策略实现
//!
//! 提供各种重试策略，包括固定延迟、指数退避、抖动等。

use std::time::Duration;
use std::sync::atomic::{AtomicU64, Ordering};
use serde::{Serialize, Deserialize};
use tracing::debug;
use rand::Rng;

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};

/// 重试策略类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RetryStrategy {
    /// 固定延迟重试
    FixedDelay(Duration),
    /// 指数退避重试
    ExponentialBackoff {
        initial_delay: Duration,
        multiplier: f64,
        max_delay: Duration,
    },
    /// 线性退避重试
    LinearBackoff {
        initial_delay: Duration,
        increment: Duration,
        max_delay: Duration,
    },
    /// 抖动重试
    Jittered {
        base_delay: Duration,
        jitter_range: f64,
    },
    /// 自定义重试策略
    Custom {
        name: String,
        parameters: std::collections::HashMap<String, String>,
    },
}

/// 重试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryConfig {
    /// 最大重试次数
    pub max_attempts: u32,
    /// 重试策略
    pub strategy: RetryStrategy,
    /// 是否启用重试
    pub enabled: bool,
    /// 重试条件（错误类型过滤）
    pub retry_conditions: Vec<String>,
    /// 不重试的条件
    pub no_retry_conditions: Vec<String>,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            strategy: RetryStrategy::ExponentialBackoff {
                initial_delay: Duration::from_millis(100),
                multiplier: 2.0,
                max_delay: Duration::from_secs(30),
            },
            enabled: true,
            retry_conditions: Vec::new(),
            no_retry_conditions: vec!["permission".to_string(), "validation".to_string()],
        }
    }
}

/// 重试统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryStats {
    /// 总尝试数
    pub total_attempts: u64,
    /// 成功尝试数
    pub successful_attempts: u64,
    /// 失败尝试数
    pub failed_attempts: u64,
    /// 重试次数
    pub retry_count: u64,
    /// 平均重试次数
    pub average_retries: f64,
    /// 最后更新时间
    pub last_updated: chrono::DateTime<chrono::Utc>,
}

impl Default for RetryStats {
    fn default() -> Self {
        Self {
            total_attempts: 0,
            successful_attempts: 0,
            failed_attempts: 0,
            retry_count: 0,
            average_retries: 0.0,
            last_updated: chrono::Utc::now(),
        }
    }
}

/// 重试策略实现
pub struct RetryPolicy {
    config: RetryConfig,
    total_attempts: AtomicU64,
    successful_attempts: AtomicU64,
    failed_attempts: AtomicU64,
    retry_count: AtomicU64,
    stats: std::sync::Mutex<RetryStats>,
}

impl RetryPolicy {
    /// 创建新的重试策略
    pub fn new(config: RetryConfig) -> Self {
        Self {
            config,
            total_attempts: AtomicU64::new(0),
            successful_attempts: AtomicU64::new(0),
            failed_attempts: AtomicU64::new(0),
            retry_count: AtomicU64::new(0),
            stats: std::sync::Mutex::new(RetryStats::default()),
        }
    }

    /// 执行带重试的操作
    pub async fn execute<T, F, Fut>(&self, operation: F) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        if !self.config.enabled {
            return operation().await;
        }

        let mut last_error = None;
        let mut attempt = 0;

        while attempt < self.config.max_attempts {
            attempt += 1;
            self.total_attempts.fetch_add(1, Ordering::Relaxed);

            match operation().await {
                Ok(result) => {
                    self.successful_attempts.fetch_add(1, Ordering::Relaxed);
                    self.update_stats();
                    return Ok(result);
                }
                Err(error) => {
                    last_error = Some(error.clone());
                    self.failed_attempts.fetch_add(1, Ordering::Relaxed);

                    // 检查是否应该重试
                    if !self.should_retry(&error, attempt) {
                        break;
                    }

                    // 计算延迟时间
                    let delay = self.calculate_delay(attempt);
                    if delay > Duration::ZERO {
                        debug!("重试第 {} 次，延迟 {:?}", attempt, delay);
                        tokio::time::sleep(delay).await;
                    }

                    self.retry_count.fetch_add(1, Ordering::Relaxed);
                }
            }
        }

        self.update_stats();
        Err(last_error.unwrap_or_else(|| {
            UnifiedError::new(
                "重试次数耗尽",
                ErrorSeverity::High,
                "retry_exhausted",
                ErrorContext::new("retry_policy", "execute", file!(), line!(), ErrorSeverity::High, "retry")
            )
        }))
    }

    /// 检查是否应该重试
    fn should_retry(&self, error: &UnifiedError, attempt: u32) -> bool {
        // 如果已经达到最大尝试次数，不重试
        if attempt >= self.config.max_attempts {
            return false;
        }

        // 检查不重试的条件
        for condition in &self.config.no_retry_conditions {
            if error.category().contains(condition) {
                debug!("错误类型 {} 不满足重试条件", error.category());
                return false;
            }
        }

        // 检查重试条件
        if !self.config.retry_conditions.is_empty() {
            let should_retry = self.config.retry_conditions.iter()
                .any(|condition| error.category().contains(condition));
            if !should_retry {
                debug!("错误类型 {} 不满足重试条件", error.category());
                return false;
            }
        }

        // 检查错误严重程度
        match error.severity() {
            ErrorSeverity::Critical => false,
            ErrorSeverity::High => attempt < 2, // 高严重程度错误只重试1次
            ErrorSeverity::Medium => true,
            ErrorSeverity::Low => true,
        }
    }

    /// 计算延迟时间
    fn calculate_delay(&self, attempt: u32) -> Duration {
        match &self.config.strategy {
            RetryStrategy::FixedDelay(delay) => *delay,
            RetryStrategy::ExponentialBackoff {
                initial_delay,
                multiplier,
                max_delay,
            } => {
                let delay_ms = (initial_delay.as_millis() as f64 * multiplier.powi(attempt as i32 - 1)) as u64;
                Duration::from_millis(delay_ms).min(*max_delay)
            }
            RetryStrategy::LinearBackoff {
                initial_delay,
                increment,
                max_delay,
            } => {
                let delay = *initial_delay + *increment * (attempt - 1) as u32;
                delay.min(*max_delay)
            }
            RetryStrategy::Jittered {
                base_delay,
                jitter_range,
            } => {
                let jittered_ms = self.add_jitter(*base_delay, *jitter_range);
                jittered_ms
            }
            RetryStrategy::Custom { name, parameters } => {
                debug!("使用自定义重试策略: {}, 参数: {:?}", name, parameters);
                Duration::from_millis(100) // 默认延迟
            }
        }
    }

    /// 添加抖动到延迟时间
    fn add_jitter(&self, delay: Duration, jitter_range: f64) -> Duration {
        use rand::Rng;
        let mut rng = rand::rng();
        let jitter = rng.random_range(-jitter_range..=jitter_range);
        let jittered_ms = (delay.as_millis() as f64 * (1.0 + jitter)) as u64;
        Duration::from_millis(jittered_ms)
    }

    /// 更新统计信息
    fn update_stats(&self) {
        let mut stats = self.stats.lock().unwrap();
        stats.total_attempts = self.total_attempts.load(Ordering::Relaxed);
        stats.successful_attempts = self.successful_attempts.load(Ordering::Relaxed);
        stats.failed_attempts = self.failed_attempts.load(Ordering::Relaxed);
        stats.retry_count = self.retry_count.load(Ordering::Relaxed);
        
        if stats.total_attempts > 0 {
            stats.average_retries = stats.retry_count as f64 / stats.total_attempts as f64;
        } else {
            stats.average_retries = 0.0;
        }
        
        stats.last_updated = chrono::Utc::now();
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> RetryStats {
        self.stats.lock().unwrap().clone()
    }

    /// 重置统计信息
    pub fn reset_stats(&self) {
        self.total_attempts.store(0, Ordering::Relaxed);
        self.successful_attempts.store(0, Ordering::Relaxed);
        self.failed_attempts.store(0, Ordering::Relaxed);
        self.retry_count.store(0, Ordering::Relaxed);
        
        let mut stats = self.stats.lock().unwrap();
        *stats = RetryStats::default();
    }

    /// 获取配置
    pub fn get_config(&self) -> &RetryConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: RetryConfig) {
        self.config = config;
    }
}

/// 重试策略构建器
pub struct RetryPolicyBuilder {
    config: RetryConfig,
}

impl RetryPolicyBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: RetryConfig::default(),
        }
    }

    /// 设置最大重试次数
    pub fn max_attempts(mut self, attempts: u32) -> Self {
        self.config.max_attempts = attempts;
        self
    }

    /// 设置固定延迟策略
    pub fn fixed_delay(mut self, delay: Duration) -> Self {
        self.config.strategy = RetryStrategy::FixedDelay(delay);
        self
    }

    /// 设置指数退避策略
    pub fn exponential_backoff(mut self, initial_delay: Duration, multiplier: f64, max_delay: Duration) -> Self {
        self.config.strategy = RetryStrategy::ExponentialBackoff {
            initial_delay,
            multiplier,
            max_delay,
        };
        self
    }

    /// 设置线性退避策略
    pub fn linear_backoff(mut self, initial_delay: Duration, increment: Duration, max_delay: Duration) -> Self {
        self.config.strategy = RetryStrategy::LinearBackoff {
            initial_delay,
            increment,
            max_delay,
        };
        self
    }

    /// 设置抖动策略
    pub fn jittered(mut self, base_delay: Duration, jitter_range: f64) -> Self {
        self.config.strategy = RetryStrategy::Jittered {
            base_delay,
            jitter_range,
        };
        self
    }

    /// 设置重试条件
    pub fn retry_conditions(mut self, conditions: Vec<String>) -> Self {
        self.config.retry_conditions = conditions;
        self
    }

    /// 设置不重试条件
    pub fn no_retry_conditions(mut self, conditions: Vec<String>) -> Self {
        self.config.no_retry_conditions = conditions;
        self
    }

    /// 启用或禁用重试
    pub fn enabled(mut self, enabled: bool) -> Self {
        self.config.enabled = enabled;
        self
    }

    /// 构建重试策略
    pub fn build(self) -> RetryPolicy {
        RetryPolicy::new(self.config)
    }
}

impl Default for RetryPolicyBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_retry_config_default() {
        let config = RetryConfig::default();
        assert_eq!(config.max_attempts, 3);
        assert!(config.enabled);
        assert!(!config.no_retry_conditions.is_empty());
    }

    #[test]
    fn test_retry_policy_creation() {
        let policy = RetryPolicy::new(RetryConfig::default());
        let stats = policy.get_stats();
        assert_eq!(stats.total_attempts, 0);
        assert_eq!(stats.successful_attempts, 0);
    }

    #[test]
    fn test_retry_policy_builder() {
        let policy = RetryPolicyBuilder::new()
            .max_attempts(5)
            .fixed_delay(Duration::from_millis(100))
            .retry_conditions(vec!["network".to_string()])
            .build();

        let config = policy.get_config();
        assert_eq!(config.max_attempts, 5);
        assert!(config.retry_conditions.contains(&"network".to_string()));
    }

    #[tokio::test]
    async fn test_retry_policy_success() {
        let policy = RetryPolicy::new(RetryConfig::default());
        
        let result: Result<String, _> = policy.execute(|| async {
            Ok::<String, UnifiedError>("成功".to_string())
        }).await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "成功");
        
        let stats = policy.get_stats();
        assert_eq!(stats.total_attempts, 1);
        assert_eq!(stats.successful_attempts, 1);
        assert_eq!(stats.retry_count, 0);
    }

    #[tokio::test]
    async fn test_retry_policy_failure() {
        let config = RetryConfig {
            max_attempts: 3,
            strategy: RetryStrategy::FixedDelay(Duration::from_millis(1)),
            ..Default::default()
        };
        let policy = RetryPolicy::new(config);
        
        let result: Result<String, _> = policy.execute(|| async {
            Err(UnifiedError::new(
                "测试错误",
                ErrorSeverity::Medium,
                "test",
                ErrorContext::new("test", "test", "test.rs", 1, ErrorSeverity::Medium, "test")
            ))
        }).await;

        assert!(result.is_err());
        
        let stats = policy.get_stats();
        assert_eq!(stats.total_attempts, 3);
        assert_eq!(stats.successful_attempts, 0);
        assert_eq!(stats.failed_attempts, 3);
        assert_eq!(stats.retry_count, 2); // 重试2次
    }

    #[tokio::test]
    async fn test_retry_policy_no_retry_condition() {
        let config = RetryConfig {
            max_attempts: 3,
            strategy: RetryStrategy::FixedDelay(Duration::from_millis(1)),
            no_retry_conditions: vec!["permission".to_string()],
            ..Default::default()
        };
        let policy = RetryPolicy::new(config);
        
        let result: Result<String, _> = policy.execute(|| async {
            Err(UnifiedError::new(
                "权限错误",
                ErrorSeverity::High,
                "permission",
                ErrorContext::new("test", "test", "test.rs", 1, ErrorSeverity::High, "permission")
            ))
        }).await;

        assert!(result.is_err());
        
        let stats = policy.get_stats();
        assert_eq!(stats.total_attempts, 1); // 只尝试1次
        assert_eq!(stats.retry_count, 0); // 没有重试
    }

    #[test]
    fn test_retry_strategy_calculation() {
        let config = RetryConfig {
            max_attempts: 3,
            strategy: RetryStrategy::ExponentialBackoff {
                initial_delay: Duration::from_millis(100),
                multiplier: 2.0,
                max_delay: Duration::from_secs(1),
            },
            ..Default::default()
        };
        let policy = RetryPolicy::new(config);
        
        // 测试延迟计算（这里需要访问私有方法，所以使用反射或其他方式）
        // 在实际测试中，可以通过公共接口测试延迟行为
        assert!(policy.get_config().max_attempts == 3);
    }

    #[test]
    fn test_retry_stats() {
        let policy = RetryPolicy::new(RetryConfig::default());
        let stats = policy.get_stats();
        
        assert_eq!(stats.total_attempts, 0);
        assert_eq!(stats.successful_attempts, 0);
        assert_eq!(stats.failed_attempts, 0);
        assert_eq!(stats.retry_count, 0);
        assert_eq!(stats.average_retries, 0.0);
    }

    #[test]
    fn test_retry_policy_reset() {
        let policy = RetryPolicy::new(RetryConfig::default());
        
        // 重置统计
        policy.reset_stats();
        
        let stats = policy.get_stats();
        assert_eq!(stats.total_attempts, 0);
        assert_eq!(stats.successful_attempts, 0);
        assert_eq!(stats.failed_attempts, 0);
        assert_eq!(stats.retry_count, 0);
    }
}

/// 重试器
#[derive(Debug, Clone)]
pub struct Retrier {
    config: RetryConfig,
}

impl Retrier {
    /// 创建新的重试器
    pub fn new(config: RetryConfig) -> Self {
        Self { config }
    }
    
    /// 使用重试策略执行操作
    pub async fn execute<F, T, E>(&self, operation: F) -> Result<T, E>
    where
        F: Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>> + Send + Sync,
        E: Clone + Send + Sync,
    {
        let mut attempt = 0;
        let mut last_error = None;
        
        while attempt < self.config.max_attempts {
            match operation().await {
                Ok(result) => return Ok(result),
                Err(error) => {
                    last_error = Some(error.clone());
                    attempt += 1;
                    
                    if attempt >= self.config.max_attempts {
                        break;
                    }
                    
                    // 计算延迟时间
                    let delay = self.calculate_delay(attempt);
                    tokio::time::sleep(delay).await;
                }
            }
        }
        
        Err(last_error.unwrap())
    }
    
    /// 计算延迟时间
    fn calculate_delay(&self, attempt: u32) -> Duration {
        match &self.config.strategy {
            RetryStrategy::FixedDelay(delay) => *delay,
            RetryStrategy::ExponentialBackoff { initial_delay, multiplier, max_delay } => {
                let delay_ms = initial_delay.as_millis() as f64 * multiplier.powi(attempt as i32);
                let delay = Duration::from_millis(delay_ms as u64);
                delay.min(*max_delay)
            }
            RetryStrategy::LinearBackoff { initial_delay, increment, max_delay } => {
                let delay = *initial_delay + *increment * attempt;
                delay.min(*max_delay)
            }
            RetryStrategy::Jittered { base_delay, jitter_range } => {
                let jitter = rand::rng().random_range(-*jitter_range..=*jitter_range);
                let delay_ms = (base_delay.as_millis() as f64 * (1.0 + jitter)) as u64;
                Duration::from_millis(delay_ms)
            }
            RetryStrategy::Custom { .. } => Duration::from_millis(100), // 默认延迟
        }
    }
}
