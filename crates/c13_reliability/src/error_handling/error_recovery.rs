//! 错误恢复策略和实现
//!
//! 提供各种错误恢复策略，包括重试、降级、忽略等。

use std::time::Duration;
use std::collections::HashMap;
use serde::{Serialize, Deserialize};
use tracing::{
    debug, warn, 
    //error,
};

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};

/// 重试策略配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryConfig {
    /// 最大重试次数
    pub max_attempts: u32,
    /// 初始延迟时间
    pub initial_delay: Duration,
    /// 退避乘数
    pub backoff_multiplier: f64,
    /// 最大延迟时间
    pub max_delay: Duration,
    /// 是否使用抖动
    pub use_jitter: bool,
    /// 抖动范围（0.0-1.0）
    pub jitter_range: f64,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            initial_delay: Duration::from_millis(100),
            backoff_multiplier: 2.0,
            max_delay: Duration::from_secs(30),
            use_jitter: true,
            jitter_range: 0.1,
        }
    }
}

/// 降级策略配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FallbackConfig {
    /// 降级值
    pub fallback_value: Option<String>,
    /// 是否通知
    pub notify: bool,
    /// 降级原因
    pub reason: Option<String>,
    /// 降级持续时间
    pub duration: Option<Duration>,
}

impl Default for FallbackConfig {
    fn default() -> Self {
        Self {
            fallback_value: None,
            notify: true,
            reason: None,
            duration: None,
        }
    }
}

/// 错误恢复策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RecoveryStrategy {
    /// 重试策略
    Retry(RetryConfig),
    /// 降级策略
    Fallback(FallbackConfig),
    /// 忽略错误
    Ignore,
    /// 传播错误
    Propagate,
    /// 自定义策略
    Custom {
        name: String,
        parameters: HashMap<String, String>,
    },
}

impl Default for RecoveryStrategy {
    fn default() -> Self {
        RecoveryStrategy::Propagate
    }
}

/// 错误恢复器
pub struct ErrorRecovery {
    strategy: RecoveryStrategy,
    recovery_count: std::sync::atomic::AtomicU64,
    last_recovery: std::sync::Mutex<Option<std::time::Instant>>,
    success_count: std::sync::atomic::AtomicU64,
}

impl ErrorRecovery {
    /// 创建新的错误恢复器
    pub fn new(strategy: RecoveryStrategy) -> Self {
        Self {
            strategy,
            recovery_count: std::sync::atomic::AtomicU64::new(0),
            last_recovery: std::sync::Mutex::new(None),
            success_count: std::sync::atomic::AtomicU64::new(0),
        }
    }

    /// 尝试恢复错误
    pub async fn recover<T, F, Fut>(&self, operation: F) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        match &self.strategy {
            RecoveryStrategy::Retry(config) => {
                self.recover_with_retry(operation, config).await
            }
            RecoveryStrategy::Fallback(config) => {
                self.recover_with_fallback(operation, config).await
            }
            RecoveryStrategy::Ignore => {
                self.recover_with_ignore(operation).await
            }
            RecoveryStrategy::Propagate => {
                operation().await
            }
            RecoveryStrategy::Custom { name, parameters } => {
                self.recover_with_custom(operation, name, parameters).await
            }
        }
    }

    async fn recover_with_retry<T, F, Fut>(
        &self,
        operation: F,
        config: &RetryConfig,
    ) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        let mut delay = config.initial_delay;
        let mut last_error = None;

        for attempt in 1..=config.max_attempts {
            match operation().await {
                Ok(result) => {
                    self.success_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    *self.last_recovery.lock().unwrap() = Some(std::time::Instant::now());
                    return Ok(result);
                }
                Err(error) => {
                    last_error = Some(error);
                    
                    if attempt < config.max_attempts {
                        let actual_delay = if config.use_jitter {
                            self.add_jitter(delay, config.jitter_range)
                        } else {
                            delay
                        };
                        
                        debug!("重试第 {} 次，延迟 {:?}", attempt, actual_delay);
                        tokio::time::sleep(actual_delay).await;
                        
                        // 计算下次延迟时间
                        delay = Duration::from_millis(
                            (delay.as_millis() as f64 * config.backoff_multiplier) as u64
                        ).min(config.max_delay);
                    }
                }
            }
        }

        self.recovery_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        *self.last_recovery.lock().unwrap() = Some(std::time::Instant::now());

        Err(last_error.unwrap_or_else(|| {
            UnifiedError::new(
                "重试次数耗尽",
                ErrorSeverity::High,
                "retry_exhausted",
                ErrorContext::new("error_recovery", "recover_with_retry", file!(), line!(), ErrorSeverity::High, "retry")
            )
        }))
    }

    async fn recover_with_fallback<T, F, Fut>(
        &self,
        operation: F,
        config: &FallbackConfig,
    ) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        match operation().await {
            Ok(result) => Ok(result),
            Err(error) => {
                self.recovery_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                *self.last_recovery.lock().unwrap() = Some(std::time::Instant::now());

                if config.notify {
                    warn!("使用降级策略处理错误: {}", error);
                }

                // 这里需要根据具体类型实现降级逻辑
                // 由于泛型限制，这里返回一个通用的降级错误
                Err(UnifiedError::new(
                    &format!("降级处理: {}", error),
                    ErrorSeverity::Medium,
                    "fallback_used",
                    ErrorContext::new("error_recovery", "recover_with_fallback", file!(), line!(), ErrorSeverity::Medium, "fallback")
                        .with_metadata("fallback_value", config.fallback_value.as_deref().unwrap_or("none"))
                        .with_metadata("fallback_reason", config.reason.as_deref().unwrap_or("unknown"))
                ))
            }
        }
    }

    async fn recover_with_ignore<T, F, Fut>(
        &self,
        operation: F,
    ) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        match operation().await {
            Ok(result) => Ok(result),
            Err(error) => {
                self.recovery_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                *self.last_recovery.lock().unwrap() = Some(std::time::Instant::now());
                
                debug!("忽略错误: {}", error);
                
                // 返回一个表示忽略的错误
                Err(UnifiedError::new(
                    "错误被忽略",
                    ErrorSeverity::Low,
                    "error_ignored",
                    ErrorContext::new("error_recovery", "recover_with_ignore", file!(), line!(), ErrorSeverity::Low, "ignore")
                        .with_metadata("original_error", error.to_string())
                ))
            }
        }
    }

    async fn recover_with_custom<T, F, Fut>(
        &self,
        operation: F,
        strategy_name: &str,
        parameters: &HashMap<String, String>,
    ) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        // 自定义恢复策略的实现
        // 这里可以根据策略名称和参数实现不同的恢复逻辑
        warn!("使用自定义恢复策略: {}，参数: {:?}", strategy_name, parameters);
        
        // 默认使用传播策略
        operation().await
    }

    /// 添加抖动到延迟时间
    fn add_jitter(&self, delay: Duration, jitter_range: f64) -> Duration {
        use rand::Rng;
        let mut rng = rand::rng();
        let jitter = rng.random_range(-jitter_range..=jitter_range);
        let jittered_ms = (delay.as_millis() as f64 * (1.0 + jitter)) as u64;
        Duration::from_millis(jittered_ms)
    }

    /// 获取恢复次数
    pub fn recovery_count(&self) -> u64 {
        self.recovery_count.load(std::sync::atomic::Ordering::Relaxed)
    }

    /// 获取成功次数
    pub fn success_count(&self) -> u64 {
        self.success_count.load(std::sync::atomic::Ordering::Relaxed)
    }

    /// 获取上次恢复时间
    pub fn last_recovery_time(&self) -> Option<std::time::Instant> {
        *self.last_recovery.lock().unwrap()
    }

    /// 获取成功率
    pub fn success_rate(&self) -> f64 {
        let total = self.recovery_count() + self.success_count();
        if total == 0 {
            0.0
        } else {
            self.success_count() as f64 / total as f64
        }
    }

    /// 重置统计
    pub fn reset_stats(&self) {
        self.recovery_count.store(0, std::sync::atomic::Ordering::Relaxed);
        self.success_count.store(0, std::sync::atomic::Ordering::Relaxed);
        *self.last_recovery.lock().unwrap() = None;
    }
}

/// 错误恢复构建器
pub struct ErrorRecoveryBuilder {
    strategy: Option<RecoveryStrategy>,
}

impl ErrorRecoveryBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self { strategy: None }
    }

    /// 设置重试策略
    pub fn with_retry(mut self, config: RetryConfig) -> Self {
        self.strategy = Some(RecoveryStrategy::Retry(config));
        self
    }

    /// 设置降级策略
    pub fn with_fallback(mut self, config: FallbackConfig) -> Self {
        self.strategy = Some(RecoveryStrategy::Fallback(config));
        self
    }

    /// 设置忽略策略
    pub fn with_ignore(mut self) -> Self {
        self.strategy = Some(RecoveryStrategy::Ignore);
        self
    }

    /// 设置传播策略
    pub fn with_propagate(mut self) -> Self {
        self.strategy = Some(RecoveryStrategy::Propagate);
        self
    }

    /// 设置自定义策略
    pub fn with_custom(mut self, name: String, parameters: HashMap<String, String>) -> Self {
        self.strategy = Some(RecoveryStrategy::Custom { name, parameters });
        self
    }

    /// 构建错误恢复器
    pub fn build(self) -> ErrorRecovery {
        ErrorRecovery::new(self.strategy.unwrap_or_default())
    }
}

impl Default for ErrorRecoveryBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[tokio::test]
    async fn test_retry_recovery() {
        let config = RetryConfig {
            max_attempts: 3,
            initial_delay: Duration::from_millis(1),
            backoff_multiplier: 2.0,
            max_delay: Duration::from_millis(100),
            use_jitter: false,
            jitter_range: 0.0,
        };

        let recovery = ErrorRecovery::new(RecoveryStrategy::Retry(config));

        let result = recovery.recover(|| async {
            Ok("成功".to_string())
        }).await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "成功");
        assert_eq!(recovery.success_count(), 1);
    }

    #[tokio::test]
    async fn test_fallback_recovery() {
        let config = FallbackConfig {
            fallback_value: Some("降级值".to_string()),
            notify: true,
            reason: Some("测试降级".to_string()),
            duration: None,
        };

        let recovery = ErrorRecovery::new(RecoveryStrategy::Fallback(config));

        let result: Result<String, _> = recovery.recover(|| async {
            Err(UnifiedError::new(
                "原始错误",
                ErrorSeverity::Medium,
                "original_error",
                ErrorContext::new("test", "test_fallback", file!(), line!(), ErrorSeverity::Medium, "test")
            ))
        }).await;

        assert!(result.is_err());
        let error = result.unwrap_err();
        assert!(error.message().contains("降级处理"));
        assert_eq!(recovery.recovery_count(), 1);
    }

    #[tokio::test]
    async fn test_ignore_recovery() {
        let recovery = ErrorRecovery::new(RecoveryStrategy::Ignore);

        let result: Result<String, _> = recovery.recover(|| async {
            Err(UnifiedError::new(
                "被忽略的错误",
                ErrorSeverity::Low,
                "ignored_error",
                ErrorContext::new("test", "test_ignore", file!(), line!(), ErrorSeverity::Low, "test")
            ))
        }).await;

        assert!(result.is_err());
        let error = result.unwrap_err();
        assert!(error.message().contains("错误被忽略"));
        assert_eq!(recovery.recovery_count(), 1);
    }

    #[test]
    fn test_recovery_builder() {
        let config = RetryConfig::default();
        let recovery = ErrorRecoveryBuilder::new()
            .with_retry(config)
            .build();

        assert_eq!(recovery.recovery_count(), 0);
        assert_eq!(recovery.success_count(), 0);
        assert_eq!(recovery.success_rate(), 0.0);
    }

    #[test]
    fn test_retry_config_default() {
        let config = RetryConfig::default();
        assert_eq!(config.max_attempts, 3);
        assert_eq!(config.initial_delay, Duration::from_millis(100));
        assert_eq!(config.backoff_multiplier, 2.0);
        assert!(config.use_jitter);
    }

    #[test]
    fn test_fallback_config_default() {
        let config = FallbackConfig::default();
        assert!(config.notify);
        assert!(config.fallback_value.is_none());
        assert!(config.reason.is_none());
        assert!(config.duration.is_none());
    }
}
