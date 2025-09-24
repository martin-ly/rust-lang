//! 断路器模式实现
//!
//! 提供完整的断路器功能，包括状态管理、故障检测和自动恢复。

use std::sync::atomic::{AtomicU64, AtomicU8, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use serde::{Serialize, Deserialize};
use tracing::{
    //debug, 
    warn, error, info
};

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};

/// 断路器状态
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CircuitBreakerState {
    /// 关闭状态：正常执行
    Closed,
    /// 开启状态：拒绝执行
    Open,
    /// 半开状态：允许部分执行
    HalfOpen,
}

impl CircuitBreakerState {
    /// 获取状态的字符串表示
    pub fn as_str(&self) -> &'static str {
        match self {
            CircuitBreakerState::Closed => "CLOSED",
            CircuitBreakerState::Open => "OPEN",
            CircuitBreakerState::HalfOpen => "HALF_OPEN",
        }
    }
}

/// 断路器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircuitBreakerConfig {
    /// 失败阈值
    pub failure_threshold: u64,
    /// 恢复超时时间
    pub recovery_timeout: Duration,
    /// 半开状态最大请求数
    pub half_open_max_requests: u64,
    /// 成功阈值（半开状态下需要多少成功请求才能关闭）
    pub success_threshold: u64,
    /// 滑动窗口大小
    pub sliding_window_size: Duration,
    /// 最小请求数（在计算失败率之前需要的最小请求数）
    pub minimum_requests: u64,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 5,
            recovery_timeout: Duration::from_secs(60),
            half_open_max_requests: 3,
            success_threshold: 2,
            sliding_window_size: Duration::from_secs(60),
            minimum_requests: 10,
        }
    }
}

/// 断路器统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircuitBreakerStats {
    /// 总请求数
    pub total_requests: u64,
    /// 成功请求数
    pub successful_requests: u64,
    /// 失败请求数
    pub failed_requests: u64,
    /// 被拒绝的请求数
    pub rejected_requests: u64,
    /// 当前状态
    pub current_state: CircuitBreakerState,
    /// 状态转换次数
    pub state_transitions: u64,
    /// 最后状态转换时间
    pub last_state_transition: Option<chrono::DateTime<chrono::Utc>>,
    /// 失败率
    pub failure_rate: f64,
}

impl Default for CircuitBreakerStats {
    fn default() -> Self {
        Self {
            total_requests: 0,
            successful_requests: 0,
            failed_requests: 0,
            rejected_requests: 0,
            current_state: CircuitBreakerState::Closed,
            state_transitions: 0,
            last_state_transition: None,
            failure_rate: 0.0,
        }
    }
}

/// 断路器实现
pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: AtomicU8, // 0: Closed, 1: Open, 2: HalfOpen
    failure_count: AtomicU64,
    success_count: AtomicU64,
    request_count: AtomicU64,
    last_failure_time: Arc<Mutex<Option<Instant>>>,
    last_success_time: Arc<Mutex<Option<Instant>>>,
    state_transition_time: Arc<Mutex<Option<Instant>>>,
    half_open_requests: AtomicU64,
    half_open_successes: AtomicU64,
    stats: Arc<Mutex<CircuitBreakerStats>>,
}

impl CircuitBreaker {
    /// 创建新的断路器
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            config,
            state: AtomicU8::new(0), // Closed
            failure_count: AtomicU64::new(0),
            success_count: AtomicU64::new(0),
            request_count: AtomicU64::new(0),
            last_failure_time: Arc::new(Mutex::new(None)),
            last_success_time: Arc::new(Mutex::new(None)),
            state_transition_time: Arc::new(Mutex::new(None)),
            half_open_requests: AtomicU64::new(0),
            half_open_successes: AtomicU64::new(0),
            stats: Arc::new(Mutex::new(CircuitBreakerStats::default())),
        }
    }

    /// 检查是否可以执行请求
    pub fn can_execute(&self) -> bool {
        match self.state() {
            CircuitBreakerState::Closed => true,
            CircuitBreakerState::Open => {
                // 检查是否超过恢复超时时间
                if let Some(last_failure) = *self.last_failure_time.lock().unwrap() {
                    if last_failure.elapsed() >= self.config.recovery_timeout {
                        self.transition_to_half_open();
                        true
                    } else {
                        false
                    }
                } else {
                    false
                }
            }
            CircuitBreakerState::HalfOpen => {
                // 检查半开状态下的请求数限制
                self.half_open_requests.load(Ordering::Relaxed) < self.config.half_open_max_requests
            }
        }
    }

    /// 执行操作
    pub async fn execute<T, F, Fut>(&self, operation: F) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        if !self.can_execute() {
            self.record_rejected_request();
            return Err(self.create_circuit_open_error());
        }

        self.record_request();

        match operation().await {
            Ok(result) => {
                self.record_success();
                Ok(result)
            }
            Err(error) => {
                self.record_failure();
                Err(error)
            }
        }
    }

    /// 记录成功请求
    pub fn record_success(&self) {
        self.success_count.fetch_add(1, Ordering::Relaxed);
        *self.last_success_time.lock().unwrap() = Some(Instant::now());

        match self.state() {
            CircuitBreakerState::Closed => {
                // 重置失败计数
                self.failure_count.store(0, Ordering::Relaxed);
            }
            CircuitBreakerState::HalfOpen => {
                let successes = self.half_open_successes.fetch_add(1, Ordering::Relaxed) + 1;
                if successes >= self.config.success_threshold {
                    self.transition_to_closed();
                }
            }
            CircuitBreakerState::Open => {
                // 在开启状态下不应该有成功请求
                warn!("在断路器开启状态下记录成功请求");
            }
        }

        self.update_stats();
    }

    /// 记录失败请求
    pub fn record_failure(&self) {
        self.failure_count.fetch_add(1, Ordering::Relaxed);
        *self.last_failure_time.lock().unwrap() = Some(Instant::now());

        match self.state() {
            CircuitBreakerState::Closed => {
                if self.should_open() {
                    self.transition_to_open();
                }
            }
            CircuitBreakerState::HalfOpen => {
                // 半开状态下的任何失败都会重新开启断路器
                self.transition_to_open();
            }
            CircuitBreakerState::Open => {
                // 在开启状态下不应该有失败请求
                warn!("在断路器开启状态下记录失败请求");
            }
        }

        self.update_stats();
    }

    /// 记录被拒绝的请求
    fn record_rejected_request(&self) {
        self.update_stats();
    }

    /// 记录请求
    fn record_request(&self) {
        self.request_count.fetch_add(1, Ordering::Relaxed);
        
        if self.state() == CircuitBreakerState::HalfOpen {
            self.half_open_requests.fetch_add(1, Ordering::Relaxed);
        }
    }

    /// 检查是否应该开启断路器
    fn should_open(&self) -> bool {
        let total_requests = self.request_count.load(Ordering::Relaxed);
        let failures = self.failure_count.load(Ordering::Relaxed);

        // 如果请求数少于最小请求数，不开启断路器
        if total_requests < self.config.minimum_requests {
            return false;
        }

        // 检查失败数量是否超过阈值
        failures >= self.config.failure_threshold
    }

    /// 转换到关闭状态
    fn transition_to_closed(&self) {
        self.state.store(0, Ordering::Relaxed); // Closed
        self.failure_count.store(0, Ordering::Relaxed);
        self.half_open_requests.store(0, Ordering::Relaxed);
        self.half_open_successes.store(0, Ordering::Relaxed);
        *self.state_transition_time.lock().unwrap() = Some(Instant::now());

        info!("断路器转换到关闭状态");
        self.update_stats();
    }

    /// 转换到开启状态
    fn transition_to_open(&self) {
        self.state.store(1, Ordering::Relaxed); // Open
        *self.state_transition_time.lock().unwrap() = Some(Instant::now());

        error!("断路器转换到开启状态");
        self.update_stats();
    }

    /// 转换到半开状态
    fn transition_to_half_open(&self) {
        self.state.store(2, Ordering::Relaxed); // HalfOpen
        self.half_open_requests.store(0, Ordering::Relaxed);
        self.half_open_successes.store(0, Ordering::Relaxed);
        *self.state_transition_time.lock().unwrap() = Some(Instant::now());

        warn!("断路器转换到半开状态");
        self.update_stats();
    }

    /// 获取当前状态
    pub fn state(&self) -> CircuitBreakerState {
        match self.state.load(Ordering::Relaxed) {
            0 => CircuitBreakerState::Closed,
            1 => CircuitBreakerState::Open,
            2 => CircuitBreakerState::HalfOpen,
            _ => CircuitBreakerState::Closed,
        }
    }

    /// 创建断路器开启错误
    fn create_circuit_open_error(&self) -> UnifiedError {
        let context = ErrorContext::new(
            "circuit_breaker",
            "execute",
            file!(),
            line!(),
            ErrorSeverity::High,
            "circuit_breaker"
        );

        UnifiedError::new(
            "断路器已开启，请求被拒绝",
            ErrorSeverity::High,
            "circuit_breaker_open",
            context
        ).with_code("CB_001")
        .with_suggestion("等待断路器恢复或检查服务状态")
    }

    /// 更新统计信息
    fn update_stats(&self) {
        let mut stats = self.stats.lock().unwrap();
        stats.total_requests = self.request_count.load(Ordering::Relaxed);
        stats.successful_requests = self.success_count.load(Ordering::Relaxed);
        stats.failed_requests = self.failure_count.load(Ordering::Relaxed);
        stats.current_state = self.state();
        
        if let Some(_transition_time) = *self.state_transition_time.lock().unwrap() {
            stats.last_state_transition = Some(chrono::Utc::now());
        }

        // 计算失败率
        if stats.total_requests > 0 {
            stats.failure_rate = stats.failed_requests as f64 / stats.total_requests as f64;
        } else {
            stats.failure_rate = 0.0;
        }
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> CircuitBreakerStats {
        self.stats.lock().unwrap().clone()
    }

    /// 重置统计信息
    pub fn reset_stats(&self) {
        self.failure_count.store(0, Ordering::Relaxed);
        self.success_count.store(0, Ordering::Relaxed);
        self.request_count.store(0, Ordering::Relaxed);
        self.half_open_requests.store(0, Ordering::Relaxed);
        self.half_open_successes.store(0, Ordering::Relaxed);
        *self.last_failure_time.lock().unwrap() = None;
        *self.last_success_time.lock().unwrap() = None;
        *self.state_transition_time.lock().unwrap() = None;
        
        let mut stats = self.stats.lock().unwrap();
        *stats = CircuitBreakerStats::default();
    }

    /// 手动重置断路器
    pub fn reset(&self) {
        self.transition_to_closed();
        info!("断路器已手动重置");
    }

    /// 获取配置
    pub fn get_config(&self) -> &CircuitBreakerConfig {
        &self.config
    }

    /// 更新配置
    pub fn update_config(&mut self, config: CircuitBreakerConfig) {
        self.config = config;
        info!("断路器配置已更新");
    }
}

/// 断路器构建器
pub struct CircuitBreakerBuilder {
    config: CircuitBreakerConfig,
}

impl CircuitBreakerBuilder {
    /// 创建新的构建器
    pub fn new() -> Self {
        Self {
            config: CircuitBreakerConfig::default(),
        }
    }

    /// 设置失败阈值
    pub fn failure_threshold(mut self, threshold: u64) -> Self {
        self.config.failure_threshold = threshold;
        self
    }

    /// 设置恢复超时时间
    pub fn recovery_timeout(mut self, timeout: Duration) -> Self {
        self.config.recovery_timeout = timeout;
        self
    }

    /// 设置半开状态最大请求数
    pub fn half_open_max_requests(mut self, max_requests: u64) -> Self {
        self.config.half_open_max_requests = max_requests;
        self
    }

    /// 设置成功阈值
    pub fn success_threshold(mut self, threshold: u64) -> Self {
        self.config.success_threshold = threshold;
        self
    }

    /// 设置滑动窗口大小
    pub fn sliding_window_size(mut self, size: Duration) -> Self {
        self.config.sliding_window_size = size;
        self
    }

    /// 设置最小请求数
    pub fn minimum_requests(mut self, min_requests: u64) -> Self {
        self.config.minimum_requests = min_requests;
        self
    }

    /// 构建断路器
    pub fn build(self) -> CircuitBreaker {
        CircuitBreaker::new(self.config)
    }
}

impl Default for CircuitBreakerBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_circuit_breaker_config_default() {
        let config = CircuitBreakerConfig::default();
        assert_eq!(config.failure_threshold, 5);
        assert_eq!(config.recovery_timeout, Duration::from_secs(60));
        assert_eq!(config.half_open_max_requests, 3);
        assert_eq!(config.success_threshold, 2);
    }

    #[test]
    fn test_circuit_breaker_creation() {
        let circuit_breaker = CircuitBreaker::new(CircuitBreakerConfig::default());
        assert_eq!(circuit_breaker.state(), CircuitBreakerState::Closed);
        assert!(circuit_breaker.can_execute());
    }

    #[test]
    fn test_circuit_breaker_builder() {
        let circuit_breaker = CircuitBreakerBuilder::new()
            .failure_threshold(10)
            .recovery_timeout(Duration::from_secs(30))
            .half_open_max_requests(5)
            .build();

        assert_eq!(circuit_breaker.get_config().failure_threshold, 10);
        assert_eq!(circuit_breaker.get_config().recovery_timeout, Duration::from_secs(30));
        assert_eq!(circuit_breaker.get_config().half_open_max_requests, 5);
    }

    #[tokio::test]
    async fn test_circuit_breaker_success() {
        let circuit_breaker = CircuitBreaker::new(CircuitBreakerConfig::default());
        
        let result: Result<String, _> = circuit_breaker.execute(|| async {
            Ok::<String, UnifiedError>("成功".to_string())
        }).await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "成功");
        assert_eq!(circuit_breaker.state(), CircuitBreakerState::Closed);
    }

    #[tokio::test]
    async fn test_circuit_breaker_failure() {
        let config = CircuitBreakerConfig {
            failure_threshold: 2,
            ..Default::default()
        };
        let circuit_breaker = CircuitBreaker::new(config);
        
        // 第一次失败
        let result: Result<String, _> = circuit_breaker.execute(|| async {
            Err(UnifiedError::new(
                "测试错误",
                ErrorSeverity::Medium,
                "test",
                ErrorContext::new("test", "test", "test.rs", 1, ErrorSeverity::Medium, "test")
            ))
        }).await;

        assert!(result.is_err());
        assert_eq!(circuit_breaker.state(), CircuitBreakerState::Closed);

        // 第二次失败，应该开启断路器
        let result: Result<String, _> = circuit_breaker.execute(|| async {
            Err(UnifiedError::new(
                "测试错误",
                ErrorSeverity::Medium,
                "test",
                ErrorContext::new("test", "test", "test.rs", 1, ErrorSeverity::Medium, "test")
            ))
        }).await;

        assert!(result.is_err());
        assert_eq!(circuit_breaker.state(), CircuitBreakerState::Open);
        assert!(!circuit_breaker.can_execute());
    }

    #[tokio::test]
    async fn test_circuit_breaker_half_open() {
        let config = CircuitBreakerConfig {
            failure_threshold: 1,
            recovery_timeout: Duration::from_millis(100),
            success_threshold: 1,
            ..Default::default()
        };
        let circuit_breaker = CircuitBreaker::new(config);
        
        // 触发断路器开启
        let _: Result<String, _> = circuit_breaker.execute(|| async {
            Err(UnifiedError::new(
                "测试错误",
                ErrorSeverity::Medium,
                "test",
                ErrorContext::new("test", "test", "test.rs", 1, ErrorSeverity::Medium, "test")
            ))
        }).await;

        assert_eq!(circuit_breaker.state(), CircuitBreakerState::Open);

        // 等待恢复超时
        tokio::time::sleep(Duration::from_millis(150)).await;

        // 应该转换到半开状态
        assert_eq!(circuit_breaker.state(), CircuitBreakerState::HalfOpen);
        assert!(circuit_breaker.can_execute());

        // 成功请求应该关闭断路器
        let result: Result<String, _> = circuit_breaker.execute(|| async {
            Ok::<String, UnifiedError>("成功".to_string())
        }).await;

        assert!(result.is_ok());
        assert_eq!(circuit_breaker.state(), CircuitBreakerState::Closed);
    }

    #[test]
    fn test_circuit_breaker_stats() {
        let circuit_breaker = CircuitBreaker::new(CircuitBreakerConfig::default());
        let stats = circuit_breaker.get_stats();
        
        assert_eq!(stats.total_requests, 0);
        assert_eq!(stats.successful_requests, 0);
        assert_eq!(stats.failed_requests, 0);
        assert_eq!(stats.current_state, CircuitBreakerState::Closed);
        assert_eq!(stats.failure_rate, 0.0);
    }

    #[test]
    fn test_circuit_breaker_reset() {
        let circuit_breaker = CircuitBreaker::new(CircuitBreakerConfig::default());
        
        // 记录一些失败
        circuit_breaker.record_failure();
        circuit_breaker.record_failure();
        
        // 重置
        circuit_breaker.reset();
        
        assert_eq!(circuit_breaker.state(), CircuitBreakerState::Closed);
        let stats = circuit_breaker.get_stats();
        assert_eq!(stats.failed_requests, 0);
    }
}
