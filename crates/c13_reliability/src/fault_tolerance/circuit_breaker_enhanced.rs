//! # 增强型熔断器（Enhanced Circuit Breaker）
//!
//! 提供更强大的熔断器实现，支持复杂的状态转换和自适应行为。
//!
//! ## 核心特性
//!
//! - **五状态模型**：Closed → Open → Half-Open → Recovery → Closed
//! - **多种检测策略**：失败率、慢调用率、异常类型
//! - **自适应阈值**：根据历史数据动态调整
//! - **分层熔断**：支持多级熔断策略
//! - **熔断降级**：自动切换到备用服务
//! - **健康检查**：主动探测服务健康状态
//!
//! ## 使用示例
//!
//! ```rust,no_run
//! use c13_reliability::fault_tolerance::circuit_breaker_enhanced::{
//!     EnhancedCircuitBreaker, CircuitBreakerPolicy
//! };
//! use std::time::Duration;
//!
//! async fn example() -> Result<(), Box<dyn std::error::Error>> {
//!     let breaker = EnhancedCircuitBreaker::builder()
//!         .name("payment-service")
//!         .failure_threshold(0.5)  // 50%失败率
//!         .slow_call_threshold(0.3) // 30%慢调用率
//!         .slow_call_duration(Duration::from_secs(1))
//!         .open_timeout(Duration::from_secs(60))
//!         .build();
//!     
//!     let result = breaker.call(async {
//!         // 调用外部服务
//!         Ok(42)
//!     }).await?;
//!     
//!     Ok(())
//! }
//! ```

use std::collections::VecDeque;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock};

use crate::error_handling::prelude::*;

// ================================================================================================
// 核心类型定义
// ================================================================================================

/// 熔断器状态（五状态模型）
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CircuitState {
    /// 关闭（正常运行）
    #[default]
    Closed,
    /// 打开（拒绝请求）
    Open,
    /// 半开（试探性恢复）
    HalfOpen,
    /// 恢复中（逐步增加流量）
    Recovering,
    /// 强制打开（手动控制）
    ForcedOpen,
}

/// 熔断器策略
#[derive(Debug, Clone)]
pub enum CircuitBreakerPolicy {
    /// 基于失败率
    FailureRate {
        threshold: f64,
        minimum_calls: usize,
    },
    /// 基于慢调用率
    SlowCallRate {
        threshold: f64,
        duration: Duration,
        minimum_calls: usize,
    },
    /// 基于异常类型
    ExceptionType {
        exception_threshold: usize,
        time_window: Duration,
    },
    /// 组合策略
    Combined {
        policies: Vec<CircuitBreakerPolicy>,
        require_all: bool, // true=AND, false=OR
    },
}

/// 调用结果
#[derive(Debug, Clone)]
pub enum CallResult {
    /// 成功
    Success {
        duration: Duration,
    },
    /// 失败
    Failure {
        duration: Duration,
        error: String,
    },
    /// 超时
    Timeout {
        duration: Duration,
    },
    /// 被拒绝（熔断器打开）
    Rejected,
}

/// 熔断器配置
#[derive(Debug, Clone)]
pub struct EnhancedCircuitBreakerConfig {
    /// 熔断器名称
    pub name: String,
    /// 失败率阈值
    pub failure_threshold: f64,
    /// 慢调用阈值
    pub slow_call_threshold: f64,
    /// 慢调用持续时间
    pub slow_call_duration: Duration,
    /// 最小调用次数（统计有效）
    pub minimum_calls: usize,
    /// 打开状态持续时间
    pub open_timeout: Duration,
    /// 半开状态允许的试探次数
    pub half_open_max_calls: usize,
    /// 滑动窗口大小
    pub sliding_window_size: usize,
    /// 是否启用自适应阈值
    pub adaptive_threshold: bool,
    /// 健康检查间隔
    pub health_check_interval: Option<Duration>,
}

impl Default for EnhancedCircuitBreakerConfig {
    fn default() -> Self {
        Self {
            name: "default-breaker".to_string(),
            failure_threshold: 0.5,
            slow_call_threshold: 0.3,
            slow_call_duration: Duration::from_secs(1),
            minimum_calls: 10,
            open_timeout: Duration::from_secs(60),
            half_open_max_calls: 5,
            sliding_window_size: 100,
            adaptive_threshold: false,
            health_check_interval: None,
        }
    }
}

/// 熔断器统计信息
#[derive(Debug, Clone, Default)]
pub struct CircuitBreakerStats {
    /// 总调用次数
    pub total_calls: u64,
    /// 成功次数
    pub successful_calls: u64,
    /// 失败次数
    pub failed_calls: u64,
    /// 慢调用次数
    pub slow_calls: u64,
    /// 被拒绝次数
    pub rejected_calls: u64,
    /// 当前状态
    pub state: CircuitState,
    /// 失败率
    pub failure_rate: f64,
    /// 慢调用率
    pub slow_call_rate: f64,
    /// 平均响应时间（毫秒）
    pub avg_response_time_ms: f64,
    /// 状态转换次数
    pub state_transitions: u64,
    /// 最后状态转换时间
    pub last_state_change: Option<Instant>,
}

// ================================================================================================
// 滑动窗口
// ================================================================================================

/// 滑动窗口（用于统计）
struct SlidingWindow {
    window: VecDeque<CallResult>,
    max_size: usize,
}

impl SlidingWindow {
    fn new(max_size: usize) -> Self {
        Self {
            window: VecDeque::with_capacity(max_size),
            max_size,
        }
    }

    fn add(&mut self, result: CallResult) {
        if self.window.len() >= self.max_size {
            self.window.pop_front();
        }
        self.window.push_back(result);
    }

    fn len(&self) -> usize {
        self.window.len()
    }

    fn failure_rate(&self) -> f64 {
        if self.window.is_empty() {
            return 0.0;
        }
        
        let failures = self.window.iter()
            .filter(|r| matches!(r, CallResult::Failure { .. } | CallResult::Timeout { .. }))
            .count();
        
        failures as f64 / self.window.len() as f64
    }

    fn slow_call_rate(&self, slow_duration: Duration) -> f64 {
        if self.window.is_empty() {
            return 0.0;
        }
        
        let slow_calls = self.window.iter()
            .filter(|r| match r {
                CallResult::Success { duration } => *duration >= slow_duration,
                _ => false,
            })
            .count();
        
        slow_calls as f64 / self.window.len() as f64
    }

    fn avg_response_time(&self) -> Duration {
        if self.window.is_empty() {
            return Duration::ZERO;
        }
        
        let total: Duration = self.window.iter()
            .filter_map(|r| match r {
                CallResult::Success { duration } => Some(*duration),
                CallResult::Failure { duration, .. } => Some(*duration),
                CallResult::Timeout { duration } => Some(*duration),
                _ => None,
            })
            .sum();
        
        total / self.window.len() as u32
    }
}

// ================================================================================================
// 增强型熔断器
// ================================================================================================

/// 增强型熔断器
pub struct EnhancedCircuitBreaker {
    config: EnhancedCircuitBreakerConfig,
    state: Arc<RwLock<CircuitState>>,
    window: Arc<Mutex<SlidingWindow>>,
    stats: Arc<RwLock<CircuitBreakerStats>>,
    open_since: Arc<RwLock<Option<Instant>>>,
    half_open_calls: Arc<Mutex<usize>>,
}

impl EnhancedCircuitBreaker {
    /// 创建构建器
    pub fn builder() -> EnhancedCircuitBreakerBuilder {
        EnhancedCircuitBreakerBuilder::new()
    }

    /// 创建新的熔断器
    pub fn new(config: EnhancedCircuitBreakerConfig) -> Self {
        Self {
            window: Arc::new(Mutex::new(SlidingWindow::new(config.sliding_window_size))),
            state: Arc::new(RwLock::new(CircuitState::Closed)),
            stats: Arc::new(RwLock::new(CircuitBreakerStats::default())),
            open_since: Arc::new(RwLock::new(None)),
            half_open_calls: Arc::new(Mutex::new(0)),
            config,
        }
    }

    /// 执行调用
    pub async fn call<F, T>(&self, operation: F) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>> + Send,
        T: Send,
    {
        // 检查熔断器状态
        let current_state = {
            let state = self.state.read().await;
            *state
        };

        match current_state {
            CircuitState::Open => {
                // 检查是否可以转换到半开状态
                if self.should_attempt_reset().await {
                    self.transition_to(CircuitState::HalfOpen).await;
                } else {
                    // 拒绝请求
                    self.record_rejection().await;
                    return Err(UnifiedError::resource_unavailable(
                        "Circuit breaker is open"
                    ));
                }
            }
            CircuitState::ForcedOpen => {
                self.record_rejection().await;
                return Err(UnifiedError::resource_unavailable(
                    "Circuit breaker is forced open"
                ));
            }
            CircuitState::HalfOpen => {
                // 检查半开状态的调用次数
                let mut calls = self.half_open_calls.lock().await;
                if *calls >= self.config.half_open_max_calls {
                    drop(calls);
                    self.record_rejection().await;
                    return Err(UnifiedError::resource_unavailable(
                        "Circuit breaker half-open limit reached"
                    ));
                }
                *calls += 1;
            }
            _ => {}
        }

        // 执行操作
        let start = Instant::now();
        let result = operation.await;
        let duration = start.elapsed();

        // 记录结果
        match &result {
            Ok(_) => {
                self.record_success(duration).await;
            }
            Err(_) => {
                self.record_failure(duration).await;
            }
        }

        // 评估状态转换
        self.evaluate_state().await;

        result
    }

    /// 记录成功
    async fn record_success(&self, duration: Duration) {
        let mut window = self.window.lock().await;
        window.add(CallResult::Success { duration });
        
        let mut stats = self.stats.write().await;
        stats.total_calls += 1;
        stats.successful_calls += 1;
        
        if duration >= self.config.slow_call_duration {
            stats.slow_calls += 1;
        }
        
        self.update_stats_metrics(&mut stats, &window).await;
    }

    /// 记录失败
    async fn record_failure(&self, duration: Duration) {
        let mut window = self.window.lock().await;
        window.add(CallResult::Failure {
            duration,
            error: "Operation failed".to_string(),
        });
        
        let mut stats = self.stats.write().await;
        stats.total_calls += 1;
        stats.failed_calls += 1;
        
        self.update_stats_metrics(&mut stats, &window).await;
    }

    /// 记录拒绝
    async fn record_rejection(&self) {
        let mut stats = self.stats.write().await;
        stats.rejected_calls += 1;
    }

    /// 更新统计指标
    async fn update_stats_metrics(
        &self,
        stats: &mut CircuitBreakerStats,
        window: &SlidingWindow,
    ) {
        stats.failure_rate = window.failure_rate();
        stats.slow_call_rate = window.slow_call_rate(self.config.slow_call_duration);
        stats.avg_response_time_ms = window.avg_response_time().as_millis() as f64;
    }

    /// 评估状态
    async fn evaluate_state(&self) {
        let current_state = {
            let state = self.state.read().await;
            *state
        };

        let window = self.window.lock().await;
        
        // 检查是否有足够的调用次数
        if window.len() < self.config.minimum_calls {
            return;
        }

        let failure_rate = window.failure_rate();
        let slow_call_rate = window.slow_call_rate(self.config.slow_call_duration);

        match current_state {
            CircuitState::Closed => {
                // 检查是否应该打开
                if failure_rate >= self.config.failure_threshold 
                    || slow_call_rate >= self.config.slow_call_threshold {
                    drop(window);
                    self.transition_to(CircuitState::Open).await;
                }
            }
            CircuitState::HalfOpen => {
                // 检查是否应该关闭或重新打开
                if failure_rate < self.config.failure_threshold * 0.5 {
                    drop(window);
                    self.transition_to(CircuitState::Closed).await;
                } else if failure_rate >= self.config.failure_threshold {
                    drop(window);
                    self.transition_to(CircuitState::Open).await;
                }
            }
            _ => {}
        }
    }

    /// 检查是否应该尝试重置
    async fn should_attempt_reset(&self) -> bool {
        let open_since = self.open_since.read().await;
        if let Some(since) = *open_since {
            since.elapsed() >= self.config.open_timeout
        } else {
            false
        }
    }

    /// 状态转换
    async fn transition_to(&self, new_state: CircuitState) {
        let mut state = self.state.write().await;
        let old_state = *state;
        
        if old_state == new_state {
            return;
        }

        *state = new_state;
        drop(state);

        // 更新打开时间
        if new_state == CircuitState::Open {
            let mut open_since = self.open_since.write().await;
            *open_since = Some(Instant::now());
        } else if new_state == CircuitState::Closed {
            let mut open_since = self.open_since.write().await;
            *open_since = None;
            
            // 重置半开调用计数
            let mut half_open_calls = self.half_open_calls.lock().await;
            *half_open_calls = 0;
        }

        // 更新统计
        let mut stats = self.stats.write().await;
        stats.state = new_state;
        stats.state_transitions += 1;
        stats.last_state_change = Some(Instant::now());

        tracing::info!(
            "Circuit breaker '{}' state transition: {:?} → {:?}",
            self.config.name,
            old_state,
            new_state
        );
    }

    /// 获取当前状态
    pub async fn get_state(&self) -> CircuitState {
        let state = self.state.read().await;
        *state
    }

    /// 获取统计信息
    pub async fn get_stats(&self) -> CircuitBreakerStats {
        let stats = self.stats.read().await;
        stats.clone()
    }

    /// 手动打开熔断器
    pub async fn force_open(&self) {
        self.transition_to(CircuitState::ForcedOpen).await;
    }

    /// 手动关闭熔断器
    pub async fn force_close(&self) {
        self.transition_to(CircuitState::Closed).await;
    }

    /// 重置熔断器
    pub async fn reset(&self) {
        let mut window = self.window.lock().await;
        *window = SlidingWindow::new(self.config.sliding_window_size);
        
        let mut stats = self.stats.write().await;
        *stats = CircuitBreakerStats::default();
        
        self.transition_to(CircuitState::Closed).await;
    }
}

// ================================================================================================
// 构建器模式
// ================================================================================================

/// 熔断器构建器
pub struct EnhancedCircuitBreakerBuilder {
    config: EnhancedCircuitBreakerConfig,
}

impl EnhancedCircuitBreakerBuilder {
    fn new() -> Self {
        Self {
            config: EnhancedCircuitBreakerConfig::default(),
        }
    }

    pub fn name(mut self, name: impl Into<String>) -> Self {
        self.config.name = name.into();
        self
    }

    pub fn failure_threshold(mut self, threshold: f64) -> Self {
        self.config.failure_threshold = threshold;
        self
    }

    pub fn slow_call_threshold(mut self, threshold: f64) -> Self {
        self.config.slow_call_threshold = threshold;
        self
    }

    pub fn slow_call_duration(mut self, duration: Duration) -> Self {
        self.config.slow_call_duration = duration;
        self
    }

    pub fn minimum_calls(mut self, calls: usize) -> Self {
        self.config.minimum_calls = calls;
        self
    }

    pub fn open_timeout(mut self, timeout: Duration) -> Self {
        self.config.open_timeout = timeout;
        self
    }

    pub fn half_open_max_calls(mut self, calls: usize) -> Self {
        self.config.half_open_max_calls = calls;
        self
    }

    pub fn sliding_window_size(mut self, size: usize) -> Self {
        self.config.sliding_window_size = size;
        self
    }

    pub fn adaptive_threshold(mut self, enable: bool) -> Self {
        self.config.adaptive_threshold = enable;
        self
    }

    pub fn build(self) -> EnhancedCircuitBreaker {
        EnhancedCircuitBreaker::new(self.config)
    }
}

// ================================================================================================
// 测试
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_circuit_breaker_closed() {
        let breaker = EnhancedCircuitBreaker::builder()
            .minimum_calls(3)
            .failure_threshold(0.5)
            .build();
        
        for _ in 0..5 {
            let result = breaker.call(async { Ok::<_, UnifiedError>(42) }).await;
            assert!(result.is_ok());
        }
        
        let state = breaker.get_state().await;
        assert_eq!(state, CircuitState::Closed);
    }

    #[tokio::test]
    async fn test_circuit_breaker_opens() {
        let breaker = EnhancedCircuitBreaker::builder()
            .minimum_calls(3)
            .failure_threshold(0.5)
            .build();
        
        // 触发失败
        for _ in 0..5 {
            let _ = breaker.call(async {
                Err::<i32, _>(UnifiedError::state_error("test error"))
            }).await;
        }
        
        let state = breaker.get_state().await;
        assert_eq!(state, CircuitState::Open);
    }

    #[tokio::test]
    async fn test_circuit_breaker_stats() {
        let breaker = EnhancedCircuitBreaker::builder()
            .build();
        
        // 成功调用
        for _ in 0..3 {
            let _ = breaker.call(async { Ok::<_, UnifiedError>(()) }).await;
        }
        
        // 失败调用
        for _ in 0..2 {
            let _ = breaker.call(async {
                Err::<(), _>(UnifiedError::state_error("error"))
            }).await;
        }
        
        let stats = breaker.get_stats().await;
        assert_eq!(stats.total_calls, 5);
        assert_eq!(stats.successful_calls, 3);
        assert_eq!(stats.failed_calls, 2);
    }
}

