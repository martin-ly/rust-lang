//! 熔断器模块
//!
//! 提供熔断器模式实现，用于保护服务调用

use std::sync::atomic::{AtomicU32, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// 熔断器
#[derive(Debug)]
pub struct CircuitBreaker {
    config: CircuitBreakerConfig,
    state: Arc<AtomicUsize>,
    failure_count: Arc<AtomicU32>,
    success_count: Arc<AtomicU32>,
    last_failure_time: Arc<std::sync::Mutex<Option<Instant>>>,
    last_success_time: Arc<std::sync::Mutex<Option<Instant>>>,
    last_state_change: Arc<std::sync::Mutex<Instant>>,
}

impl CircuitBreaker {
    /// 创建新的熔断器
    pub fn new(config: CircuitBreakerConfig) -> Self {
        Self {
            config,
            state: Arc::new(AtomicUsize::new(CircuitBreakerState::Closed as usize)),
            failure_count: Arc::new(AtomicU32::new(0)),
            success_count: Arc::new(AtomicU32::new(0)),
            last_failure_time: Arc::new(std::sync::Mutex::new(None)),
            last_success_time: Arc::new(std::sync::Mutex::new(None)),
            last_state_change: Arc::new(std::sync::Mutex::new(Instant::now())),
        }
    }

    /// 检查是否可以执行
    pub fn can_execute(&self) -> bool {
        match self.get_state() {
            CircuitBreakerState::Closed => true,
            CircuitBreakerState::Open => self.should_attempt_reset(),
            CircuitBreakerState::HalfOpen => true,
        }
    }

    /// 执行操作
    pub async fn execute<F, T>(&self, operation: F) -> Result<T, CircuitBreakerError>
    where
        F: std::future::Future<Output = Result<T, CircuitBreakerError>>,
    {
        if !self.can_execute() {
            return Err(CircuitBreakerError::CircuitBreakerOpen);
        }

        let result = operation.await;

        match result {
            Ok(value) => {
                self.record_success();
                Ok(value)
            }
            Err(error) => {
                self.record_failure();
                Err(error)
            }
        }
    }

    /// 记录成功
    pub fn record_success(&self) {
        self.success_count.fetch_add(1, Ordering::Relaxed);
        
        {
            let mut last_success = self.last_success_time.lock().unwrap();
            *last_success = Some(Instant::now());
        }

        match self.get_state() {
            CircuitBreakerState::HalfOpen => {
                // 在半开状态下，连续成功达到阈值则关闭熔断器
                if self.success_count.load(Ordering::Relaxed) >= self.config.success_threshold {
                    self.transition_to_closed();
                }
            }
            CircuitBreakerState::Closed => {
                // 在关闭状态下，重置失败计数
                if self.failure_count.load(Ordering::Relaxed) > 0 {
                    self.failure_count.store(0, Ordering::Relaxed);
                }
            }
            _ => {}
        }
    }

    /// 记录失败
    pub fn record_failure(&self) {
        self.failure_count.fetch_add(1, Ordering::Relaxed);
        
        {
            let mut last_failure = self.last_failure_time.lock().unwrap();
            *last_failure = Some(Instant::now());
        }

        match self.get_state() {
            CircuitBreakerState::Closed => {
                // 在关闭状态下，失败次数达到阈值则打开熔断器
                if self.failure_count.load(Ordering::Relaxed) >= self.config.failure_threshold {
                    self.transition_to_open();
                }
            }
            CircuitBreakerState::HalfOpen => {
                // 在半开状态下，任何失败都会重新打开熔断器
                self.transition_to_open();
            }
            _ => {}
        }
    }

    /// 获取当前状态
    pub fn get_state(&self) -> CircuitBreakerState {
        let state_value = self.state.load(Ordering::Relaxed);
        match state_value {
            0 => CircuitBreakerState::Closed,
            1 => CircuitBreakerState::Open,
            2 => CircuitBreakerState::HalfOpen,
            _ => CircuitBreakerState::Closed,
        }
    }

    /// 检查是否应该尝试重置
    fn should_attempt_reset(&self) -> bool {
        if let Some(last_failure) = *self.last_failure_time.lock().unwrap() {
            Instant::now().duration_since(last_failure) >= self.config.timeout
        } else {
            true
        }
    }

    /// 转换到关闭状态
    fn transition_to_closed(&self) {
        self.state.store(CircuitBreakerState::Closed as usize, Ordering::Relaxed);
        self.failure_count.store(0, Ordering::Relaxed);
        self.success_count.store(0, Ordering::Relaxed);
        
        {
            let mut last_state_change = self.last_state_change.lock().unwrap();
            *last_state_change = Instant::now();
        }

        tracing::info!("熔断器状态转换到: Closed");
    }

    /// 转换到打开状态
    fn transition_to_open(&self) {
        self.state.store(CircuitBreakerState::Open as usize, Ordering::Relaxed);
        
        {
            let mut last_state_change = self.last_state_change.lock().unwrap();
            *last_state_change = Instant::now();
        }

        tracing::warn!("熔断器状态转换到: Open");
    }

    /// 转换到半开状态
    #[allow(dead_code)]
    fn transition_to_half_open(&self) {
        self.state.store(CircuitBreakerState::HalfOpen as usize, Ordering::Relaxed);
        self.success_count.store(0, Ordering::Relaxed);
        
        {
            let mut last_state_change = self.last_state_change.lock().unwrap();
            *last_state_change = Instant::now();
        }

        tracing::info!("熔断器状态转换到: HalfOpen");
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> CircuitBreakerStats {
        CircuitBreakerStats {
            state: self.get_state(),
            failure_count: self.failure_count.load(Ordering::Relaxed),
            success_count: self.success_count.load(Ordering::Relaxed),
            last_failure_time: *self.last_failure_time.lock().unwrap(),
            last_success_time: *self.last_success_time.lock().unwrap(),
            last_state_change: *self.last_state_change.lock().unwrap(),
        }
    }

    /// 重置熔断器
    pub fn reset(&self) {
        self.transition_to_closed();
    }

    /// 手动打开熔断器
    pub fn open(&self) {
        self.transition_to_open();
    }

    /// 手动关闭熔断器
    pub fn close(&self) {
        self.transition_to_closed();
    }
}

/// 熔断器状态
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CircuitBreakerState {
    Closed,    // 关闭状态，正常处理请求
    Open,      // 打开状态，拒绝所有请求
    HalfOpen,  // 半开状态，允许少量请求通过
}

impl std::fmt::Display for CircuitBreakerState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CircuitBreakerState::Closed => write!(f, "Closed"),
            CircuitBreakerState::Open => write!(f, "Open"),
            CircuitBreakerState::HalfOpen => write!(f, "HalfOpen"),
        }
    }
}

/// 熔断器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircuitBreakerConfig {
    pub failure_threshold: u32,
    pub success_threshold: u32,
    pub timeout: Duration,
    pub max_failures: u32,
    pub slow_call_threshold: Duration,
    pub slow_call_threshold_percentage: f64,
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 5,
            success_threshold: 3,
            timeout: Duration::from_secs(60),
            max_failures: 10,
            slow_call_threshold: Duration::from_secs(2),
            slow_call_threshold_percentage: 50.0,
        }
    }
}

/// 熔断器统计信息
#[derive(Debug, Clone)]
pub struct CircuitBreakerStats {
    pub state: CircuitBreakerState,
    pub failure_count: u32,
    pub success_count: u32,
    pub last_failure_time: Option<Instant>,
    pub last_success_time: Option<Instant>,
    pub last_state_change: Instant,
}

/// 熔断器错误
#[derive(Error, Debug)]
pub enum CircuitBreakerError {
    #[error("熔断器打开")]
    CircuitBreakerOpen,
    #[error("操作超时")]
    Timeout,
    #[error("调用失败: {0}")]
    CallFailed(String),
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    #[error("状态错误: {0}")]
    StateError(String),
}

/// 熔断器结果类型别名
pub type CircuitBreakerResult<T> = Result<T, CircuitBreakerError>;
