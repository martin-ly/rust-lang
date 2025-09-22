//! 流量管理模块
//!
//! 提供流量策略、重试、超时和限流功能

use std::collections::HashMap;
use std::time::Duration;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// 流量管理器
#[derive(Debug)]
pub struct TrafficManager {
    policies: HashMap<String, TrafficPolicy>,
    config: TrafficConfig,
}

impl TrafficManager {
    /// 创建新的流量管理器
    pub fn new(config: TrafficConfig) -> Self {
        Self {
            policies: HashMap::new(),
            config,
        }
    }

    /// 添加流量策略
    pub fn add_policy(&mut self, service_name: String, policy: TrafficPolicy) {
        self.policies.insert(service_name, policy);
    }

    /// 获取流量策略
    pub fn get_policy(&self, service_name: &str) -> Option<&TrafficPolicy> {
        self.policies.get(service_name)
    }

    /// 获取策略数量
    pub fn get_policy_count(&self) -> usize {
        self.policies.len()
    }

    /// 移除流量策略
    pub fn remove_policy(&mut self, service_name: &str) -> Option<TrafficPolicy> {
        self.policies.remove(service_name)
    }

    /// 应用流量策略
    pub async fn apply_policy<F, T>(&self, service_name: &str, operation: F) -> Result<T, TrafficError>
    where
        F: Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, TrafficError>> + Send + 'static>> + Send + 'static,
        T: Send + 'static,
    {
        let policy = self.get_policy(service_name)
            .unwrap_or(&self.config.default_policy);

        self.apply_retry_policy(policy, operation).await
    }

    /// 应用重试策略
    async fn apply_retry_policy<F, T>(&self, policy: &TrafficPolicy, operation: F) -> Result<T, TrafficError>
    where
        F: Fn() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, TrafficError>> + Send + 'static>> + Send + 'static,
        T: Send + 'static,
    {
        let mut last_error = None;
        
        for attempt in 0..=policy.retry.max_attempts {
            if attempt > 0 {
                let delay = policy.retry.calculate_delay(attempt);
                tokio::time::sleep(delay).await;
            }

            // 应用超时策略
            let result = tokio::time::timeout(policy.timeout.timeout, operation()).await;
            
            match result {
                Ok(Ok(value)) => return Ok(value),
                Ok(Err(error)) => {
                    last_error = Some(error);
                    if !policy.retry.should_retry(&last_error.as_ref().unwrap()) {
                        break;
                    }
                }
                Err(_) => {
                    last_error = Some(TrafficError::Timeout);
                    if !policy.retry.should_retry(&TrafficError::Timeout) {
                        break;
                    }
                }
            }
        }

        Err(last_error.unwrap_or(TrafficError::MaxRetriesExceeded))
    }

    /// 检查限流
    pub fn check_rate_limit(&self, _service_name: &str, _client_id: &str) -> Result<(), TrafficError> {
        // 这里简化处理，实际应用中应该使用更复杂的限流算法
        Ok(())
    }
}

/// 流量策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrafficPolicy {
    pub retry: RetryPolicy,
    pub timeout: TimeoutPolicy,
    pub rate_limit: RateLimitPolicy,
    pub circuit_breaker: Option<String>,
}

impl Default for TrafficPolicy {
    fn default() -> Self {
        Self {
            retry: RetryPolicy::default(),
            timeout: TimeoutPolicy::default(),
            rate_limit: RateLimitPolicy::default(),
            circuit_breaker: None,
        }
    }
}

/// 重试策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryPolicy {
    pub max_attempts: u32,
    pub initial_delay: Duration,
    pub max_delay: Duration,
    pub backoff_multiplier: f64,
    pub jitter: bool,
    pub retryable_errors: Vec<String>,
}

impl Default for RetryPolicy {
    fn default() -> Self {
        Self {
            max_attempts: 3,
            initial_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(5),
            backoff_multiplier: 2.0,
            jitter: true,
            retryable_errors: vec![
                "timeout".to_string(),
                "connection_error".to_string(),
                "service_unavailable".to_string(),
            ],
        }
    }
}

impl RetryPolicy {
    /// 计算重试延迟
    pub fn calculate_delay(&self, attempt: u32) -> Duration {
        let delay_ms = (self.initial_delay.as_millis() as f64 * self.backoff_multiplier.powi(attempt as i32 - 1)) as u64;
        let delay = Duration::from_millis(delay_ms.min(self.max_delay.as_millis() as u64));
        
        if self.jitter {
            // 添加随机抖动，避免惊群效应
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            
            let mut hasher = DefaultHasher::new();
            std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos()
                .hash(&mut hasher);
            
            let jitter_factor = 0.5 + (hasher.finish() % 100) as f64 / 200.0; // 0.5-1.0
            Duration::from_millis((delay.as_millis() as f64 * jitter_factor) as u64)
        } else {
            delay
        }
    }

    /// 检查是否应该重试
    pub fn should_retry(&self, error: &TrafficError) -> bool {
        match error {
            TrafficError::Timeout => self.retryable_errors.contains(&"timeout".to_string()),
            TrafficError::ConnectionError => self.retryable_errors.contains(&"connection_error".to_string()),
            TrafficError::ServiceUnavailable => self.retryable_errors.contains(&"service_unavailable".to_string()),
            _ => false,
        }
    }
}

/// 超时策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimeoutPolicy {
    pub timeout: Duration,
    pub connection_timeout: Duration,
    pub read_timeout: Duration,
    pub write_timeout: Duration,
}

impl Default for TimeoutPolicy {
    fn default() -> Self {
        Self {
            timeout: Duration::from_secs(30),
            connection_timeout: Duration::from_secs(10),
            read_timeout: Duration::from_secs(30),
            write_timeout: Duration::from_secs(30),
        }
    }
}

/// 限流策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimitPolicy {
    pub requests_per_second: u32,
    pub burst_size: u32,
    pub window_size: Duration,
    pub per_client: bool,
}

impl Default for RateLimitPolicy {
    fn default() -> Self {
        Self {
            requests_per_second: 100,
            burst_size: 10,
            window_size: Duration::from_secs(1),
            per_client: false,
        }
    }
}

/// 流量规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrafficRule {
    pub service_name: String,
    pub path_pattern: String,
    pub method: Option<String>,
    pub weight: u32,
    pub tags: HashMap<String, String>,
    pub policy: TrafficPolicy,
}

impl TrafficRule {
    /// 创建新的流量规则
    pub fn new(service_name: String, path_pattern: String) -> Self {
        Self {
            service_name,
            path_pattern,
            method: None,
            weight: 100,
            tags: HashMap::new(),
            policy: TrafficPolicy::default(),
        }
    }

    /// 匹配路径
    pub fn matches_path(&self, path: &str) -> bool {
        // 简单的通配符匹配，实际应用中应该使用更复杂的路由匹配
        if self.path_pattern == "*" {
            return true;
        }
        
        if self.path_pattern.ends_with("*") {
            let prefix = &self.path_pattern[..self.path_pattern.len() - 1];
            return path.starts_with(prefix);
        }
        
        self.path_pattern == path
    }

    /// 匹配方法
    pub fn matches_method(&self, method: &str) -> bool {
        self.method.as_ref().map_or(true, |m| m == method)
    }
}

/// 流量配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TrafficConfig {
    pub default_policy: TrafficPolicy,
    pub rules: Vec<TrafficRule>,
    pub global_rate_limit: Option<RateLimitPolicy>,
}

impl Default for TrafficConfig {
    fn default() -> Self {
        Self {
            default_policy: TrafficPolicy::default(),
            rules: Vec::new(),
            global_rate_limit: None,
        }
    }
}

/// 流量错误
#[derive(Error, Debug)]
pub enum TrafficError {
    #[error("超时错误")]
    Timeout,
    #[error("连接错误")]
    ConnectionError,
    #[error("服务不可用")]
    ServiceUnavailable,
    #[error("限流错误")]
    RateLimited,
    #[error("重试次数超限")]
    MaxRetriesExceeded,
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    #[error("策略错误: {0}")]
    PolicyError(String),
}

/// 流量结果类型别名
pub type TrafficResult<T> = Result<T, TrafficError>;
