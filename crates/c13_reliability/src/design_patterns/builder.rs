/// 建造者模式 (Builder Pattern)
///
/// 使用多个简单的对象一步一步构建成一个复杂的对象
///
/// # 应用场景
///
/// - 复杂配置对象的构建
/// - 可选参数众多的对象创建
/// - 需要step-by-step构建的对象
/// - 不可变对象的构建

use crate::prelude::*;
//use crate::error_handling::{ErrorContext, ErrorSeverity};
use std::time::Duration;
//use std::collections::HashMap;
use serde::{Serialize, Deserialize};

// Helper function to create validation errors
fn validation_error(msg: impl Into<String>) -> anyhow::Error {
    anyhow::anyhow!(msg.into())
}

/// 建造者 trait
pub trait Builder {
    type Product;
    
    /// 构建产品
    fn build(self) -> Result<Self::Product>;
    
    /// 验证构建参数
    fn validate(&self) -> Result<()> {
        Ok(())
    }
}

// ============================================================================
// 重试配置建造者
// ============================================================================

/// 重试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryConfig {
    pub max_attempts: u32,
    pub initial_delay: Duration,
    pub max_delay: Duration,
    pub backoff_multiplier: f64,
    pub jitter: bool,
    pub retryable_errors: Vec<String>,
}

/// 重试配置建造者
#[derive(Debug, Clone)]
pub struct RetryConfigBuilder {
    max_attempts: Option<u32>,
    initial_delay: Option<Duration>,
    max_delay: Option<Duration>,
    backoff_multiplier: Option<f64>,
    jitter: Option<bool>,
    retryable_errors: Vec<String>,
}

impl RetryConfigBuilder {
    pub fn new() -> Self {
        Self {
            max_attempts: None,
            initial_delay: None,
            max_delay: None,
            backoff_multiplier: None,
            jitter: None,
            retryable_errors: Vec::new(),
        }
    }
    
    pub fn max_attempts(mut self, attempts: u32) -> Self {
        self.max_attempts = Some(attempts);
        self
    }
    
    pub fn initial_delay(mut self, delay: Duration) -> Self {
        self.initial_delay = Some(delay);
        self
    }
    
    pub fn max_delay(mut self, delay: Duration) -> Self {
        self.max_delay = Some(delay);
        self
    }
    
    pub fn backoff_multiplier(mut self, multiplier: f64) -> Self {
        self.backoff_multiplier = Some(multiplier);
        self
    }
    
    pub fn with_jitter(mut self) -> Self {
        self.jitter = Some(true);
        self
    }
    
    pub fn retryable_error(mut self, error: impl Into<String>) -> Self {
        self.retryable_errors.push(error.into());
        self
    }
}

impl Default for RetryConfigBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl Builder for RetryConfigBuilder {
    type Product = RetryConfig;
    
    fn validate(&self) -> Result<()> {
        if let Some(max_attempts) = self.max_attempts {
            if max_attempts == 0 {
                return Err(validation_error("max_attempts must be > 0"));
            }
        }
        
        if let Some(multiplier) = self.backoff_multiplier {
            if multiplier <= 0.0 {
                return Err(validation_error("backoff_multiplier must be > 0"));
            }
        }
        
        Ok(())
    }
    
    fn build(self) -> Result<RetryConfig> {
        self.validate()?;
        
        Ok(RetryConfig {
            max_attempts: self.max_attempts.unwrap_or(3),
            initial_delay: self.initial_delay.unwrap_or(Duration::from_millis(100)),
            max_delay: self.max_delay.unwrap_or(Duration::from_secs(30)),
            backoff_multiplier: self.backoff_multiplier.unwrap_or(2.0),
            jitter: self.jitter.unwrap_or(true),
            retryable_errors: self.retryable_errors,
        })
    }
}

// ============================================================================
// 熔断器配置建造者
// ============================================================================

/// 熔断器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircuitBreakerConfig {
    pub failure_threshold: u32,
    pub success_threshold: u32,
    pub timeout: Duration,
    pub half_open_max_calls: u32,
    pub error_rate_threshold: f64,
    pub min_calls: u32,
}

/// 熔断器配置建造者
#[derive(Debug, Clone)]
pub struct CircuitBreakerConfigBuilder {
    failure_threshold: Option<u32>,
    success_threshold: Option<u32>,
    timeout: Option<Duration>,
    half_open_max_calls: Option<u32>,
    error_rate_threshold: Option<f64>,
    min_calls: Option<u32>,
}

impl CircuitBreakerConfigBuilder {
    pub fn new() -> Self {
        Self {
            failure_threshold: None,
            success_threshold: None,
            timeout: None,
            half_open_max_calls: None,
            error_rate_threshold: None,
            min_calls: None,
        }
    }
    
    pub fn failure_threshold(mut self, threshold: u32) -> Self {
        self.failure_threshold = Some(threshold);
        self
    }
    
    pub fn success_threshold(mut self, threshold: u32) -> Self {
        self.success_threshold = Some(threshold);
        self
    }
    
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }
    
    pub fn half_open_max_calls(mut self, max_calls: u32) -> Self {
        self.half_open_max_calls = Some(max_calls);
        self
    }
    
    pub fn error_rate_threshold(mut self, threshold: f64) -> Self {
        self.error_rate_threshold = Some(threshold);
        self
    }
    
    pub fn min_calls(mut self, min: u32) -> Self {
        self.min_calls = Some(min);
        self
    }
}

impl Default for CircuitBreakerConfigBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl Builder for CircuitBreakerConfigBuilder {
    type Product = CircuitBreakerConfig;
    
    fn validate(&self) -> Result<()> {
        if let Some(rate) = self.error_rate_threshold {
            if !(0.0..=1.0).contains(&rate) {
                return Err(validation_error("error_rate_threshold must be between 0 and 1"));
            }
        }
        
        Ok(())
    }
    
    fn build(self) -> Result<CircuitBreakerConfig> {
        self.validate()?;
        
        Ok(CircuitBreakerConfig {
            failure_threshold: self.failure_threshold.unwrap_or(5),
            success_threshold: self.success_threshold.unwrap_or(2),
            timeout: self.timeout.unwrap_or(Duration::from_secs(60)),
            half_open_max_calls: self.half_open_max_calls.unwrap_or(3),
            error_rate_threshold: self.error_rate_threshold.unwrap_or(0.5),
            min_calls: self.min_calls.unwrap_or(10),
        })
    }
}

// ============================================================================
// 服务配置建造者
// ============================================================================

/// 服务配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceConfig {
    pub name: String,
    pub host: String,
    pub port: u16,
    pub protocol: String,
    pub timeout: Duration,
    pub max_connections: u32,
    pub retry_config: Option<RetryConfig>,
    pub circuit_breaker_config: Option<CircuitBreakerConfig>,
    pub metadata: std::collections::HashMap<String, String>,
}

/// 服务配置建造者
#[derive(Debug, Clone)]
pub struct ServiceConfigBuilder {
    name: Option<String>,
    host: Option<String>,
    port: Option<u16>,
    protocol: Option<String>,
    timeout: Option<Duration>,
    max_connections: Option<u32>,
    retry_config: Option<RetryConfig>,
    circuit_breaker_config: Option<CircuitBreakerConfig>,
    metadata: std::collections::HashMap<String, String>,
}

impl ServiceConfigBuilder {
    pub fn new() -> Self {
        Self {
            name: None,
            host: None,
            port: None,
            protocol: None,
            timeout: None,
            max_connections: None,
            retry_config: None,
            circuit_breaker_config: None,
            metadata: std::collections::HashMap::new(),
        }
    }
    
    pub fn name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }
    
    pub fn host(mut self, host: impl Into<String>) -> Self {
        self.host = Some(host.into());
        self
    }
    
    pub fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }
    
    pub fn protocol(mut self, protocol: impl Into<String>) -> Self {
        self.protocol = Some(protocol.into());
        self
    }
    
    pub fn timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }
    
    pub fn max_connections(mut self, max: u32) -> Self {
        self.max_connections = Some(max);
        self
    }
    
    pub fn retry_config(mut self, config: RetryConfig) -> Self {
        self.retry_config = Some(config);
        self
    }
    
    pub fn circuit_breaker_config(mut self, config: CircuitBreakerConfig) -> Self {
        self.circuit_breaker_config = Some(config);
        self
    }
    
    pub fn metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }
}

impl Default for ServiceConfigBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl Builder for ServiceConfigBuilder {
    type Product = ServiceConfig;
    
    fn validate(&self) -> Result<()> {
        if self.name.is_none() {
            return Err(validation_error("Service name is required"));
        }
        
        if self.host.is_none() {
            return Err(validation_error("Service host is required"));
        }
        
        Ok(())
    }
    
    fn build(self) -> Result<ServiceConfig> {
        self.validate()?;
        
        Ok(ServiceConfig {
            name: self.name.unwrap(),
            host: self.host.unwrap(),
            port: self.port.unwrap_or(8080),
            protocol: self.protocol.unwrap_or_else(|| "http".to_string()),
            timeout: self.timeout.unwrap_or(Duration::from_secs(30)),
            max_connections: self.max_connections.unwrap_or(100),
            retry_config: self.retry_config,
            circuit_breaker_config: self.circuit_breaker_config,
            metadata: self.metadata,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_retry_config_builder() {
        let config = RetryConfigBuilder::new()
            .max_attempts(5)
            .initial_delay(Duration::from_millis(100))
            .max_delay(Duration::from_secs(10))
            .backoff_multiplier(2.0)
            .with_jitter()
            .retryable_error("timeout")
            .build()
            .unwrap();
        
        assert_eq!(config.max_attempts, 5);
        assert!(config.jitter);
        assert_eq!(config.retryable_errors.len(), 1);
    }
    
    #[test]
    fn test_circuit_breaker_config_builder() {
        let config = CircuitBreakerConfigBuilder::new()
            .failure_threshold(10)
            .success_threshold(5)
            .timeout(Duration::from_secs(30))
            .error_rate_threshold(0.6)
            .build()
            .unwrap();
        
        assert_eq!(config.failure_threshold, 10);
        assert_eq!(config.error_rate_threshold, 0.6);
    }
    
    #[test]
    fn test_service_config_builder() {
        let config = ServiceConfigBuilder::new()
            .name("my-service")
            .host("localhost")
            .port(8080)
            .protocol("http")
            .timeout(Duration::from_secs(5))
            .metadata("version", "1.0")
            .build()
            .unwrap();
        
        assert_eq!(config.name, "my-service");
        assert_eq!(config.port, 8080);
        assert_eq!(config.metadata.get("version"), Some(&"1.0".to_string()));
    }
    
    #[test]
    fn test_validation_error() {
        let result = RetryConfigBuilder::new()
            .max_attempts(0)
            .build();
        
        assert!(result.is_err());
    }
}

