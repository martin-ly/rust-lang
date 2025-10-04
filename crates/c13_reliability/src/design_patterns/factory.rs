/// 工厂模式 (Factory Pattern)
///
/// 定义一个创建对象的接口，让子类决定实例化哪个类
///
/// # 应用场景
///
/// - 对象创建逻辑复杂
/// - 需要根据配置创建不同对象
/// - 依赖注入和IoC容器
/// - 插件系统

use crate::prelude::*;
//use crate::error_handling::{ErrorContext, ErrorSeverity};
use std::sync::Arc;
use std::collections::HashMap;

// Helper function to create validation errors
fn validation_error(msg: impl Into<String>) -> anyhow::Error {
    anyhow::anyhow!(msg.into())
}

/// 工厂 trait
pub trait Factory<Product>: Send + Sync {
    /// 创建产品
    fn create(&self) -> Result<Product>;
    
    /// 工厂名称
    fn name(&self) -> &str;
}

/// 抽象工厂 trait
pub trait AbstractFactory: Send + Sync {
    /// 产品类型名称
    fn product_type(&self) -> &str;
    
    /// 创建产品（返回动态类型）
    fn create_boxed(&self) -> Result<Box<dyn std::any::Any + Send>>;
}

/// 工厂注册表
pub struct FactoryRegistry {
    factories: HashMap<String, Arc<dyn AbstractFactory>>,
}

impl FactoryRegistry {
    pub fn new() -> Self {
        Self {
            factories: HashMap::new(),
        }
    }
    
    /// 注册工厂
    pub fn register(&mut self, name: impl Into<String>, factory: Arc<dyn AbstractFactory>) {
        self.factories.insert(name.into(), factory);
    }
    
    /// 创建产品
    pub fn create(&self, name: &str) -> Result<Box<dyn std::any::Any + Send>> {
        self.factories
            .get(name)
            .ok_or_else(|| UnifiedError::not_found(format!("Factory not found: {}", name)))?
            .create_boxed()
    }
    
    /// 列出所有工厂
    pub fn list_factories(&self) -> Vec<String> {
        self.factories.keys().cloned().collect()
    }
}

impl Default for FactoryRegistry {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// 连接池工厂示例
// ============================================================================

/// 连接 trait
pub trait Connection: Send + Sync {
    fn id(&self) -> &str;
    fn is_valid(&self) -> bool;
}

/// HTTP连接
#[allow(dead_code)]
pub struct HttpConnection {
    id: String,
    url: String,
}

#[allow(dead_code)]
impl HttpConnection {
    pub fn new(url: impl Into<String>) -> Self {
        Self {
            id: uuid::Uuid::new_v4().to_string(),
            url: url.into(),
        }
    }
}

impl Connection for HttpConnection {
    fn id(&self) -> &str {
        &self.id
    }
    
    fn is_valid(&self) -> bool {
        true // 简化实现
    }
}

/// HTTP连接工厂
pub struct HttpConnectionFactory {
    url: String,
}

#[allow(dead_code)]
impl HttpConnectionFactory {
    pub fn new(url: impl Into<String>) -> Self {
        Self {
            url: url.into(),
        }
    }
}

impl Factory<Box<dyn Connection>> for HttpConnectionFactory {
    fn create(&self) -> Result<Box<dyn Connection>> {
        Ok(Box::new(HttpConnection::new(self.url.clone())))
    }
    
    fn name(&self) -> &str {
        "http_connection"
    }
}

/// 数据库连接
#[allow(dead_code)]
pub struct DatabaseConnection {
    id: String,
    dsn: String,
}

#[allow(dead_code)]
impl DatabaseConnection {
    pub fn new(dsn: impl Into<String>) -> Self {
        Self {
            id: uuid::Uuid::new_v4().to_string(),
            dsn: dsn.into(),
        }
    }
}

impl Connection for DatabaseConnection {
    fn id(&self) -> &str {
        &self.id
    }
    
    fn is_valid(&self) -> bool {
        true // 简化实现
    }
}

/// 数据库连接工厂
#[allow(dead_code)]
pub struct DatabaseConnectionFactory {
    dsn: String,
}

#[allow(dead_code)]
impl DatabaseConnectionFactory {
    pub fn new(dsn: impl Into<String>) -> Self {
        Self {
            dsn: dsn.into(),
        }
    }
}

impl Factory<Box<dyn Connection>> for DatabaseConnectionFactory {
    fn create(&self) -> Result<Box<dyn Connection>> {
        Ok(Box::new(DatabaseConnection::new(self.dsn.clone())))
    }
    
    fn name(&self) -> &str {
        "database_connection"
    }
}

// ============================================================================
// 限流器工厂示例（重用fault_tolerance模块）
// ============================================================================

use crate::fault_tolerance::rate_limiting::RateLimiter;

/// 限流器工厂
#[allow(dead_code)]
pub struct RateLimiterFactory {
    algorithm: String,
    rate: u64,
    period_ms: u64,
}

#[allow(dead_code)]
impl RateLimiterFactory {
    pub fn new(algorithm: impl Into<String>, rate: u64, period_ms: u64) -> Self {
        Self {
            algorithm: algorithm.into(),
            rate,
            period_ms,
        }
    }
}

impl Factory<Arc<dyn RateLimiter>> for RateLimiterFactory {
    fn create(&self) -> Result<Arc<dyn RateLimiter>> {
        use crate::fault_tolerance::rate_limiting::*;
        use std::time::Duration;
        
        let period = Duration::from_millis(self.period_ms);
        
        match self.algorithm.as_str() {
            "token_bucket" => Ok(Arc::new(TokenBucket::new(self.rate, period))),
            "leaky_bucket" => Ok(Arc::new(LeakyBucket::new(self.rate, period))),
            "fixed_window" => Ok(Arc::new(FixedWindow::new(self.rate, period))),
            "sliding_window" => Ok(Arc::new(SlidingWindow::new(self.rate, period))),
            "sliding_window_log" => Ok(Arc::new(SlidingWindowLog::new(self.rate, period))),
            _ => Err(validation_error(format!("Unknown rate limiter algorithm: {}", self.algorithm))),
        }
    }
    
    fn name(&self) -> &str {
        "rate_limiter"
    }
}

// ============================================================================
// 熔断器工厂示例
// ============================================================================

use crate::fault_tolerance::circuit_breaker::CircuitBreaker;

/// 熔断器工厂
#[allow(dead_code)]
pub struct CircuitBreakerFactory {
    failure_threshold: u32,
    success_threshold: u32,
    timeout_ms: u64,
}

#[allow(dead_code)]
impl CircuitBreakerFactory {
    pub fn new(failure_threshold: u32, success_threshold: u32, timeout_ms: u64) -> Self {
        Self {
            failure_threshold,
            success_threshold,
            timeout_ms,
        }
    }
}

impl Factory<Arc<CircuitBreaker>> for CircuitBreakerFactory {
    fn create(&self) -> Result<Arc<CircuitBreaker>> {
        use std::time::Duration;
        use crate::fault_tolerance::circuit_breaker::CircuitBreakerConfig;
        
        let config = CircuitBreakerConfig {
            failure_threshold: self.failure_threshold as u64,
            success_threshold: self.success_threshold as u64,
            recovery_timeout: Duration::from_millis(self.timeout_ms),
            half_open_max_requests: 3,
            sliding_window_size: Duration::from_secs(60),
            minimum_requests: 10,
        };
        
        Ok(Arc::new(CircuitBreaker::new(config)))
    }
    
    fn name(&self) -> &str {
        "circuit_breaker"
    }
}

// ============================================================================
// 配置驱动工厂
// ============================================================================

use serde::{Serialize, Deserialize};

/// 工厂配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FactoryConfig {
    pub factory_type: String,
    pub parameters: HashMap<String, serde_json::Value>,
}

/// 配置驱动的工厂
#[allow(dead_code)]
pub struct ConfigDrivenFactory {
    config: FactoryConfig,
}

#[allow(dead_code)]
impl ConfigDrivenFactory {
    pub fn new(config: FactoryConfig) -> Self {
        Self { config }
    }
    
    /// 从配置创建限流器
    pub fn create_rate_limiter(&self) -> Result<Arc<dyn RateLimiter>> {
        use crate::fault_tolerance::rate_limiting::*;
        use std::time::Duration;
        
        let algorithm = self.config.parameters.get("algorithm")
            .and_then(|v| v.as_str())
            .ok_or_else(|| validation_error("Missing algorithm parameter"))?;
        
        let rate = self.config.parameters.get("rate")
            .and_then(|v| v.as_u64())
            .ok_or_else(|| validation_error("Missing rate parameter"))?;
        
        let period_ms = self.config.parameters.get("period_ms")
            .and_then(|v| v.as_u64())
            .unwrap_or(1000);
        
        let period = Duration::from_millis(period_ms);
        
        match algorithm {
            "token_bucket" => Ok(Arc::new(TokenBucket::new(rate, period))),
            "leaky_bucket" => Ok(Arc::new(LeakyBucket::new(rate, period))),
            "fixed_window" => Ok(Arc::new(FixedWindow::new(rate, period))),
            "sliding_window" => Ok(Arc::new(SlidingWindow::new(rate, period))),
            "sliding_window_log" => Ok(Arc::new(SlidingWindowLog::new(rate, period))),
            _ => Err(validation_error(format!("Unknown algorithm: {}", algorithm))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_connection_factory() {
        let http_factory = HttpConnectionFactory::new("https://api.example.com");
        let conn = http_factory.create().unwrap();
        assert!(conn.is_valid());
        
        let db_factory = DatabaseConnectionFactory::new("postgresql://localhost/db");
        let conn = db_factory.create().unwrap();
        assert!(conn.is_valid());
    }
    
    #[tokio::test]
    async fn test_rate_limiter_factory() {
        let factory = RateLimiterFactory::new("token_bucket", 100, 1000);
        let limiter = factory.create().unwrap();
        
        assert!(limiter.try_acquire().await);
    }
    
    #[test]
    fn test_circuit_breaker_factory() {
        let factory = CircuitBreakerFactory::new(5, 3, 5000);
        let cb = factory.create().unwrap();
        
        // CircuitBreaker创建成功即可
        assert!(std::sync::Arc::strong_count(&cb) == 1);
    }
}

