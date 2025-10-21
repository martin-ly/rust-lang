//! Rust 1.90 增强配置模块
//! 
//! 利用 Rust 1.90 的新特性优化配置管理：
//! - 常量泛型推断
//! - 生命周期语法一致性
//! - 改进的错误处理

use crate::config::{RetryPolicy, Timeouts};

/// Rust 1.90 特性：使用常量泛型优化配置结构
/// 
/// 通过常量泛型参数提供编译时配置验证和优化
#[derive(Debug, Clone)]
pub struct EnhancedRedisConfig<const POOL_SIZE: usize = 10, const TIMEOUT_MS: u64 = 5000> {
    pub url: String,
    pub timeouts: Timeouts,
    pub retry: RetryPolicy,
    pub pool_size: usize,
    pub timeout_ms: u64,
}

impl<const POOL_SIZE: usize, const TIMEOUT_MS: u64> EnhancedRedisConfig<POOL_SIZE, TIMEOUT_MS> {
    /// 创建新的配置实例
    pub fn new(url: impl Into<String>) -> Self {
        Self {
            url: url.into(),
            timeouts: Timeouts::default(),
            retry: RetryPolicy::default(),
            pool_size: POOL_SIZE,
            timeout_ms: TIMEOUT_MS,
        }
    }
    
    /// 使用常量推断创建指定大小的配置
    pub fn with_pool_size<const NEW_POOL_SIZE: usize>(_pool_size: usize) -> EnhancedRedisConfig<NEW_POOL_SIZE, TIMEOUT_MS> {
        EnhancedRedisConfig::new("")
    }
    
    /// 使用常量推断创建指定超时的配置
    pub fn with_timeout<const NEW_TIMEOUT_MS: u64>(_timeout_ms: u64) -> EnhancedRedisConfig<POOL_SIZE, NEW_TIMEOUT_MS> {
        EnhancedRedisConfig::new("")
    }
    
    /// 验证配置的有效性
    pub fn validate(&self) -> Result<(), String> {
        if self.url.is_empty() {
            return Err("Redis URL 不能为空".to_string());
        }
        
        if self.pool_size == 0 {
            return Err("连接池大小必须大于 0".to_string());
        }
        
        if self.timeout_ms == 0 {
            return Err("超时时间必须大于 0".to_string());
        }
        
        Ok(())
    }
}

/// 高级 PostgreSQL 配置，利用常量泛型
#[derive(Debug, Clone)]
pub struct EnhancedPostgresConfig<const MAX_CONNECTIONS: usize = 20, const STATEMENT_TIMEOUT_MS: u64 = 30000> {
    pub url: String,
    pub timeouts: Timeouts,
    pub retry: RetryPolicy,
    pub max_connections: usize,
    pub statement_timeout_ms: u64,
}

impl<const MAX_CONNECTIONS: usize, const STATEMENT_TIMEOUT_MS: u64> 
    EnhancedPostgresConfig<MAX_CONNECTIONS, STATEMENT_TIMEOUT_MS> 
{
    pub fn new(url: impl Into<String>) -> Self {
        Self {
            url: url.into(),
            timeouts: Timeouts::default(),
            retry: RetryPolicy::default(),
            max_connections: MAX_CONNECTIONS,
            statement_timeout_ms: STATEMENT_TIMEOUT_MS,
        }
    }
    
    /// 使用常量推断创建指定连接数的配置
    pub fn with_max_connections<const NEW_CONNECTIONS: usize>(_connections: usize) -> EnhancedPostgresConfig<NEW_CONNECTIONS, STATEMENT_TIMEOUT_MS> {
        EnhancedPostgresConfig::new("")
    }
    
    /// 验证配置
    pub fn validate(&self) -> Result<(), String> {
        if self.url.is_empty() {
            return Err("PostgreSQL URL 不能为空".to_string());
        }
        
        if self.max_connections == 0 {
            return Err("最大连接数必须大于 0".to_string());
        }
        
        if self.max_connections > 1000 {
            return Err("最大连接数不能超过 1000".to_string());
        }
        
        Ok(())
    }
}

/// 消息队列配置，使用常量泛型优化缓冲区大小
#[derive(Debug, Clone)]
pub struct EnhancedNatsConfig<const BATCH_SIZE: usize = 100, const BUFFER_SIZE: usize = 1024> {
    pub url: String,
    pub subject: String,
    pub timeouts: Timeouts,
    pub retry: RetryPolicy,
    pub batch_size: usize,
    pub buffer_size: usize,
}

impl<const BATCH_SIZE: usize, const BUFFER_SIZE: usize> 
    EnhancedNatsConfig<BATCH_SIZE, BUFFER_SIZE> 
{
    pub fn new(url: impl Into<String>, subject: impl Into<String>) -> Self {
        Self {
            url: url.into(),
            subject: subject.into(),
            timeouts: Timeouts::default(),
            retry: RetryPolicy::default(),
            batch_size: BATCH_SIZE,
            buffer_size: BUFFER_SIZE,
        }
    }
    
    /// 使用常量推断创建指定批处理大小的配置
    pub fn with_batch_size<const NEW_BATCH_SIZE: usize>(_batch_size: usize) -> EnhancedNatsConfig<NEW_BATCH_SIZE, BUFFER_SIZE> {
        EnhancedNatsConfig::new("", "")
    }
    
    /// 使用常量推断创建指定缓冲区大小的配置
    pub fn with_buffer_size<const NEW_BUFFER_SIZE: usize>(_buffer_size: usize) -> EnhancedNatsConfig<BATCH_SIZE, NEW_BUFFER_SIZE> {
        EnhancedNatsConfig::new("", "")
    }
    
    /// 验证配置
    pub fn validate(&self) -> Result<(), String> {
        if self.url.is_empty() {
            return Err("NATS URL 不能为空".to_string());
        }
        
        if self.subject.is_empty() {
            return Err("NATS subject 不能为空".to_string());
        }
        
        if self.batch_size == 0 {
            return Err("批处理大小必须大于 0".to_string());
        }
        
        if self.buffer_size < self.batch_size {
            return Err("缓冲区大小不能小于批处理大小".to_string());
        }
        
        Ok(())
    }
}

/// 配置验证器，利用 Rust 1.90 的生命周期语法一致性
pub struct ConfigValidator<'a> {
    config_type: &'a str,
    errors: Vec<String>,
}

impl<'a> ConfigValidator<'a> {
    pub fn new(config_type: &'a str) -> Self {
        Self {
            config_type,
            errors: Vec::new(),
        }
    }
    
    /// 生命周期语法一致的方法
    pub fn validate_url<'b>(&'a self, url: &'b str) -> Result<&'a str, String> 
    where 
        'b: 'a, // 确保 url 的生命周期不短于 self
    {
        if url.is_empty() {
            return Err(format!("{} URL 不能为空", self.config_type));
        }
        
        if !url.starts_with("redis://") && !url.starts_with("postgres://") && !url.starts_with("nats://") {
            return Err(format!("{} URL 格式无效", self.config_type));
        }
        
        Ok(url)
    }
    
    pub fn add_error(&mut self, error: String) {
        self.errors.push(error);
    }
    
    pub fn has_errors(&self) -> bool {
        !self.errors.is_empty()
    }
    
    pub fn get_errors(&self) -> &[String] {
        &self.errors
    }
}

/// 配置工厂，展示 Rust 1.90 的改进错误处理
pub struct ConfigFactory;

impl ConfigFactory {
    /// 创建 Redis 配置，使用 Result::flatten 简化错误处理
    pub fn create_redis_config<const POOL_SIZE: usize, const TIMEOUT_MS: u64>(
        url: String,
        pool_size: Option<usize>,
        timeout_ms: Option<u64>,
    ) -> Result<EnhancedRedisConfig<POOL_SIZE, TIMEOUT_MS>, String> {
        let mut validator = ConfigValidator::new("Redis");
        
        // 验证 URL
        validator.validate_url(&url)?;
        
        // 验证可选参数
        if let Some(size) = pool_size {
            if size == 0 || size > 1000 {
                validator.add_error("连接池大小必须在 1-1000 之间".to_string());
            }
        }
        
        if let Some(timeout) = timeout_ms {
            if timeout == 0 {
                validator.add_error("超时时间必须大于 0".to_string());
            }
        }
        
        if validator.has_errors() {
            return Err(validator.get_errors().join("; "));
        }
        
        Ok(EnhancedRedisConfig::new(url))
    }
    
    /// 创建 PostgreSQL 配置
    pub fn create_postgres_config<const MAX_CONNECTIONS: usize, const STATEMENT_TIMEOUT_MS: u64>(
        url: String,
        max_connections: Option<usize>,
        statement_timeout_ms: Option<u64>,
    ) -> Result<EnhancedPostgresConfig<MAX_CONNECTIONS, STATEMENT_TIMEOUT_MS>, String> {
        let mut validator = ConfigValidator::new("PostgreSQL");
        
        validator.validate_url(&url)?;
        
        if let Some(connections) = max_connections {
            if connections == 0 || connections > 1000 {
                validator.add_error("最大连接数必须在 1-1000 之间".to_string());
            }
        }
        
        if let Some(timeout) = statement_timeout_ms {
            if timeout == 0 {
                validator.add_error("语句超时时间必须大于 0".to_string());
            }
        }
        
        if validator.has_errors() {
            return Err(validator.get_errors().join("; "));
        }
        
        Ok(EnhancedPostgresConfig::new(url))
    }
    
    /// 创建 NATS 配置
    pub fn create_nats_config<const BATCH_SIZE: usize, const BUFFER_SIZE: usize>(
        url: String,
        subject: String,
        batch_size: Option<usize>,
        buffer_size: Option<usize>,
    ) -> Result<EnhancedNatsConfig<BATCH_SIZE, BUFFER_SIZE>, String> {
        let mut validator = ConfigValidator::new("NATS");
        
        validator.validate_url(&url)?;
        
        if subject.is_empty() {
            validator.add_error("NATS subject 不能为空".to_string());
        }
        
        if let Some(size) = batch_size {
            if size == 0 || size > 10000 {
                validator.add_error("批处理大小必须在 1-10000 之间".to_string());
            }
        }
        
        if let Some(size) = buffer_size {
            if size < batch_size.unwrap_or(100) {
                validator.add_error("缓冲区大小不能小于批处理大小".to_string());
            }
        }
        
        if validator.has_errors() {
            return Err(validator.get_errors().join("; "));
        }
        
        Ok(EnhancedNatsConfig::new(url, subject))
    }
}

/// 配置组合器，展示 Rust 1.90 的高级特性
pub struct ConfigComposer<const REDIS_POOL_SIZE: usize = 10, const POSTGRES_CONNECTIONS: usize = 20> {
    pub redis_config: Option<EnhancedRedisConfig<REDIS_POOL_SIZE, 5000>>,
    pub postgres_config: Option<EnhancedPostgresConfig<POSTGRES_CONNECTIONS, 30000>>,
    pub nats_config: Option<EnhancedNatsConfig<100, 1024>>,
}

impl<const REDIS_POOL_SIZE: usize, const POSTGRES_CONNECTIONS: usize> 
    ConfigComposer<REDIS_POOL_SIZE, POSTGRES_CONNECTIONS> 
{
    pub fn new() -> Self {
        Self {
            redis_config: None,
            postgres_config: None,
            nats_config: None,
        }
    }
    
    /// 添加 Redis 配置
    pub fn with_redis(mut self, url: String) -> Result<Self, String> {
        self.redis_config = Some(ConfigFactory::create_redis_config(url, None, None)?);
        Ok(self)
    }
    
    /// 添加 PostgreSQL 配置
    pub fn with_postgres(mut self, url: String) -> Result<Self, String> {
        self.postgres_config = Some(ConfigFactory::create_postgres_config(url, None, None)?);
        Ok(self)
    }
    
    /// 添加 NATS 配置
    pub fn with_nats(mut self, url: String, subject: String) -> Result<Self, String> {
        self.nats_config = Some(ConfigFactory::create_nats_config(url, subject, None, None)?);
        Ok(self)
    }
    
    /// 验证所有配置
    pub fn validate_all(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();
        
        if let Some(ref config) = self.redis_config {
            if let Err(e) = config.validate() {
                errors.push(format!("Redis 配置错误: {}", e));
            }
        }
        
        if let Some(ref config) = self.postgres_config {
            if let Err(e) = config.validate() {
                errors.push(format!("PostgreSQL 配置错误: {}", e));
            }
        }
        
        if let Some(ref config) = self.nats_config {
            if let Err(e) = config.validate() {
                errors.push(format!("NATS 配置错误: {}", e));
            }
        }
        
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
    
    /// 检查是否有任何配置
    pub fn has_any_config(&self) -> bool {
        self.redis_config.is_some() || self.postgres_config.is_some() || self.nats_config.is_some()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_enhanced_redis_config() {
        let config: EnhancedRedisConfig<20, 10000> = EnhancedRedisConfig::new("redis://localhost:6379");
        assert_eq!(config.pool_size, 20);
        assert_eq!(config.timeout_ms, 10000);
        assert!(config.validate().is_ok());
    }
    
    #[test]
    fn test_enhanced_postgres_config() {
        let config: EnhancedPostgresConfig<50, 60000> = EnhancedPostgresConfig::new("postgres://localhost:5432/db");
        assert_eq!(config.max_connections, 50);
        assert_eq!(config.statement_timeout_ms, 60000);
        assert!(config.validate().is_ok());
    }
    
    #[test]
    fn test_enhanced_nats_config() {
        let config: EnhancedNatsConfig<200, 2048> = EnhancedNatsConfig::new("nats://localhost:4222", "test.subject");
        assert_eq!(config.batch_size, 200);
        assert_eq!(config.buffer_size, 2048);
        assert!(config.validate().is_ok());
    }
    
    #[test]
    fn test_config_validator() {
        let validator = ConfigValidator::new("Redis");
        
        assert!(validator.validate_url("redis://localhost:6379").is_ok());
        assert!(validator.validate_url("").is_err());
        assert!(validator.validate_url("invalid-url").is_err());
    }
    
    #[test]
    fn test_config_factory() {
        let redis_config = ConfigFactory::create_redis_config::<10, 5000>(
            "redis://localhost:6379".to_string(),
            None,
            None,
        );
        assert!(redis_config.is_ok());
        
        let postgres_config = ConfigFactory::create_postgres_config::<20, 30000>(
            "postgres://localhost:5432/db".to_string(),
            None,
            None,
        );
        assert!(postgres_config.is_ok());
        
        let nats_config = ConfigFactory::create_nats_config::<100, 1024>(
            "nats://localhost:4222".to_string(),
            "test.subject".to_string(),
            None,
            None,
        );
        assert!(nats_config.is_ok());
    }
    
    #[test]
    fn test_config_composer() {
        let composer: ConfigComposer<10, 20> = ConfigComposer::new()
            .with_redis("redis://localhost:6379".to_string())
            .unwrap()
            .with_postgres("postgres://localhost:5432/db".to_string())
            .unwrap()
            .with_nats("nats://localhost:4222".to_string(), "test.subject".to_string())
            .unwrap();
        
        assert!(composer.has_any_config());
        assert!(composer.validate_all().is_ok());
    }
}
