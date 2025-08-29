# 🛡️ Rust错误类型设计最佳实践

## 📋 概述

**文档类型**: 最佳实践指南  
**适用版本**: Rust 2021 Edition+  
**创建日期**: 2025年1月27日  
**最后更新**: 2025年1月27日  
**质量等级**: 🏆 **工业级标准**  

## 🎯 目标

本文档提供Rust错误类型设计的最佳实践，帮助开发者建立健壮、可维护、用户友好的错误处理体系。通过合理的错误类型设计，提高代码的可靠性和用户体验。

## 📊 核心原则

### 1. 错误分类原则

- **可恢复错误**: 程序可以继续执行，用户可以进行修正
- **不可恢复错误**: 程序无法继续，需要终止或重启
- **系统错误**: 底层系统或外部依赖的错误
- **业务错误**: 业务逻辑相关的错误

### 2. 错误信息原则

- **用户友好**: 错误信息对用户有意义
- **调试友好**: 包含足够的调试信息
- **结构化**: 错误信息结构化和可解析
- **本地化**: 支持多语言错误信息

### 3. 错误传播原则

- **显式处理**: 明确处理每个可能的错误
- **类型安全**: 利用类型系统保证错误处理
- **性能考虑**: 错误处理不应显著影响性能
- **向后兼容**: 错误类型变更保持兼容性

## 🏗️ 错误类型设计模式

### 1. 基础错误类型

```rust
use std::fmt;
use std::error::Error as StdError;

/// 应用程序错误类型
#[derive(Debug)]
pub enum AppError {
    // 系统级错误
    System(SystemError),
    // 业务逻辑错误
    Business(BusinessError),
    // 验证错误
    Validation(ValidationError),
    // 外部服务错误
    External(ExternalError),
}

/// 系统错误
#[derive(Debug)]
pub enum SystemError {
    Database(String),
    Network(String),
    FileSystem(String),
    Configuration(String),
}

/// 业务错误
#[derive(Debug)]
pub enum BusinessError {
    UserNotFound(String),
    InsufficientPermissions(String),
    ResourceConflict(String),
    InvalidOperation(String),
}

/// 验证错误
#[derive(Debug)]
pub enum ValidationError {
    InvalidInput(String),
    MissingRequired(String),
    FormatError(String),
    RangeError(String),
}

/// 外部服务错误
#[derive(Debug)]
pub enum ExternalError {
    ServiceUnavailable(String),
    Timeout(String),
    AuthenticationFailed(String),
    RateLimitExceeded(String),
}

impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AppError::System(err) => write!(f, "System error: {}", err),
            AppError::Business(err) => write!(f, "Business error: {}", err),
            AppError::Validation(err) => write!(f, "Validation error: {}", err),
            AppError::External(err) => write!(f, "External error: {}", err),
        }
    }
}

impl fmt::Display for SystemError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SystemError::Database(msg) => write!(f, "Database: {}", msg),
            SystemError::Network(msg) => write!(f, "Network: {}", msg),
            SystemError::FileSystem(msg) => write!(f, "File system: {}", msg),
            SystemError::Configuration(msg) => write!(f, "Configuration: {}", msg),
        }
    }
}

impl fmt::Display for BusinessError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BusinessError::UserNotFound(id) => write!(f, "User not found: {}", id),
            BusinessError::InsufficientPermissions(action) => {
                write!(f, "Insufficient permissions for: {}", action)
            }
            BusinessError::ResourceConflict(resource) => {
                write!(f, "Resource conflict: {}", resource)
            }
            BusinessError::InvalidOperation(operation) => {
                write!(f, "Invalid operation: {}", operation)
            }
        }
    }
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValidationError::InvalidInput(field) => write!(f, "Invalid input: {}", field),
            ValidationError::MissingRequired(field) => write!(f, "Missing required: {}", field),
            ValidationError::FormatError(field) => write!(f, "Format error: {}", field),
            ValidationError::RangeError(field) => write!(f, "Range error: {}", field),
        }
    }
}

impl fmt::Display for ExternalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExternalError::ServiceUnavailable(service) => {
                write!(f, "Service unavailable: {}", service)
            }
            ExternalError::Timeout(operation) => write!(f, "Timeout: {}", operation),
            ExternalError::AuthenticationFailed(service) => {
                write!(f, "Authentication failed: {}", service)
            }
            ExternalError::RateLimitExceeded(service) => {
                write!(f, "Rate limit exceeded: {}", service)
            }
        }
    }
}

impl StdError for AppError {}
impl StdError for SystemError {}
impl StdError for BusinessError {}
impl StdError for ValidationError {}
impl StdError for ExternalError {}

// 类型别名
pub type AppResult<T> = Result<T, AppError>;
```

### 2. 使用 thiserror 简化错误定义

```rust
use thiserror::Error;

/// 使用 thiserror 宏简化错误定义
#[derive(Error, Debug)]
pub enum AppError {
    #[error("Database error: {message}")]
    Database { message: String, source: sqlx::Error },
    
    #[error("Network error: {message}")]
    Network { message: String, source: reqwest::Error },
    
    #[error("User not found: {user_id}")]
    UserNotFound { user_id: String },
    
    #[error("Insufficient permissions for: {action}")]
    InsufficientPermissions { action: String },
    
    #[error("Validation error: {field} - {message}")]
    Validation { field: String, message: String },
    
    #[error("External service error: {service} - {message}")]
    ExternalService { service: String, message: String },
}

// 实现转换特征
impl From<sqlx::Error> for AppError {
    fn from(err: sqlx::Error) -> Self {
        AppError::Database {
            message: "Database operation failed".to_string(),
            source: err,
        }
    }
}

impl From<reqwest::Error> for AppError {
    fn from(err: reqwest::Error) -> Self {
        AppError::Network {
            message: "Network request failed".to_string(),
            source: err,
        }
    }
}
```

### 3. 上下文错误类型

```rust
use std::error::Error;
use std::fmt;

/// 带上下文的错误类型
#[derive(Debug)]
pub struct ContextError {
    pub context: String,
    pub source: Box<dyn Error + Send + Sync>,
}

impl ContextError {
    pub fn new(context: impl Into<String>, source: impl Error + Send + Sync + 'static) -> Self {
        Self {
            context: context.into(),
            source: Box::new(source),
        }
    }
    
    pub fn context(&self) -> &str {
        &self.context
    }
    
    pub fn source(&self) -> &(dyn Error + Send + Sync) {
        self.source.as_ref()
    }
}

impl fmt::Display for ContextError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.context, self.source)
    }
}

impl Error for ContextError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(self.source.as_ref())
    }
}

// 扩展 Result 类型
pub trait ResultExt<T, E> {
    fn with_context<C>(self, context: C) -> Result<T, ContextError>
    where
        C: Into<String>;
}

impl<T, E> ResultExt<T, E> for Result<T, E>
where
    E: Error + Send + Sync + 'static,
{
    fn with_context<C>(self, context: C) -> Result<T, ContextError>
    where
        C: Into<String>,
    {
        self.map_err(|e| ContextError::new(context, e))
    }
}
```

## 🔧 错误处理策略

### 1. 错误传播模式

```rust
use std::fs::File;
use std::io::{self, Read};

/// 使用 ? 操作符进行错误传播
pub fn read_config_file(path: &str) -> AppResult<String> {
    let mut file = File::open(path)
        .map_err(|e| AppError::System(SystemError::FileSystem(e.to_string())))?;
    
    let mut contents = String::new();
    file.read_to_string(&mut contents)
        .map_err(|e| AppError::System(SystemError::FileSystem(e.to_string())))?;
    
    Ok(contents)
}

/// 使用 map_err 转换错误类型
pub fn read_config_file_improved(path: &str) -> AppResult<String> {
    let mut file = File::open(path)
        .map_err(|e| AppError::System(SystemError::FileSystem(e.to_string())))?;
    
    let mut contents = String::new();
    file.read_to_string(&mut contents)
        .map_err(|e| AppError::System(SystemError::FileSystem(e.to_string())))?;
    
    Ok(contents)
}

/// 使用自定义错误类型
#[derive(Debug, thiserror::Error)]
pub enum ConfigError {
    #[error("Failed to open config file: {path}")]
    FileOpen { path: String, source: io::Error },
    
    #[error("Failed to read config file: {path}")]
    FileRead { path: String, source: io::Error },
    
    #[error("Invalid config format: {message}")]
    InvalidFormat { message: String },
}

pub fn read_config_file_custom(path: &str) -> Result<String, ConfigError> {
    let mut file = File::open(path)
        .map_err(|e| ConfigError::FileOpen {
            path: path.to_string(),
            source: e,
        })?;
    
    let mut contents = String::new();
    file.read_to_string(&mut contents)
        .map_err(|e| ConfigError::FileRead {
            path: path.to_string(),
            source: e,
        })?;
    
    Ok(contents)
}
```

### 2. 错误恢复策略

```rust
/// 可恢复错误处理
pub fn process_user_input(input: &str) -> AppResult<String> {
    // 尝试解析输入
    match parse_input(input) {
        Ok(result) => Ok(result),
        Err(ValidationError::InvalidInput(field)) => {
            // 尝试修复输入
            let fixed_input = fix_input(input);
            parse_input(&fixed_input)
                .map_err(|e| AppError::Validation(e))
        }
        Err(e) => Err(AppError::Validation(e)),
    }
}

/// 重试机制
pub async fn retry_operation<F, T, E>(
    mut operation: F,
    max_retries: usize,
    delay: std::time::Duration,
) -> Result<T, E>
where
    F: FnMut() -> Result<T, E>,
    E: std::fmt::Debug,
{
    let mut last_error = None;
    
    for attempt in 0..=max_retries {
        match operation() {
            Ok(result) => return Ok(result),
            Err(e) => {
                last_error = Some(e);
                if attempt < max_retries {
                    tokio::time::sleep(delay).await;
                }
            }
        }
    }
    
    Err(last_error.unwrap())
}

/// 降级策略
pub async fn fetch_data_with_fallback(url: &str) -> AppResult<String> {
    // 尝试主要数据源
    match fetch_from_primary_source(url).await {
        Ok(data) => Ok(data),
        Err(_) => {
            // 降级到备用数据源
            fetch_from_fallback_source(url).await
        }
    }
}
```

### 3. 错误日志记录

```rust
use tracing::{error, warn, info, debug};

/// 结构化错误日志
pub fn log_error(err: &AppError, context: &str) {
    match err {
        AppError::System(system_err) => {
            error!(
                error_type = "system",
                error = %system_err,
                context = context,
                "System error occurred"
            );
        }
        AppError::Business(business_err) => {
            warn!(
                error_type = "business",
                error = %business_err,
                context = context,
                "Business logic error"
            );
        }
        AppError::Validation(validation_err) => {
            info!(
                error_type = "validation",
                error = %validation_err,
                context = context,
                "Validation error"
            );
        }
        AppError::External(external_err) => {
            error!(
                error_type = "external",
                error = %external_err,
                context = context,
                "External service error"
            );
        }
    }
}

/// 错误追踪
pub fn log_error_with_trace(err: &AppError, context: &str) {
    error!(
        error = %err,
        context = context,
        backtrace = ?err.backtrace(),
        "Error occurred with full trace"
    );
}
```

## 📋 错误处理最佳实践

### 1. 错误类型设计检查清单

- [ ] 错误类型是否分类清晰？
- [ ] 错误信息是否用户友好？
- [ ] 是否包含足够的调试信息？
- [ ] 错误类型是否支持错误链？
- [ ] 是否实现了必要的特征？

### 2. 错误处理检查清单

- [ ] 是否明确处理了所有可能的错误？
- [ ] 错误传播是否使用了合适的模式？
- [ ] 是否提供了错误恢复机制？
- [ ] 错误日志是否结构化？
- [ ] 是否考虑了性能影响？

### 3. 用户体验检查清单

- [ ] 错误信息是否对用户有意义？
- [ ] 是否提供了错误解决建议？
- [ ] 是否支持错误本地化？
- [ ] 是否提供了错误报告机制？
- [ ] 是否考虑了可访问性？

## 🚀 高级错误处理模式

### 1. 错误包装器

```rust
/// 错误包装器模式
pub struct ErrorWrapper<E> {
    pub error: E,
    pub context: Vec<String>,
    pub timestamp: std::time::SystemTime,
}

impl<E> ErrorWrapper<E> {
    pub fn new(error: E) -> Self {
        Self {
            error,
            context: Vec::new(),
            timestamp: std::time::SystemTime::now(),
        }
    }
    
    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context.push(context.into());
        self
    }
    
    pub fn add_context(&mut self, context: impl Into<String>) {
        self.context.push(context.into());
    }
}

impl<E: std::fmt::Display> std::fmt::Display for ErrorWrapper<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Error: {}", self.error)?;
        if !self.context.is_empty() {
            write!(f, " (Context: {})", self.context.join(" -> "))?;
        }
        Ok(())
    }
}
```

### 2. 错误聚合

```rust
/// 错误聚合模式
#[derive(Debug)]
pub struct ErrorAggregate {
    pub errors: Vec<Box<dyn std::error::Error + Send + Sync>>,
    pub context: String,
}

impl ErrorAggregate {
    pub fn new(context: impl Into<String>) -> Self {
        Self {
            errors: Vec::new(),
            context: context.into(),
        }
    }
    
    pub fn add_error<E>(&mut self, error: E)
    where
        E: std::error::Error + Send + Sync + 'static,
    {
        self.errors.push(Box::new(error));
    }
    
    pub fn is_empty(&self) -> bool {
        self.errors.is_empty()
    }
    
    pub fn len(&self) -> usize {
        self.errors.len()
    }
}

impl std::fmt::Display for ErrorAggregate {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Multiple errors in {}: ", self.context)?;
        for (i, error) in self.errors.iter().enumerate() {
            if i > 0 {
                write!(f, "; ")?;
            }
            write!(f, "{}", error)?;
        }
        Ok(())
    }
}

impl std::error::Error for ErrorAggregate {}
```

### 3. 错误恢复策略

```rust
/// 错误恢复策略
pub trait ErrorRecovery {
    type Error;
    
    fn can_recover(&self) -> bool;
    fn recovery_strategy(&self) -> Option<RecoveryStrategy>;
}

#[derive(Debug)]
pub enum RecoveryStrategy {
    Retry { max_attempts: usize, delay: std::time::Duration },
    Fallback { alternative: String },
    Degrade { reduced_functionality: String },
    UserIntervention { message: String },
}

impl ErrorRecovery for AppError {
    type Error = AppError;
    
    fn can_recover(&self) -> bool {
        matches!(self, AppError::Validation(_) | AppError::External(_))
    }
    
    fn recovery_strategy(&self) -> Option<RecoveryStrategy> {
        match self {
            AppError::External(ExternalError::ServiceUnavailable(_)) => {
                Some(RecoveryStrategy::Retry {
                    max_attempts: 3,
                    delay: std::time::Duration::from_secs(1),
                })
            }
            AppError::External(ExternalError::RateLimitExceeded(_)) => {
                Some(RecoveryStrategy::Retry {
                    max_attempts: 5,
                    delay: std::time::Duration::from_secs(30),
                })
            }
            AppError::Validation(_) => {
                Some(RecoveryStrategy::UserIntervention {
                    message: "Please check your input and try again".to_string(),
                })
            }
            _ => None,
        }
    }
}
```

## 📈 性能优化

### 1. 错误类型优化

```rust
/// 使用 Box<dyn Error> 减少枚举大小
#[derive(Debug)]
pub enum OptimizedError {
    Simple(String),
    Complex(Box<dyn std::error::Error + Send + Sync>),
}

/// 使用静态字符串减少内存分配
#[derive(Debug)]
pub enum StaticError {
    Database(&'static str),
    Network(&'static str),
    Validation(&'static str),
}
```

### 2. 错误处理性能

```rust
/// 避免在热路径中分配错误
pub fn fast_error_check(value: &str) -> Result<(), &'static str> {
    if value.is_empty() {
        return Err("Value cannot be empty");
    }
    if value.len() > 100 {
        return Err("Value too long");
    }
    Ok(())
}

/// 使用 const 错误消息
pub const ERR_EMPTY_VALUE: &str = "Value cannot be empty";
pub const ERR_VALUE_TOO_LONG: &str = "Value too long";
```

## 📚 参考资料

- [Rust Book - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [thiserror Documentation](https://docs.rs/thiserror/)
- [anyhow Documentation](https://docs.rs/anyhow/)
- [Rust Error Handling Patterns](https://blog.burntsushi.net/rust-error-handling/)

---

**文档状态**: 🎯 **持续更新**  
**实用价值**: ⭐⭐⭐⭐⭐ **工业级标准**  
**创新引领**: 🚀 **持续突破**  
**开放协作**: 🤝 **欢迎贡献**
