//! 错误处理模块
//! 
//! 提供统一的错误处理机制，支持多种错误类型和错误链

use thiserror::Error;
use serde::{Deserialize, Serialize};
use std::fmt;

/// 应用错误类型
#[derive(Error, Debug, Clone, Serialize, Deserialize)]
pub enum AppError {
    #[error("配置错误: {message}")]
    Config { message: String },
    
    #[error("数据库错误: {message}")]
    Database { message: String },
    
    #[error("网络错误: {message}")]
    Network { message: String },
    
    #[error("认证错误: {message}")]
    Authentication { message: String },
    
    #[error("授权错误: {message}")]
    Authorization { message: String },
    
    #[error("验证错误: {message}")]
    Validation { message: String },
    
    #[error("业务逻辑错误: {message}")]
    Business { message: String },
    
    #[error("内部服务器错误: {message}")]
    Internal { message: String },
    
    #[error("外部服务错误: {service} - {message}")]
    External { service: String, message: String },
    
    #[error("超时错误: {operation}")]
    Timeout { operation: String },
    
    #[error("资源未找到: {resource}")]
    NotFound { resource: String },
    
    #[error("资源已存在: {resource}")]
    Conflict { resource: String },
    
    #[error("请求过大: {size} bytes")]
    PayloadTooLarge { size: usize },
    
    #[error("请求频率限制: {limit} requests per {period}")]
    RateLimited { limit: u32, period: String },
}

/// 错误严重程度
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ErrorSeverity {
    Low,
    Medium,
    High,
    Critical,
}

impl AppError {
    /// 获取错误严重程度
    pub fn severity(&self) -> ErrorSeverity {
        match self {
            AppError::Config { .. } => ErrorSeverity::Medium,
            AppError::Database { .. } => ErrorSeverity::High,
            AppError::Network { .. } => ErrorSeverity::Medium,
            AppError::Authentication { .. } => ErrorSeverity::High,
            AppError::Authorization { .. } => ErrorSeverity::High,
            AppError::Validation { .. } => ErrorSeverity::Low,
            AppError::Business { .. } => ErrorSeverity::Medium,
            AppError::Internal { .. } => ErrorSeverity::Critical,
            AppError::External { .. } => ErrorSeverity::Medium,
            AppError::Timeout { .. } => ErrorSeverity::Medium,
            AppError::NotFound { .. } => ErrorSeverity::Low,
            AppError::Conflict { .. } => ErrorSeverity::Low,
            AppError::PayloadTooLarge { .. } => ErrorSeverity::Low,
            AppError::RateLimited { .. } => ErrorSeverity::Low,
        }
    }
    
    /// 获取错误代码
    pub fn code(&self) -> &'static str {
        match self {
            AppError::Config { .. } => "CONFIG_ERROR",
            AppError::Database { .. } => "DATABASE_ERROR",
            AppError::Network { .. } => "NETWORK_ERROR",
            AppError::Authentication { .. } => "AUTH_ERROR",
            AppError::Authorization { .. } => "AUTHZ_ERROR",
            AppError::Validation { .. } => "VALIDATION_ERROR",
            AppError::Business { .. } => "BUSINESS_ERROR",
            AppError::Internal { .. } => "INTERNAL_ERROR",
            AppError::External { .. } => "EXTERNAL_ERROR",
            AppError::Timeout { .. } => "TIMEOUT_ERROR",
            AppError::NotFound { .. } => "NOT_FOUND",
            AppError::Conflict { .. } => "CONFLICT",
            AppError::PayloadTooLarge { .. } => "PAYLOAD_TOO_LARGE",
            AppError::RateLimited { .. } => "RATE_LIMITED",
        }
    }
    
    /// 检查是否可重试
    pub fn is_retryable(&self) -> bool {
        match self {
            AppError::Network { .. } => true,
            AppError::Database { .. } => true,
            AppError::External { .. } => true,
            AppError::Timeout { .. } => true,
            AppError::Internal { .. } => true,
            _ => false,
        }
    }
    
    /// 检查是否为客户端错误
    pub fn is_client_error(&self) -> bool {
        match self {
            AppError::Validation { .. } => true,
            AppError::Authentication { .. } => true,
            AppError::Authorization { .. } => true,
            AppError::NotFound { .. } => true,
            AppError::Conflict { .. } => true,
            AppError::PayloadTooLarge { .. } => true,
            AppError::RateLimited { .. } => true,
            _ => false,
        }
    }
    
    /// 检查是否为服务器错误
    pub fn is_server_error(&self) -> bool {
        match self {
            AppError::Internal { .. } => true,
            AppError::Database { .. } => true,
            AppError::Config { .. } => true,
            _ => false,
        }
    }
}

/// 错误上下文
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorContext {
    pub request_id: Option<String>,
    pub user_id: Option<String>,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub source: Option<String>,
    pub metadata: std::collections::HashMap<String, String>,
}

impl Default for ErrorContext {
    fn default() -> Self {
        Self {
            request_id: None,
            user_id: None,
            timestamp: chrono::Utc::now(),
            source: None,
            metadata: std::collections::HashMap::new(),
        }
    }
}

/// 带上下文的错误
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ContextualError {
    pub error: AppError,
    pub context: ErrorContext,
}

impl ContextualError {
    pub fn new(error: AppError) -> Self {
        Self {
            error,
            context: ErrorContext::default(),
        }
    }
    
    pub fn with_context(mut self, context: ErrorContext) -> Self {
        self.context = context;
        self
    }
    
    pub fn with_request_id(mut self, request_id: String) -> Self {
        self.context.request_id = Some(request_id);
        self
    }
    
    pub fn with_user_id(mut self, user_id: String) -> Self {
        self.context.user_id = Some(user_id);
        self
    }
    
    pub fn with_source(mut self, source: String) -> Self {
        self.context.source = Some(source);
        self
    }
    
    pub fn with_metadata(mut self, key: String, value: String) -> Self {
        self.context.metadata.insert(key, value);
        self
    }
}

impl fmt::Display for ContextualError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.error)?;
        if let Some(request_id) = &self.context.request_id {
            write!(f, " [Request ID: {}]", request_id)?;
        }
        if let Some(user_id) = &self.context.user_id {
            write!(f, " [User ID: {}]", user_id)?;
        }
        Ok(())
    }
}

impl std::error::Error for ContextualError {}

/// 错误结果类型
pub type AppResult<T> = Result<T, ContextualError>;

/// 错误处理工具函数
pub mod utils {
    use super::*;
    
    /// 将标准错误转换为应用错误
    pub fn from_std_error(error: Box<dyn std::error::Error + Send + Sync>) -> ContextualError {
        ContextualError::new(AppError::Internal {
            message: error.to_string(),
        })
    }
    
    /// 从字符串创建配置错误
    pub fn config_error(message: impl Into<String>) -> ContextualError {
        ContextualError::new(AppError::Config {
            message: message.into(),
        })
    }
    
    /// 从字符串创建数据库错误
    pub fn database_error(message: impl Into<String>) -> ContextualError {
        ContextualError::new(AppError::Database {
            message: message.into(),
        })
    }
    
    /// 从字符串创建网络错误
    pub fn network_error(message: impl Into<String>) -> ContextualError {
        ContextualError::new(AppError::Network {
            message: message.into(),
        })
    }
    
    /// 从字符串创建验证错误
    pub fn validation_error(message: impl Into<String>) -> ContextualError {
        ContextualError::new(AppError::Validation {
            message: message.into(),
        })
    }
    
    /// 从字符串创建业务错误
    pub fn business_error(message: impl Into<String>) -> ContextualError {
        ContextualError::new(AppError::Business {
            message: message.into(),
        })
    }
    
    /// 创建资源未找到错误
    pub fn not_found_error(resource: impl Into<String>) -> ContextualError {
        ContextualError::new(AppError::NotFound {
            resource: resource.into(),
        })
    }
    
    /// 创建资源冲突错误
    pub fn conflict_error(resource: impl Into<String>) -> ContextualError {
        ContextualError::new(AppError::Conflict {
            resource: resource.into(),
        })
    }
    
    /// 创建超时错误
    pub fn timeout_error(operation: impl Into<String>) -> ContextualError {
        ContextualError::new(AppError::Timeout {
            operation: operation.into(),
        })
    }
    
    /// 创建外部服务错误
    pub fn external_error(service: impl Into<String>, message: impl Into<String>) -> ContextualError {
        ContextualError::new(AppError::External {
            service: service.into(),
            message: message.into(),
        })
    }
}