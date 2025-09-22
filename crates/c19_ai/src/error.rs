//! 统一错误处理模块
//! 
//! 提供统一的错误类型、错误转换和错误处理功能

use serde::{Deserialize, Serialize};
use std::fmt;
use std::error::Error as StdError;
use std::collections::HashMap;

/// 错误代码枚举
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ErrorCode {
    // 通用错误 (1000-1999)
    InternalError,
    InvalidInput,
    NotFound,
    Unauthorized,
    Forbidden,
    Conflict,
    TooManyRequests,
    ServiceUnavailable,
    
    // 认证错误 (2000-2999)
    InvalidCredentials,
    TokenExpired,
    TokenInvalid,
    AccountLocked,
    TwoFactorRequired,
    PasswordTooWeak,
    
    // 数据库错误 (3000-3999)
    DatabaseConnectionFailed,
    DatabaseQueryFailed,
    DatabaseTransactionFailed,
    DatabaseConstraintViolation,
    
    // 缓存错误 (4000-4999)
    CacheConnectionFailed,
    CacheOperationFailed,
    CacheKeyNotFound,
    
    // 存储错误 (5000-5999)
    StorageConnectionFailed,
    StorageOperationFailed,
    FileNotFound,
    FileTooLarge,
    InvalidFileFormat,
    
    // 模型错误 (6000-6999)
    ModelNotFound,
    ModelLoadFailed,
    ModelInferenceFailed,
    ModelTrainingFailed,
    InvalidModelFormat,
    
    // 配置错误 (7000-7999)
    ConfigurationError,
    ConfigurationNotFound,
    ConfigurationInvalid,
    
    // 网络错误 (8000-8999)
    NetworkError,
    TimeoutError,
    ConnectionRefused,
    
    // 业务逻辑错误 (9000-9999)
    BusinessLogicError,
    ValidationError,
    WorkflowError,
}

impl ErrorCode {
    /// 获取错误代码的数值
    pub fn code(&self) -> u32 {
        match self {
            // 通用错误
            ErrorCode::InternalError => 1000,
            ErrorCode::InvalidInput => 1001,
            ErrorCode::NotFound => 1002,
            ErrorCode::Unauthorized => 1003,
            ErrorCode::Forbidden => 1004,
            ErrorCode::Conflict => 1005,
            ErrorCode::TooManyRequests => 1006,
            ErrorCode::ServiceUnavailable => 1007,
            
            // 认证错误
            ErrorCode::InvalidCredentials => 2000,
            ErrorCode::TokenExpired => 2001,
            ErrorCode::TokenInvalid => 2002,
            ErrorCode::AccountLocked => 2003,
            ErrorCode::TwoFactorRequired => 2004,
            ErrorCode::PasswordTooWeak => 2005,
            
            // 数据库错误
            ErrorCode::DatabaseConnectionFailed => 3000,
            ErrorCode::DatabaseQueryFailed => 3001,
            ErrorCode::DatabaseTransactionFailed => 3002,
            ErrorCode::DatabaseConstraintViolation => 3003,
            
            // 缓存错误
            ErrorCode::CacheConnectionFailed => 4000,
            ErrorCode::CacheOperationFailed => 4001,
            ErrorCode::CacheKeyNotFound => 4002,
            
            // 存储错误
            ErrorCode::StorageConnectionFailed => 5000,
            ErrorCode::StorageOperationFailed => 5001,
            ErrorCode::FileNotFound => 5002,
            ErrorCode::FileTooLarge => 5003,
            ErrorCode::InvalidFileFormat => 5004,
            
            // 模型错误
            ErrorCode::ModelNotFound => 6000,
            ErrorCode::ModelLoadFailed => 6001,
            ErrorCode::ModelInferenceFailed => 6002,
            ErrorCode::ModelTrainingFailed => 6003,
            ErrorCode::InvalidModelFormat => 6004,
            
            // 配置错误
            ErrorCode::ConfigurationError => 7000,
            ErrorCode::ConfigurationNotFound => 7001,
            ErrorCode::ConfigurationInvalid => 7002,
            
            // 网络错误
            ErrorCode::NetworkError => 8000,
            ErrorCode::TimeoutError => 8001,
            ErrorCode::ConnectionRefused => 8002,
            
            // 业务逻辑错误
            ErrorCode::BusinessLogicError => 9000,
            ErrorCode::ValidationError => 9001,
            ErrorCode::WorkflowError => 9002,
        }
    }
    
    /// 获取错误代码的HTTP状态码
    pub fn http_status(&self) -> u16 {
        match self {
            ErrorCode::InternalError | ErrorCode::ServiceUnavailable => 500,
            ErrorCode::InvalidInput | ErrorCode::ValidationError => 400,
            ErrorCode::NotFound | ErrorCode::FileNotFound | ErrorCode::ModelNotFound => 404,
            ErrorCode::Unauthorized | ErrorCode::InvalidCredentials | ErrorCode::TokenExpired | ErrorCode::TokenInvalid => 401,
            ErrorCode::Forbidden | ErrorCode::AccountLocked => 403,
            ErrorCode::Conflict => 409,
            ErrorCode::TooManyRequests => 429,
            _ => 500,
        }
    }
    
    /// 获取错误代码的描述
    pub fn description(&self) -> &'static str {
        match self {
            ErrorCode::InternalError => "内部服务器错误",
            ErrorCode::InvalidInput => "输入参数无效",
            ErrorCode::NotFound => "资源未找到",
            ErrorCode::Unauthorized => "未授权访问",
            ErrorCode::Forbidden => "禁止访问",
            ErrorCode::Conflict => "资源冲突",
            ErrorCode::TooManyRequests => "请求过于频繁",
            ErrorCode::ServiceUnavailable => "服务不可用",
            
            ErrorCode::InvalidCredentials => "凭据无效",
            ErrorCode::TokenExpired => "令牌已过期",
            ErrorCode::TokenInvalid => "令牌无效",
            ErrorCode::AccountLocked => "账户已锁定",
            ErrorCode::TwoFactorRequired => "需要双因素认证",
            ErrorCode::PasswordTooWeak => "密码强度不足",
            
            ErrorCode::DatabaseConnectionFailed => "数据库连接失败",
            ErrorCode::DatabaseQueryFailed => "数据库查询失败",
            ErrorCode::DatabaseTransactionFailed => "数据库事务失败",
            ErrorCode::DatabaseConstraintViolation => "数据库约束违反",
            
            ErrorCode::CacheConnectionFailed => "缓存连接失败",
            ErrorCode::CacheOperationFailed => "缓存操作失败",
            ErrorCode::CacheKeyNotFound => "缓存键未找到",
            
            ErrorCode::StorageConnectionFailed => "存储连接失败",
            ErrorCode::StorageOperationFailed => "存储操作失败",
            ErrorCode::FileNotFound => "文件未找到",
            ErrorCode::FileTooLarge => "文件过大",
            ErrorCode::InvalidFileFormat => "文件格式无效",
            
            ErrorCode::ModelNotFound => "模型未找到",
            ErrorCode::ModelLoadFailed => "模型加载失败",
            ErrorCode::ModelInferenceFailed => "模型推理失败",
            ErrorCode::ModelTrainingFailed => "模型训练失败",
            ErrorCode::InvalidModelFormat => "模型格式无效",
            
            ErrorCode::ConfigurationError => "配置错误",
            ErrorCode::ConfigurationNotFound => "配置未找到",
            ErrorCode::ConfigurationInvalid => "配置无效",
            
            ErrorCode::NetworkError => "网络错误",
            ErrorCode::TimeoutError => "超时错误",
            ErrorCode::ConnectionRefused => "连接被拒绝",
            
            ErrorCode::BusinessLogicError => "业务逻辑错误",
            ErrorCode::ValidationError => "验证错误",
            ErrorCode::WorkflowError => "工作流错误",
        }
    }
}

/// 应用错误结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppError {
    pub code: ErrorCode,
    pub message: String,
    pub details: Option<HashMap<String, serde_json::Value>>,
    pub context: Option<String>,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub request_id: Option<String>,
}

impl AppError {
    /// 创建新的应用错误
    pub fn new(code: ErrorCode, message: String) -> Self {
        Self {
            code,
            message,
            details: None,
            context: None,
            timestamp: chrono::Utc::now(),
            request_id: None,
        }
    }
    
    /// 创建带详细信息的应用错误
    pub fn with_details(code: ErrorCode, message: String, details: HashMap<String, serde_json::Value>) -> Self {
        Self {
            code,
            message,
            details: Some(details),
            context: None,
            timestamp: chrono::Utc::now(),
            request_id: None,
        }
    }
    
    /// 创建带上下文的应用错误
    pub fn with_context(code: ErrorCode, message: String, context: String) -> Self {
        Self {
            code,
            message,
            details: None,
            context: Some(context),
            timestamp: chrono::Utc::now(),
            request_id: None,
        }
    }
    
    /// 设置请求ID
    pub fn with_request_id(mut self, request_id: String) -> Self {
        self.request_id = Some(request_id);
        self
    }
    
    /// 获取HTTP状态码
    pub fn http_status(&self) -> u16 {
        self.code.http_status()
    }
    
    /// 获取错误代码
    pub fn error_code(&self) -> u32 {
        self.code.code()
    }
}

impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {}: {}", self.code.code(), self.code.description(), self.message)
    }
}

impl StdError for AppError {}

/// 错误结果类型别名
pub type AppResult<T> = Result<T, AppError>;

/// 从各种错误类型转换为AppError
impl From<anyhow::Error> for AppError {
    fn from(err: anyhow::Error) -> Self {
        AppError::new(
            ErrorCode::InternalError,
            format!("内部错误: {}", err)
        )
    }
}

impl From<serde_json::Error> for AppError {
    fn from(err: serde_json::Error) -> Self {
        AppError::new(
            ErrorCode::InvalidInput,
            format!("JSON解析错误: {}", err)
        )
    }
}

impl From<std::io::Error> for AppError {
    fn from(err: std::io::Error) -> Self {
        AppError::new(
            ErrorCode::InternalError,
            format!("IO错误: {}", err)
        )
    }
}

impl From<tokio::time::error::Elapsed> for AppError {
    fn from(_err: tokio::time::error::Elapsed) -> Self {
        AppError::new(
            ErrorCode::TimeoutError,
            "操作超时".to_string()
        )
    }
}

// 数据库错误转换（当sqlx可用时）
#[cfg(feature = "database")]
impl From<sqlx::Error> for AppError {
    fn from(err: sqlx::Error) -> Self {
        let (code, message) = match err {
            sqlx::Error::Database(db_err) => {
                if db_err.constraint().is_some() {
                    (ErrorCode::DatabaseConstraintViolation, format!("数据库约束错误: {}", db_err))
                } else {
                    (ErrorCode::DatabaseQueryFailed, format!("数据库查询错误: {}", db_err))
                }
            }
            sqlx::Error::ConnectionFailed(_) => {
                (ErrorCode::DatabaseConnectionFailed, "数据库连接失败".to_string())
            }
            sqlx::Error::RowNotFound => {
                (ErrorCode::NotFound, "数据行未找到".to_string())
            }
            _ => {
                (ErrorCode::DatabaseQueryFailed, format!("数据库错误: {}", err))
            }
        };
        
        AppError::new(code, message)
    }
}

// Redis错误转换（当redis可用时）
#[cfg(feature = "cache")]
impl From<redis::RedisError> for AppError {
    fn from(err: redis::RedisError) -> Self {
        let (code, message) = match err.kind() {
            redis::ErrorKind::IoError => {
                (ErrorCode::CacheConnectionFailed, "缓存连接失败".to_string())
            }
            redis::ErrorKind::TypeError => {
                (ErrorCode::CacheOperationFailed, "缓存操作失败".to_string())
            }
            _ => {
                (ErrorCode::CacheOperationFailed, format!("缓存错误: {}", err))
            }
        };
        
        AppError::new(code, message)
    }
}

/// 错误处理宏
#[macro_export]
macro_rules! app_error {
    ($code:expr, $msg:expr) => {
        AppError::new($code, $msg.to_string())
    };
    ($code:expr, $msg:expr, $details:expr) => {
        AppError::with_details($code, $msg.to_string(), $details)
    };
    ($code:expr, $msg:expr, $context:expr) => {
        AppError::with_context($code, $msg.to_string(), $context.to_string())
    };
}

/// 错误处理宏（带请求ID）
#[macro_export]
macro_rules! app_error_with_id {
    ($code:expr, $msg:expr, $request_id:expr) => {
        AppError::new($code, $msg.to_string()).with_request_id($request_id.to_string())
    };
}

/// 快速创建常见错误
impl AppError {
    /// 创建内部错误
    pub fn internal_error(message: &str) -> Self {
        Self::new(ErrorCode::InternalError, message.to_string())
    }
    
    /// 创建无效输入错误
    pub fn invalid_input(message: &str) -> Self {
        Self::new(ErrorCode::InvalidInput, message.to_string())
    }
    
    /// 创建未找到错误
    pub fn not_found(message: &str) -> Self {
        Self::new(ErrorCode::NotFound, message.to_string())
    }
    
    /// 创建未授权错误
    pub fn unauthorized(message: &str) -> Self {
        Self::new(ErrorCode::Unauthorized, message.to_string())
    }
    
    /// 创建禁止访问错误
    pub fn forbidden(message: &str) -> Self {
        Self::new(ErrorCode::Forbidden, message.to_string())
    }
    
    /// 创建冲突错误
    pub fn conflict(message: &str) -> Self {
        Self::new(ErrorCode::Conflict, message.to_string())
    }
    
    /// 创建验证错误
    pub fn validation_error(message: &str) -> Self {
        Self::new(ErrorCode::ValidationError, message.to_string())
    }
}
