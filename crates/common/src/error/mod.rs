//! 公共错误类型模块
//! 
//! 提供统一的错误处理类型和 Result 别名，用于整个 Rust 学习项目。

#![cfg(feature = "error-trait")]

use thiserror::Error;

/// 通用错误类型
#[derive(Error, Debug, Clone)]
pub enum CommonError {
    /// I/O 错误
    #[error("I/O error: {0}")]
    Io(String),
    
    /// 解析错误
    #[error("Parse error: {0}")]
    Parse(String),
    
    /// 验证错误
    #[error("Validation error: {0}")]
    Validation(String),
    
    /// 未找到
    #[error("Not found: {0}")]
    NotFound(String),
    
    /// 超时
    #[error("Timeout: {0}")]
    Timeout(String),
    
    /// 取消
    #[error("Operation cancelled")]
    Cancelled,
    
    /// 无效状态
    #[error("Invalid state: {0}")]
    InvalidState(String),
    
    /// 配置错误
    #[error("Configuration error: {0}")]
    Config(String),
    
    /// 网络错误
    #[error("Network error: {0}")]
    Network(String),
    
    /// 序列化错误
    #[cfg(feature = "serde")]
    #[error("Serialization error: {0}")]
    Serialization(String),
    
    /// 其他错误
    #[error("Other error: {0}")]
    Other(String),
}

/// 通用 Result 类型别名
pub type Result<T> = std::result::Result<T, CommonError>;

/// 项目错误类型别名（向后兼容）
pub use CommonError as RustLangError;

/// 可重试错误 trait
pub trait Retryable {
    /// 判断是否可重试
    fn is_retryable(&self) -> bool;
    
    /// 获取重试延迟（毫秒）
    fn retry_delay_ms(&self) -> u64;
}

impl Retryable for CommonError {
    fn is_retryable(&self) -> bool {
        matches!(
            self,
            CommonError::Io(_) | 
            CommonError::Network(_) | 
            CommonError::Timeout(_) |
            CommonError::Cancelled
        )
    }
    
    fn retry_delay_ms(&self) -> u64 {
        match self {
            CommonError::Timeout(_) => 100,
            CommonError::Network(_) => 500,
            CommonError::Io(_) => 200,
            _ => 1000,
        }
    }
}

impl From<std::io::Error> for CommonError {
    fn from(e: std::io::Error) -> Self {
        CommonError::Io(e.to_string())
    }
}

#[cfg(feature = "serde")]
impl From<serde_json::Error> for CommonError {
    fn from(e: serde_json::Error) -> Self {
        CommonError::Serialization(e.to_string())
    }
}

/// 错误转换辅助函数
pub fn to_common_error<E: std::fmt::Display>(e: E) -> CommonError {
    CommonError::Other(e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_error_display() {
        let err = CommonError::NotFound("test".to_string());
        assert!(err.to_string().contains("test"));
    }
    
    #[test]
    fn test_retryable() {
        let err = CommonError::Network("connection failed".to_string());
        assert!(err.is_retryable());
        assert_eq!(err.retry_delay_ms(), 500);
        
        let err = CommonError::Validation("invalid".to_string());
        assert!(!err.is_retryable());
    }
}
