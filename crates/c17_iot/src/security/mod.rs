//! 安全模块
//! 
//! 提供IoT设备安全功能，包括认证、加密、访问控制等

pub mod authentication;

pub use authentication::{DeviceAuthenticator, AuthToken, DeviceCredentials};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum SecurityError {
    #[error("认证失败: {0}")]
    AuthenticationFailed(String),
    #[error("授权失败: {0}")]
    AuthorizationFailed(String),
    #[error("证书错误: {0}")]
    CertificateError(String),
    #[error("密钥管理错误: {0}")]
    KeyManagementError(String),
    #[error("会话错误: {0}")]
    SessionError(String),
    #[error("序列化错误: {0}")]
    SerializationError(String),
    #[error("反序列化错误: {0}")]
    DeserializationError(String),
    #[error("无效令牌")]
    InvalidToken,
}
