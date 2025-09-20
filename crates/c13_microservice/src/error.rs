//! 错误处理模块
//!
//! 提供统一的错误类型和处理机制，支持多种错误源和链式错误处理。

use std::fmt;
use thiserror::Error;

/// 微服务框架的统一错误类型
#[derive(Error, Debug)]
pub enum Error {
    /// 配置错误
    #[error("配置错误: {0}")]
    Config(String),

    /// 数据库错误
    #[error("数据库错误: {0}")]
    Database(String),

    /// 序列化/反序列化错误
    #[error("序列化错误: {0}")]
    Serialization(#[from] serde_json::Error),

    /// HTTP错误
    #[error("HTTP错误: {0}")]
    Http(#[from] reqwest::Error),

    /// gRPC错误
    #[error("gRPC错误: {0}")]
    Grpc(#[from] tonic::Status),

    /// 认证错误
    #[error("认证错误: {0}")]
    Auth(String),

    /// 服务发现错误
    #[error("服务发现错误: {0}")]
    ServiceDiscovery(String),

    /// 负载均衡错误
    #[error("负载均衡错误: {0}")]
    LoadBalancer(String),

    /// 熔断器错误
    #[error("熔断器错误: {0}")]
    CircuitBreaker(String),

    /// 消息队列错误
    #[error("消息队列错误: {0}")]
    Messaging(String),

    /// Kubernetes错误
    #[error("Kubernetes错误: {0}")]
    Kubernetes(String),

    /// 通用IO错误
    #[error("IO错误: {0}")]
    Io(#[from] std::io::Error),

    /// 其他错误
    #[error("未知错误: {0}")]
    Other(#[from] anyhow::Error),
}

/// 结果类型别名
pub type Result<T> = std::result::Result<T, Error>;

impl Error {
    /// 创建配置错误
    pub fn config(msg: impl Into<String>) -> Self {
        Self::Config(msg.into())
    }

    /// 创建认证错误
    pub fn auth(msg: impl Into<String>) -> Self {
        Self::Auth(msg.into())
    }

    /// 创建服务发现错误
    pub fn service_discovery(msg: impl Into<String>) -> Self {
        Self::ServiceDiscovery(msg.into())
    }

    /// 创建负载均衡错误
    pub fn load_balancer(msg: impl Into<String>) -> Self {
        Self::LoadBalancer(msg.into())
    }

    /// 创建熔断器错误
    pub fn circuit_breaker(msg: impl Into<String>) -> Self {
        Self::CircuitBreaker(msg.into())
    }

    /// 创建消息队列错误
    pub fn messaging(msg: impl Into<String>) -> Self {
        Self::Messaging(msg.into())
    }

    /// 创建Kubernetes错误
    pub fn kubernetes(msg: impl Into<String>) -> Self {
        Self::Kubernetes(msg.into())
    }
}

/// 错误上下文扩展
pub trait ErrorContext<T> {
    /// 为错误添加上下文信息
    fn with_context<F>(self, f: F) -> Result<T>
    where
        F: FnOnce() -> String;
}

impl<T, E> ErrorContext<T> for std::result::Result<T, E>
where
    E: Into<Error>,
{
    fn with_context<F>(self, _f: F) -> Result<T>
    where
        F: FnOnce() -> String,
    {
        self.map_err(|e| {
            
            // 这里可以添加上下文信息到错误中
            e.into()
        })
    }
}

/// 错误码枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorCode {
    /// 配置错误
    ConfigError = 1000,
    /// 数据库错误
    DatabaseError = 2000,
    /// 认证错误
    AuthError = 3000,
    /// 服务发现错误
    ServiceDiscoveryError = 4000,
    /// 负载均衡错误
    LoadBalancerError = 5000,
    /// 熔断器错误
    CircuitBreakerError = 6000,
    /// 消息队列错误
    MessagingError = 7000,
    /// Kubernetes错误
    KubernetesError = 8000,
    /// 通用错误
    GenericError = 9000,
}

impl ErrorCode {
    /// 获取错误码的数值
    pub fn code(&self) -> u32 {
        *self as u32
    }

    /// 获取错误码的描述
    pub fn description(&self) -> &'static str {
        match self {
            ErrorCode::ConfigError => "配置错误",
            ErrorCode::DatabaseError => "数据库错误",
            ErrorCode::AuthError => "认证错误",
            ErrorCode::ServiceDiscoveryError => "服务发现错误",
            ErrorCode::LoadBalancerError => "负载均衡错误",
            ErrorCode::CircuitBreakerError => "熔断器错误",
            ErrorCode::MessagingError => "消息队列错误",
            ErrorCode::KubernetesError => "Kubernetes错误",
            ErrorCode::GenericError => "通用错误",
        }
    }
}

impl fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.code(), self.description())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let config_error = Error::config("测试配置错误");
        assert!(matches!(config_error, Error::Config(_)));

        let auth_error = Error::auth("测试认证错误");
        assert!(matches!(auth_error, Error::Auth(_)));
    }

    #[test]
    fn test_error_code() {
        let code = ErrorCode::ConfigError;
        assert_eq!(code.code(), 1000);
        assert_eq!(code.description(), "配置错误");
    }
}
