//! C10: 网络错误处理 (统一版本)

pub use crate::error::{NetworkError as LegacyNetworkError, NetworkResult};
pub use common::{
    NetworkError, RustLangError, Result,
    ErrorContext, ErrorRecovery,
};
use std::time::Duration;

/// C10 crate 的结果类型（统一版本）
pub type C10Result<T> = Result<T>;

/// 创建连接错误
pub fn connection_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Network(NetworkError::Connection(msg.into()))
}

/// 创建协议错误
pub fn protocol_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Network(NetworkError::Protocol(msg.into()))
}

/// 创建网络超时错误
pub fn network_timeout(duration: Duration) -> RustLangError {
    RustLangError::Network(NetworkError::Timeout(duration))
}

/// 创建 DNS 错误
pub fn dns_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Network(NetworkError::Dns(msg.into()))
}

/// 创建 TLS 错误
pub fn tls_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Network(NetworkError::Tls(msg.into()))
}

/// 创建 HTTP 错误
pub fn http_error(status: u16, message: impl Into<String>) -> RustLangError {
    RustLangError::Network(NetworkError::Http {
        status,
        message: message.into(),
    })
}

/// 创建 WebSocket 错误
pub fn websocket_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Network(NetworkError::WebSocket(msg.into()))
}

/// 创建认证错误
pub fn authentication_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Network(NetworkError::Authentication(msg.into()))
}

/// 创建缓冲区错误
pub fn buffer_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Network(NetworkError::Buffer(msg.into()))
}
