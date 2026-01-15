//! 网络编程错误处理模块
//!
//! 本模块定义了网络编程中使用的各种错误类型，
//! 利用 Rust 1.92.0 的新特性提供更好的错误处理体验。

use std::time::Duration;
use thiserror::Error;

/// 网络编程中的主要错误类型
#[derive(Error, Debug)]
pub enum NetworkError {
    /// IO 错误
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    /// 协议解析错误
    #[error("Protocol error: {0}")]
    Protocol(String),

    /// 超时错误
    #[error("Timeout after {0:?}")]
    Timeout(Duration),

    /// 连接错误
    #[error("Connection error: {0}")]
    Connection(String),

    /// 认证错误
    #[error("Authentication error: {0}")]
    Authentication(String),

    /// 加密错误
    #[error("Encryption error: {0}")]
    Encryption(String),

    /// 配置错误
    #[error("Configuration error: {0}")]
    Configuration(String),

    /// 其他错误
    #[error("Other error: {0}")]
    Other(String),

    /// 无效状态错误
    #[error("Invalid state: {0}")]
    InvalidState(String),

    /// 缓冲区错误
    #[error("Buffer error: {0}")]
    Buffer(String),

    /// 序列化/反序列化错误
    #[error("Serialization error: {0}")]
    Serialization(#[from] serde_json::Error),

    /// URL 解析错误
    #[error("URL parsing error: {0}")]
    Url(#[from] url::ParseError),
}

/// 网络结果类型别名
pub type NetworkResult<T> = Result<T, NetworkError>;

/// 协议特定的错误类型
#[derive(Error, Debug)]
pub enum ProtocolError {
    /// HTTP 协议错误
    #[error("HTTP error: {status} - {message}")]
    Http { status: u16, message: String },

    /// WebSocket 协议错误
    #[error("WebSocket error: {0}")]
    WebSocket(String),

    /// TCP 协议错误
    #[error("TCP error: {0}")]
    Tcp(String),

    /// UDP 协议错误
    #[error("UDP error: {0}")]
    Udp(String),

    /// DNS 协议错误
    #[error("DNS error: {0}")]
    Dns(String),
}

/// 性能相关错误
#[derive(Error, Debug)]
pub enum PerformanceError {
    /// 连接池耗尽
    #[error("Connection pool exhausted")]
    PoolExhausted,

    /// 速率限制
    #[error("Rate limit exceeded: {limit} requests per {period:?}")]
    RateLimit { limit: u64, period: Duration },

    /// 内存不足
    #[error("Insufficient memory: required {required}, available {available}")]
    InsufficientMemory { required: usize, available: usize },

    /// 负载过高
    #[error("High load: {load}%")]
    HighLoad { load: f64 },
}

/// 安全相关错误
#[derive(Error, Debug)]
pub enum SecurityError {
    /// 证书验证失败
    #[error("Certificate verification failed: {0}")]
    CertificateVerification(String),

    /// 签名验证失败
    #[error("Signature verification failed: {0}")]
    SignatureVerification(String),

    /// 权限不足
    #[error("Insufficient permissions: {0}")]
    InsufficientPermissions(String),

    /// 恶意请求
    #[error("Malicious request detected: {0}")]
    MaliciousRequest(String),
}

/// 错误恢复策略
pub trait ErrorRecovery {
    /// 是否可以重试
    fn is_retryable(&self) -> bool;

    /// 获取重试延迟
    fn retry_delay(&self) -> Option<Duration>;

    /// 获取最大重试次数
    fn max_retries(&self) -> Option<u32>;
}

impl ErrorRecovery for NetworkError {
    fn is_retryable(&self) -> bool {
        match self {
            NetworkError::Timeout(_) => true,
            NetworkError::Connection(_) => true,
            NetworkError::Io(io_err) => {
                matches!(
                    io_err.kind(),
                    std::io::ErrorKind::TimedOut
                        | std::io::ErrorKind::ConnectionRefused
                        | std::io::ErrorKind::ConnectionReset
                        | std::io::ErrorKind::ConnectionAborted
                )
            }
            _ => false,
        }
    }

    fn retry_delay(&self) -> Option<Duration> {
        match self {
            NetworkError::Timeout(_) => Some(Duration::from_millis(100)),
            NetworkError::Connection(_) => Some(Duration::from_millis(500)),
            NetworkError::Io(_) => Some(Duration::from_millis(200)),
            _ => None,
        }
    }

    fn max_retries(&self) -> Option<u32> {
        match self {
            NetworkError::Timeout(_) => Some(3),
            NetworkError::Connection(_) => Some(5),
            NetworkError::Io(_) => Some(3),
            _ => None,
        }
    }
}

/// 错误上下文扩展
pub trait ErrorContext<T> {
    /// 添加上下文信息
    fn with_context<F>(self, f: F) -> Result<T, NetworkError>
    where
        F: FnOnce() -> String;
}

impl<T, E> ErrorContext<T> for Result<T, E>
where
    E: Into<NetworkError>,
{
    fn with_context<F>(self, _f: F) -> Result<T, NetworkError>
    where
        F: FnOnce() -> String,
    {
        self.map_err(|e| {
            let network_err: NetworkError = e.into();
            // 这里可以添加上下文信息的逻辑
            network_err
        })
    }
}

/// 错误统计
#[derive(Debug, Default)]
pub struct ErrorStats {
    pub total_errors: u64,
    pub io_errors: u64,
    pub protocol_errors: u64,
    pub timeout_errors: u64,
    pub connection_errors: u64,
}

impl ErrorStats {
    /// 记录错误
    pub fn record_error(&mut self, error: &NetworkError) {
        self.total_errors += 1;
        match error {
            NetworkError::Io(_) => self.io_errors += 1,
            NetworkError::Protocol(_) => self.protocol_errors += 1,
            NetworkError::Timeout(_) => self.timeout_errors += 1,
            NetworkError::Connection(_) => self.connection_errors += 1,
            _ => {}
        }
    }

    /// 获取错误率
    pub fn error_rate(&self, total_operations: u64) -> f64 {
        if total_operations == 0 {
            0.0
        } else {
            self.total_errors as f64 / total_operations as f64
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Error as IoError, ErrorKind};

    #[test]
    fn test_error_recovery() {
        let timeout_error = NetworkError::Timeout(Duration::from_secs(5));
        assert!(timeout_error.is_retryable());
        assert_eq!(
            timeout_error.retry_delay(),
            Some(Duration::from_millis(100))
        );
        assert_eq!(timeout_error.max_retries(), Some(3));
    }

    #[test]
    fn test_error_stats() {
        let mut stats = ErrorStats::default();
        let io_error = NetworkError::Io(IoError::new(ErrorKind::TimedOut, "test"));

        stats.record_error(&io_error);
        assert_eq!(stats.total_errors, 1);
        assert_eq!(stats.io_errors, 1);
        assert_eq!(stats.error_rate(10), 0.1);
    }

    #[test]
    fn test_protocol_error() {
        let http_error = ProtocolError::Http {
            status: 404,
            message: "Not Found".to_string(),
        };

        assert_eq!(format!("{}", http_error), "HTTP error: 404 - Not Found");
    }
}
