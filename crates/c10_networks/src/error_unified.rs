//! C10: Network Error Handling (Unified Version)
//!
//! This module provides crate-specific error types and utilities using
//! the trait-based error design from the common crate.

use common::{impl_into_unified_error, ErrorCode};
use std::time::Duration;
use thiserror::Error;

/// C10 crate-specific error type
#[derive(Error, Debug, Clone)]
pub enum NetworkError {
    #[error("connection error: {0}")]
    Connection(String),
    
    #[error("protocol error: {0}")]
    Protocol(String),
    
    #[error("timeout: {0:?}")]
    Timeout(Duration),
    
    #[error("DNS error: {0}")]
    Dns(String),
    
    #[error("TLS error: {0}")]
    Tls(String),
    
    #[error("HTTP error: status={status}, message={message}")]
    Http { status: u16, message: String },
    
    #[error("WebSocket error: {0}")]
    WebSocket(String),
    
    #[error("authentication error: {0}")]
    Authentication(String),
    
    #[error("buffer error: {0}")]
    Buffer(String),
}

// Network timeout and connection errors are typically retryable
impl common::RustLangError for NetworkError {
    fn error_code(&self) -> ErrorCode {
        ErrorCode::Network
    }
    
    fn is_retryable(&self) -> bool {
        matches!(self, NetworkError::Timeout(_) | NetworkError::Connection(_))
    }
    
    fn retry_delay(&self) -> Option<Duration> {
        match self {
            NetworkError::Timeout(_) => Some(Duration::from_millis(100)),
            NetworkError::Connection(_) => Some(Duration::from_millis(500)),
            _ => None,
        }
    }
    
    fn max_retries(&self) -> Option<u32> {
        match self {
            NetworkError::Timeout(_) => Some(3),
            NetworkError::Connection(_) => Some(5),
            _ => None,
        }
    }
}

impl_into_unified_error!(NetworkError);

/// Re-export common error types for convenience
pub use common::{
    CommonError, DynamicResult, ErrorContext, ErrorRecovery, Result, RustLangError,
    UnifiedError,
};

/// C10 crate's result type (Unified version)
pub type C10Result<T> = Result<T>;

/// Create connection error
pub fn connection_error<T: Into<String>>(msg: T) -> NetworkError {
    NetworkError::Connection(msg.into())
}

/// Create protocol error
pub fn protocol_error<T: Into<String>>(msg: T) -> NetworkError {
    NetworkError::Protocol(msg.into())
}

/// Create network timeout error
pub fn network_timeout(duration: Duration) -> NetworkError {
    NetworkError::Timeout(duration)
}

/// Create DNS error
pub fn dns_error<T: Into<String>>(msg: T) -> NetworkError {
    NetworkError::Dns(msg.into())
}

/// Create TLS error
pub fn tls_error<T: Into<String>>(msg: T) -> NetworkError {
    NetworkError::Tls(msg.into())
}

/// Create HTTP error
pub fn http_error(status: u16, message: impl Into<String>) -> NetworkError {
    NetworkError::Http {
        status,
        message: message.into(),
    }
}

/// Create WebSocket error
pub fn websocket_error<T: Into<String>>(msg: T) -> NetworkError {
    NetworkError::WebSocket(msg.into())
}

/// Create authentication error
pub fn authentication_error<T: Into<String>>(msg: T) -> NetworkError {
    NetworkError::Authentication(msg.into())
}

/// Create buffer error
pub fn buffer_error<T: Into<String>>(msg: T) -> NetworkError {
    NetworkError::Buffer(msg.into())
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let err = connection_error("test");
        assert!(matches!(err, NetworkError::Connection(_)));
        assert_eq!(err.error_code(), ErrorCode::Network);
    }

    #[test]
    fn test_retryable_error() {
        let err = network_timeout(Duration::from_secs(1));
        assert!(err.is_retryable());
        assert_eq!(err.retry_delay(), Some(Duration::from_millis(100)));
        assert_eq!(err.max_retries(), Some(3));
        
        let err = tls_error("test");
        assert!(!err.is_retryable());
    }

    #[test]
    fn test_http_error() {
        let err = http_error(404, "not found");
        assert!(matches!(err, NetworkError::Http { status: 404, .. }));
    }
}
