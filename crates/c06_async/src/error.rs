//! C06: Async Error Handling
//!
//! This module provides crate-specific error types and utilities using
//! the trait-based error design from the common crate.

use common::{impl_into_unified_error, ErrorCode};
use std::time::Duration;
use thiserror::Error;

/// C06 crate-specific error type
#[derive(Error, Debug, Clone)]
pub enum AsyncError {
    #[error("cancelled: {0}")]
    Cancelled(String),
    
    #[error("timeout: {0:?}")]
    Timeout(Duration),
    
    #[error("runtime error: {0}")]
    Runtime(String),
    
    #[error("scheduler error: {0}")]
    Scheduler(String),
    
    #[error("stream error: {0}")]
    Stream(String),
    
    #[error("backpressure error: {0}")]
    Backpressure(String),
}

// Async timeout and backpressure errors are typically retryable
impl common::RustLangError for AsyncError {
    fn error_code(&self) -> ErrorCode {
        ErrorCode::Async
    }
    
    fn is_retryable(&self) -> bool {
        matches!(self, AsyncError::Timeout(_) | AsyncError::Backpressure(_))
    }
    
    fn retry_delay(&self) -> Option<Duration> {
        match self {
            AsyncError::Timeout(_) => Some(Duration::from_millis(100)),
            AsyncError::Backpressure(_) => Some(Duration::from_millis(50)),
            _ => None,
        }
    }
    
    fn max_retries(&self) -> Option<u32> {
        if common::RustLangError::is_retryable(self) {
            Some(3)
        } else {
            None
        }
    }
}

impl_into_unified_error!(AsyncError);

/// Re-export common error types for convenience
pub use common::{
    CommonError, DynamicResult, ErrorContext, ErrorRecovery, Result, RustLangError,
    UnifiedError,
};

/// C06 crate's result type
pub type C06Result<T> = Result<T>;

/// Create task cancelled error
pub fn task_cancelled<T: Into<String>>(msg: T) -> AsyncError {
    AsyncError::Cancelled(msg.into())
}

/// Create timeout error
pub fn timeout(duration: Duration) -> AsyncError {
    AsyncError::Timeout(duration)
}

/// Create runtime error
pub fn runtime_error<T: Into<String>>(msg: T) -> AsyncError {
    AsyncError::Runtime(msg.into())
}

/// Create scheduler error
pub fn scheduler_error<T: Into<String>>(msg: T) -> AsyncError {
    AsyncError::Scheduler(msg.into())
}

/// Create stream error
pub fn stream_error<T: Into<String>>(msg: T) -> AsyncError {
    AsyncError::Stream(msg.into())
}

/// Create backpressure error
pub fn backpressure_error<T: Into<String>>(msg: T) -> AsyncError {
    AsyncError::Backpressure(msg.into())
}


#[cfg(test)]
mod tests {
    use super::*;
    use common::RustLangError;

    #[test]
    fn test_error_creation() {
        let err = task_cancelled("test");
        assert!(matches!(err, AsyncError::Cancelled(_)));
        assert_eq!(err.error_code(), ErrorCode::Async);
    }

    #[test]
    fn test_retryable_error() {
        let err = timeout(Duration::from_secs(1));
        assert!(RustLangError::is_retryable(&err));
        assert_eq!(RustLangError::retry_delay(&err), Some(Duration::from_millis(100)));
        
        let err = runtime_error("test");
        assert!(!RustLangError::is_retryable(&err));
    }

    #[test]
    fn test_error_conversion() {
        let err = scheduler_error("test");
        let unified: UnifiedError = err.into();
        assert!(matches!(unified, UnifiedError::Custom(_)));
    }
}
