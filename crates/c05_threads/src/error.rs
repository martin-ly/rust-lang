//! C05: Threading and Concurrency Error Handling
//!
//! This module provides crate-specific error types and utilities using
//! the trait-based error design from the common crate.

use common::{impl_into_unified_error, ErrorCode};
use std::time::Duration;
use thiserror::Error;

/// C05 crate-specific error type
#[derive(Error, Debug, Clone)]
pub enum ThreadError {
    #[error("creation failed: {0}")]
    CreationFailed(String),
    
    #[error("panicked: {0}")]
    Panicked(String),
    
    #[error("deadlock detected: {0}")]
    Deadlock(String),
    
    #[error("data race: {0}")]
    DataRace(String),
    
    #[error("lock acquisition failed: {0}")]
    LockAcquisition(String),
    
    #[error("send error: {0}")]
    SendError(String),
    
    #[error("receive error: {0}")]
    ReceiveError(String),
    
    #[error("lock-free error: {0}")]
    LockFree(String),
}

// Thread errors involving lock acquisition or send failures may be retryable
impl common::RustLangError for ThreadError {
    fn error_code(&self) -> ErrorCode {
        ErrorCode::Thread
    }
    
    fn is_retryable(&self) -> bool {
        matches!(self, ThreadError::LockAcquisition(_) | ThreadError::SendError(_))
    }
    
    fn retry_delay(&self) -> Option<Duration> {
        if RustLangError::is_retryable(self) {
            Some(Duration::from_millis(10))
        } else {
            None
        }
    }
    
    fn max_retries(&self) -> Option<u32> {
        if RustLangError::is_retryable(self) {
            Some(5)
        } else {
            None
        }
    }
}

impl_into_unified_error!(ThreadError);

/// Re-export common error types for convenience
pub use common::{
    CommonError, DynamicResult, ErrorContext, ErrorRecovery, Result, RustLangError,
    UnifiedError,
};

/// C05 crate's result type
pub type C05Result<T> = Result<T>;

/// Create thread creation failed error
pub fn thread_creation_failed<T: Into<String>>(msg: T) -> ThreadError {
    ThreadError::CreationFailed(msg.into())
}

/// Create thread panic error
pub fn thread_panicked<T: Into<String>>(msg: T) -> ThreadError {
    ThreadError::Panicked(msg.into())
}

/// Create deadlock detected error
pub fn deadlock_detected<T: Into<String>>(msg: T) -> ThreadError {
    ThreadError::Deadlock(msg.into())
}

/// Create data race error
pub fn data_race<T: Into<String>>(msg: T) -> ThreadError {
    ThreadError::DataRace(msg.into())
}

/// Create lock acquisition failed error
pub fn lock_acquisition_failed<T: Into<String>>(msg: T) -> ThreadError {
    ThreadError::LockAcquisition(msg.into())
}

/// Create send error
pub fn send_error<T: Into<String>>(msg: T) -> ThreadError {
    ThreadError::SendError(msg.into())
}

/// Create receive error
pub fn receive_error<T: Into<String>>(msg: T) -> ThreadError {
    ThreadError::ReceiveError(msg.into())
}

/// Create lock-free error
pub fn lock_free_error<T: Into<String>>(msg: T) -> ThreadError {
    ThreadError::LockFree(msg.into())
}


#[cfg(test)]
mod tests {
    use super::*;
    use common::RustLangError;

    #[test]
    fn test_error_creation() {
        let err = thread_creation_failed("test");
        assert!(matches!(err, ThreadError::CreationFailed(_)));
        assert_eq!(err.error_code(), ErrorCode::Thread);
    }

    #[test]
    fn test_retryable_error() {
        let err = lock_acquisition_failed("test");
        assert!(common::RustLangError::is_retryable(&err));
        assert_eq!(common::RustLangError::retry_delay(&err), Some(Duration::from_millis(10)));
        
        let err = thread_panicked("test");
        assert!(!common::RustLangError::is_retryable(&err));
    }

    #[test]
    fn test_error_conversion() {
        let err = deadlock_detected("test");
        let unified: UnifiedError = err.into();
        assert!(matches!(unified, UnifiedError::Custom(_)));
    }
}
