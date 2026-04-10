//! C07: Process Error Handling (Unified Version)
//!
//! This module provides crate-specific error types and utilities using
//! the trait-based error design from the common crate.

use common::{impl_into_unified_error, impl_rust_lang_error, ErrorCode, UnifiedError};
use std::time::Duration;
use thiserror::Error;

/// C07 crate-specific error type
#[derive(Error, Debug, Clone)]
pub enum ProcessError {
    #[error("creation failed: {0}")]
    CreationFailed(String),
    
    #[error("start failed: {0}")]
    StartFailed(String),
    
    #[error("wait failed: {0}")]
    WaitFailed(String),
    
    #[error("termination failed: {0}")]
    TerminationFailed(String),
    
    #[error("not found: {0}")]
    NotFound(u32),
    
    #[error("permission denied: {0}")]
    PermissionDenied(String),
    
    #[error("already terminated")]
    AlreadyTerminated,
    
    #[error("IPC error: {0}")]
    Ipc(String),
    
    #[error("signal error: {0}")]
    Signal(String),
    
    #[error("{0}")]
    Other(String),
}

// Process start and IPC errors may be retryable
impl common::RustLangError for ProcessError {
    fn error_code(&self) -> ErrorCode {
        ErrorCode::Process
    }
    
    fn is_retryable(&self) -> bool {
        matches!(self, ProcessError::StartFailed(_) | ProcessError::Ipc(_))
    }
    
    fn retry_delay(&self) -> Option<Duration> {
        if self.is_retryable() {
            Some(Duration::from_millis(200))
        } else {
            None
        }
    }
    
    fn max_retries(&self) -> Option<u32> {
        if self.is_retryable() {
            Some(3)
        } else {
            None
        }
    }
}

impl_into_unified_error!(ProcessError);

/// Re-export common error types for convenience
pub use common::{
    CommonError, DynamicResult, ErrorContext, ErrorRecovery, Result, RustLangError,
    UnifiedError,
};

/// C07 crate's result type (Unified version)
pub type C07Result<T> = Result<T>;

/// Create process error from existing error
pub fn process_error_from_existing<T: std::fmt::Display>(e: T) -> ProcessError {
    ProcessError::Other(e.to_string())
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let err = ProcessError::CreationFailed("test".to_string());
        assert_eq!(err.error_code(), ErrorCode::Process);
        assert!(!err.is_retryable());
    }

    #[test]
    fn test_retryable_error() {
        let err = ProcessError::StartFailed("test".to_string());
        assert!(err.is_retryable());
        assert_eq!(err.retry_delay(), Some(Duration::from_millis(200)));
        
        let err = ProcessError::AlreadyTerminated;
        assert!(!err.is_retryable());
    }

    #[test]
    fn test_error_conversion() {
        let err = ProcessError::PermissionDenied("test".to_string());
        let unified: UnifiedError = err.into();
        assert!(matches!(unified, UnifiedError::Custom(_)));
    }
}
