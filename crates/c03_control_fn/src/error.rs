//! C03: Control Flow and Functions Error Handling
//!
//! This module provides crate-specific error types and utilities using
//! the trait-based error design from the common crate.

use common::{impl_into_unified_error, impl_rust_lang_error, ErrorCode};
use thiserror::Error;

/// C03 crate-specific error type
#[derive(Error, Debug, Clone)]
pub enum ControlFlowError {
    #[error("non-exhaustive match: {0}")]
    NonExhaustiveMatch(String),
    
    #[error("stack overflow: {0}")]
    StackOverflow(String),
    
    #[error("interrupted: {0}")]
    Interrupted(String),
    
    #[error("closure capture error: {0}")]
    ClosureCapture(String),
    
    #[error("generator error: {0}")]
    Generator(String),
}

impl_rust_lang_error!(ControlFlowError, ErrorCode::ControlFlow);
impl_into_unified_error!(ControlFlowError);

/// Re-export common error types for convenience
pub use common::{
    CommonError, DynamicResult, ErrorContext, ErrorRecovery, Result, RustLangError,
    UnifiedError,
};

/// C03 crate's result type
pub type C03Result<T> = Result<T>;

/// Create non-exhaustive match error
pub fn non_exhaustive_match<T: Into<String>>(msg: T) -> ControlFlowError {
    ControlFlowError::NonExhaustiveMatch(msg.into())
}

/// Create stack overflow error
pub fn stack_overflow<T: Into<String>>(msg: T) -> ControlFlowError {
    ControlFlowError::StackOverflow(msg.into())
}

/// Create control flow interrupted error
pub fn control_flow_interrupted<T: Into<String>>(msg: T) -> ControlFlowError {
    ControlFlowError::Interrupted(msg.into())
}

/// Create closure capture error
pub fn closure_capture<T: Into<String>>(msg: T) -> ControlFlowError {
    ControlFlowError::ClosureCapture(msg.into())
}

/// Create generator error
pub fn generator_error<T: Into<String>>(msg: T) -> ControlFlowError {
    ControlFlowError::Generator(msg.into())
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let err = non_exhaustive_match("test");
        assert!(matches!(err, ControlFlowError::NonExhaustiveMatch(_)));
        assert_eq!(err.error_code(), ErrorCode::ControlFlow);
    }

    #[test]
    fn test_error_conversion() {
        let err = stack_overflow("test");
        let unified: UnifiedError = err.into();
        assert!(matches!(unified, UnifiedError::Custom(_)));
    }
}
