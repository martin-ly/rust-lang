//! C08: Algorithm Error Handling
//!
//! This module provides crate-specific error types and utilities using
//! the trait-based error design from the common crate.

use common::{impl_into_unified_error, impl_rust_lang_error, ErrorCode};
use thiserror::Error;

/// C08 crate-specific error type
#[derive(Error, Debug, Clone)]
pub enum AlgorithmError {
    #[error("invalid input: {0}")]
    InvalidInput(String),
    
    #[error("not implemented: {0}")]
    NotImplemented(String),
    
    #[error("complexity exceeded: {0}")]
    ComplexityExceeded(String),
    
    #[error("numeric overflow: {0}")]
    NumericOverflow(String),
    
    #[error("convergence failed: {0}")]
    ConvergenceFailed(String),
    
    #[error("data structure error: {0}")]
    DataStructure(String),
}

impl_rust_lang_error!(AlgorithmError, ErrorCode::Algorithm);
impl_into_unified_error!(AlgorithmError);

/// Re-export common error types for convenience
pub use common::{
    CommonError, DynamicResult, ErrorContext, ErrorRecovery, Result, RustLangError,
    UnifiedError,
};

/// C08 crate's result type
pub type C08Result<T> = Result<T>;

/// Create invalid input error
pub fn invalid_input<T: Into<String>>(msg: T) -> AlgorithmError {
    AlgorithmError::InvalidInput(msg.into())
}

/// Create algorithm not implemented error
pub fn algorithm_not_implemented<T: Into<String>>(msg: T) -> AlgorithmError {
    AlgorithmError::NotImplemented(msg.into())
}

/// Create complexity exceeded error
pub fn complexity_exceeded<T: Into<String>>(msg: T) -> AlgorithmError {
    AlgorithmError::ComplexityExceeded(msg.into())
}

/// Create numeric overflow error
pub fn numeric_overflow<T: Into<String>>(msg: T) -> AlgorithmError {
    AlgorithmError::NumericOverflow(msg.into())
}

/// Create convergence failed error
pub fn convergence_failed<T: Into<String>>(msg: T) -> AlgorithmError {
    AlgorithmError::ConvergenceFailed(msg.into())
}

/// Create data structure error
pub fn data_structure_error<T: Into<String>>(msg: T) -> AlgorithmError {
    AlgorithmError::DataStructure(msg.into())
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let err = invalid_input("test");
        assert!(matches!(err, AlgorithmError::InvalidInput(_)));
        assert_eq!(err.error_code(), ErrorCode::Algorithm);
    }

    #[test]
    fn test_error_conversion() {
        let err = complexity_exceeded("test");
        let unified: UnifiedError = err.into();
        assert!(matches!(unified, UnifiedError::Custom(_)));
    }
}
