//! C02: Type System Error Handling
//!
//! This module provides crate-specific error types and utilities using
//! the trait-based error design from the common crate.

use common::{impl_into_unified_error, impl_rust_lang_error, ErrorCode};
use thiserror::Error;

/// C02 crate-specific error type
#[derive(Error, Debug, Clone)]
pub enum TypeError {
    #[error("type mismatch: expected {expected}, found {found}")]
    TypeMismatch { expected: String, found: String },
    
    #[error("inference failed: {0}")]
    InferenceFailed(String),
    
    #[error("trait bound not satisfied: {0}")]
    TraitBoundNotSatisfied(String),
    
    #[error("conversion error: {0}")]
    Conversion(String),
    
    #[error("null pointer: {0}")]
    NullPointer(String),
    
    #[error("variance error: {0}")]
    Variance(String),
}

impl_rust_lang_error!(TypeError, ErrorCode::Type);
impl_into_unified_error!(TypeError);

/// Re-export common error types for convenience
pub use common::{
    CommonError, DynamicResult, ErrorContext, ErrorRecovery, Result, RustLangError,
    UnifiedError,
};

/// C02 crate's result type
pub type C02Result<T> = Result<T>;

/// Create type mismatch error
pub fn type_mismatch(expected: impl Into<String>, found: impl Into<String>) -> TypeError {
    TypeError::TypeMismatch {
        expected: expected.into(),
        found: found.into(),
    }
}

/// Create type inference failed error
pub fn inference_failed<T: Into<String>>(msg: T) -> TypeError {
    TypeError::InferenceFailed(msg.into())
}

/// Create trait bound not satisfied error
pub fn trait_bound_not_satisfied<T: Into<String>>(msg: T) -> TypeError {
    TypeError::TraitBoundNotSatisfied(msg.into())
}

/// Create type conversion error
pub fn type_conversion<T: Into<String>>(msg: T) -> TypeError {
    TypeError::Conversion(msg.into())
}

/// Create null pointer error
pub fn null_pointer<T: Into<String>>(msg: T) -> TypeError {
    TypeError::NullPointer(msg.into())
}

/// Create variance error
pub fn variance_error<T: Into<String>>(msg: T) -> TypeError {
    TypeError::Variance(msg.into())
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let err = type_mismatch("i32", "String");
        assert!(matches!(err, TypeError::TypeMismatch { .. }));
        assert_eq!(err.error_code(), ErrorCode::Type);
    }

    #[test]
    fn test_error_conversion() {
        let err = inference_failed("test");
        let unified: UnifiedError = err.into();
        assert!(matches!(unified, UnifiedError::Custom(_)));
    }
}
