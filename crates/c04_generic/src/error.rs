//! C04: Generics Error Handling
//!
//! This module provides crate-specific error types and utilities using
//! the trait-based error design from the common crate.

use common::{impl_into_unified_error, impl_rust_lang_error, ErrorCode};
use thiserror::Error;

/// C04 crate-specific error type
#[derive(Error, Debug, Clone)]
pub enum GenericError {
    #[error("type parameter mismatch: {0}")]
    TypeParameterMismatch(String),
    
    #[error("associated type error: {0}")]
    AssociatedType(String),
    
    #[error("constraint conflict: {0}")]
    ConstraintConflict(String),
    
    #[error("GAT error: {0}")]
    GatError(String),
    
    #[error("HRTB error: {0}")]
    HrtbError(String),
}

impl_rust_lang_error!(GenericError, ErrorCode::Generic);
impl_into_unified_error!(GenericError);

/// Re-export common error types for convenience
pub use common::{
    CommonError, DynamicResult, ErrorContext, ErrorRecovery, Result, RustLangError,
    UnifiedError,
};

/// C04 crate's result type
pub type C04Result<T> = Result<T>;

/// Create type parameter mismatch error
pub fn type_parameter_mismatch<T: Into<String>>(msg: T) -> GenericError {
    GenericError::TypeParameterMismatch(msg.into())
}

/// Create associated type error
pub fn associated_type_error<T: Into<String>>(msg: T) -> GenericError {
    GenericError::AssociatedType(msg.into())
}

/// Create generic constraint conflict error
pub fn constraint_conflict<T: Into<String>>(msg: T) -> GenericError {
    GenericError::ConstraintConflict(msg.into())
}

/// Create GAT error
pub fn gat_error<T: Into<String>>(msg: T) -> GenericError {
    GenericError::GatError(msg.into())
}

/// Create HRTB error
pub fn hrtb_error<T: Into<String>>(msg: T) -> GenericError {
    GenericError::HrtbError(msg.into())
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let err = type_parameter_mismatch("test");
        assert!(matches!(err, GenericError::TypeParameterMismatch(_)));
        assert_eq!(err.error_code(), ErrorCode::Generic);
    }

    #[test]
    fn test_error_conversion() {
        let err = constraint_conflict("test");
        let unified: UnifiedError = err.into();
        assert!(matches!(unified, UnifiedError::Custom(_)));
    }
}
