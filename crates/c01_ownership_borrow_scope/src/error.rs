//! C01: Ownership, Borrowing, and Scope Error Handling
//!
//! This module provides crate-specific error types and utilities using
//! the trait-based error design from the common crate.

use common::{impl_into_unified_error, impl_rust_lang_error, ErrorCode};
use thiserror::Error;

/// C01 crate-specific error type
#[derive(Error, Debug, Clone)]
pub enum OwnershipError {
    #[error("borrow conflict: {0}")]
    BorrowConflict(String),
    
    #[error("lifetime error: {0}")]
    Lifetime(String),
    
    #[error("move error: {0}")]
    MoveError(String),
    
    #[error("mutable borrow conflict: {0}")]
    MutableBorrowConflict(String),
    
    #[error("interior mutability error: {0}")]
    InteriorMutability(String),
    
    #[error("memory safety error: {0}")]
    MemorySafety(String),
}

impl_rust_lang_error!(OwnershipError, ErrorCode::Ownership);
impl_into_unified_error!(OwnershipError);

/// Re-export common error types for convenience
pub use common::{
    CommonError, DynamicResult, ErrorContext, ErrorRecovery, Result, RustLangError,
    UnifiedError,
};

/// C01 crate's result type
pub type C01Result<T> = Result<T>;

/// Create borrow conflict error
pub fn borrow_conflict<T: Into<String>>(msg: T) -> OwnershipError {
    OwnershipError::BorrowConflict(msg.into())
}

/// Create lifetime error
pub fn lifetime_error<T: Into<String>>(msg: T) -> OwnershipError {
    OwnershipError::Lifetime(msg.into())
}

/// Create ownership transfer error
pub fn move_error<T: Into<String>>(msg: T) -> OwnershipError {
    OwnershipError::MoveError(msg.into())
}

/// Create mutable borrow conflict error
pub fn mutable_borrow_conflict<T: Into<String>>(msg: T) -> OwnershipError {
    OwnershipError::MutableBorrowConflict(msg.into())
}

/// Create interior mutability error
pub fn interior_mutability_error<T: Into<String>>(msg: T) -> OwnershipError {
    OwnershipError::InteriorMutability(msg.into())
}

/// Create memory safety error
pub fn memory_safety_error<T: Into<String>>(msg: T) -> OwnershipError {
    OwnershipError::MemorySafety(msg.into())
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let err = borrow_conflict("test");
        assert!(matches!(err, OwnershipError::BorrowConflict(_)));
        assert_eq!(err.error_code(), ErrorCode::Ownership);
    }

    #[test]
    fn test_error_conversion() {
        let err = lifetime_error("test");
        let unified: UnifiedError = err.into();
        assert!(matches!(unified, UnifiedError::Custom(_)));
    }
}
