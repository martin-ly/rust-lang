//! C09: Design Pattern Error Handling (Unified Version)
//!
//! This module provides crate-specific error types and utilities using
//! the trait-based error design from the common crate.

use common::{impl_into_unified_error, impl_rust_lang_error, ErrorCode};
use thiserror::Error;

/// C09 crate-specific error type
#[derive(Error, Debug, Clone)]
pub enum DesignPatternError {
    #[error("singleton error: {0}")]
    Singleton(String),
    
    #[error("factory error: {0}")]
    Factory(String),
    
    #[error("proxy error: {0}")]
    Proxy(String),
    
    #[error("flyweight error: {0}")]
    Flyweight(String),
    
    #[error("chain error: {0}")]
    Chain(String),
    
    #[error("observer error: {0}")]
    Observer(String),
    
    #[error("concurrency error: {0}")]
    Concurrency(String),
}

impl_rust_lang_error!(DesignPatternError, ErrorCode::DesignPattern);
impl_into_unified_error!(DesignPatternError);

/// Re-export common error types for convenience
pub use common::{
    CommonError, DynamicResult, ErrorContext, ErrorRecovery, Result, RustLangError,
    UnifiedError,
};

/// C09 crate's result type (Unified version)
pub type C09Result<T> = Result<T>;

/// Create singleton error
pub fn singleton_error<T: Into<String>>(msg: T) -> DesignPatternError {
    DesignPatternError::Singleton(msg.into())
}

/// Create factory error
pub fn factory_error<T: Into<String>>(msg: T) -> DesignPatternError {
    DesignPatternError::Factory(msg.into())
}

/// Create proxy error
pub fn proxy_error<T: Into<String>>(msg: T) -> DesignPatternError {
    DesignPatternError::Proxy(msg.into())
}

/// Create flyweight error
pub fn flyweight_error<T: Into<String>>(msg: T) -> DesignPatternError {
    DesignPatternError::Flyweight(msg.into())
}

/// Create chain error
pub fn chain_error<T: Into<String>>(msg: T) -> DesignPatternError {
    DesignPatternError::Chain(msg.into())
}

/// Create observer error
pub fn observer_error<T: Into<String>>(msg: T) -> DesignPatternError {
    DesignPatternError::Observer(msg.into())
}

/// Create concurrency pattern error
pub fn concurrency_pattern_error<T: Into<String>>(msg: T) -> DesignPatternError {
    DesignPatternError::Concurrency(msg.into())
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let err = singleton_error("test");
        assert!(matches!(err, DesignPatternError::Singleton(_)));
        assert_eq!(err.error_code(), ErrorCode::DesignPattern);
    }

    #[test]
    fn test_error_conversion() {
        let err = factory_error("test");
        let unified: UnifiedError = err.into();
        assert!(matches!(unified, UnifiedError::Custom(_)));
    }
}
