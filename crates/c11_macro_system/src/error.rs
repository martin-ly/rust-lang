//! C11: Macro System Error Handling
//!
//! This module provides crate-specific error types and utilities using
//! the trait-based error design from the common crate.

use common::{impl_into_unified_error, impl_rust_lang_error, ErrorCode};
use thiserror::Error;

/// C11 crate-specific error type
#[derive(Error, Debug, Clone)]
pub enum MacroError {
    #[error("parse error: {0}")]
    ParseError(String),
    
    #[error("expansion error: {0}")]
    ExpansionError(String),
    
    #[error("proc macro error: {0}")]
    ProcMacro(String),
    
    #[error("decl macro error: {0}")]
    DeclMacro(String),
    
    #[error("hygiene error: {0}")]
    Hygiene(String),
}

impl_rust_lang_error!(MacroError, ErrorCode::Macro);
impl_into_unified_error!(MacroError);

/// Re-export common error types for convenience
pub use common::{
    CommonError, DynamicResult, ErrorContext, ErrorRecovery, Result, RustLangError,
    UnifiedError,
};

/// C11 crate's result type
pub type C11Result<T> = Result<T>;

/// Create macro parse error
pub fn macro_parse_error<T: Into<String>>(msg: T) -> MacroError {
    MacroError::ParseError(msg.into())
}

/// Create macro expansion error
pub fn macro_expansion_error<T: Into<String>>(msg: T) -> MacroError {
    MacroError::ExpansionError(msg.into())
}

/// Create proc macro error
pub fn proc_macro_error<T: Into<String>>(msg: T) -> MacroError {
    MacroError::ProcMacro(msg.into())
}

/// Create decl macro error
pub fn decl_macro_error<T: Into<String>>(msg: T) -> MacroError {
    MacroError::DeclMacro(msg.into())
}

/// Create hygiene error
pub fn hygiene_error<T: Into<String>>(msg: T) -> MacroError {
    MacroError::Hygiene(msg.into())
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_error_creation() {
        let err = macro_parse_error("test");
        assert!(matches!(err, MacroError::ParseError(_)));
        assert_eq!(err.error_code(), ErrorCode::Macro);
    }

    #[test]
    fn test_error_conversion() {
        let err = macro_expansion_error("test");
        let unified: UnifiedError = err.into();
        assert!(matches!(unified, UnifiedError::Custom(_)));
    }
}
