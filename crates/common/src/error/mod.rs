//! Unified error handling module with trait-based design
//! 
//! This module provides:
//! - `RustLangError` trait: Core trait for all errors in the system
//! - `CommonError`: Generic error types that don't depend on specific crates
//! - `UnifiedError`: Minimal unified error type for cross-crate error handling
//! - Macros for easy trait implementation

use std::fmt::Debug;
use std::time::Duration;
use thiserror::Error;

/// Error code for categorizing errors
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorCode {
    // Common errors (0-999)
    Io = 100,
    Parse = 101,
    Validation = 102,
    NotFound = 103,
    Timeout = 104,
    Cancelled = 105,
    Config = 106,
    Other = 107,
    
    // Category-based codes (1000+)
    Ownership = 1000,
    Type = 2000,
    ControlFlow = 3000,
    Generic = 4000,
    Thread = 5000,
    Async = 6000,
    Process = 7000,
    Algorithm = 8000,
    DesignPattern = 9000,
    Network = 10000,
    Macro = 11000,
    Wasm = 12000,
    
    // Custom errors (20000+)
    Custom = 20000,
}

impl ErrorCode {
    /// Get the error category based on error code
    pub fn category(&self) -> &'static str {
        match self {
            ErrorCode::Io | ErrorCode::Parse | ErrorCode::Validation |
            ErrorCode::NotFound | ErrorCode::Timeout | ErrorCode::Cancelled |
            ErrorCode::Config | ErrorCode::Other => "common",
            ErrorCode::Ownership => "ownership",
            ErrorCode::Type => "type",
            ErrorCode::ControlFlow => "control_flow",
            ErrorCode::Generic => "generic",
            ErrorCode::Thread => "thread",
            ErrorCode::Async => "async",
            ErrorCode::Process => "process",
            ErrorCode::Algorithm => "algorithm",
            ErrorCode::DesignPattern => "design_pattern",
            ErrorCode::Network => "network",
            ErrorCode::Macro => "macro",
            ErrorCode::Wasm => "wasm",
            ErrorCode::Custom => "custom",
        }
    }
}

/// Core trait for all errors in the rust-lang system
/// 
/// This trait provides a unified interface for error handling across all crates,
/// allowing each crate to define its own error types while maintaining compatibility.
pub trait RustLangError: std::error::Error + Send + Sync + 'static {
    /// Get the error code for categorization
    fn error_code(&self) -> ErrorCode;
    
    /// Check if this error is retryable
    fn is_retryable(&self) -> bool {
        false
    }
    
    /// Get retry delay if applicable
    fn retry_delay(&self) -> Option<Duration> {
        None
    }
    
    /// Get max retry count if applicable
    fn max_retries(&self) -> Option<u32> {
        None
    }
}

/// Generic error types that don't depend on specific crates
/// 
/// These are common errors that can be used across the entire system
/// without creating circular dependencies.
#[derive(Error, Debug, Clone)]
pub enum CommonError {
    #[error("IO error: {0}")]
    Io(String),
    
    #[error("parse error: {0}")]
    Parse(String),
    
    #[error("validation error: {0}")]
    Validation(String),
    
    #[error("not found: {0}")]
    NotFound(String),
    
    #[error("operation timed out")]
    Timeout,
    
    #[error("operation cancelled")]
    Cancelled,
    
    #[error("config error: {0}")]
    Config(String),
    
    #[error("{0}")]
    Other(String),
}

impl RustLangError for CommonError {
    fn error_code(&self) -> ErrorCode {
        match self {
            CommonError::Io(_) => ErrorCode::Io,
            CommonError::Parse(_) => ErrorCode::Parse,
            CommonError::Validation(_) => ErrorCode::Validation,
            CommonError::NotFound(_) => ErrorCode::NotFound,
            CommonError::Timeout => ErrorCode::Timeout,
            CommonError::Cancelled => ErrorCode::Cancelled,
            CommonError::Config(_) => ErrorCode::Config,
            CommonError::Other(_) => ErrorCode::Other,
        }
    }
    
    fn is_retryable(&self) -> bool {
        matches!(self, CommonError::Timeout | CommonError::Io(_))
    }
    
    fn retry_delay(&self) -> Option<Duration> {
        match self {
            CommonError::Timeout => Some(Duration::from_millis(100)),
            CommonError::Io(_) => Some(Duration::from_millis(50)),
            _ => None,
        }
    }
    
    fn max_retries(&self) -> Option<u32> {
        match self {
            CommonError::Timeout => Some(3),
            CommonError::Io(_) => Some(3),
            _ => None,
        }
    }
}

impl From<std::io::Error> for CommonError {
    fn from(e: std::io::Error) -> Self {
        CommonError::Io(e.to_string())
    }
}

impl From<String> for CommonError {
    fn from(s: String) -> Self {
        CommonError::Other(s)
    }
}

impl From<&str> for CommonError {
    fn from(s: &str) -> Self {
        CommonError::Other(s.to_string())
    }
}

/// Minimal unified error type for cross-crate error handling
/// 
/// This enum provides a way to handle errors from multiple crates
/// when you need a concrete type rather than a trait object.
#[derive(Error, Debug, Clone)]
pub enum UnifiedError {
    #[error("common error: {0}")]
    Common(CommonError),
    
    #[error("custom error: {0}")]
    Custom(String),
}

impl RustLangError for UnifiedError {
    fn error_code(&self) -> ErrorCode {
        match self {
            UnifiedError::Common(e) => RustLangError::error_code(e),
            UnifiedError::Custom(_) => ErrorCode::Custom,
        }
    }
    
    fn is_retryable(&self) -> bool {
        match self {
            UnifiedError::Common(e) => RustLangError::is_retryable(e),
            UnifiedError::Custom(_) => false,
        }
    }
    
    fn retry_delay(&self) -> Option<Duration> {
        match self {
            UnifiedError::Common(e) => RustLangError::retry_delay(e),
            UnifiedError::Custom(_) => None,
        }
    }
    
    fn max_retries(&self) -> Option<u32> {
        match self {
            UnifiedError::Common(e) => RustLangError::max_retries(e),
            UnifiedError::Custom(_) => None,
        }
    }
}

impl From<CommonError> for UnifiedError {
    fn from(e: CommonError) -> Self {
        UnifiedError::Common(e)
    }
}

impl From<std::io::Error> for UnifiedError {
    fn from(e: std::io::Error) -> Self {
        UnifiedError::Common(e.into())
    }
}

impl From<String> for UnifiedError {
    fn from(s: String) -> Self {
        UnifiedError::Common(s.into())
    }
}

impl From<&str> for UnifiedError {
    fn from(s: &str) -> Self {
        UnifiedError::Common(s.into())
    }
}

/// Generic result type using the UnifiedError
pub type Result<T, E = UnifiedError> = std::result::Result<T, E>;

/// Result type with boxed dynamic error for maximum flexibility
pub type DynamicResult<T> = std::result::Result<T, Box<dyn RustLangError>>;

/// Extension trait for error context
pub trait ErrorContext<T> {
    /// Add context to an error
    fn with_context<F>(self, f: F) -> Result<T>
    where
        F: FnOnce() -> String;
}

impl<T, E> ErrorContext<T> for std::result::Result<T, E>
where
    E: Into<CommonError>,
{
    fn with_context<F>(self, _f: F) -> Result<T>
    where
        F: FnOnce() -> String,
    {
        self.map_err(|e| UnifiedError::Common(e.into()))
    }
}

/// Legacy ErrorRecovery trait - maintained for backward compatibility
/// 
/// This trait is implemented for types that implement RustLangError.
/// For new code, prefer using RustLangError trait directly.
pub trait ErrorRecovery {
    fn is_retryable(&self) -> bool;
    fn retry_delay(&self) -> Option<Duration>;
    fn max_retries(&self) -> Option<u32>;
}

// Implement ErrorRecovery for types that implement RustLangError
// Use a wrapper to avoid blanket impl conflicts
impl<T: RustLangError> ErrorRecovery for T {
    fn is_retryable(&self) -> bool {
        RustLangError::is_retryable(self)
    }
    
    fn retry_delay(&self) -> Option<Duration> {
        RustLangError::retry_delay(self)
    }
    
    fn max_retries(&self) -> Option<u32> {
        RustLangError::max_retries(self)
    }
}

/// Macro to simplify RustLangError trait implementation
/// 
/// # Examples
/// 
/// ```rust,ignore
/// #[derive(Error, Debug)]
/// pub enum MyError {
///     #[error("something failed")]
///     Failed,
/// }
/// 
/// impl_rust_lang_error!(MyError, ErrorCode::Custom);
/// ```
#[macro_export]
macro_rules! impl_rust_lang_error {
    // Basic implementation with just error code
    ($type:ty, $code:expr) => {
        impl $crate::error::RustLangError for $type {
            fn error_code(&self) -> $crate::error::ErrorCode {
                $code
            }
            
            fn is_retryable(&self) -> bool {
                false
            }
        }
    };
    
    // Implementation with custom retryable logic
    ($type:ty, $code:expr, retryable: $retryable:expr) => {
        impl $crate::error::RustLangError for $type {
            fn error_code(&self) -> $crate::error::ErrorCode {
                $code
            }
            
            fn is_retryable(&self) -> bool {
                $retryable
            }
        }
    };
    
    // Full implementation with all options
    ($type:ty, $code:expr, retryable: $retryable:expr, retry_delay: $delay:expr, max_retries: $retries:expr) => {
        impl $crate::error::RustLangError for $type {
            fn error_code(&self) -> $crate::error::ErrorCode {
                $code
            }
            
            fn is_retryable(&self) -> bool {
                $retryable
            }
            
            fn retry_delay(&self) -> Option<std::time::Duration> {
                $delay
            }
            
            fn max_retries(&self) -> Option<u32> {
                $retries
            }
        }
    };
}

/// Macro to implement From<ErrorType> for UnifiedError
#[macro_export]
macro_rules! impl_into_unified_error {
    ($type:ty) => {
        impl From<$type> for $crate::error::UnifiedError {
            fn from(e: $type) -> Self {
                $crate::error::UnifiedError::Custom(e.to_string())
            }
        }
    };
}

/// Macro to create a crate-specific error module
/// 
/// This macro sets up the standard boilerplate for a crate's error handling.
#[macro_export]
macro_rules! define_crate_error {
    (
        crate_name: $crate_name:ident,
        error_type: $error_type:ty,
        error_code: $error_code:expr,
        result_type: $result_name:ident
    ) => {
        pub use $crate::{
            RustLangError, CommonError, UnifiedError, Result,
            ErrorContext, ErrorRecovery, ErrorCode,
            impl_rust_lang_error, impl_into_unified_error,
        };
        
        /// Crate-specific result type
        pub type $result_name<T> = $crate::Result<T>;
        
        // Implement RustLangError for this crate's error type
        $crate::impl_rust_lang_error!($error_type, $error_code);
        
        // Implement conversion to UnifiedError
        $crate::impl_into_unified_error!($error_type);
    };
}

// Legacy type aliases for backward compatibility
/// Legacy OwnershipError - now replaced by trait-based approach
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub type OwnershipError = CommonError;

/// Legacy TypeError - now replaced by trait-based approach
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub type TypeError = CommonError;

/// Legacy ControlFlowError - now replaced by trait-based approach
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub type ControlFlowError = CommonError;

/// Legacy GenericError - now replaced by trait-based approach
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub type GenericError = CommonError;

/// Legacy ThreadError - now replaced by trait-based approach
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub type ThreadError = CommonError;

/// Legacy AsyncError - now replaced by trait-based approach
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub type AsyncError = CommonError;

/// Legacy ProcessError - now replaced by trait-based approach
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub type ProcessError = CommonError;

/// Legacy AlgorithmError - now replaced by trait-based approach
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub type AlgorithmError = CommonError;

/// Legacy DesignPatternError - now replaced by trait-based approach
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub type DesignPatternError = CommonError;

/// Legacy NetworkError - now replaced by trait-based approach
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub type NetworkError = CommonError;

/// Legacy MacroError - now replaced by trait-based approach
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub type MacroError = CommonError;

/// Legacy WasmError - now replaced by trait-based approach
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub type WasmError = CommonError;

/// Legacy Retryable alias - maintained for backward compatibility
pub use ErrorRecovery as Retryable;

#[cfg(test)]
mod tests {
    use super::*;
    use thiserror::Error;
    
    #[derive(Error, Debug, Clone)]
    enum TestError {
        #[error("test failed")]
        Failed,
        #[error("test retryable")]
        Retryable,
    }
    
    impl RustLangError for TestError {
        fn error_code(&self) -> ErrorCode {
            ErrorCode::Custom
        }
        
        fn is_retryable(&self) -> bool {
            matches!(self, TestError::Retryable)
        }
        
        fn retry_delay(&self) -> Option<Duration> {
            if RustLangError::is_retryable(self) {
                Some(Duration::from_millis(100))
            } else {
                None
            }
        }
    }
    
    #[test]
    fn test_common_error() {
        let err = CommonError::Io("file not found".to_string());
        assert_eq!(RustLangError::error_code(&err), ErrorCode::Io);
        assert!(RustLangError::is_retryable(&err));
        
        let err = CommonError::Validation("invalid".to_string());
        assert_eq!(RustLangError::error_code(&err), ErrorCode::Validation);
        assert!(!RustLangError::is_retryable(&err));
    }
    
    #[test]
    fn test_unified_error() {
        let err = UnifiedError::Common(CommonError::Timeout);
        assert_eq!(RustLangError::error_code(&err), ErrorCode::Timeout);
        assert!(RustLangError::is_retryable(&err));
    }
    
    #[test]
    fn test_trait_impl() {
        let err = TestError::Failed;
        assert!(!RustLangError::is_retryable(&err));
        
        let err = TestError::Retryable;
        assert!(RustLangError::is_retryable(&err));
        assert_eq!(RustLangError::retry_delay(&err), Some(Duration::from_millis(100)));
    }
    
    #[test]
    fn test_error_code_category() {
        assert_eq!(ErrorCode::Io.category(), "common");
        assert_eq!(ErrorCode::Network.category(), "network");
        assert_eq!(ErrorCode::Custom.category(), "custom");
    }
    
    #[test]
    fn test_error_recovery_trait() {
        // Test that ErrorRecovery is correctly implemented via blanket impl
        fn check_recovery<T: ErrorRecovery>(e: &T) -> bool {
            ErrorRecovery::is_retryable(e)
        }
        
        let err = CommonError::Timeout;
        assert!(check_recovery(&err));
    }
    
    #[test]
    fn test_macro_impl() {
        #[derive(Error, Debug)]
        enum MacroTestError {
            #[error("macro test")]
            Test,
        }
        
        impl_rust_lang_error!(MacroTestError, ErrorCode::Custom);
        
        let err = MacroTestError::Test;
        assert_eq!(RustLangError::error_code(&err), ErrorCode::Custom);
        assert!(!RustLangError::is_retryable(&err));
    }
}
