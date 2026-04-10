//! # Common - Project Common Utilities Library
//!
//! Provides unified error handling mechanism using trait-based design.
//!
//! ## Usage Example
//!
//! ```rust
//! use common::{RustLangError, Result, CommonError};
//!
//! fn may_fail() -> Result<i32> {
//!     Ok(42)
//! }
//!
//! fn with_specific_error() -> Result<i32, CommonError> {
//!     Ok(42)
//! }
//! ```
//!
//! ## Migration from Old Design
//!
//! The error handling has been redesigned to use traits instead of a large enum.
//! Old crate-specific error types are now deprecated - use your own crate-specific
//! error types and implement `RustLangError` trait.

#![allow(clippy::empty_line_after_doc_comments)]
#![allow(deprecated)] // Allow deprecated items for backward compatibility

// Re-export the error module
pub mod error;

// Primary re-exports - new trait-based design
pub use error::{
    // Core trait and types
    RustLangError,
    CommonError,
    UnifiedError,
    ErrorCode,
    
    // Result types
    Result,
    DynamicResult,
    
    // Extension traits
    ErrorContext,
    ErrorRecovery,
};

// Macros are exported at crate root via #[macro_export]
// Use them directly as common::impl_rust_lang_error, etc.

// Legacy re-exports - deprecated, for backward compatibility
#[deprecated(since = "0.2.0", note = "Use your crate's specific error type instead")]
pub use error::{
    OwnershipError, TypeError, ControlFlowError, GenericError,
    ThreadError, AsyncError, ProcessError, AlgorithmError,
    DesignPatternError, NetworkError, MacroError, WasmError,
};

// Legacy alias
#[deprecated(since = "0.2.0", note = "Use UnifiedError instead")]
pub use error::UnifiedError as RustLangErrorEnum;

// Backward compatibility alias
pub use error::UnifiedError as CommonErrorAlias;

// Other public modules
pub mod traits;
pub mod types;
pub mod utils;

// Re-export commonly used traits
pub use traits::{Identifiable, Measurable, Validatable};

// Re-export commonly used types
pub use types::{Pagination, Paginated, Version};

// Re-export commonly used utility functions
pub use utils::{format_duration, format_bytes, truncate_with_ellipsis};
