//! # Common - 项目通用工具库
//!
//! 提供统一的错误处理机制，使用 thiserror 和 anyhow 模式
//!
//! ## 使用示例
//!
//! ```rust
//! use common::{RustLangError, Result};
//!
//! fn may_fail() -> Result<i32> {
//!     Ok(42)
//! }
//! ```

#![allow(clippy::empty_line_after_doc_comments)]

// 错误处理模块
pub mod error;

// 重新导出主要错误类型
pub use error::{
    RustLangError, Result, ErrorContext, ErrorRecovery,
    OwnershipError, TypeError, ControlFlowError, GenericError,
    ThreadError, AsyncError, ProcessError, AlgorithmError,
    DesignPatternError, NetworkError, MacroError, WasmError,
};

// 向后兼容别名
pub use error::RustLangError as CommonError;

// 其他公共模块
pub mod traits;
pub mod types;
pub mod utils;

// 重新导出常用 trait
pub use traits::{Identifiable, Measurable, Validatable};

// 重新导出常用类型
pub use types::{Pagination, Paginated, Version};

// 重新导出常用工具函数
pub use utils::{format_duration, format_bytes, truncate_with_ellipsis};
