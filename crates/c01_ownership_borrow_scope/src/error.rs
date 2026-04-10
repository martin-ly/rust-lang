//! # C01: 所有权、借用和作用域错误处理
//!
//! 提供所有权相关的错误类型，集成到统一的错误处理系统中。

use common::{OwnershipError, RustLangError, Result};

pub use common::{ErrorContext, ErrorRecovery};

/// C01 crate 的结果类型
pub type C01Result<T> = Result<T>;

/// 创建借用冲突错误
pub fn borrow_conflict<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Ownership(OwnershipError::BorrowConflict(msg.into()))
}

/// 创建生命周期错误
pub fn lifetime_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Ownership(OwnershipError::Lifetime(msg.into()))
}

/// 创建所有权转移错误
pub fn move_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Ownership(OwnershipError::MoveError(msg.into()))
}

/// 创建可变借用冲突错误
pub fn mutable_borrow_conflict<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Ownership(OwnershipError::MutableBorrowConflict(msg.into()))
}

/// 创建内部可变性错误
pub fn interior_mutability_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Ownership(OwnershipError::InteriorMutability(msg.into()))
}

/// 创建内存安全错误
pub fn memory_safety_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Ownership(OwnershipError::MemorySafety(msg.into()))
}

/// 便捷宏：检查借用冲突
#[macro_export]
macro_rules! ensure_no_borrow_conflict {
    ($condition:expr, $msg:expr) => {
        if !$condition {
            return Err($crate::error::borrow_conflict($msg));
        }
    };
}

/// 便捷宏：检查内存安全
#[macro_export]
macro_rules! ensure_memory_safe {
    ($condition:expr, $msg:expr) => {
        if !$condition {
            return Err($crate::error::memory_safety_error($msg));
        }
    };
}
