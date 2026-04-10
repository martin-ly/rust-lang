//! C01: 所有权、借用和作用域错误处理

pub use common::{
    OwnershipError, RustLangError, Result,
    ErrorContext, ErrorRecovery,
};

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
