//! C07: 进程错误处理 (统一版本)

pub use crate::error::*;
pub use common::{
    ProcessError, RustLangError, Result,
    ErrorContext, ErrorRecovery,
};

/// C07 crate 的结果类型（统一版本）
pub type C07Result<T> = Result<T>;

/// 从现有错误创建统一进程错误
pub fn process_error_from_existing<T: std::fmt::Display>(e: T) -> RustLangError {
    RustLangError::Process(ProcessError::Other(e.to_string()))
}
