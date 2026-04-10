//! C06: 异步错误处理

use std::time::Duration;
pub use common::{
    AsyncError, RustLangError, Result,
    ErrorContext, ErrorRecovery,
};

/// C06 crate 的结果类型
pub type C06Result<T> = Result<T>;

/// 创建任务取消错误
pub fn task_cancelled<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Async(AsyncError::Cancelled(msg.into()))
}

/// 创建超时错误
pub fn timeout(duration: Duration) -> RustLangError {
    RustLangError::Async(AsyncError::Timeout(duration))
}

/// 创建运行时错误
pub fn runtime_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Async(AsyncError::Runtime(msg.into()))
}

/// 创建调度错误
pub fn scheduler_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Async(AsyncError::Scheduler(msg.into()))
}

/// 创建流处理错误
pub fn stream_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Async(AsyncError::Stream(msg.into()))
}

/// 创建背压错误
pub fn backpressure_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Async(AsyncError::Backpressure(msg.into()))
}
