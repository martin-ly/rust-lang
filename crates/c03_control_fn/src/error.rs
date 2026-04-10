//! # C03: 控制流和函数错误处理
//!
//! 提供控制流相关的错误类型，集成到统一的错误处理系统中。

use common::{ControlFlowError, RustLangError, Result};

pub use common::{ErrorContext, ErrorRecovery};

/// C03 crate 的结果类型
pub type C03Result<T> = Result<T>;

/// 创建匹配穷尽性错误
pub fn non_exhaustive_match<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::ControlFlow(ControlFlowError::NonExhaustiveMatch(msg.into()))
}

/// 创建递归溢出错误
pub fn stack_overflow<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::ControlFlow(ControlFlowError::StackOverflow(msg.into()))
}

/// 创建控制流中断错误
pub fn control_flow_interrupted<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::ControlFlow(ControlFlowError::Interrupted(msg.into()))
}

/// 创建闭包捕获错误
pub fn closure_capture<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::ControlFlow(ControlFlowError::ClosureCapture(msg.into()))
}

/// 创建生成器错误
pub fn generator_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::ControlFlow(ControlFlowError::Generator(msg.into()))
}
