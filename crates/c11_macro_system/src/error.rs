//! C11: 宏系统错误处理

pub use common::{
    MacroError, RustLangError, Result,
    ErrorContext, ErrorRecovery,
};

/// C11 crate 的结果类型
pub type C11Result<T> = Result<T>;

/// 创建宏解析错误
pub fn macro_parse_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Macro(MacroError::ParseError(msg.into()))
}

/// 创建宏展开错误
pub fn macro_expansion_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Macro(MacroError::ExpansionError(msg.into()))
}

/// 创建过程宏错误
pub fn proc_macro_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Macro(MacroError::ProcMacro(msg.into()))
}

/// 创建声明宏错误
pub fn decl_macro_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Macro(MacroError::DeclMacro(msg.into()))
}

/// 创建卫生性错误
pub fn hygiene_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Macro(MacroError::Hygiene(msg.into()))
}
