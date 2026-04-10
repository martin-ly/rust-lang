//! C02: 类型系统错误处理

pub use common::{
    TypeError, RustLangError, Result,
    ErrorContext, ErrorRecovery,
};

/// C02 crate 的结果类型
pub type C02Result<T> = Result<T>;

/// 创建类型不匹配错误
pub fn type_mismatch(expected: impl Into<String>, found: impl Into<String>) -> RustLangError {
    RustLangError::Type(TypeError::TypeMismatch {
        expected: expected.into(),
        found: found.into(),
    })
}

/// 创建类型推导失败错误
pub fn inference_failed<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Type(TypeError::InferenceFailed(msg.into()))
}

/// 创建 trait 约束不满足错误
pub fn trait_bound_not_satisfied<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Type(TypeError::TraitBoundNotSatisfied(msg.into()))
}

/// 创建类型转换错误
pub fn type_conversion<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Type(TypeError::Conversion(msg.into()))
}

/// 创建空指针错误
pub fn null_pointer<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Type(TypeError::NullPointer(msg.into()))
}

/// 创建变型错误
pub fn variance_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Type(TypeError::Variance(msg.into()))
}
