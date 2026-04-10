//! C04: 泛型错误处理

pub use common::{
    GenericError, RustLangError, Result,
    ErrorContext, ErrorRecovery,
};

/// C04 crate 的结果类型
pub type C04Result<T> = Result<T>;

/// 创建类型参数不匹配错误
pub fn type_parameter_mismatch<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Generic(GenericError::TypeParameterMismatch(msg.into()))
}

/// 创建关联类型错误
pub fn associated_type_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Generic(GenericError::AssociatedType(msg.into()))
}

/// 创建泛型约束冲突错误
pub fn constraint_conflict<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Generic(GenericError::ConstraintConflict(msg.into()))
}

/// 创建 GAT 错误
pub fn gat_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Generic(GenericError::GatError(msg.into()))
}

/// 创建 HRTB 错误
pub fn hrtb_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Generic(GenericError::HrtbError(msg.into()))
}
