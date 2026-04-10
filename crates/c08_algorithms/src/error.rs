//! C08: 算法错误处理

pub use common::{
    AlgorithmError, RustLangError, Result,
    ErrorContext, ErrorRecovery,
};

/// C08 crate 的结果类型
pub type C08Result<T> = Result<T>;

/// 创建无效输入错误
pub fn invalid_input<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Algorithm(AlgorithmError::InvalidInput(msg.into()))
}

/// 创建算法未实现错误
pub fn algorithm_not_implemented<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Algorithm(AlgorithmError::NotImplemented(msg.into()))
}

/// 创建复杂度超限错误
pub fn complexity_exceeded<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Algorithm(AlgorithmError::ComplexityExceeded(msg.into()))
}

/// 创建数值溢出错误
pub fn numeric_overflow<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Algorithm(AlgorithmError::NumericOverflow(msg.into()))
}

/// 创建收敛失败错误
pub fn convergence_failed<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Algorithm(AlgorithmError::ConvergenceFailed(msg.into()))
}

/// 创建数据结构错误
pub fn data_structure_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::Algorithm(AlgorithmError::DataStructure(msg.into()))
}
