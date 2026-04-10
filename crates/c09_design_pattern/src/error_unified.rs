//! C09: 设计模式错误处理 (统一版本)

pub use crate::error_handling::DesignPatternError as LegacyDesignPatternError;
pub use common::{
    DesignPatternError, RustLangError, Result,
    ErrorContext, ErrorRecovery,
};

/// C09 crate 的结果类型（统一版本）
pub type C09Result<T> = Result<T>;

/// 创建单例模式错误
pub fn singleton_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::DesignPattern(DesignPatternError::Singleton(msg.into()))
}

/// 创建工厂模式错误
pub fn factory_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::DesignPattern(DesignPatternError::Factory(msg.into()))
}

/// 创建代理模式错误
pub fn proxy_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::DesignPattern(DesignPatternError::Proxy(msg.into()))
}

/// 创建享元模式错误
pub fn flyweight_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::DesignPattern(DesignPatternError::Flyweight(msg.into()))
}

/// 创建责任链模式错误
pub fn chain_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::DesignPattern(DesignPatternError::Chain(msg.into()))
}

/// 创建观察者模式错误
pub fn observer_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::DesignPattern(DesignPatternError::Observer(msg.into()))
}

/// 创建并发模式错误
pub fn concurrency_pattern_error<T: Into<String>>(msg: T) -> RustLangError {
    RustLangError::DesignPattern(DesignPatternError::Concurrency(msg.into()))
}
