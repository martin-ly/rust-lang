//! 边缘计算模块
//! 
//! 提供边缘计算功能，包括规则引擎、数据处理、机器学习等

pub mod rule_engine;

pub use rule_engine::{RuleEngine, Rule, Condition, Action, RuleContext};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum EdgeComputingError {
    #[error("规则引擎错误: {0}")]
    RuleEngineError(String),
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    #[error("模型未找到: {0}")]
    ModelNotFound(String),
    #[error("模板未找到: {0}")]
    TemplateNotFound(String),
    #[error("序列化错误: {0}")]
    SerializationError(String),
    #[error("反序列化错误: {0}")]
    DeserializationError(String),
}
