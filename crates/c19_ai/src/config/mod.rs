//! 配置管理模块
//! 
//! 提供系统配置的加载、验证和管理功能

pub mod manager;
pub mod schema;
pub mod validation;

pub use manager::ConfigManager;
pub use schema::ConfigSchema;
pub use validation::ConfigValidator;

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 配置值类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
#[serde(untagged)]
pub enum ConfigValue {
    String(String),
    Integer(i64),
    Float(f64),
    Boolean(bool),
    Array(Vec<ConfigValue>),
    Object(HashMap<String, ConfigValue>),
}

/// 配置项
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConfigItem {
    pub key: String,
    pub value: ConfigValue,
    pub description: Option<String>,
    pub required: bool,
    pub default_value: Option<ConfigValue>,
}

/// 配置源类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ConfigSource {
    /// 环境变量
    Environment,
    /// 配置文件
    File(String),
    /// 数据库
    Database,
    /// 命令行参数
    CommandLine,
    /// 默认值
    Default,
}

/// 配置错误
#[derive(Debug, thiserror::Error)]
pub enum ConfigError {
    #[error("配置项 '{key}' 未找到")]
    MissingKey { key: String },
    
    #[error("配置项 '{key}' 类型错误: 期望 {expected}, 实际 {actual}")]
    TypeMismatch { 
        key: String, 
        expected: String, 
        actual: String 
    },
    
    #[error("配置验证失败: {message}")]
    ValidationFailed { message: String },
    
    #[error("配置文件加载失败: {path}")]
    FileLoadError { path: String },
    
    #[error("配置解析失败: {message}")]
    ParseError { message: String },
    
    #[error("IO错误: {0}")]
    IoError(#[from] std::io::Error),
    
    #[error("序列化错误: {0}")]
    SerializationError(#[from] serde_json::Error),
}
