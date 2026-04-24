//! # 练习 2: 自定义错误类型
//!
//! **难度**: Medium  
//! **考点**: 自定义 Error 类型、thiserror、 anyhow
//!
//! ## 题目描述
//!
//! 为领域逻辑定义专门的错误类型。

use std::error::Error;
use std::fmt;

/// 配置错误
#[derive(Debug, PartialEq)]
pub enum ConfigError {
    MissingField(String),
    InvalidValue { field: String, value: String },
    FileNotFound(String),
}

impl fmt::Display for ConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConfigError::MissingField(field) => write!(f, "缺少必填字段: {}", field),
            ConfigError::InvalidValue { field, value } => {
                write!(f, "字段 '{}' 的值 '{}' 无效", field, value)
            }
            ConfigError::FileNotFound(path) => write!(f, "配置文件未找到: {}", path),
        }
    }
}

impl Error for ConfigError {}

/// 验证配置项
pub fn validate_config(port: Option<u16>, host: Option<&str>) -> Result<(), ConfigError> {
    let port = port.ok_or(ConfigError::MissingField("port".to_string()))?;
    if port == 0 {
        return Err(ConfigError::InvalidValue {
            field: "port".to_string(),
            value: "0".to_string(),
        });
    }

    let host = host.ok_or(ConfigError::MissingField("host".to_string()))?;
    if host.is_empty() {
        return Err(ConfigError::InvalidValue {
            field: "host".to_string(),
            value: "".to_string(),
        });
    }

    Ok(())
}

/// 将错误转换为用户友好的消息
pub fn format_error(err: &dyn Error) -> String {
    let mut msg = err.to_string();
    if let Some(source) = err.source() {
        msg.push_str(&format!(" (原因: {})", source));
    }
    msg
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_config_ok() {
        assert!(validate_config(Some(8080), Some("localhost")).is_ok());
    }

    #[test]
    fn test_validate_config_missing_port() {
        assert_eq!(
            validate_config(None, Some("localhost")),
            Err(ConfigError::MissingField("port".to_string()))
        );
    }

    #[test]
    fn test_validate_config_invalid_port() {
        assert_eq!(
            validate_config(Some(0), Some("localhost")),
            Err(ConfigError::InvalidValue {
                field: "port".to_string(),
                value: "0".to_string(),
            })
        );
    }

    #[test]
    fn test_format_error() {
        let err = ConfigError::FileNotFound("config.toml".to_string());
        assert!(format_error(&err).contains("config.toml"));
    }
}
