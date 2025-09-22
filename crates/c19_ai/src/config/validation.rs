//! 配置验证模块
//! 
//! 提供配置值的验证功能

use super::{ConfigError, ConfigValue};
use std::collections::HashMap;

/// 配置验证器
pub struct ConfigValidator;

impl ConfigValidator {
    /// 验证配置值
    pub fn validate_value(
        key: &str,
        value: &ConfigValue,
        rules: &ValidationRules,
    ) -> Result<(), ConfigError> {
        match value {
            ConfigValue::String(s) => {
                Self::validate_string(key, s, rules)?;
            }
            ConfigValue::Integer(i) => {
                Self::validate_integer(key, *i, rules)?;
            }
            ConfigValue::Float(f) => {
                Self::validate_float(key, *f, rules)?;
            }
            ConfigValue::Boolean(_) => {
                // 布尔值通常不需要额外验证
            }
            ConfigValue::Array(arr) => {
                Self::validate_array(key, arr, rules)?;
            }
            ConfigValue::Object(obj) => {
                Self::validate_object(key, obj, rules)?;
            }
        }
        Ok(())
    }

    /// 验证字符串
    fn validate_string(
        key: &str,
        value: &str,
        rules: &ValidationRules,
    ) -> Result<(), ConfigError> {
        if let Some(min_len) = rules.min_length {
            if value.len() < min_len {
                return Err(ConfigError::ValidationFailed {
                    message: format!("配置项 '{}' 长度不能少于 {} 个字符", key, min_len),
                });
            }
        }

        if let Some(max_len) = rules.max_length {
            if value.len() > max_len {
                return Err(ConfigError::ValidationFailed {
                    message: format!("配置项 '{}' 长度不能超过 {} 个字符", key, max_len),
                });
            }
        }

        if let Some(pattern) = &rules.pattern {
            if !regex::Regex::new(pattern)
                .map_err(|e| ConfigError::ValidationFailed {
                    message: format!("正则表达式错误: {}", e),
                })?
                .is_match(value)
            {
                return Err(ConfigError::ValidationFailed {
                    message: format!("配置项 '{}' 格式不正确", key),
                });
            }
        }

        if let Some(allowed_values) = &rules.allowed_values {
            if !allowed_values.contains(&ConfigValue::String(value.to_string())) {
                return Err(ConfigError::ValidationFailed {
                    message: format!("配置项 '{}' 的值不在允许的范围内", key),
                });
            }
        }

        Ok(())
    }

    /// 验证整数
    fn validate_integer(
        key: &str,
        value: i64,
        rules: &ValidationRules,
    ) -> Result<(), ConfigError> {
        if let Some(min) = rules.min_value {
            if value < min {
                return Err(ConfigError::ValidationFailed {
                    message: format!("配置项 '{}' 的值不能小于 {}", key, min),
                });
            }
        }

        if let Some(max) = rules.max_value {
            if value > max {
                return Err(ConfigError::ValidationFailed {
                    message: format!("配置项 '{}' 的值不能大于 {}", key, max),
                });
            }
        }

        if let Some(allowed_values) = &rules.allowed_values {
            if !allowed_values.contains(&ConfigValue::Integer(value)) {
                return Err(ConfigError::ValidationFailed {
                    message: format!("配置项 '{}' 的值不在允许的范围内", key),
                });
            }
        }

        Ok(())
    }

    /// 验证浮点数
    fn validate_float(
        key: &str,
        value: f64,
        rules: &ValidationRules,
    ) -> Result<(), ConfigError> {
        if let Some(min) = rules.min_value {
            if value < min as f64 {
                return Err(ConfigError::ValidationFailed {
                    message: format!("配置项 '{}' 的值不能小于 {}", key, min),
                });
            }
        }

        if let Some(max) = rules.max_value {
            if value > max as f64 {
                return Err(ConfigError::ValidationFailed {
                    message: format!("配置项 '{}' 的值不能大于 {}", key, max),
                });
            }
        }

        if let Some(allowed_values) = &rules.allowed_values {
            if !allowed_values.contains(&ConfigValue::Float(value)) {
                return Err(ConfigError::ValidationFailed {
                    message: format!("配置项 '{}' 的值不在允许的范围内", key),
                });
            }
        }

        Ok(())
    }

    /// 验证数组
    fn validate_array(
        key: &str,
        value: &[ConfigValue],
        rules: &ValidationRules,
    ) -> Result<(), ConfigError> {
        if let Some(min_items) = rules.min_items {
            if value.len() < min_items {
                return Err(ConfigError::ValidationFailed {
                    message: format!("配置项 '{}' 的数组长度不能少于 {} 个元素", key, min_items),
                });
            }
        }

        if let Some(max_items) = rules.max_items {
            if value.len() > max_items {
                return Err(ConfigError::ValidationFailed {
                    message: format!("配置项 '{}' 的数组长度不能超过 {} 个元素", key, max_items),
                });
            }
        }

        // 验证数组中的每个元素
        for (i, item) in value.iter().enumerate() {
            let item_key = format!("{}.{}", key, i);
            Self::validate_value(&item_key, item, rules)?;
        }

        Ok(())
    }

    /// 验证对象
    fn validate_object(
        key: &str,
        value: &HashMap<String, ConfigValue>,
        rules: &ValidationRules,
    ) -> Result<(), ConfigError> {
        if let Some(required_fields) = &rules.required_fields {
            for field in required_fields {
                if !value.contains_key(field) {
                    return Err(ConfigError::ValidationFailed {
                        message: format!("配置项 '{}' 缺少必需字段 '{}'", key, field),
                    });
                }
            }
        }

        // 验证对象中的每个字段
        for (field_key, field_value) in value {
            let full_key = format!("{}.{}", key, field_key);
            Self::validate_value(&full_key, field_value, rules)?;
        }

        Ok(())
    }

    /// 验证整个配置
    pub fn validate_config(
        configs: &HashMap<String, ConfigValue>,
        schema: &HashMap<String, ValidationRules>,
    ) -> Result<(), ConfigError> {
        for (key, value) in configs {
            if let Some(rules) = schema.get(key) {
                Self::validate_value(key, value, rules)?;
            }
        }
        Ok(())
    }
}

/// 验证规则
#[derive(Debug, Clone)]
pub struct ValidationRules {
    /// 最小值（用于数字）
    pub min_value: Option<i64>,
    /// 最大值（用于数字）
    pub max_value: Option<i64>,
    /// 最小长度（用于字符串和数组）
    pub min_length: Option<usize>,
    /// 最大长度（用于字符串和数组）
    pub max_length: Option<usize>,
    /// 最小项目数（用于数组）
    pub min_items: Option<usize>,
    /// 最大项目数（用于数组）
    pub max_items: Option<usize>,
    /// 正则表达式模式（用于字符串）
    pub pattern: Option<String>,
    /// 允许的值列表
    pub allowed_values: Option<Vec<ConfigValue>>,
    /// 必需字段（用于对象）
    pub required_fields: Option<Vec<String>>,
}

impl ValidationRules {
    /// 创建新的验证规则
    pub fn new() -> Self {
        Self {
            min_value: None,
            max_value: None,
            min_length: None,
            max_length: None,
            min_items: None,
            max_items: None,
            pattern: None,
            allowed_values: None,
            required_fields: None,
        }
    }

    /// 设置最小值
    pub fn min_value(mut self, value: i64) -> Self {
        self.min_value = Some(value);
        self
    }

    /// 设置最大值
    pub fn max_value(mut self, value: i64) -> Self {
        self.max_value = Some(value);
        self
    }

    /// 设置最小长度
    pub fn min_length(mut self, value: usize) -> Self {
        self.min_length = Some(value);
        self
    }

    /// 设置最大长度
    pub fn max_length(mut self, value: usize) -> Self {
        self.max_length = Some(value);
        self
    }

    /// 设置正则表达式模式
    pub fn pattern(mut self, value: String) -> Self {
        self.pattern = Some(value);
        self
    }

    /// 设置允许的值
    pub fn allowed_values(mut self, values: Vec<ConfigValue>) -> Self {
        self.allowed_values = Some(values);
        self
    }

    /// 设置必需字段
    pub fn required_fields(mut self, fields: Vec<String>) -> Self {
        self.required_fields = Some(fields);
        self
    }
}

impl Default for ValidationRules {
    fn default() -> Self {
        Self::new()
    }
}
