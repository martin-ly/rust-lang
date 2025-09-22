//! 数据模式定义
//! 
//! 提供数据结构和验证规则定义

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;

/// 数据模式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataSchema {
    pub name: String,
    pub version: String,
    pub fields: Vec<FieldDefinition>,
    pub constraints: Vec<Constraint>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 字段定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldDefinition {
    pub name: String,
    pub data_type: DataType,
    pub required: bool,
    pub nullable: bool,
    pub default_value: Option<serde_json::Value>,
    pub constraints: Vec<FieldConstraint>,
    pub description: Option<String>,
}

/// 数据类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DataType {
    String,
    Integer,
    Float,
    Boolean,
    DateTime,
    Array(Box<DataType>),
    Object(HashMap<String, DataType>),
    Custom(String),
}

/// 字段约束
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum FieldConstraint {
    MinLength(usize),
    MaxLength(usize),
    MinValue(f64),
    MaxValue(f64),
    Pattern(String),
    Enum(Vec<serde_json::Value>),
    Range(f64, f64),
    NotEmpty,
    Unique,
    Custom(String, serde_json::Value),
}

/// 全局约束
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Constraint {
    RequiredFields(Vec<String>),
    UniqueCombination(Vec<String>),
    ConditionalRequired(String, String, serde_json::Value),
    CrossFieldValidation(String, String, ValidationRule),
    Custom(String, serde_json::Value),
}

/// 验证规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ValidationRule {
    Equal,
    NotEqual,
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,
    Contains,
    NotContains,
    Regex(String),
    Custom(String),
}

/// 验证结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationResult {
    pub is_valid: bool,
    pub errors: Vec<ValidationError>,
    pub warnings: Vec<ValidationWarning>,
    pub statistics: ValidationStatistics,
}

/// 验证错误
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationError {
    pub field: Option<String>,
    pub code: String,
    pub message: String,
    pub severity: ErrorSeverity,
    pub context: HashMap<String, serde_json::Value>,
}

/// 验证警告
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationWarning {
    pub field: Option<String>,
    pub code: String,
    pub message: String,
    pub context: HashMap<String, serde_json::Value>,
}

/// 错误严重程度
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ErrorSeverity {
    Low,
    Medium,
    High,
    Critical,
}

/// 验证统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationStatistics {
    pub total_records: u64,
    pub valid_records: u64,
    pub invalid_records: u64,
    pub error_count: u64,
    pub warning_count: u64,
    pub processing_time_ms: u64,
    pub field_statistics: HashMap<String, FieldStatistics>,
}

/// 字段统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FieldStatistics {
    pub total_values: u64,
    pub null_values: u64,
    pub unique_values: u64,
    pub min_value: Option<serde_json::Value>,
    pub max_value: Option<serde_json::Value>,
    pub mean_value: Option<f64>,
    pub median_value: Option<f64>,
    pub mode_value: Option<serde_json::Value>,
    pub distribution: HashMap<String, u64>,
}

impl DataSchema {
    /// 创建新的数据模式
    pub fn new(name: String, version: String) -> Self {
        Self {
            name,
            version,
            fields: Vec::new(),
            constraints: Vec::new(),
            metadata: HashMap::new(),
        }
    }

    /// 添加字段定义
    pub fn add_field(&mut self, field: FieldDefinition) {
        self.fields.push(field);
    }

    /// 添加约束
    pub fn add_constraint(&mut self, constraint: Constraint) {
        self.constraints.push(constraint);
    }

    /// 获取字段定义
    pub fn get_field(&self, name: &str) -> Option<&FieldDefinition> {
        self.fields.iter().find(|f| f.name == name)
    }

    /// 验证数据
    pub fn validate(&self, data: &serde_json::Value) -> ValidationResult {
        let mut errors = Vec::new();
        let warnings = Vec::new();
        let start_time = std::time::Instant::now();

        // 验证字段
        for field in &self.fields {
            let field_errors = self.validate_field(field, data);
            errors.extend(field_errors);
        }

        // 验证全局约束
        for constraint in &self.constraints {
            let constraint_errors = self.validate_constraint(constraint, data);
            errors.extend(constraint_errors);
        }

        let processing_time = start_time.elapsed().as_millis() as u64;
        let is_valid = errors.is_empty();

        let error_count = errors.len() as u64;
        let warning_count = warnings.len() as u64;
        
        ValidationResult {
            is_valid,
            errors,
            warnings,
            statistics: ValidationStatistics {
                total_records: 1,
                valid_records: if is_valid { 1 } else { 0 },
                invalid_records: if is_valid { 0 } else { 1 },
                error_count,
                warning_count,
                processing_time_ms: processing_time,
                field_statistics: HashMap::new(),
            },
        }
    }

    /// 验证字段
    fn validate_field(&self, field: &FieldDefinition, data: &serde_json::Value) -> Vec<ValidationError> {
        let mut errors = Vec::new();
        let field_value = data.get(&field.name);

        // 检查必需字段
        if field.required && field_value.is_none() {
            errors.push(ValidationError {
                field: Some(field.name.clone()),
                code: "REQUIRED_FIELD_MISSING".to_string(),
                message: format!("Required field '{}' is missing", field.name),
                severity: ErrorSeverity::High,
                context: HashMap::new(),
            });
            return errors;
        }

        // 如果字段不存在且不是必需的，跳过验证
        let field_value = match field_value {
            Some(value) => value,
            None => return errors,
        };

        // 检查空值
        if !field.nullable && field_value.is_null() {
            errors.push(ValidationError {
                field: Some(field.name.clone()),
                code: "NULL_VALUE_NOT_ALLOWED".to_string(),
                message: format!("Field '{}' cannot be null", field.name),
                severity: ErrorSeverity::Medium,
                context: HashMap::new(),
            });
            return errors;
        }

        // 如果值为空且允许为空，跳过类型验证
        if field_value.is_null() {
            return errors;
        }

        // 验证数据类型
        if let Err(type_error) = self.validate_data_type(field_value, &field.data_type) {
            errors.push(ValidationError {
                field: Some(field.name.clone()),
                code: "INVALID_DATA_TYPE".to_string(),
                message: type_error,
                severity: ErrorSeverity::High,
                context: HashMap::new(),
            });
        }

        // 验证字段约束
        for constraint in &field.constraints {
            if let Err(constraint_error) = self.validate_field_constraint(field_value, constraint) {
                errors.push(ValidationError {
                    field: Some(field.name.clone()),
                    code: "CONSTRAINT_VIOLATION".to_string(),
                    message: constraint_error,
                    severity: ErrorSeverity::Medium,
                    context: HashMap::new(),
                });
            }
        }

        errors
    }

    /// 验证数据类型
    fn validate_data_type(&self, value: &serde_json::Value, expected_type: &DataType) -> Result<(), String> {
        match (value, expected_type) {
            (serde_json::Value::String(_), DataType::String) => Ok(()),
            (serde_json::Value::Number(_), DataType::Integer) => {
                if value.as_i64().is_some() {
                    Ok(())
                } else {
                    Err("Expected integer, got float".to_string())
                }
            }
            (serde_json::Value::Number(_), DataType::Float) => Ok(()),
            (serde_json::Value::Bool(_), DataType::Boolean) => Ok(()),
            (serde_json::Value::Array(_), DataType::Array(_)) => Ok(()),
            (serde_json::Value::Object(_), DataType::Object(_)) => Ok(()),
            (serde_json::Value::String(_), DataType::DateTime) => {
                // 简单的日期时间验证
                if value.as_str().unwrap().contains("T") || value.as_str().unwrap().contains("-") {
                    Ok(())
                } else {
                    Err("Invalid datetime format".to_string())
                }
            }
            _ => Err(format!("Type mismatch: expected {:?}, got {:?}", expected_type, value)),
        }
    }

    /// 验证字段约束
    fn validate_field_constraint(&self, value: &serde_json::Value, constraint: &FieldConstraint) -> Result<(), String> {
        match constraint {
            FieldConstraint::MinLength(min) => {
                if let Some(s) = value.as_str() {
                    if s.len() < *min {
                        return Err(format!("String length {} is less than minimum {}", s.len(), min));
                    }
                }
            }
            FieldConstraint::MaxLength(max) => {
                if let Some(s) = value.as_str() {
                    if s.len() > *max {
                        return Err(format!("String length {} exceeds maximum {}", s.len(), max));
                    }
                }
            }
            FieldConstraint::MinValue(min) => {
                if let Some(n) = value.as_f64() {
                    if n < *min {
                        return Err(format!("Value {} is less than minimum {}", n, min));
                    }
                }
            }
            FieldConstraint::MaxValue(max) => {
                if let Some(n) = value.as_f64() {
                    if n > *max {
                        return Err(format!("Value {} exceeds maximum {}", n, max));
                    }
                }
            }
            FieldConstraint::Pattern(pattern) => {
                if let Some(s) = value.as_str() {
                    if !regex::Regex::new(pattern).unwrap().is_match(s) {
                        return Err(format!("Value '{}' does not match pattern '{}'", s, pattern));
                    }
                }
            }
            FieldConstraint::Enum(allowed_values) => {
                if !allowed_values.contains(value) {
                    return Err(format!("Value {:?} is not in allowed values {:?}", value, allowed_values));
                }
            }
            FieldConstraint::Range(min, max) => {
                if let Some(n) = value.as_f64() {
                    if n < *min || n > *max {
                        return Err(format!("Value {} is not in range [{}, {}]", n, min, max));
                    }
                }
            }
            FieldConstraint::NotEmpty => {
                if let Some(s) = value.as_str() {
                    if s.trim().is_empty() {
                        return Err("String cannot be empty".to_string());
                    }
                }
            }
            _ => {} // 其他约束的实现
        }
        Ok(())
    }

    /// 验证全局约束
    fn validate_constraint(&self, constraint: &Constraint, data: &serde_json::Value) -> Vec<ValidationError> {
        let mut errors = Vec::new();

        match constraint {
            Constraint::RequiredFields(fields) => {
                for field in fields {
                    if data.get(field).is_none() {
                        errors.push(ValidationError {
                            field: Some(field.clone()),
                            code: "REQUIRED_FIELD_MISSING".to_string(),
                            message: format!("Required field '{}' is missing", field),
                            severity: ErrorSeverity::High,
                            context: HashMap::new(),
                        });
                    }
                }
            }
            Constraint::UniqueCombination(_fields) => {
                // 这里需要实现唯一性检查，通常需要访问整个数据集
                // 暂时跳过实现
            }
            Constraint::ConditionalRequired(condition_field, required_field, expected_value) => {
                if let Some(condition_value) = data.get(condition_field) {
                    if condition_value == expected_value {
                        if data.get(required_field).is_none() {
                            errors.push(ValidationError {
                                field: Some(required_field.clone()),
                                code: "CONDITIONAL_REQUIRED_FIELD_MISSING".to_string(),
                                message: format!("Field '{}' is required when '{}' equals {:?}", required_field, condition_field, expected_value),
                                severity: ErrorSeverity::Medium,
                                context: HashMap::new(),
                            });
                        }
                    }
                }
            }
            _ => {} // 其他约束的实现
        }

        errors
    }
}

impl fmt::Display for DataType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DataType::String => write!(f, "String"),
            DataType::Integer => write!(f, "Integer"),
            DataType::Float => write!(f, "Float"),
            DataType::Boolean => write!(f, "Boolean"),
            DataType::DateTime => write!(f, "DateTime"),
            DataType::Array(inner) => write!(f, "Array<{}>", inner),
            DataType::Object(fields) => {
                write!(f, "Object{{")?;
                for (i, (name, dtype)) in fields.iter().enumerate() {
                    if i > 0 { write!(f, ", ")?; }
                    write!(f, "{}: {}", name, dtype)?;
                }
                write!(f, "}}")
            }
            DataType::Custom(name) => write!(f, "Custom({})", name),
        }
    }
}

impl fmt::Display for ErrorSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorSeverity::Low => write!(f, "Low"),
            ErrorSeverity::Medium => write!(f, "Medium"),
            ErrorSeverity::High => write!(f, "High"),
            ErrorSeverity::Critical => write!(f, "Critical"),
        }
    }
}
