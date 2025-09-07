//! 数据验证模块
//! 
//! 提供数据质量检查、验证和报告功能

use crate::data_processing::DataFrame;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 数据验证器
#[derive(Debug, Clone)]
pub struct DataValidator {
    pub name: String,
    pub rules: Vec<ValidationRule>,
}

/// 验证规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ValidationRule {
    /// 非空检查
    NotNull { column: String },
    /// 数值范围检查
    Range { column: String, min: f64, max: f64 },
    /// 唯一性检查
    Unique { column: String },
    /// 数据类型检查
    DataType { column: String, expected_type: DataType },
    /// 格式检查
    Format { column: String, pattern: String },
    /// 自定义检查
    Custom { column: String, validator: String },
}

/// 数据类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DataType {
    /// 整数
    Integer,
    /// 浮点数
    Float,
    /// 字符串
    String,
    /// 布尔值
    Boolean,
    /// 日期
    Date,
}

/// 验证结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationResult {
    pub is_valid: bool,
    pub errors: Vec<ValidationError>,
    pub warnings: Vec<ValidationWarning>,
    pub summary: ValidationSummary,
}

/// 验证错误
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationError {
    pub rule: String,
    pub column: String,
    pub row_index: Option<usize>,
    pub message: String,
    pub severity: ErrorSeverity,
}

/// 验证警告
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationWarning {
    pub rule: String,
    pub column: String,
    pub row_index: Option<usize>,
    pub message: String,
}

/// 错误严重程度
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ErrorSeverity {
    /// 严重错误
    Critical,
    /// 错误
    Error,
    /// 警告
    Warning,
    /// 信息
    Info,
}

/// 验证摘要
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ValidationSummary {
    pub total_rows: usize,
    pub total_columns: usize,
    pub error_count: usize,
    pub warning_count: usize,
    pub valid_rows: usize,
    pub invalid_rows: usize,
    pub data_quality_score: f64,
}

impl DataValidator {
    /// 创建新的数据验证器
    pub fn new(name: String) -> Self {
        Self {
            name,
            rules: Vec::new(),
        }
    }
    
    /// 添加验证规则
    pub fn add_rule(&mut self, rule: ValidationRule) {
        self.rules.push(rule);
    }
    
    /// 验证数据
    pub fn validate(&self, df: &DataFrame) -> ValidationResult {
        let mut errors = Vec::new();
        let warnings = Vec::new();
        
        for rule in &self.rules {
            let rule_errors = self.apply_rule(df, rule);
            errors.extend(rule_errors);
        }
        
        let summary = self.create_summary(df, &errors, &warnings);
        let is_valid = errors.iter().all(|e| !matches!(e.severity, ErrorSeverity::Critical | ErrorSeverity::Error));
        
        ValidationResult {
            is_valid,
            errors,
            warnings,
            summary,
        }
    }
    
    /// 应用单个验证规则
    fn apply_rule(&self, df: &DataFrame, rule: &ValidationRule) -> Vec<ValidationError> {
        let mut errors = Vec::new();
        
        match rule {
            ValidationRule::NotNull { column } => {
                if let Some(col_idx) = df.columns.iter().position(|col| col == column) {
                    for (row_idx, row) in df.data.iter().enumerate() {
                        if row[col_idx].is_nan() {
                            errors.push(ValidationError {
                                rule: "NotNull".to_string(),
                                column: column.clone(),
                                row_index: Some(row_idx),
                                message: format!("列 '{}' 在第 {} 行包含空值", column, row_idx),
                                severity: ErrorSeverity::Error,
                            });
                        }
                    }
                } else {
                    errors.push(ValidationError {
                        rule: "NotNull".to_string(),
                        column: column.clone(),
                        row_index: None,
                        message: format!("列 '{}' 不存在", column),
                        severity: ErrorSeverity::Critical,
                    });
                }
            }
            ValidationRule::Range { column, min, max } => {
                if let Some(col_idx) = df.columns.iter().position(|col| col == column) {
                    for (row_idx, row) in df.data.iter().enumerate() {
                        let value = row[col_idx];
                        if value < *min || value > *max {
                            errors.push(ValidationError {
                                rule: "Range".to_string(),
                                column: column.clone(),
                                row_index: Some(row_idx),
                                message: format!("列 '{}' 在第 {} 行的值 {} 超出范围 [{}, {}]", 
                                    column, row_idx, value, min, max),
                                severity: ErrorSeverity::Error,
                            });
                        }
                    }
                } else {
                    errors.push(ValidationError {
                        rule: "Range".to_string(),
                        column: column.clone(),
                        row_index: None,
                        message: format!("列 '{}' 不存在", column),
                        severity: ErrorSeverity::Critical,
                    });
                }
            }
            ValidationRule::Unique { column } => {
                if let Some(col_idx) = df.columns.iter().position(|col| col == column) {
                    let mut seen_values = HashMap::new();
                    for (row_idx, row) in df.data.iter().enumerate() {
                        let value = row[col_idx];
                        if let Some(&first_occurrence) = seen_values.get(&value) {
                            errors.push(ValidationError {
                                rule: "Unique".to_string(),
                                column: column.clone(),
                                row_index: Some(row_idx),
                                message: format!("列 '{}' 在第 {} 行的值 {} 与第 {} 行重复", 
                                    column, row_idx, value, first_occurrence),
                                severity: ErrorSeverity::Warning,
                            });
                        } else {
                            seen_values.insert(value, row_idx);
                        }
                    }
                } else {
                    errors.push(ValidationError {
                        rule: "Unique".to_string(),
                        column: column.clone(),
                        row_index: None,
                        message: format!("列 '{}' 不存在", column),
                        severity: ErrorSeverity::Critical,
                    });
                }
            }
            ValidationRule::DataType { column, expected_type } => {
                if let Some(col_idx) = df.columns.iter().position(|col| col == column) {
                    for (row_idx, row) in df.data.iter().enumerate() {
                        let value = row[col_idx];
                        let is_valid_type = match expected_type {
                            DataType::Integer => value.fract() == 0.0,
                            DataType::Float => true, // 所有数值都是浮点数
                            DataType::String => false, // 简化实现：不支持字符串
                            DataType::Boolean => value == 0.0 || value == 1.0,
                            DataType::Date => false, // 简化实现：不支持日期
                        };
                        
                        if !is_valid_type {
                            errors.push(ValidationError {
                                rule: "DataType".to_string(),
                                column: column.clone(),
                                row_index: Some(row_idx),
                                message: format!("列 '{}' 在第 {} 行的值 {} 不符合期望的数据类型 {:?}", 
                                    column, row_idx, value, expected_type),
                                severity: ErrorSeverity::Error,
                            });
                        }
                    }
                } else {
                    errors.push(ValidationError {
                        rule: "DataType".to_string(),
                        column: column.clone(),
                        row_index: None,
                        message: format!("列 '{}' 不存在", column),
                        severity: ErrorSeverity::Critical,
                    });
                }
            }
            ValidationRule::Format { column, pattern: _ } => {
                // 简化实现：格式检查
                if let Some(col_idx) = df.columns.iter().position(|col| col == column) {
                    for (row_idx, row) in df.data.iter().enumerate() {
                        let value = row[col_idx];
                        if value.is_infinite() {
                            errors.push(ValidationError {
                                rule: "Format".to_string(),
                                column: column.clone(),
                                row_index: Some(row_idx),
                                message: format!("列 '{}' 在第 {} 行包含无穷大值", column, row_idx),
                                severity: ErrorSeverity::Error,
                            });
                        }
                    }
                }
            }
            ValidationRule::Custom { column, validator: _ } => {
                // 简化实现：自定义验证
                if df.columns.iter().position(|col| col == column).is_none() {
                    errors.push(ValidationError {
                        rule: "Custom".to_string(),
                        column: column.clone(),
                        row_index: None,
                        message: format!("列 '{}' 不存在", column),
                        severity: ErrorSeverity::Critical,
                    });
                }
            }
        }
        
        errors
    }
    
    /// 创建验证摘要
    fn create_summary(&self, df: &DataFrame, errors: &[ValidationError], warnings: &[ValidationWarning]) -> ValidationSummary {
        let total_rows = df.len();
        let total_columns = df.column_count();
        let error_count = errors.len();
        let warning_count = warnings.len();
        
        let invalid_rows: std::collections::HashSet<usize> = errors.iter()
            .filter_map(|e| e.row_index)
            .collect();
        
        let valid_rows = total_rows - invalid_rows.len();
        let invalid_rows_count = invalid_rows.len();
        
        // 计算数据质量分数 (0-100)
        let quality_score = if total_rows > 0 {
            let error_penalty = (error_count as f64 / total_rows as f64) * 50.0;
            let warning_penalty = (warning_count as f64 / total_rows as f64) * 10.0;
            (100.0 - error_penalty - warning_penalty).max(0.0)
        } else {
            100.0
        };
        
        ValidationSummary {
            total_rows,
            total_columns,
            error_count,
            warning_count,
            valid_rows,
            invalid_rows: invalid_rows_count,
            data_quality_score: quality_score,
        }
    }
}

impl ValidationResult {
    /// 获取错误报告
    pub fn get_error_report(&self) -> String {
        let mut report = String::new();
        report.push_str(&format!("数据验证报告\n"));
        report.push_str(&format!("==============\n"));
        report.push_str(&format!("验证状态: {}\n", if self.is_valid { "通过" } else { "失败" }));
        report.push_str(&format!("数据质量分数: {:.2}/100\n", self.summary.data_quality_score));
        report.push_str(&format!("总行数: {}\n", self.summary.total_rows));
        report.push_str(&format!("有效行数: {}\n", self.summary.valid_rows));
        report.push_str(&format!("无效行数: {}\n", self.summary.invalid_rows));
        report.push_str(&format!("错误数量: {}\n", self.summary.error_count));
        report.push_str(&format!("警告数量: {}\n", self.summary.warning_count));
        
        if !self.errors.is_empty() {
            report.push_str(&format!("\n错误详情:\n"));
            for error in &self.errors {
                report.push_str(&format!("- {}: {}\n", error.rule, error.message));
            }
        }
        
        if !self.warnings.is_empty() {
            report.push_str(&format!("\n警告详情:\n"));
            for warning in &self.warnings {
                report.push_str(&format!("- {}: {}\n", warning.rule, warning.message));
            }
        }
        
        report
    }
    
    /// 检查是否有严重错误
    pub fn has_critical_errors(&self) -> bool {
        self.errors.iter().any(|e| matches!(e.severity, ErrorSeverity::Critical))
    }
    
    /// 获取按严重程度分组的错误
    pub fn get_errors_by_severity(&self) -> HashMap<ErrorSeverity, Vec<&ValidationError>> {
        let mut grouped: HashMap<ErrorSeverity, Vec<&ValidationError>> = HashMap::new();
        
        for error in &self.errors {
            grouped.entry(error.severity.clone()).or_insert_with(Vec::new).push(error);
        }
        
        grouped
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_validator_creation() {
        let mut validator = DataValidator::new("test".to_string());
        validator.add_rule(ValidationRule::NotNull { column: "col1".to_string() });
        
        assert_eq!(validator.rules.len(), 1);
    }
    
    #[test]
    fn test_not_null_validation() {
        let mut df = DataFrame::new("test".to_string(), vec!["col1".to_string()]);
        df.add_row(vec![1.0]).unwrap();
        df.add_row(vec![f64::NAN]).unwrap(); // 空值
        
        let mut validator = DataValidator::new("test".to_string());
        validator.add_rule(ValidationRule::NotNull { column: "col1".to_string() });
        
        let result = validator.validate(&df);
        assert!(!result.is_valid);
        assert_eq!(result.errors.len(), 1);
    }
    
    #[test]
    fn test_range_validation() {
        let mut df = DataFrame::new("test".to_string(), vec!["col1".to_string()]);
        df.add_row(vec![5.0]).unwrap();
        df.add_row(vec![15.0]).unwrap(); // 超出范围
        
        let mut validator = DataValidator::new("test".to_string());
        validator.add_rule(ValidationRule::Range { 
            column: "col1".to_string(), 
            min: 0.0, 
            max: 10.0 
        });
        
        let result = validator.validate(&df);
        assert!(!result.is_valid);
        assert_eq!(result.errors.len(), 1);
    }
    
    #[test]
    fn test_unique_validation() {
        let mut df = DataFrame::new("test".to_string(), vec!["col1".to_string()]);
        df.add_row(vec![1.0]).unwrap();
        df.add_row(vec![2.0]).unwrap();
        df.add_row(vec![1.0]).unwrap(); // 重复值
        
        let mut validator = DataValidator::new("test".to_string());
        validator.add_rule(ValidationRule::Unique { column: "col1".to_string() });
        
        let result = validator.validate(&df);
        assert!(result.is_valid); // 唯一性检查产生警告，不是错误
        assert_eq!(result.warnings.len(), 1);
    }
    
    #[test]
    fn test_validation_summary() {
        let mut df = DataFrame::new("test".to_string(), vec!["col1".to_string()]);
        df.add_row(vec![1.0]).unwrap();
        df.add_row(vec![2.0]).unwrap();
        
        let mut validator = DataValidator::new("test".to_string());
        validator.add_rule(ValidationRule::NotNull { column: "col1".to_string() });
        
        let result = validator.validate(&df);
        assert_eq!(result.summary.total_rows, 2);
        assert_eq!(result.summary.valid_rows, 2);
        assert_eq!(result.summary.error_count, 0);
    }
}
