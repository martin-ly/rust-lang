//! 统一错误处理模块
//!
//! 本模块提供了统一的错误处理机制，包括错误类型定义、
//! 错误转换、错误格式化等。使用Rust的Result类型确保错误安全处理。

use std::fmt;
use thiserror::Error;

/// 模型错误类型
#[derive(Error, Debug)]
pub enum ModelError {
    /// 数学计算错误
    #[error("数学计算错误: {0}")]
    MathError(String),

    /// 数据验证错误
    #[error("数据验证错误: {0}")]
    ValidationError(String),

    /// 配置错误
    #[error("配置错误: {0}")]
    ConfigError(String),

    /// 计算错误
    #[error("计算错误: {0}")]
    ComputationError(String),

    /// IO错误
    #[error("IO错误: {0}")]
    IoError(String),

    /// 序列化错误
    #[error("序列化错误: {0}")]
    SerializationError(String),

    /// 数值溢出错误
    #[error("数值溢出错误: {0}")]
    OverflowError(String),

    /// 除零错误
    #[error("除零错误: {0}")]
    DivisionByZeroError(String),

    /// 收敛失败错误
    #[error("算法收敛失败: {0}")]
    ConvergenceError(String),

    /// 维度不匹配错误
    #[error("维度不匹配: {0}")]
    DimensionMismatchError(String),

    /// 参数范围错误
    #[error("参数超出有效范围: {0}")]
    ParameterRangeError(String),

    /// 系统不稳定错误
    #[error("系统不稳定: {0}")]
    SystemUnstableError(String),

    /// 内存不足错误
    #[error("内存不足: {0}")]
    OutOfMemoryError(String),

    /// 超时错误
    #[error("操作超时: {0}")]
    TimeoutError(String),

    /// 不支持的操作错误
    #[error("不支持的操作: {0}")]
    UnsupportedOperationError(String),

    /// 内部错误
    #[error("内部错误: {0}")]
    InternalError(String),
}

/// 错误严重级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ErrorSeverity {
    /// 信息级别
    Info,
    /// 警告级别
    Warning,
    /// 错误级别
    Error,
    /// 严重错误级别
    Critical,
}

impl Clone for ModelError {
    fn clone(&self) -> Self {
        match self {
            ModelError::MathError(msg) => ModelError::MathError(msg.clone()),
            ModelError::ValidationError(msg) => ModelError::ValidationError(msg.clone()),
            ModelError::ConfigError(msg) => ModelError::ConfigError(msg.clone()),
            ModelError::ComputationError(msg) => ModelError::ComputationError(msg.clone()),
            ModelError::IoError(msg) => ModelError::IoError(msg.clone()),
            ModelError::SerializationError(msg) => ModelError::SerializationError(msg.clone()),
            ModelError::OverflowError(msg) => ModelError::OverflowError(msg.clone()),
            ModelError::DivisionByZeroError(msg) => ModelError::DivisionByZeroError(msg.clone()),
            ModelError::ConvergenceError(msg) => ModelError::ConvergenceError(msg.clone()),
            ModelError::DimensionMismatchError(msg) => {
                ModelError::DimensionMismatchError(msg.clone())
            }
            ModelError::ParameterRangeError(msg) => ModelError::ParameterRangeError(msg.clone()),
            ModelError::SystemUnstableError(msg) => ModelError::SystemUnstableError(msg.clone()),
            ModelError::OutOfMemoryError(msg) => ModelError::OutOfMemoryError(msg.clone()),
            ModelError::TimeoutError(msg) => ModelError::TimeoutError(msg.clone()),
            ModelError::UnsupportedOperationError(msg) => {
                ModelError::UnsupportedOperationError(msg.clone())
            }
            ModelError::InternalError(msg) => ModelError::InternalError(msg.clone()),
        }
    }
}

impl From<std::io::Error> for ModelError {
    fn from(error: std::io::Error) -> Self {
        ModelError::IoError(error.to_string())
    }
}

impl From<serde_json::Error> for ModelError {
    fn from(error: serde_json::Error) -> Self {
        ModelError::SerializationError(error.to_string())
    }
}

impl ModelError {
    /// 获取错误严重级别
    pub fn severity(&self) -> ErrorSeverity {
        match self {
            ModelError::MathError(_) => ErrorSeverity::Error,
            ModelError::ValidationError(_) => ErrorSeverity::Warning,
            ModelError::ConfigError(_) => ErrorSeverity::Error,
            ModelError::ComputationError(_) => ErrorSeverity::Error,
            ModelError::IoError(_) => ErrorSeverity::Error,
            ModelError::SerializationError(_) => ErrorSeverity::Error,
            ModelError::OverflowError(_) => ErrorSeverity::Critical,
            ModelError::DivisionByZeroError(_) => ErrorSeverity::Critical,
            ModelError::ConvergenceError(_) => ErrorSeverity::Warning,
            ModelError::DimensionMismatchError(_) => ErrorSeverity::Error,
            ModelError::ParameterRangeError(_) => ErrorSeverity::Warning,
            ModelError::SystemUnstableError(_) => ErrorSeverity::Critical,
            ModelError::OutOfMemoryError(_) => ErrorSeverity::Critical,
            ModelError::TimeoutError(_) => ErrorSeverity::Warning,
            ModelError::UnsupportedOperationError(_) => ErrorSeverity::Error,
            ModelError::InternalError(_) => ErrorSeverity::Critical,
        }
    }

    /// 检查是否为严重错误
    pub fn is_critical(&self) -> bool {
        self.severity() >= ErrorSeverity::Critical
    }

    /// 检查是否为可恢复错误
    pub fn is_recoverable(&self) -> bool {
        self.severity() <= ErrorSeverity::Warning
    }

    /// 获取错误代码
    pub fn error_code(&self) -> &'static str {
        match self {
            ModelError::MathError(_) => "MATH_001",
            ModelError::ValidationError(_) => "VALID_001",
            ModelError::ConfigError(_) => "CONFIG_001",
            ModelError::ComputationError(_) => "COMP_001",
            ModelError::IoError(_) => "IO_001",
            ModelError::SerializationError(_) => "SERIAL_001",
            ModelError::OverflowError(_) => "OVERFLOW_001",
            ModelError::DivisionByZeroError(_) => "DIVZERO_001",
            ModelError::ConvergenceError(_) => "CONV_001",
            ModelError::DimensionMismatchError(_) => "DIM_001",
            ModelError::ParameterRangeError(_) => "PARAM_001",
            ModelError::SystemUnstableError(_) => "UNSTABLE_001",
            ModelError::OutOfMemoryError(_) => "MEMORY_001",
            ModelError::TimeoutError(_) => "TIMEOUT_001",
            ModelError::UnsupportedOperationError(_) => "UNSUPPORTED_001",
            ModelError::InternalError(_) => "INTERNAL_001",
        }
    }

    /// 获取错误建议
    pub fn suggestion(&self) -> Option<&'static str> {
        match self {
            ModelError::MathError(_) => Some("检查输入数据的有效性和数值范围"),
            ModelError::ValidationError(_) => Some("验证输入数据格式和约束条件"),
            ModelError::ConfigError(_) => Some("检查配置文件格式和参数设置"),
            ModelError::ComputationError(_) => Some("检查计算参数和算法设置"),
            ModelError::IoError(_) => Some("检查文件路径和权限设置"),
            ModelError::SerializationError(_) => Some("检查数据格式和序列化设置"),
            ModelError::OverflowError(_) => Some("使用更高精度的数据类型或调整算法参数"),
            ModelError::DivisionByZeroError(_) => Some("检查除数是否为零，添加边界条件处理"),
            ModelError::ConvergenceError(_) => Some("增加迭代次数或调整收敛参数"),
            ModelError::DimensionMismatchError(_) => Some("检查矩阵和向量的维度匹配"),
            ModelError::ParameterRangeError(_) => Some("检查参数是否在有效范围内"),
            ModelError::SystemUnstableError(_) => Some("调整系统参数以确保稳定性"),
            ModelError::OutOfMemoryError(_) => Some("减少数据规模或使用更高效的内存管理"),
            ModelError::TimeoutError(_) => Some("增加超时时间或优化算法性能"),
            ModelError::UnsupportedOperationError(_) => Some("使用支持的操作或升级到兼容版本"),
            ModelError::InternalError(_) => Some("联系技术支持或查看详细日志"),
        }
    }
}

impl fmt::Display for ErrorSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorSeverity::Info => write!(f, "INFO"),
            ErrorSeverity::Warning => write!(f, "WARNING"),
            ErrorSeverity::Error => write!(f, "ERROR"),
            ErrorSeverity::Critical => write!(f, "CRITICAL"),
        }
    }
}

/// 错误上下文
#[derive(Debug, Clone)]
pub struct ErrorContext {
    /// 错误发生的位置
    pub location: String,
    /// 错误发生的时间
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// 额外的上下文信息
    pub additional_info: std::collections::HashMap<String, String>,
}

impl ErrorContext {
    /// 创建新的错误上下文
    pub fn new(location: String) -> Self {
        Self {
            location,
            timestamp: chrono::Utc::now(),
            additional_info: std::collections::HashMap::new(),
        }
    }

    /// 添加额外信息
    pub fn with_info(mut self, key: String, value: String) -> Self {
        self.additional_info.insert(key, value);
        self
    }
}

/// 带上下文的错误
#[derive(Debug)]
pub struct ContextualError {
    /// 原始错误
    pub error: ModelError,
    /// 错误上下文
    pub context: ErrorContext,
}

impl ContextualError {
    /// 创建带上下文的错误
    pub fn new(error: ModelError, context: ErrorContext) -> Self {
        Self { error, context }
    }

    /// 创建带位置的错误
    pub fn with_location(error: ModelError, location: &str) -> Self {
        Self::new(error, ErrorContext::new(location.to_string()))
    }

    /// 获取格式化的错误信息
    pub fn format(&self) -> String {
        let mut result = format!(
            "[{}] {}: {}",
            self.error.severity(),
            self.error.error_code(),
            self.error
        );

        if let Some(suggestion) = self.error.suggestion() {
            result.push_str(&format!("\n建议: {}", suggestion));
        }

        result.push_str(&format!(
            "\n位置: {}\n时间: {}",
            self.context.location,
            self.context.timestamp.format("%Y-%m-%d %H:%M:%S UTC")
        ));

        if !self.context.additional_info.is_empty() {
            result.push_str("\n额外信息:");
            for (key, value) in &self.context.additional_info {
                result.push_str(&format!("\n  {}: {}", key, value));
            }
        }

        result
    }
}

impl fmt::Display for ContextualError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format())
    }
}

/// 错误处理结果类型
pub type Result<T> = std::result::Result<T, ModelError>;

/// 带上下文的错误处理结果类型
pub type ContextualResult<T> = std::result::Result<T, ContextualError>;

/// 错误处理工具
pub struct ErrorHandler;

impl ErrorHandler {
    /// 创建数学错误
    pub fn math_error(message: &str) -> ModelError {
        ModelError::MathError(message.to_string())
    }

    /// 创建验证错误
    pub fn validation_error(message: &str) -> ModelError {
        ModelError::ValidationError(message.to_string())
    }

    /// 创建配置错误
    pub fn config_error(message: &str) -> ModelError {
        ModelError::ConfigError(message.to_string())
    }

    /// 创建计算错误
    pub fn computation_error(message: &str) -> ModelError {
        ModelError::ComputationError(message.to_string())
    }

    /// 创建溢出错误
    pub fn overflow_error(message: &str) -> ModelError {
        ModelError::OverflowError(message.to_string())
    }

    /// 创建除零错误
    pub fn division_by_zero_error(message: &str) -> ModelError {
        ModelError::DivisionByZeroError(message.to_string())
    }

    /// 创建收敛错误
    pub fn convergence_error(message: &str) -> ModelError {
        ModelError::ConvergenceError(message.to_string())
    }

    /// 创建维度不匹配错误
    pub fn dimension_mismatch_error(message: &str) -> ModelError {
        ModelError::DimensionMismatchError(message.to_string())
    }

    /// 创建参数范围错误
    pub fn parameter_range_error(message: &str) -> ModelError {
        ModelError::ParameterRangeError(message.to_string())
    }

    /// 创建系统不稳定错误
    pub fn system_unstable_error(message: &str) -> ModelError {
        ModelError::SystemUnstableError(message.to_string())
    }

    /// 创建带上下文的错误
    pub fn contextual_error(error: ModelError, location: &str) -> ContextualError {
        ContextualError::with_location(error, location)
    }

    /// 处理错误并记录
    pub fn handle_error(error: &ModelError, location: &str) -> String {
        let contextual = ContextualError::with_location(error.clone(), location);
        contextual.format()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_model_error_severity() {
        let math_error = ModelError::MathError("test".to_string());
        assert_eq!(math_error.severity(), ErrorSeverity::Error);
        assert!(!math_error.is_critical());
        assert!(!math_error.is_recoverable());

        let overflow_error = ModelError::OverflowError("test".to_string());
        assert_eq!(overflow_error.severity(), ErrorSeverity::Critical);
        assert!(overflow_error.is_critical());
        assert!(!overflow_error.is_recoverable());

        let validation_error = ModelError::ValidationError("test".to_string());
        assert_eq!(validation_error.severity(), ErrorSeverity::Warning);
        assert!(!validation_error.is_critical());
        assert!(validation_error.is_recoverable());
    }

    #[test]
    fn test_model_error_codes() {
        let math_error = ModelError::MathError("test".to_string());
        assert_eq!(math_error.error_code(), "MATH_001");

        let overflow_error = ModelError::OverflowError("test".to_string());
        assert_eq!(overflow_error.error_code(), "OVERFLOW_001");
    }

    #[test]
    fn test_model_error_suggestions() {
        let math_error = ModelError::MathError("test".to_string());
        assert!(math_error.suggestion().is_some());

        let overflow_error = ModelError::OverflowError("test".to_string());
        assert!(overflow_error.suggestion().is_some());
    }

    #[test]
    fn test_error_context() {
        let context = ErrorContext::new("test_location".to_string())
            .with_info("key1".to_string(), "value1".to_string())
            .with_info("key2".to_string(), "value2".to_string());

        assert_eq!(context.location, "test_location");
        assert_eq!(context.additional_info.len(), 2);
        assert_eq!(
            context.additional_info.get("key1"),
            Some(&"value1".to_string())
        );
    }

    #[test]
    fn test_contextual_error() {
        let error = ModelError::MathError("test error".to_string());
        let contextual = ContextualError::with_location(error, "test_location");

        let formatted = contextual.format();
        assert!(formatted.contains("test error"));
        assert!(formatted.contains("test_location"));
        assert!(formatted.contains("MATH_001"));
    }

    #[test]
    fn test_error_handler() {
        let math_error = ErrorHandler::math_error("test");
        assert!(matches!(math_error, ModelError::MathError(_)));

        let overflow_error = ErrorHandler::overflow_error("test");
        assert!(matches!(overflow_error, ModelError::OverflowError(_)));

        let contextual = ErrorHandler::contextual_error(math_error, "test_location");
        assert!(contextual.format().contains("test_location"));
    }

    #[test]
    fn test_error_severity_display() {
        assert_eq!(ErrorSeverity::Info.to_string(), "INFO");
        assert_eq!(ErrorSeverity::Warning.to_string(), "WARNING");
        assert_eq!(ErrorSeverity::Error.to_string(), "ERROR");
        assert_eq!(ErrorSeverity::Critical.to_string(), "CRITICAL");
    }

    #[test]
    fn test_error_severity_ordering() {
        assert!(ErrorSeverity::Info < ErrorSeverity::Warning);
        assert!(ErrorSeverity::Warning < ErrorSeverity::Error);
        assert!(ErrorSeverity::Error < ErrorSeverity::Critical);
    }
}
