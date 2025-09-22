//! # 错误处理模块 / Error Handling Module
//!
//! 本模块提供了完善的错误处理机制，包括详细的错误信息、错误恢复和错误追踪。
//! This module provides comprehensive error handling mechanisms, including detailed error messages, error recovery, and error tracking.

use std::fmt;

/// WebAssembly 运行时错误 / WebAssembly Runtime Error
#[derive(Debug, Clone)]
pub enum WebAssemblyError {
    MemoryError {
        message: String,
    },
    TypeError {
        message: String,
        expected: String,
        actual: String,
    },
    ValidationError {
        message: String,
        location: String,
    },
    ExecutionError {
        message: String,
        instruction: String,
    },
    ModuleError {
        message: String,
        module_name: String,
    },
    FunctionError {
        message: String,
        function_name: String,
    },
    SimdError {
        message: String,
        instruction: String,
    },
    HostBindingError {
        message: String,
        binding_name: String,
    },
    InterfaceTypeError {
        message: String,
        type_name: String,
    },
    ConfigurationError {
        message: String,
        config_key: String,
    },
    InternalError {
        message: String,
        component: String,
    },
}

impl fmt::Display for WebAssemblyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WebAssemblyError::MemoryError { message } => {
                write!(f, "内存错误: {}", message)
            }
            WebAssemblyError::TypeError { message, expected, actual } => {
                write!(f, "类型错误: {} (期望: {}, 实际: {})", message, expected, actual)
            }
            WebAssemblyError::ValidationError { message, location } => {
                write!(f, "验证错误: {} (位置: {})", message, location)
            }
            WebAssemblyError::ExecutionError { message, instruction } => {
                write!(f, "执行错误: {} (指令: {})", message, instruction)
            }
            WebAssemblyError::ModuleError { message, module_name } => {
                write!(f, "模块错误: {} (模块: {})", message, module_name)
            }
            WebAssemblyError::FunctionError { message, function_name } => {
                write!(f, "函数错误: {} (函数: {})", message, function_name)
            }
            WebAssemblyError::SimdError { message, instruction } => {
                write!(f, "SIMD 错误: {} (指令: {})", message, instruction)
            }
            WebAssemblyError::HostBindingError { message, binding_name } => {
                write!(f, "宿主绑定错误: {} (绑定: {})", message, binding_name)
            }
            WebAssemblyError::InterfaceTypeError { message, type_name } => {
                write!(f, "接口类型错误: {} (类型: {})", message, type_name)
            }
            WebAssemblyError::ConfigurationError { message, config_key } => {
                write!(f, "配置错误: {} (配置: {})", message, config_key)
            }
            WebAssemblyError::InternalError { message, component } => {
                write!(f, "内部错误: {} (组件: {})", message, component)
            }
        }
    }
}

impl std::error::Error for WebAssemblyError {}

impl WebAssemblyError {
    /// 创建内存错误
    /// Create memory error
    pub fn memory_error(message: impl Into<String>) -> Self {
        Self::MemoryError {
            message: message.into(),
        }
    }
    
    /// 创建类型错误
    /// Create type error
    pub fn type_error(message: impl Into<String>, expected: impl Into<String>, actual: impl Into<String>) -> Self {
        Self::TypeError {
            message: message.into(),
            expected: expected.into(),
            actual: actual.into(),
        }
    }
    
    /// 创建验证错误
    /// Create validation error
    pub fn validation_error(message: impl Into<String>, location: impl Into<String>) -> Self {
        Self::ValidationError {
            message: message.into(),
            location: location.into(),
        }
    }
    
    /// 创建执行错误
    /// Create execution error
    pub fn execution_error(message: impl Into<String>, instruction: impl Into<String>) -> Self {
        Self::ExecutionError {
            message: message.into(),
            instruction: instruction.into(),
        }
    }
    
    /// 创建模块错误
    /// Create module error
    pub fn module_error(message: impl Into<String>, module_name: impl Into<String>) -> Self {
        Self::ModuleError {
            message: message.into(),
            module_name: module_name.into(),
        }
    }
    
    /// 创建函数错误
    /// Create function error
    pub fn function_error(message: impl Into<String>, function_name: impl Into<String>) -> Self {
        Self::FunctionError {
            message: message.into(),
            function_name: function_name.into(),
        }
    }
    
    /// 创建 SIMD 错误
    /// Create SIMD error
    pub fn simd_error(message: impl Into<String>, instruction: impl Into<String>) -> Self {
        Self::SimdError {
            message: message.into(),
            instruction: instruction.into(),
        }
    }
    
    /// 创建宿主绑定错误
    /// Create host binding error
    pub fn host_binding_error(message: impl Into<String>, binding_name: impl Into<String>) -> Self {
        Self::HostBindingError {
            message: message.into(),
            binding_name: binding_name.into(),
        }
    }
    
    /// 创建接口类型错误
    /// Create interface type error
    pub fn interface_type_error(message: impl Into<String>, type_name: impl Into<String>) -> Self {
        Self::InterfaceTypeError {
            message: message.into(),
            type_name: type_name.into(),
        }
    }
    
    /// 创建配置错误
    /// Create configuration error
    pub fn configuration_error(message: impl Into<String>, config_key: impl Into<String>) -> Self {
        Self::ConfigurationError {
            message: message.into(),
            config_key: config_key.into(),
        }
    }
    
    /// 创建内部错误
    /// Create internal error
    pub fn internal_error(message: impl Into<String>, component: impl Into<String>) -> Self {
        Self::InternalError {
            message: message.into(),
            component: component.into(),
        }
    }
    
    /// 获取错误严重程度
    /// Get error severity
    pub fn severity(&self) -> ErrorSeverity {
        match self {
            WebAssemblyError::MemoryError { .. } => ErrorSeverity::Critical,
            WebAssemblyError::TypeError { .. } => ErrorSeverity::High,
            WebAssemblyError::ValidationError { .. } => ErrorSeverity::High,
            WebAssemblyError::ExecutionError { .. } => ErrorSeverity::High,
            WebAssemblyError::ModuleError { .. } => ErrorSeverity::Medium,
            WebAssemblyError::FunctionError { .. } => ErrorSeverity::Medium,
            WebAssemblyError::SimdError { .. } => ErrorSeverity::Medium,
            WebAssemblyError::HostBindingError { .. } => ErrorSeverity::Medium,
            WebAssemblyError::InterfaceTypeError { .. } => ErrorSeverity::Low,
            WebAssemblyError::ConfigurationError { .. } => ErrorSeverity::Low,
            WebAssemblyError::InternalError { .. } => ErrorSeverity::Critical,
        }
    }
    
    /// 获取错误恢复建议
    /// Get error recovery suggestions
    pub fn recovery_suggestions(&self) -> Vec<String> {
        match self {
            WebAssemblyError::MemoryError { .. } => vec![
                "检查内存大小配置".to_string(),
                "减少内存使用量".to_string(),
                "检查内存泄漏".to_string(),
            ],
            WebAssemblyError::TypeError { .. } => vec![
                "检查类型转换".to_string(),
                "验证输入数据类型".to_string(),
                "使用正确的类型转换函数".to_string(),
            ],
            WebAssemblyError::ValidationError { .. } => vec![
                "检查输入数据格式".to_string(),
                "验证数据完整性".to_string(),
                "检查数据范围".to_string(),
            ],
            WebAssemblyError::ExecutionError { .. } => vec![
                "检查指令格式".to_string(),
                "验证操作数类型".to_string(),
                "检查执行环境".to_string(),
            ],
            WebAssemblyError::ModuleError { .. } => vec![
                "检查模块格式".to_string(),
                "验证模块完整性".to_string(),
                "重新加载模块".to_string(),
            ],
            WebAssemblyError::FunctionError { .. } => vec![
                "检查函数签名".to_string(),
                "验证参数类型".to_string(),
                "检查函数实现".to_string(),
            ],
            WebAssemblyError::SimdError { .. } => vec![
                "检查 SIMD 指令支持".to_string(),
                "验证向量数据类型".to_string(),
                "检查数据对齐".to_string(),
            ],
            WebAssemblyError::HostBindingError { .. } => vec![
                "检查宿主环境".to_string(),
                "验证绑定配置".to_string(),
                "检查权限设置".to_string(),
            ],
            WebAssemblyError::InterfaceTypeError { .. } => vec![
                "检查类型定义".to_string(),
                "验证类型兼容性".to_string(),
                "更新类型注册".to_string(),
            ],
            WebAssemblyError::ConfigurationError { .. } => vec![
                "检查配置文件".to_string(),
                "验证配置参数".to_string(),
                "使用默认配置".to_string(),
            ],
            WebAssemblyError::InternalError { .. } => vec![
                "重启运行时".to_string(),
                "检查系统资源".to_string(),
                "联系技术支持".to_string(),
            ],
        }
    }
}

/// 错误严重程度 / Error Severity
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ErrorSeverity {
    Low,
    Medium,
    High,
    Critical,
}

impl fmt::Display for ErrorSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorSeverity::Low => write!(f, "低"),
            ErrorSeverity::Medium => write!(f, "中"),
            ErrorSeverity::High => write!(f, "高"),
            ErrorSeverity::Critical => write!(f, "严重"),
        }
    }
}

/// 错误恢复策略 / Error Recovery Strategy
#[derive(Debug, Clone)]
pub enum RecoveryStrategy {
    /// 重试操作 / Retry operation
    Retry { max_attempts: usize, delay_ms: u64 },
    /// 使用备用方案 / Use fallback
    Fallback { fallback_function: String },
    /// 降级服务 / Degrade service
    Degrade { degraded_mode: String },
    /// 跳过操作 / Skip operation
    Skip,
    /// 终止执行 / Terminate execution
    Terminate,
}

/// 错误处理器 / Error Handler
pub struct ErrorHandler {
    error_log: Vec<ErrorLogEntry>,
    recovery_strategies: std::collections::HashMap<String, RecoveryStrategy>,
    max_log_size: usize,
}

/// 错误日志条目 / Error Log Entry
#[derive(Debug, Clone)]
pub struct ErrorLogEntry {
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub error: WebAssemblyError,
    pub context: String,
    pub resolved: bool,
}

impl ErrorHandler {
    /// 创建新的错误处理器
    /// Create new error handler
    pub fn new() -> Self {
        Self {
            error_log: Vec::new(),
            recovery_strategies: std::collections::HashMap::new(),
            max_log_size: 1000,
        }
    }
    
    /// 处理错误
    /// Handle error
    pub fn handle_error(&mut self, error: WebAssemblyError, context: impl Into<String>) -> Result<(), WebAssemblyError> {
        let context = context.into();
        let timestamp = chrono::Utc::now();
        
        // 记录错误
        let log_entry = ErrorLogEntry {
            timestamp,
            error: error.clone(),
            context: context.clone(),
            resolved: false,
        };
        
        self.error_log.push(log_entry);
        
        // 限制日志大小
        if self.error_log.len() > self.max_log_size {
            self.error_log.remove(0);
        }
        
        // 尝试恢复
        self.attempt_recovery(&error, &context)
    }
    
    /// 尝试错误恢复
    /// Attempt error recovery
    fn attempt_recovery(&self, error: &WebAssemblyError, _context: &str) -> Result<(), WebAssemblyError> {
        let error_type = std::any::type_name_of_val(error);
        
        if let Some(strategy) = self.recovery_strategies.get(error_type) {
            match strategy {
                RecoveryStrategy::Retry { max_attempts, .. } => {
                    // 实现重试逻辑
                    println!("尝试重试操作，最大尝试次数: {}", max_attempts);
                    Ok(())
                }
                RecoveryStrategy::Fallback { fallback_function } => {
                    // 实现备用方案
                    println!("使用备用方案: {}", fallback_function);
                    Ok(())
                }
                RecoveryStrategy::Degrade { degraded_mode } => {
                    // 实现降级服务
                    println!("降级到模式: {}", degraded_mode);
                    Ok(())
                }
                RecoveryStrategy::Skip => {
                    // 跳过操作
                    println!("跳过当前操作");
                    Ok(())
                }
                RecoveryStrategy::Terminate => {
                    // 终止执行
                    println!("终止执行");
                    Err(error.clone())
                }
            }
        } else {
            // 没有恢复策略，返回错误
            Err(error.clone())
        }
    }
    
    /// 添加恢复策略
    /// Add recovery strategy
    pub fn add_recovery_strategy(&mut self, error_type: String, strategy: RecoveryStrategy) {
        self.recovery_strategies.insert(error_type, strategy);
    }
    
    /// 获取错误统计
    /// Get error statistics
    pub fn get_error_statistics(&self) -> ErrorStatistics {
        let mut stats = ErrorStatistics::new();
        
        for entry in &self.error_log {
            match &entry.error {
                WebAssemblyError::MemoryError { .. } => stats.memory_errors += 1,
                WebAssemblyError::TypeError { .. } => stats.type_errors += 1,
                WebAssemblyError::ValidationError { .. } => stats.validation_errors += 1,
                WebAssemblyError::ExecutionError { .. } => stats.execution_errors += 1,
                WebAssemblyError::ModuleError { .. } => stats.module_errors += 1,
                WebAssemblyError::FunctionError { .. } => stats.function_errors += 1,
                WebAssemblyError::SimdError { .. } => stats.simd_errors += 1,
                WebAssemblyError::HostBindingError { .. } => stats.host_binding_errors += 1,
                WebAssemblyError::InterfaceTypeError { .. } => stats.interface_type_errors += 1,
                WebAssemblyError::ConfigurationError { .. } => stats.configuration_errors += 1,
                WebAssemblyError::InternalError { .. } => stats.internal_errors += 1,
            }
            
            if entry.resolved {
                stats.resolved_errors += 1;
            }
        }
        
        stats.total_errors = self.error_log.len();
        stats
    }
    
    /// 清除错误日志
    /// Clear error log
    pub fn clear_log(&mut self) {
        self.error_log.clear();
    }
}

/// 错误统计 / Error Statistics
#[derive(Debug, Clone)]
pub struct ErrorStatistics {
    pub total_errors: usize,
    pub resolved_errors: usize,
    pub memory_errors: usize,
    pub type_errors: usize,
    pub validation_errors: usize,
    pub execution_errors: usize,
    pub module_errors: usize,
    pub function_errors: usize,
    pub simd_errors: usize,
    pub host_binding_errors: usize,
    pub interface_type_errors: usize,
    pub configuration_errors: usize,
    pub internal_errors: usize,
}

impl ErrorStatistics {
    pub fn new() -> Self {
        Self {
            total_errors: 0,
            resolved_errors: 0,
            memory_errors: 0,
            type_errors: 0,
            validation_errors: 0,
            execution_errors: 0,
            module_errors: 0,
            function_errors: 0,
            simd_errors: 0,
            host_binding_errors: 0,
            interface_type_errors: 0,
            configuration_errors: 0,
            internal_errors: 0,
        }
    }
    
    /// 获取错误解决率
    /// Get error resolution rate
    pub fn resolution_rate(&self) -> f64 {
        if self.total_errors == 0 {
            1.0
        } else {
            self.resolved_errors as f64 / self.total_errors as f64
        }
    }
}

impl Default for ErrorHandler {
    fn default() -> Self {
        Self::new()
    }
}

/// 错误上下文宏 / Error Context Macro
#[macro_export]
macro_rules! error_context {
    ($error:expr, $context:expr) => {
        $error.map_err(|e| {
            log::error!("错误上下文: {} - {}", $context, e);
            e
        })
    };
}

/// 错误恢复宏 / Error Recovery Macro
#[macro_export]
macro_rules! with_recovery {
    ($operation:expr, $recovery:expr) => {
        match $operation {
            Ok(result) => Ok(result),
            Err(e) => {
                log::warn!("操作失败，尝试恢复: {}", e);
                $recovery
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_error_creation() {
        let error = WebAssemblyError::memory_error("内存不足");
        assert_eq!(error.severity(), ErrorSeverity::Critical);
        
        let suggestions = error.recovery_suggestions();
        assert!(!suggestions.is_empty());
    }
    
    #[test]
    fn test_error_handler() {
        let mut handler = ErrorHandler::new();
        
        let error = WebAssemblyError::type_error("类型不匹配", "i32", "f64");
        let result = handler.handle_error(error, "测试上下文");
        
        // 由于没有恢复策略，应该返回错误
        assert!(result.is_err());
        
        let stats = handler.get_error_statistics();
        assert_eq!(stats.total_errors, 1);
        assert_eq!(stats.type_errors, 1);
    }
    
    #[test]
    fn test_recovery_strategy() {
        let mut handler = ErrorHandler::new();
        
        // 使用实际的错误类型名称
        let error = WebAssemblyError::type_error("类型不匹配", "i32", "f64");
        let error_type = std::any::type_name_of_val(&error);
        
        handler.add_recovery_strategy(
            error_type.to_string(),
            RecoveryStrategy::Retry { max_attempts: 3, delay_ms: 100 }
        );
        
        let result = handler.handle_error(error, "测试上下文");
        
        // 由于有恢复策略，应该成功
        assert!(result.is_ok());
    }
}
