//! 高级错误处理模块
//!
//! 本模块展示了 Rust 1.90 中的高级错误处理特性，包括：
//! - 自定义错误类型
//! - 错误链和上下文
//! - 错误恢复机制
//! - 错误转换和映射
//! - 错误日志和监控
//! - 错误处理最佳实践
//!
//! # 文件信息
//! - 文件: advanced_error_handling.rs
//! - 创建日期: 2025-01-27
//! - 版本: 1.0
//! - Rust版本: 1.90.0
// - Edition: 2024

use std::collections::HashMap;
use std::fmt;
use std::sync::{Arc, Mutex};
use std::time::{SystemTime, UNIX_EPOCH};

// ==================== 1. 自定义错误类型 ====================

/// 应用错误类型
/// 
/// 展示了 Rust 1.90 中的自定义错误类型设计
#[derive(Debug, Clone)]
pub enum AppError {
    /// 输入验证错误
    Validation(ValidationError),
    /// 网络错误
    Network(NetworkError),
    /// 数据库错误
    Database(DatabaseError),
    /// 业务逻辑错误
    Business(BusinessError),
    /// 系统错误
    System(SystemError),
    /// 配置错误
    Config(ConfigError),
    /// 权限错误
    Permission(PermissionError),
    /// 资源错误
    Resource(ResourceError),
    /// 超时错误
    Timeout(TimeoutError),
    /// 未知错误
    Unknown(String),
}

/// 输入验证错误
#[derive(Debug, Clone)]
pub struct ValidationError {
    pub field: String,
    pub message: String,
    pub value: Option<String>,
}

/// 网络错误
#[derive(Debug, Clone)]
pub struct NetworkError {
    pub url: String,
    pub status_code: Option<u16>,
    pub message: String,
}

/// 数据库错误
#[derive(Debug, Clone)]
pub struct DatabaseError {
    pub operation: String,
    pub table: Option<String>,
    pub message: String,
    pub sql_state: Option<String>,
}

/// 业务逻辑错误
#[derive(Debug, Clone)]
pub struct BusinessError {
    pub code: String,
    pub message: String,
    pub context: HashMap<String, String>,
}

/// 系统错误
#[derive(Debug, Clone)]
pub struct SystemError {
    pub component: String,
    pub message: String,
    pub error_code: Option<i32>,
}

/// 配置错误
#[derive(Debug, Clone)]
pub struct ConfigError {
    pub key: String,
    pub message: String,
    pub file: Option<String>,
}

/// 权限错误
#[derive(Debug, Clone)]
pub struct PermissionError {
    pub resource: String,
    pub action: String,
    pub user_id: Option<String>,
}

/// 资源错误
#[derive(Debug, Clone)]
pub struct ResourceError {
    pub resource_type: String,
    pub resource_id: String,
    pub message: String,
}

/// 超时错误
#[derive(Debug, Clone)]
pub struct TimeoutError {
    pub operation: String,
    pub timeout_duration: u64,
    pub message: String,
}

// 实现 Display trait
impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AppError::Validation(e) => write!(f, "Validation error in field '{}': {}", e.field, e.message),
            AppError::Network(e) => write!(f, "Network error for URL '{}': {}", e.url, e.message),
            AppError::Database(e) => write!(f, "Database error in operation '{}': {}", e.operation, e.message),
            AppError::Business(e) => write!(f, "Business error [{}]: {}", e.code, e.message),
            AppError::System(e) => write!(f, "System error in component '{}': {}", e.component, e.message),
            AppError::Config(e) => write!(f, "Config error for key '{}': {}", e.key, e.message),
            AppError::Permission(e) => write!(f, "Permission error for resource '{}' action '{}'", e.resource, e.action),
            AppError::Resource(e) => write!(f, "Resource error for {} '{}': {}", e.resource_type, e.resource_id, e.message),
            AppError::Timeout(e) => write!(f, "Timeout error for operation '{}': {}", e.operation, e.message),
            AppError::Unknown(msg) => write!(f, "Unknown error: {}", msg),
        }
    }
}

impl std::error::Error for AppError {}

// ==================== 2. 错误链和上下文 ====================

/// 错误上下文
/// 
/// 提供了错误的上下文信息
#[derive(Debug, Clone)]
pub struct ErrorContext {
    pub timestamp: u64,
    pub request_id: Option<String>,
    pub user_id: Option<String>,
    pub component: String,
    pub operation: String,
    pub metadata: HashMap<String, String>,
}

impl ErrorContext {
    pub fn new(component: String, operation: String) -> Self {
        Self {
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs(),
            request_id: None,
            user_id: None,
            component,
            operation,
            metadata: HashMap::new(),
        }
    }
    
    pub fn with_request_id(mut self, request_id: String) -> Self {
        self.request_id = Some(request_id);
        self
    }
    
    pub fn with_user_id(mut self, user_id: String) -> Self {
        self.user_id = Some(user_id);
        self
    }
    
    pub fn with_metadata(mut self, key: String, value: String) -> Self {
        self.metadata.insert(key, value);
        self
    }
}

/// 带上下文的错误
#[derive(Debug, Clone)]
pub struct ContextualError {
    pub error: AppError,
    pub context: ErrorContext,
    pub cause: Option<Box<ContextualError>>,
}

impl ContextualError {
    pub fn new(error: AppError, context: ErrorContext) -> Self {
        Self {
            error,
            context,
            cause: None,
        }
    }
    
    pub fn with_cause(mut self, cause: ContextualError) -> Self {
        self.cause = Some(Box::new(cause));
        self
    }
    
    pub fn chain_length(&self) -> usize {
        let mut length = 1;
        let mut current = &self.cause;
        while let Some(cause) = current {
            length += 1;
            current = &cause.cause;
        }
        length
    }
    
    pub fn get_root_cause(&self) -> &AppError {
        let mut current = self;
        while let Some(cause) = &current.cause {
            current = cause;
        }
        &current.error
    }
}

impl fmt::Display for ContextualError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} [Context: {}:{}]", self.error, self.context.component, self.context.operation)?;
        
        if let Some(request_id) = &self.context.request_id {
            write!(f, " [Request: {}]", request_id)?;
        }
        
        if let Some(user_id) = &self.context.user_id {
            write!(f, " [User: {}]", user_id)?;
        }
        
        if let Some(cause) = &self.cause {
            write!(f, " [Caused by: {}]", cause)?;
        }
        
        Ok(())
    }
}

impl std::error::Error for ContextualError {}

// ==================== 3. 错误恢复机制 ====================

/// 错误恢复策略
#[derive(Debug, Clone)]
pub enum RecoveryStrategy {
    /// 重试
    Retry { max_attempts: u32, delay_ms: u64 },
    /// 回退到默认值
    Fallback { default_value: String },
    /// 跳过操作
    Skip,
    /// 降级服务
    Degrade { fallback_service: String },
    /// 失败
    Fail,
}

/// 错误恢复器
#[allow(dead_code)]
pub struct ErrorRecovery {
    strategies: HashMap<String, RecoveryStrategy>,
    retry_counts: Arc<Mutex<HashMap<String, u32>>>,
}

impl ErrorRecovery {
    pub fn new() -> Self {
        Self {
            strategies: HashMap::new(),
            retry_counts: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn add_strategy(&mut self, error_type: String, strategy: RecoveryStrategy) {
        self.strategies.insert(error_type, strategy);
    }
    
    #[allow(unused_variables)]
    pub fn recover<F, T>(&self, error: &AppError, operation: F) -> Result<T, AppError>
    where
        F: Fn() -> Result<T, AppError>,
    {
        let error_type = self.get_error_type(error);
        
        if let Some(strategy) = self.strategies.get(&error_type) {
            match strategy {
                RecoveryStrategy::Retry { max_attempts, delay_ms } => {
                    self.retry_operation(operation, *max_attempts, *delay_ms)
                },
                RecoveryStrategy::Fallback { default_value } => {
                    // 简化实现，实际中需要根据类型进行转换
                    Err(AppError::Unknown(format!("Fallback not implemented for type T")))
                },
                RecoveryStrategy::Skip => {
                    Err(AppError::Unknown("Operation skipped".to_string()))
                },
                RecoveryStrategy::Degrade { fallback_service } => {
                    Err(AppError::Unknown(format!("Degraded to service: {}", fallback_service)))
                },
                RecoveryStrategy::Fail => {
                    Err(error.clone())
                },
            }
        } else {
            Err(error.clone())
        }
    }
    
    fn get_error_type(&self, error: &AppError) -> String {
        match error {
            AppError::Validation(_) => "validation".to_string(),
            AppError::Network(_) => "network".to_string(),
            AppError::Database(_) => "database".to_string(),
            AppError::Business(_) => "business".to_string(),
            AppError::System(_) => "system".to_string(),
            AppError::Config(_) => "config".to_string(),
            AppError::Permission(_) => "permission".to_string(),
            AppError::Resource(_) => "resource".to_string(),
            AppError::Timeout(_) => "timeout".to_string(),
            AppError::Unknown(_) => "unknown".to_string(),
        }
    }
    
    fn retry_operation<F, T>(&self, operation: F, max_attempts: u32, delay_ms: u64) -> Result<T, AppError>
    where
        F: Fn() -> Result<T, AppError>,
    {
        let mut last_error = None;
        
        for attempt in 1..=max_attempts {
            match operation() {
                Ok(result) => return Ok(result),
                Err(error) => {
                    last_error = Some(error);
                    if attempt < max_attempts {
                        std::thread::sleep(std::time::Duration::from_millis(delay_ms));
                    }
                }
            }
        }
        
        Err(last_error.unwrap())
    }
}

impl Default for ErrorRecovery {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 4. 错误转换和映射 ====================

/// 错误转换器
#[allow(dead_code)]
pub struct ErrorTransformer {
    mappings: HashMap<String, Box<dyn Fn(AppError) -> AppError + Send + Sync>>,
}

impl ErrorTransformer {
    pub fn new() -> Self {
        Self {
            mappings: HashMap::new(),
        }
    }
    
    #[allow(unused_variables)]
    pub fn add_mapping<F>(&mut self, from_type: String, transformer: F)
    where
        F: Fn(AppError) -> AppError + Send + Sync + 'static,
    {
        self.mappings.insert(from_type, Box::new(transformer));
    }
    
    pub fn transform(&self, error: AppError) -> AppError {
        let error_type = self.get_error_type(&error);
        
        if let Some(transformer) = self.mappings.get(&error_type) {
            transformer(error)
        } else {
            error
        }
    }
    
    fn get_error_type(&self, error: &AppError) -> String {
        match error {
            AppError::Validation(_) => "validation".to_string(),
            AppError::Network(_) => "network".to_string(),
            AppError::Database(_) => "database".to_string(),
            AppError::Business(_) => "business".to_string(),
            AppError::System(_) => "system".to_string(),
            AppError::Config(_) => "config".to_string(),
            AppError::Permission(_) => "permission".to_string(),
            AppError::Resource(_) => "resource".to_string(),
            AppError::Timeout(_) => "timeout".to_string(),
            AppError::Unknown(_) => "unknown".to_string(),
        }
    }
}

impl Default for ErrorTransformer {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 5. 错误日志和监控 ====================

/// 错误日志级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ErrorLevel {
    Debug,
    Info,
    Warning,
    Error,
    Critical,
}

/// 错误日志条目
#[derive(Debug, Clone)]
pub struct ErrorLogEntry {
    pub timestamp: u64,
    pub level: ErrorLevel,
    pub error: AppError,
    pub context: ErrorContext,
    pub stack_trace: Option<String>,
}

/// 错误监控器
#[allow(dead_code)]
pub struct ErrorMonitor {
    logs: Arc<Mutex<Vec<ErrorLogEntry>>>,
    metrics: Arc<Mutex<ErrorMetrics>>,
}

/// 错误指标
#[derive(Debug, Default)]
pub struct ErrorMetrics {
    pub total_errors: u64,
    pub errors_by_type: HashMap<String, u64>,
    pub errors_by_level: HashMap<ErrorLevel, u64>,
    pub errors_by_component: HashMap<String, u64>,
    pub recent_errors: Vec<ErrorLogEntry>,
}

impl ErrorMonitor {
    pub fn new() -> Self {
        Self {
            logs: Arc::new(Mutex::new(Vec::new())),
            metrics: Arc::new(Mutex::new(ErrorMetrics::default())),
        }
    }
    
    pub fn log_error(&self, error: AppError, context: ErrorContext, level: ErrorLevel) {
        let entry = ErrorLogEntry {
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs(),
            level,
            error: error.clone(),
            context: context.clone(),
            stack_trace: None, // 简化实现
        };
        
        // 记录日志
        {
            let mut logs = self.logs.lock().unwrap();
            logs.push(entry.clone());
            
            // 保持最近1000条日志
            if logs.len() > 1000 {
                logs.remove(0);
            }
        }
        
        // 更新指标
        {
            let mut metrics = self.metrics.lock().unwrap();
            metrics.total_errors += 1;
            
            let error_type = self.get_error_type(&error);
            *metrics.errors_by_type.entry(error_type).or_insert(0) += 1;
            *metrics.errors_by_level.entry(level).or_insert(0) += 1;
            *metrics.errors_by_component.entry(context.component.clone()).or_insert(0) += 1;
            
            metrics.recent_errors.push(entry);
            if metrics.recent_errors.len() > 100 {
                metrics.recent_errors.remove(0);
            }
        }
    }
    
    pub fn get_metrics(&self) -> ErrorMetrics {
        let metrics = self.metrics.lock().unwrap();
        ErrorMetrics {
            total_errors: metrics.total_errors,
            errors_by_type: metrics.errors_by_type.clone(),
            errors_by_level: metrics.errors_by_level.clone(),
            errors_by_component: metrics.errors_by_component.clone(),
            recent_errors: metrics.recent_errors.clone(),
        }
    }
    
    pub fn get_recent_errors(&self, limit: usize) -> Vec<ErrorLogEntry> {
        let logs = self.logs.lock().unwrap();
        logs.iter().rev().take(limit).cloned().collect()
    }
    
    fn get_error_type(&self, error: &AppError) -> String {
        match error {
            AppError::Validation(_) => "validation".to_string(),
            AppError::Network(_) => "network".to_string(),
            AppError::Database(_) => "database".to_string(),
            AppError::Business(_) => "business".to_string(),
            AppError::System(_) => "system".to_string(),
            AppError::Config(_) => "config".to_string(),
            AppError::Permission(_) => "permission".to_string(),
            AppError::Resource(_) => "resource".to_string(),
            AppError::Timeout(_) => "timeout".to_string(),
            AppError::Unknown(_) => "unknown".to_string(),
        }
    }
}

impl Default for ErrorMonitor {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 6. 错误处理最佳实践 ====================

/// 错误处理工具
#[allow(dead_code)]
pub struct ErrorHandler {
    monitor: ErrorMonitor,
    recovery: ErrorRecovery,
    transformer: ErrorTransformer,
}

impl ErrorHandler {
    pub fn new() -> Self {
        Self {
            monitor: ErrorMonitor::new(),
            recovery: ErrorRecovery::new(),
            transformer: ErrorTransformer::new(),
        }
    }
    
    /// 处理错误
    pub fn handle_error(&self, error: AppError, context: ErrorContext) -> Result<(), AppError> {
        // 转换错误
        let transformed_error = self.transformer.transform(error);
        
        // 记录错误
        let level = self.determine_error_level(&transformed_error);
        self.monitor.log_error(transformed_error.clone(), context.clone(), level);
        
        // 尝试恢复
        self.recovery.recover(&transformed_error, || Err(transformed_error.clone()))
    }
    
    /// 确定错误级别
    fn determine_error_level(&self, error: &AppError) -> ErrorLevel {
        match error {
            AppError::Validation(_) => ErrorLevel::Warning,
            AppError::Network(_) => ErrorLevel::Error,
            AppError::Database(_) => ErrorLevel::Error,
            AppError::Business(_) => ErrorLevel::Warning,
            AppError::System(_) => ErrorLevel::Critical,
            AppError::Config(_) => ErrorLevel::Error,
            AppError::Permission(_) => ErrorLevel::Warning,
            AppError::Resource(_) => ErrorLevel::Error,
            AppError::Timeout(_) => ErrorLevel::Error,
            AppError::Unknown(_) => ErrorLevel::Error,
        }
    }
    
    /// 获取错误统计
    pub fn get_error_stats(&self) -> ErrorMetrics {
        self.monitor.get_metrics()
    }
    
    /// 获取最近错误
    pub fn get_recent_errors(&self, limit: usize) -> Vec<ErrorLogEntry> {
        self.monitor.get_recent_errors(limit)
    }
    
    /// 添加恢复策略
    pub fn add_recovery_strategy(&mut self, error_type: String, strategy: RecoveryStrategy) {
        self.recovery.add_strategy(error_type, strategy);
    }
    
    /// 添加错误转换
    pub fn add_error_transformation<F>(&mut self, from_type: String, transformer: F)
    where
        F: Fn(AppError) -> AppError + Send + Sync + 'static,
    {
        self.transformer.add_mapping(from_type, transformer);
    }
}

impl Default for ErrorHandler {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 演示函数 ====================

/// 演示所有高级错误处理特性
pub fn demonstrate_advanced_error_handling() {
    println!("=== 高级错误处理演示 ===\n");
    
    // 1. 自定义错误类型演示
    println!("1. 自定义错误类型演示:");
    let validation_error = AppError::Validation(ValidationError {
        field: "email".to_string(),
        message: "Invalid email format".to_string(),
        value: Some("invalid-email".to_string()),
    });
    println!("  验证错误: {}", validation_error);
    
    let network_error = AppError::Network(NetworkError {
        url: "https://api.example.com".to_string(),
        status_code: Some(404),
        message: "Not found".to_string(),
    });
    println!("  网络错误: {}", network_error);
    
    let business_error = AppError::Business(BusinessError {
        code: "INSUFFICIENT_BALANCE".to_string(),
        message: "Account balance is too low".to_string(),
        context: {
            let mut map = HashMap::new();
            map.insert("current_balance".to_string(), "100.00".to_string());
            map.insert("required_amount".to_string(), "150.00".to_string());
            map
        },
    });
    println!("  业务错误: {}", business_error);
    println!();
    
    // 2. 错误链和上下文演示
    println!("2. 错误链和上下文演示:");
    let context = ErrorContext::new("user_service".to_string(), "create_user".to_string())
        .with_request_id("req-123".to_string())
        .with_user_id("user-456".to_string())
        .with_metadata("ip".to_string(), "192.168.1.1".to_string());
    
    let contextual_error = ContextualError::new(validation_error.clone(), context);
    println!("  上下文错误: {}", contextual_error);
    println!("  错误链长度: {}", contextual_error.chain_length());
    println!("  根本原因: {}", contextual_error.get_root_cause());
    println!();
    
    // 3. 错误恢复机制演示
    println!("3. 错误恢复机制演示:");
    let mut recovery = ErrorRecovery::new();
    recovery.add_strategy("network".to_string(), RecoveryStrategy::Retry {
        max_attempts: 3,
        delay_ms: 1000,
    });
    recovery.add_strategy("validation".to_string(), RecoveryStrategy::Fallback {
        default_value: "default@example.com".to_string(),
    });
    
    println!("  添加了网络重试策略和验证回退策略");
    println!();
    
    // 4. 错误转换和映射演示
    println!("4. 错误转换和映射演示:");
    let mut transformer = ErrorTransformer::new();
    transformer.add_mapping("network".to_string(), |error| {
        if let AppError::Network(network_error) = error {
            AppError::Business(BusinessError {
                code: "SERVICE_UNAVAILABLE".to_string(),
                message: format!("External service unavailable: {}", network_error.url),
                context: HashMap::new(),
            })
        } else {
            error
        }
    });
    
    let transformed_error = transformer.transform(network_error.clone());
    println!("  转换后的错误: {}", transformed_error);
    println!();
    
    // 5. 错误日志和监控演示
    println!("5. 错误日志和监控演示:");
    let monitor = ErrorMonitor::new();
    
    let context1 = ErrorContext::new("auth_service".to_string(), "login".to_string());
    let context2 = ErrorContext::new("payment_service".to_string(), "process_payment".to_string());
    
    monitor.log_error(validation_error.clone(), context1, ErrorLevel::Warning);
    monitor.log_error(network_error.clone(), context2.clone(), ErrorLevel::Error);
    monitor.log_error(business_error.clone(), context2, ErrorLevel::Warning);
    
    let metrics = monitor.get_metrics();
    println!("  错误统计:");
    println!("    总错误数: {}", metrics.total_errors);
    println!("    按类型分布: {:?}", metrics.errors_by_type);
    println!("    按级别分布: {:?}", metrics.errors_by_level);
    println!("    按组件分布: {:?}", metrics.errors_by_component);
    
    let recent_errors = monitor.get_recent_errors(2);
    println!("  最近错误数量: {}", recent_errors.len());
    println!();
    
    // 6. 错误处理最佳实践演示
    println!("6. 错误处理最佳实践演示:");
    let mut error_handler = ErrorHandler::new();
    
    // 添加恢复策略
    error_handler.add_recovery_strategy("network".to_string(), RecoveryStrategy::Retry {
        max_attempts: 2,
        delay_ms: 500,
    });
    
    // 添加错误转换
    error_handler.add_error_transformation("validation".to_string(), |error| {
        if let AppError::Validation(validation_error) = error {
            AppError::Business(BusinessError {
                code: "INVALID_INPUT".to_string(),
                message: format!("Input validation failed: {}", validation_error.message),
                context: HashMap::new(),
            })
        } else {
            error
        }
    });
    
    let context = ErrorContext::new("api_service".to_string(), "handle_request".to_string());
    let _ = error_handler.handle_error(validation_error, context);
    
    let stats = error_handler.get_error_stats();
    println!("  处理后的错误统计: {:?}", stats);
    
    println!("\n=== 高级错误处理演示完成 ===");
}

// ==================== 测试模块 ====================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_error_context() {
        let context = ErrorContext::new("test".to_string(), "operation".to_string())
            .with_request_id("req-123".to_string())
            .with_user_id("user-456".to_string());
        
        assert_eq!(context.component, "test");
        assert_eq!(context.operation, "operation");
        assert_eq!(context.request_id, Some("req-123".to_string()));
        assert_eq!(context.user_id, Some("user-456".to_string()));
    }
    
    #[test]
    fn test_contextual_error() {
        let error = AppError::Validation(ValidationError {
            field: "test".to_string(),
            message: "test error".to_string(),
            value: None,
        });
        let context = ErrorContext::new("test".to_string(), "operation".to_string());
        let contextual_error = ContextualError::new(error, context);
        
        assert_eq!(contextual_error.chain_length(), 1);
    }
    
    #[test]
    fn test_error_monitor() {
        let monitor = ErrorMonitor::new();
        let error = AppError::Validation(ValidationError {
            field: "test".to_string(),
            message: "test error".to_string(),
            value: None,
        });
        let context = ErrorContext::new("test".to_string(), "operation".to_string());
        
        monitor.log_error(error, context, ErrorLevel::Warning);
        
        let metrics = monitor.get_metrics();
        assert_eq!(metrics.total_errors, 1);
        assert_eq!(metrics.errors_by_type.get("validation"), Some(&1));
    }
    
    #[test]
    fn test_error_recovery() {
        let mut recovery = ErrorRecovery::new();
        recovery.add_strategy("test".to_string(), RecoveryStrategy::Retry {
            max_attempts: 3,
            delay_ms: 100,
        });
        
        let error = AppError::Unknown("test error".to_string());
        let result: Result<(), AppError> = recovery.recover(&error, || Err(error.clone()));
        
        assert!(result.is_err());
    }
}
