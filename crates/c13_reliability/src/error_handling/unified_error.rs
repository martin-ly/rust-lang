//! 统一错误类型定义
//!
//! 提供类型安全、上下文丰富的错误类型，支持错误分类、堆栈跟踪和恢复信息。

use std::fmt;
use std::error::Error as StdError;
use std::sync::Arc;
use serde::{Serialize, Deserialize};

use crate::error_handling::{ErrorSeverity, ErrorContext};

/// 统一错误类型
/// 
/// 这是整个可靠性框架的核心错误类型，提供了丰富的错误信息和上下文
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UnifiedError {
    /// 错误消息
    message: String,
    /// 错误严重程度
    severity: ErrorSeverity,
    /// 错误分类
    category: String,
    /// 错误上下文
    context: ErrorContext,
    /// 内部错误（用于错误链）
    #[serde(skip)]
    source: Option<Arc<dyn StdError + Send + Sync>>,
    /// 错误代码
    code: Option<String>,
    /// 错误建议
    suggestion: Option<String>,
    /// 是否可恢复
    recoverable: bool,
    /// 错误时间戳
    timestamp: chrono::DateTime<chrono::Utc>,
}

impl UnifiedError {
    /// 创建新的统一错误
    pub fn new(
        message: impl Into<String>,
        severity: ErrorSeverity,
        category: impl Into<String>,
        context: ErrorContext,
    ) -> Self {
        Self {
            message: message.into(),
            severity,
            category: category.into(),
            context,
            source: None,
            code: None,
            suggestion: None,
            recoverable: true,
            timestamp: chrono::Utc::now(),
        }
    }

    /// 从标准错误创建统一错误
    pub fn from_std_error<E>(error: E, context: ErrorContext) -> Self
    where
        E: StdError + Send + Sync + 'static,
    {
        Self {
            message: error.to_string(),
            severity: ErrorSeverity::Medium,
            category: "std_error".to_string(),
            context,
            source: Some(Arc::new(error)),
            code: None,
            suggestion: None,
            recoverable: true,
            timestamp: chrono::Utc::now(),
        }
    }

    /// 设置错误代码
    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
        self
    }

    /// 设置错误建议
    pub fn with_suggestion(mut self, suggestion: impl Into<String>) -> Self {
        self.suggestion = Some(suggestion.into());
        self
    }

    /// 设置是否可恢复
    pub fn with_recoverable(mut self, recoverable: bool) -> Self {
        self.recoverable = recoverable;
        self
    }

    /// 设置内部错误
    pub fn with_source<E>(mut self, source: E) -> Self
    where
        E: StdError + Send + Sync + 'static,
    {
        self.source = Some(Arc::new(source));
        self
    }

    /// 获取错误消息
    pub fn message(&self) -> &str {
        &self.message
    }

    /// 获取错误严重程度
    pub fn severity(&self) -> ErrorSeverity {
        self.severity
    }

    /// 获取错误分类
    pub fn category(&self) -> &str {
        &self.category
    }

    /// 获取错误上下文
    pub fn context(&self) -> &ErrorContext {
        &self.context
    }

    /// 获取错误代码
    pub fn code(&self) -> Option<&str> {
        self.code.as_deref()
    }

    /// 获取错误建议
    pub fn suggestion(&self) -> Option<&str> {
        self.suggestion.as_deref()
    }

    /// 是否可恢复
    pub fn is_recoverable(&self) -> bool {
        self.recoverable
    }

    /// 获取错误时间戳
    pub fn timestamp(&self) -> chrono::DateTime<chrono::Utc> {
        self.timestamp
    }

    /// 获取错误链
    pub fn error_chain(&self) -> Vec<String> {
        let mut chain = vec![self.message.clone()];
        
        if let Some(source) = &self.source {
            chain.push(source.to_string());
            
            // 递归获取错误链
            let mut current = source.source();
            while let Some(err) = current {
                chain.push(err.to_string());
                current = err.source();
            }
        }
        
        chain
    }

    /// 获取简化的错误信息
    pub fn summary(&self) -> String {
        format!(
            "[{}] {}: {}",
            self.severity,
            self.category,
            self.message
        )
    }

    /// 获取详细的错误信息
    pub fn details(&self) -> String {
        let mut details = format!(
            "错误详情:\n\
            消息: {}\n\
            严重程度: {}\n\
            分类: {}\n\
            时间: {}\n\
            模块: {}\n\
            函数: {}\n\
            文件: {}:{}\n\
            可恢复: {}",
            self.message,
            self.severity,
            self.category,
            self.timestamp.format("%Y-%m-%d %H:%M:%S UTC"),
            self.context.module,
            self.context.function,
            self.context.file,
            self.context.line,
            self.recoverable
        );

        if let Some(code) = &self.code {
            details.push_str(&format!("\n错误代码: {}", code));
        }

        if let Some(suggestion) = &self.suggestion {
            details.push_str(&format!("\n建议: {}", suggestion));
        }

        if !self.context.tags.is_empty() {
            details.push_str(&format!("\n标签: {:?}", self.context.tags));
        }

        if !self.context.metadata.is_empty() {
            details.push_str(&format!("\n元数据: {:?}", self.context.metadata));
        }

        if let Some(stack_trace) = &self.context.stack_trace {
            details.push_str(&format!("\n堆栈跟踪:\n{}", stack_trace));
        }

        details
    }

    // ============================================================================
    // Simple helper methods with minimal context (for convenience)
    // ============================================================================

    /// 创建配置错误（使用简单上下文）
    pub fn configuration_error(message: impl Into<String>) -> Self {
        let context = ErrorContext::new(
            "distributed_systems",
            "lock_operation",
            file!(),
            line!(),
            ErrorSeverity::Medium,
            "configuration",
        );
        Self::new(message, ErrorSeverity::Medium, "configuration", context)
            .with_code("CFG_001")
    }

    /// 创建状态错误
    pub fn state_error(message: impl Into<String>) -> Self {
        let context = ErrorContext::new(
            "distributed_systems",
            "state_operation",
            file!(),
            line!(),
            ErrorSeverity::Medium,
            "state",
        );
        Self::new(message, ErrorSeverity::Medium, "state", context)
            .with_code("STATE_001")
    }

    /// 创建资源不可用错误
    pub fn resource_unavailable(message: impl Into<String>) -> Self {
        let context = ErrorContext::new(
            "distributed_systems",
            "resource_operation",
            file!(),
            line!(),
            ErrorSeverity::Medium,
            "resource",
        );
        Self::new(message, ErrorSeverity::Medium, "resource", context)
            .with_code("RES_UNAVAIL")
    }

    /// 创建未找到错误
    pub fn not_found(message: impl Into<String>) -> Self {
        let context = ErrorContext::new(
            "distributed_systems",
            "lookup_operation",
            file!(),
            line!(),
            ErrorSeverity::Low,
            "not_found",
        );
        Self::new(message, ErrorSeverity::Low, "not_found", context)
            .with_code("NOT_FOUND")
    }
}

impl fmt::Display for UnifiedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.summary())
    }
}

impl StdError for UnifiedError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        self.source.as_ref().map(|e| e.as_ref() as &(dyn StdError + 'static))
    }
}

/// 预定义的错误类型
pub mod predefined {
    use super::*;
    use crate::error_handling::{ErrorSeverity, ErrorContext};

    /// 网络错误
    pub fn network_error(message: impl Into<String>, context: ErrorContext) -> UnifiedError {
        UnifiedError::new(message, ErrorSeverity::High, "network", context)
            .with_code("NET_001")
            .with_suggestion("检查网络连接和服务器状态")
    }

    /// 数据库错误
    pub fn database_error(message: impl Into<String>, context: ErrorContext) -> UnifiedError {
        UnifiedError::new(message, ErrorSeverity::High, "database", context)
            .with_code("DB_001")
            .with_suggestion("检查数据库连接和查询语句")
    }

    /// 配置错误
    pub fn configuration_error(message: impl Into<String>, context: ErrorContext) -> UnifiedError {
        UnifiedError::new(message, ErrorSeverity::Medium, "configuration", context)
            .with_code("CFG_001")
            .with_suggestion("检查配置文件格式和参数")
    }

    /// 权限错误
    pub fn permission_error(message: impl Into<String>, context: ErrorContext) -> UnifiedError {
        UnifiedError::new(message, ErrorSeverity::High, "permission", context)
            .with_code("PERM_001")
            .with_suggestion("检查用户权限和访问控制")
    }

    /// 资源错误
    pub fn resource_error(message: impl Into<String>, context: ErrorContext) -> UnifiedError {
        UnifiedError::new(message, ErrorSeverity::Medium, "resource", context)
            .with_code("RES_001")
            .with_suggestion("检查资源可用性和配额")
    }

    /// 超时错误
    pub fn timeout_error(message: impl Into<String>, context: ErrorContext) -> UnifiedError {
        UnifiedError::new(message, ErrorSeverity::Medium, "timeout", context)
            .with_code("TIME_001")
            .with_suggestion("增加超时时间或优化操作性能")
    }

    /// 验证错误
    pub fn validation_error(message: impl Into<String>, context: ErrorContext) -> UnifiedError {
        UnifiedError::new(message, ErrorSeverity::Low, "validation", context)
            .with_code("VAL_001")
            .with_suggestion("检查输入数据的格式和有效性")
    }

    /// 序列化错误
    pub fn serialization_error(message: impl Into<String>, context: ErrorContext) -> UnifiedError {
        UnifiedError::new(message, ErrorSeverity::Medium, "serialization", context)
            .with_code("SER_001")
            .with_suggestion("检查数据格式和序列化配置")
    }

    /// 并发错误
    pub fn concurrency_error(message: impl Into<String>, context: ErrorContext) -> UnifiedError {
        UnifiedError::new(message, ErrorSeverity::High, "concurrency", context)
            .with_code("CONC_001")
            .with_suggestion("检查并发控制和同步机制")
    }

    /// 系统错误
    pub fn system_error(message: impl Into<String>, context: ErrorContext) -> UnifiedError {
        UnifiedError::new(message, ErrorSeverity::Critical, "system", context)
            .with_code("SYS_001")
            .with_suggestion("检查系统资源和环境配置")
    }
}

/// 错误构建器
pub struct ErrorBuilder {
    message: Option<String>,
    severity: Option<ErrorSeverity>,
    category: Option<String>,
    context: Option<ErrorContext>,
    code: Option<String>,
    suggestion: Option<String>,
    recoverable: Option<bool>,
    source: Option<Arc<dyn StdError + Send + Sync>>,
}

impl ErrorBuilder {
    /// 创建新的错误构建器
    pub fn new() -> Self {
        Self {
            message: None,
            severity: None,
            category: None,
            context: None,
            code: None,
            suggestion: None,
            recoverable: None,
            source: None,
        }
    }

    /// 设置错误消息
    pub fn message(mut self, message: impl Into<String>) -> Self {
        self.message = Some(message.into());
        self
    }

    /// 设置错误严重程度
    pub fn severity(mut self, severity: ErrorSeverity) -> Self {
        self.severity = Some(severity);
        self
    }

    /// 设置错误分类
    pub fn category(mut self, category: impl Into<String>) -> Self {
        self.category = Some(category.into());
        self
    }

    /// 设置错误上下文
    pub fn context(mut self, context: ErrorContext) -> Self {
        self.context = Some(context);
        self
    }

    /// 设置错误代码
    pub fn code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
        self
    }

    /// 设置错误建议
    pub fn suggestion(mut self, suggestion: impl Into<String>) -> Self {
        self.suggestion = Some(suggestion.into());
        self
    }

    /// 设置是否可恢复
    pub fn recoverable(mut self, recoverable: bool) -> Self {
        self.recoverable = Some(recoverable);
        self
    }

    /// 设置内部错误
    pub fn source<E>(mut self, source: E) -> Self
    where
        E: StdError + Send + Sync + 'static,
    {
        self.source = Some(Arc::new(source));
        self
    }

    /// 构建错误
    pub fn build(self) -> Result<UnifiedError, String> {
        let message = self.message.ok_or("错误消息不能为空")?;
        let severity = self.severity.unwrap_or(ErrorSeverity::Medium);
        let category = self.category.unwrap_or_else(|| "unknown".to_string());
        let context = self.context.ok_or("错误上下文不能为空")?;

        let mut error = UnifiedError::new(message, severity, category, context);

        if let Some(code) = self.code {
            error = error.with_code(code);
        }

        if let Some(suggestion) = self.suggestion {
            error = error.with_suggestion(suggestion);
        }

        if let Some(recoverable) = self.recoverable {
            error = error.with_recoverable(recoverable);
        }

        if let Some(source) = self.source {
            error = error.with_source(source);
        }

        Ok(error)
    }
}

impl Default for ErrorBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// 错误转换trait
pub trait IntoUnifiedError {
    /// 转换为统一错误
    fn into_unified_error(self, context: ErrorContext) -> UnifiedError;
}

impl<E> IntoUnifiedError for E
where
    E: StdError + Send + Sync + 'static,
{
    fn into_unified_error(self, context: ErrorContext) -> UnifiedError {
        UnifiedError::from_std_error(self, context)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io;

    #[test]
    fn test_unified_error_creation() {
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test");
        let error = UnifiedError::new("测试错误", ErrorSeverity::High, "test", context.clone());

        assert_eq!(error.message(), "测试错误");
        assert_eq!(error.severity(), ErrorSeverity::High);
        assert_eq!(error.category(), "test");
        assert!(error.is_recoverable());
    }

    #[test]
    fn test_unified_error_builder() {
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test");
        
        let error = ErrorBuilder::new()
            .message("构建器测试错误")
            .severity(ErrorSeverity::Critical)
            .category("builder_test")
            .context(context)
            .code("BUILD_001")
            .suggestion("使用错误构建器")
            .recoverable(false)
            .build()
            .unwrap();

        assert_eq!(error.message(), "构建器测试错误");
        assert_eq!(error.severity(), ErrorSeverity::Critical);
        assert_eq!(error.category(), "builder_test");
        assert_eq!(error.code(), Some("BUILD_001"));
        assert_eq!(error.suggestion(), Some("使用错误构建器"));
        assert!(!error.is_recoverable());
    }

    #[test]
    fn test_predefined_errors() {
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test");
        
        let network_error = predefined::network_error("网络连接失败", context.clone());
        assert_eq!(network_error.category(), "network");
        assert_eq!(network_error.code(), Some("NET_001"));
        assert!(network_error.suggestion().unwrap().contains("网络连接"));

        let db_error = predefined::database_error("数据库查询失败", context.clone());
        assert_eq!(db_error.category(), "database");
        assert_eq!(db_error.code(), Some("DB_001"));
    }

    #[test]
    fn test_error_chain() {
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test");
        let io_error = io::Error::new(io::ErrorKind::NotFound, "文件未找到");
        
        let unified_error = UnifiedError::new("操作失败", ErrorSeverity::High, "test", context)
            .with_source(io_error);

        let chain = unified_error.error_chain();
        assert!(chain.len() >= 2);
        assert!(chain[0].contains("操作失败"));
        assert!(chain[1].contains("文件未找到"));
    }

    #[test]
    fn test_error_display() {
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test");
        let error = UnifiedError::new("显示测试", ErrorSeverity::High, "display", context);
        
        let summary = error.summary();
        assert!(summary.contains("高"));
        assert!(summary.contains("display"));
        assert!(summary.contains("显示测试"));

        let details = error.details();
        assert!(details.contains("错误详情"));
        assert!(details.contains("显示测试"));
        assert!(details.contains("test"));
    }

    #[test]
    fn test_into_unified_error() {
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test");
        let io_error = io::Error::new(io::ErrorKind::PermissionDenied, "权限不足");
        
        let unified_error = io_error.into_unified_error(context);
        assert_eq!(unified_error.category(), "std_error");
        assert!(unified_error.message().contains("权限不足"));
    }
}
