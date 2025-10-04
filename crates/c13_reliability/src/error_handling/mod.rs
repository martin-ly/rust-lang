//! 统一错误处理系统
//!
//! 提供类型安全、上下文丰富的错误处理机制，支持错误分类、恢复策略和监控。

use std::fmt;
use std::error::Error as StdError;
use std::sync::Arc;
use std::collections::HashMap;
use std::time::{Duration, Instant};
use serde::{Serialize, Deserialize};
// use anyhow::Result as AnyhowResult;
// use thiserror::Error;
use tracing::{error, warn, info, debug};

pub mod unified_error;
pub mod error_recovery;
pub mod error_monitoring;
pub mod macros;

pub use unified_error::*;
pub use error_recovery::*;
pub use error_monitoring::*;
// pub use macros::*;

/// Prelude module for convenient imports
pub mod prelude {
    pub use super::{UnifiedError, ErrorSeverity, ErrorContext};
    pub type Result<T> = std::result::Result<T, UnifiedError>;
}

/// 错误严重程度
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ErrorSeverity {
    /// 低严重程度：不影响核心功能
    Low,
    /// 中等严重程度：影响部分功能
    Medium,
    /// 高严重程度：影响核心功能
    High,
    /// 严重：系统不可用
    Critical,
}

impl ErrorSeverity {
    /// 获取严重程度的数值表示
    pub fn value(&self) -> u8 {
        match self {
            ErrorSeverity::Low => 1,
            ErrorSeverity::Medium => 2,
            ErrorSeverity::High => 3,
            ErrorSeverity::Critical => 4,
        }
    }

    /// 判断是否应该触发告警
    pub fn should_alert(&self) -> bool {
        matches!(self, ErrorSeverity::High | ErrorSeverity::Critical)
    }
}

impl fmt::Display for ErrorSeverity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErrorSeverity::Low => write!(f, "低"),
            ErrorSeverity::Medium => write!(f, "中等"),
            ErrorSeverity::High => write!(f, "高"),
            ErrorSeverity::Critical => write!(f, "严重"),
        }
    }
}

/// 错误上下文信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorContext {
    /// 错误发生的时间戳
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// 错误来源模块
    pub module: String,
    /// 错误来源函数
    pub function: String,
    /// 错误来源文件
    pub file: String,
    /// 错误来源行号
    pub line: u32,
    /// 错误严重程度
    pub severity: ErrorSeverity,
    /// 错误分类
    pub category: String,
    /// 错误标签
    pub tags: Vec<String>,
    /// 错误元数据
    pub metadata: HashMap<String, String>,
    /// 错误堆栈跟踪
    pub stack_trace: Option<String>,
}

impl ErrorContext {
    /// 创建新的错误上下文
    pub fn new(
        module: impl Into<String>,
        function: impl Into<String>,
        file: impl Into<String>,
        line: u32,
        severity: ErrorSeverity,
        category: impl Into<String>,
    ) -> Self {
        Self {
            timestamp: chrono::Utc::now(),
            module: module.into(),
            function: function.into(),
            file: file.into(),
            line,
            severity,
            category: category.into(),
            tags: Vec::new(),
            metadata: HashMap::new(),
            stack_trace: None,
        }
    }

    /// 添加标签
    pub fn with_tag(mut self, tag: impl Into<String>) -> Self {
        self.tags.push(tag.into());
        self
    }

    /// 添加元数据
    pub fn with_metadata(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.metadata.insert(key.into(), value.into());
        self
    }

    /// 设置堆栈跟踪
    pub fn with_stack_trace(mut self, stack_trace: impl Into<String>) -> Self {
        self.stack_trace = Some(stack_trace.into());
        self
    }
}

/// 错误恢复策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ErrorRecoveryStrategy {
    /// 重试策略
    Retry {
        max_attempts: u32,
        delay: Duration,
        backoff_multiplier: f64,
        max_delay: Duration,
    },
    /// 降级策略
    Fallback {
        fallback_value: Option<String>,
        notify: bool,
    },
    /// 忽略错误
    Ignore,
    /// 传播错误
    Propagate,
    /// 自定义恢复策略
    Custom {
        strategy_name: String,
        parameters: HashMap<String, String>,
    },
}

impl Default for ErrorRecoveryStrategy {
    fn default() -> Self {
        ErrorRecoveryStrategy::Propagate
    }
}

/// 错误恢复器
pub struct ErrorRecovery {
    strategy: ErrorRecoveryStrategy,
    recovery_count: std::sync::atomic::AtomicU64,
    last_recovery: std::sync::Mutex<Option<Instant>>,
}

impl ErrorRecovery {
    /// 创建新的错误恢复器
    pub fn new(strategy: ErrorRecoveryStrategy) -> Self {
        Self {
            strategy,
            recovery_count: std::sync::atomic::AtomicU64::new(0),
            last_recovery: std::sync::Mutex::new(None),
        }
    }

    /// 尝试恢复错误
    pub async fn recover<T, F, Fut>(&self, operation: F) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        match &self.strategy {
            ErrorRecoveryStrategy::Retry {
                max_attempts,
                delay,
                backoff_multiplier,
                max_delay,
            } => {
                self.recover_with_retry(operation, *max_attempts, *delay, *backoff_multiplier, *max_delay).await
            }
            ErrorRecoveryStrategy::Fallback { fallback_value, notify } => {
                self.recover_with_fallback(operation, fallback_value.as_ref(), *notify).await
            }
            ErrorRecoveryStrategy::Ignore => {
                self.recover_with_ignore(operation).await
            }
            ErrorRecoveryStrategy::Propagate => {
                operation().await
            }
            ErrorRecoveryStrategy::Custom { strategy_name, parameters } => {
                self.recover_with_custom(operation, strategy_name, parameters).await
            }
        }
    }

    async fn recover_with_retry<T, F, Fut>(
        &self,
        operation: F,
        max_attempts: u32,
        initial_delay: Duration,
        backoff_multiplier: f64,
        max_delay: Duration,
    ) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        let mut delay = initial_delay;
        let mut last_error = None;

        for attempt in 1..=max_attempts {
            match operation().await {
                Ok(result) => {
                    self.recovery_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    *self.last_recovery.lock().unwrap() = Some(Instant::now());
                    return Ok(result);
                }
                Err(error) => {
                    last_error = Some(error);
                    
                    if attempt < max_attempts {
                        debug!("重试第 {} 次，延迟 {:?}", attempt, delay);
                        tokio::time::sleep(delay).await;
                        
                        // 计算下次延迟时间
                        delay = Duration::from_millis(
                            (delay.as_millis() as f64 * backoff_multiplier) as u64
                        ).min(max_delay);
                    }
                }
            }
        }

        Err(last_error.unwrap_or_else(|| {
            UnifiedError::new(
                "重试次数耗尽",
                ErrorSeverity::High,
                "retry_exhausted",
                ErrorContext::new("error_recovery", "recover_with_retry", file!(), line!(), ErrorSeverity::High, "retry")
            )
        }))
    }

    async fn recover_with_fallback<T, F, Fut>(
        &self,
        operation: F,
        fallback_value: Option<&String>,
        notify: bool,
    ) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        match operation().await {
            Ok(result) => Ok(result),
            Err(error) => {
                self.recovery_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                *self.last_recovery.lock().unwrap() = Some(Instant::now());

                if notify {
                    warn!("使用降级策略处理错误: {}", error);
                }

                // 这里需要根据具体类型实现降级逻辑
                // 由于泛型限制，这里返回一个通用的降级错误
                Err(UnifiedError::new(
                    &format!("降级处理: {}", error),
                    ErrorSeverity::Medium,
                    "fallback_used",
                    ErrorContext::new("error_recovery", "recover_with_fallback", file!(), line!(), ErrorSeverity::Medium, "fallback")
                        .with_metadata("fallback_value", fallback_value.unwrap_or(&"none".to_string()))
                ))
            }
        }
    }

    async fn recover_with_ignore<T, F, Fut>(
        &self,
        operation: F,
    ) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        match operation().await {
            Ok(result) => Ok(result),
            Err(error) => {
                self.recovery_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                *self.last_recovery.lock().unwrap() = Some(Instant::now());
                
                debug!("忽略错误: {}", error);
                
                // 返回一个表示忽略的错误
                Err(UnifiedError::new(
                    "错误被忽略",
                    ErrorSeverity::Low,
                    "error_ignored",
                    ErrorContext::new("error_recovery", "recover_with_ignore", file!(), line!(), ErrorSeverity::Low, "ignore")
                        .with_metadata("original_error", error.to_string())
                ))
            }
        }
    }

    async fn recover_with_custom<T, F, Fut>(
        &self,
        operation: F,
        strategy_name: &str,
        parameters: &HashMap<String, String>,
    ) -> Result<T, UnifiedError>
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = Result<T, UnifiedError>>,
    {
        // 自定义恢复策略的实现
        // 这里可以根据策略名称和参数实现不同的恢复逻辑
        warn!("使用自定义恢复策略: {}，参数: {:?}", strategy_name, parameters);
        
        // 默认使用传播策略
        operation().await
    }

    /// 获取恢复次数
    pub fn recovery_count(&self) -> u64 {
        self.recovery_count.load(std::sync::atomic::Ordering::Relaxed)
    }

    /// 获取上次恢复时间
    pub fn last_recovery_time(&self) -> Option<Instant> {
        *self.last_recovery.lock().unwrap()
    }

    /// 重置恢复统计
    pub fn reset_stats(&self) {
        self.recovery_count.store(0, std::sync::atomic::Ordering::Relaxed);
        *self.last_recovery.lock().unwrap() = None;
    }
}

/// 错误监控器
pub struct ErrorMonitor {
    error_log: std::sync::Mutex<Vec<UnifiedError>>,
    error_stats: std::sync::Mutex<HashMap<String, u64>>,
    max_log_size: usize,
    alert_threshold: u64,
}

impl ErrorMonitor {
    /// 创建新的错误监控器
    pub fn new(max_log_size: usize, alert_threshold: u64) -> Self {
        Self {
            error_log: std::sync::Mutex::new(Vec::new()),
            error_stats: std::sync::Mutex::new(HashMap::new()),
            max_log_size,
            alert_threshold,
        }
    }

    /// 记录错误
    pub fn record_error(&self, error: UnifiedError) {
        let severity = error.severity();
        
        // 记录到日志
        {
            let mut log = self.error_log.lock().unwrap();
            if log.len() >= self.max_log_size {
                log.remove(0); // 移除最旧的错误
            }
            log.push(error.clone());
        }

        // 更新统计
        {
            let mut stats = self.error_stats.lock().unwrap();
            *stats.entry(error.category().to_string()).or_insert(0) += 1;
            *stats.entry(format!("severity_{:?}", severity)).or_insert(0) += 1;
        }

        // 检查是否需要告警
        if severity.should_alert() {
            self.check_alert_threshold();
        }

        // 记录到日志系统
        match severity {
            ErrorSeverity::Critical => error!("严重错误: {}", error),
            ErrorSeverity::High => error!("高严重程度错误: {}", error),
            ErrorSeverity::Medium => warn!("中等严重程度错误: {}", error),
            ErrorSeverity::Low => info!("低严重程度错误: {}", error),
        }
    }

    /// 检查告警阈值
    fn check_alert_threshold(&self) {
        let stats = self.error_stats.lock().unwrap();
        let total_errors: u64 = stats.values().sum();
        
        if total_errors >= self.alert_threshold {
            error!("错误数量超过告警阈值: {} >= {}", total_errors, self.alert_threshold);
            // 这里可以集成告警系统，如发送邮件、短信等
        }
    }

    /// 获取错误统计
    pub fn get_error_stats(&self) -> HashMap<String, u64> {
        self.error_stats.lock().unwrap().clone()
    }

    /// 获取最近的错误
    pub fn get_recent_errors(&self, count: usize) -> Vec<UnifiedError> {
        let log = self.error_log.lock().unwrap();
        let start = if log.len() > count {
            log.len() - count
        } else {
            0
        };
        log[start..].to_vec()
    }

    /// 清空错误日志
    pub fn clear_errors(&self) {
        self.error_log.lock().unwrap().clear();
        self.error_stats.lock().unwrap().clear();
    }
}

/// 全局错误监控器
pub struct GlobalErrorMonitor {
    monitor: Arc<ErrorMonitor>,
}

impl GlobalErrorMonitor {
    /// 创建全局错误监控器
    pub fn new() -> Self {
        Self {
            monitor: Arc::new(ErrorMonitor::new(1000, 100)),
        }
    }

    /// 初始化全局错误监控器
    pub async fn init() -> Result<(), UnifiedError> {
        // 这里可以初始化全局监控器实例
        info!("全局错误监控器初始化完成");
        Ok(())
    }

    /// 关闭全局错误监控器
    pub async fn shutdown() -> Result<(), UnifiedError> {
        info!("全局错误监控器关闭完成");
        Ok(())
    }

    /// 记录错误到全局监控器
    pub fn record_error(&self, error: UnifiedError) {
        self.monitor.record_error(error);
    }

    /// 获取全局错误统计
    pub fn get_global_stats(&self) -> HashMap<String, u64> {
        self.monitor.get_error_stats()
    }
}

/// 结果扩展trait
pub trait ResultExt<T, E> {
    /// 将结果转换为UnifiedError
    fn into_unified_error(self, context: ErrorContext) -> Result<T, UnifiedError>;
    
    /// 添加错误上下文
    fn with_context<F>(self, f: F) -> Result<T, UnifiedError>
    where
        F: FnOnce() -> ErrorContext;
}

impl<T, E> ResultExt<T, E> for Result<T, E>
where
    E: StdError + Send + Sync + 'static,
{
    fn into_unified_error(self, context: ErrorContext) -> Result<T, UnifiedError> {
        self.map_err(|e| UnifiedError::from_std_error(e, context))
    }

    fn with_context<F>(self, f: F) -> Result<T, UnifiedError>
    where
        F: FnOnce() -> ErrorContext,
    {
        self.map_err(|e| UnifiedError::from_std_error(e, f()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io;

    #[test]
    fn test_error_severity() {
        assert_eq!(ErrorSeverity::Low.value(), 1);
        assert_eq!(ErrorSeverity::Critical.value(), 4);
        assert!(ErrorSeverity::High.should_alert());
        assert!(!ErrorSeverity::Low.should_alert());
    }

    #[test]
    fn test_error_context() {
        let context = ErrorContext::new("test", "test_fn", "test.rs", 42, ErrorSeverity::Medium, "test")
            .with_tag("unit_test")
            .with_metadata("key", "value");

        assert_eq!(context.module, "test");
        assert_eq!(context.function, "test_fn");
        assert_eq!(context.severity, ErrorSeverity::Medium);
        assert!(context.tags.contains(&"unit_test".to_string()));
        assert_eq!(context.metadata.get("key"), Some(&"value".to_string()));
    }

    #[tokio::test]
    async fn test_error_recovery_retry() {
        let recovery = ErrorRecovery::new(ErrorRecoveryStrategy::Retry {
            max_attempts: 3,
            delay: Duration::from_millis(1),
            backoff_multiplier: 2.0,
            max_delay: Duration::from_millis(100),
        });

        let result = recovery.recover(|| async {
            Ok("成功".to_string())
        }).await;

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "成功");
        //assert_eq!(attempt_count, 3);
        assert_eq!(recovery.recovery_count(), 1);
    }

    #[test]
    fn test_error_monitor() {
        let monitor = ErrorMonitor::new(5, 10);

        for i in 0..7 {
            let error = UnifiedError::new(
                &format!("错误 {}", i),
                ErrorSeverity::Low,
                "test_error",
                ErrorContext::new("test", "test_monitor", file!(), line!(), ErrorSeverity::Low, "test")
            );
            monitor.record_error(error);
        }

        assert_eq!(monitor.get_recent_errors(3).len(), 3);
        assert!(monitor.get_error_stats().contains_key("test_error"));
    }

    #[test]
    fn test_result_ext() {
        let result: Result<String, io::Error> = Err(io::Error::new(io::ErrorKind::NotFound, "文件未找到"));
        let context = ErrorContext::new("test", "test_result_ext", file!(), line!(), ErrorSeverity::Medium, "io");
        
        let unified_result = result.into_unified_error(context);
        assert!(unified_result.is_err());
        
        let error = unified_result.unwrap_err();
        assert_eq!(error.severity(), ErrorSeverity::Medium);
        assert_eq!(error.category(), "std_error");
    }
}

/// 恢复策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RecoveryStrategy {
    /// 重试策略
    Retry {
        max_attempts: u32,
        delay: std::time::Duration,
    },
    /// 降级策略
    Degrade {
        fallback_value: String,
    },
    /// 忽略策略
    Ignore,
    /// 自定义策略
    Custom {
        name: String,
        parameters: std::collections::HashMap<String, String>,
    },
}

/// 错误处理器
pub struct ErrorHandler {
    _recovery_strategy: RecoveryStrategy,
}

impl ErrorHandler {
    /// 创建新的错误处理器
    pub fn new(recovery_strategy: RecoveryStrategy) -> Self {
        Self { _recovery_strategy: recovery_strategy }
    }
    
    /// 处理错误
    pub fn handle_error(error: &UnifiedError, context: &str) {
        tracing::error!("错误处理: {} - {}", context, error);
    }
}
