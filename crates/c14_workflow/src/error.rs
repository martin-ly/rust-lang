//! # 工作流系统错误处理模块 / Workflow System Error Handling Module
//!
//! 本模块提供了完整的错误处理机制，包括错误类型定义、错误恢复策略和错误分析。
//! This module provides complete error handling mechanisms, including error type definitions, error recovery strategies, and error analysis.

use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// 工作流错误类型 / Workflow Error Types
///
/// 定义了工作流系统中可能出现的各种错误类型。
/// Defines various error types that may occur in the workflow system.
#[derive(Debug, thiserror::Error, Clone, Serialize, Deserialize)]
pub enum WorkflowError {
    /// 工作流定义不存在 / Workflow definition not found
    #[error("工作流定义不存在 / Workflow definition not found: {0}")]
    WorkflowNotFound(String),

    /// 工作流实例不存在 / Workflow instance not found
    #[error("工作流实例不存在 / Workflow instance not found: {0}")]
    InstanceNotFound(String),

    /// 状态转换无效 / Invalid state transition
    #[error("状态转换无效 / Invalid state transition: {from} -> {to}")]
    InvalidStateTransition { from: String, to: String },

    /// 执行超时 / Execution timeout
    #[error("执行超时 / Execution timeout: {0}")]
    ExecutionTimeout(String),

    /// 事件通道关闭 / Event channel closed
    #[error("事件通道关闭 / Event channel closed")]
    EventChannelClosed,

    /// 并发访问冲突 / Concurrent access conflict
    #[error("并发访问冲突 / Concurrent access conflict")]
    ConcurrentAccessConflict,

    /// 资源限制超出 / Resource limit exceeded
    #[error("资源限制超出 / Resource limit exceeded: {0}")]
    ResourceLimitExceeded(String),

    /// 验证错误 / Validation error
    #[error("验证错误 / Validation error: {0}")]
    ValidationError(String),

    /// 数据序列化错误 / Data serialization error
    #[error("数据序列化错误 / Data serialization error: {0}")]
    SerializationError(String),

    /// 网络错误 / Network error
    #[error("网络错误 / Network error: {0}")]
    NetworkError(String),

    /// 存储错误 / Storage error
    #[error("存储错误 / Storage error: {0}")]
    StorageError(String),

    /// 权限错误 / Permission error
    #[error("权限错误 / Permission error: {0}")]
    PermissionError(String),

    /// 配置错误 / Configuration error
    #[error("配置错误 / Configuration error: {0}")]
    ConfigurationError(String),

    /// 内部错误 / Internal error
    #[error("内部错误 / Internal error: {0}")]
    InternalError(String),
}

/// 错误严重程度 / Error Severity Levels
///
/// 定义了错误的严重程度，用于错误分类和处理优先级。
/// Defines error severity levels for error classification and handling priority.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ErrorSeverity {
    /// 低严重程度 - 可恢复 / Low severity - recoverable
    Low,
    /// 中等严重程度 - 需要关注 / Medium severity - requires attention
    Medium,
    /// 高严重程度 - 需要立即处理 / High severity - requires immediate attention
    High,
    /// 严重错误 - 系统可能不可用 / Critical error - system may be unavailable
    Critical,
}

/// 错误上下文 / Error Context
///
/// 提供错误的详细上下文信息，便于调试和错误分析。
/// Provides detailed context information for errors to facilitate debugging and error analysis.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorContext {
    /// 错误发生时间 / Error occurrence time
    #[serde(with = "timestamp_serde")]
    pub timestamp: Instant,
    /// 错误发生位置 / Error location
    pub location: String,
    /// 错误上下文数据 / Error context data
    pub context_data: HashMap<String, serde_json::Value>,
    /// 错误堆栈信息 / Error stack information
    pub stack_trace: Option<String>,
    /// 用户ID / User ID
    pub user_id: Option<String>,
    /// 会话ID / Session ID
    pub session_id: Option<String>,
    /// 请求ID / Request ID
    pub request_id: Option<String>,
}

impl ErrorContext {
    /// 创建新的错误上下文 / Create new error context
    pub fn new(location: String) -> Self {
        Self {
            timestamp: Instant::now(),
            location,
            context_data: HashMap::new(),
            stack_trace: None,
            user_id: None,
            session_id: None,
            request_id: None,
        }
    }

    /// 添加上下文数据 / Add context data
    pub fn add_context_data(&mut self, key: String, value: serde_json::Value) {
        self.context_data.insert(key, value);
    }

    /// 设置堆栈跟踪 / Set stack trace
    pub fn set_stack_trace(&mut self, stack_trace: String) {
        self.stack_trace = Some(stack_trace);
    }

    /// 设置用户信息 / Set user information
    pub fn set_user_info(&mut self, user_id: String, session_id: Option<String>) {
        self.user_id = Some(user_id);
        self.session_id = session_id;
    }

    /// 设置请求信息 / Set request information
    pub fn set_request_info(&mut self, request_id: String) {
        self.request_id = Some(request_id);
    }
}

/// 增强的错误信息 / Enhanced Error Information
///
/// 包含错误类型、严重程度和上下文的完整错误信息。
/// Complete error information including error type, severity, and context.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnhancedError {
    /// 错误类型 / Error type
    pub error: WorkflowError,
    /// 错误严重程度 / Error severity
    pub severity: ErrorSeverity,
    /// 错误上下文 / Error context
    pub context: ErrorContext,
    /// 错误代码 / Error code
    pub error_code: Option<String>,
    /// 错误消息 / Error message
    pub message: String,
    /// 建议的解决方案 / Suggested solution
    pub suggested_solution: Option<String>,
}

impl EnhancedError {
    /// 创建新的增强错误 / Create new enhanced error
    pub fn new(error: WorkflowError, severity: ErrorSeverity, location: String) -> Self {
        let context = ErrorContext::new(location);
        let message = error.to_string();

        Self {
            error,
            severity,
            context,
            error_code: None,
            message,
            suggested_solution: None,
        }
    }

    /// 设置错误代码 / Set error code
    pub fn with_error_code(mut self, error_code: String) -> Self {
        self.error_code = Some(error_code);
        self
    }

    /// 设置建议解决方案 / Set suggested solution
    pub fn with_suggested_solution(mut self, solution: String) -> Self {
        self.suggested_solution = Some(solution);
        self
    }

    /// 获取错误严重程度 / Get error severity
    pub fn get_severity(&self) -> ErrorSeverity {
        self.severity.clone()
    }

    /// 检查是否为可恢复错误 / Check if error is recoverable
    pub fn is_recoverable(&self) -> bool {
        matches!(self.severity, ErrorSeverity::Low | ErrorSeverity::Medium)
    }

    /// 检查是否需要立即处理 / Check if immediate attention is required
    pub fn requires_immediate_attention(&self) -> bool {
        matches!(self.severity, ErrorSeverity::High | ErrorSeverity::Critical)
    }
}

/// 错误恢复策略 / Error Recovery Strategies
///
/// 定义了各种错误恢复策略和实现机制。
/// Defines various error recovery strategies and implementation mechanisms.
pub trait ErrorRecovery {
    /// 重试策略 / Retry strategy
    fn retry_with_backoff(&self, max_retries: usize, initial_delay: Duration) -> RetryStrategy;

    /// 回滚策略 / Rollback strategy
    fn rollback_to_checkpoint(&self, checkpoint_id: String) -> Result<(), WorkflowError>;

    /// 补偿策略 / Compensation strategy
    fn execute_compensation(&self, compensation_action: String) -> Result<(), WorkflowError>;

    /// 降级策略 / Degradation strategy
    fn execute_degradation(&self, degraded_mode: String) -> Result<(), WorkflowError>;

    /// 故障转移策略 / Failover strategy
    fn execute_failover(&self, backup_system: String) -> Result<(), WorkflowError>;
}

/// 重试策略 / Retry Strategy
///
/// 定义了指数退避重试策略的实现。
/// Defines implementation of exponential backoff retry strategy.
#[derive(Debug, Clone)]
pub struct RetryStrategy {
    /// 最大重试次数 / Maximum retry count
    pub max_retries: usize,
    /// 初始延迟 / Initial delay
    pub initial_delay: Duration,
    /// 最大延迟 / Maximum delay
    pub max_delay: Duration,
    /// 退避因子 / Backoff factor
    pub backoff_factor: f64,
    /// 当前重试次数 / Current retry count
    pub current_retry: usize,
    /// 最后重试时间 / Last retry time
    pub last_retry: Option<Instant>,
}

impl RetryStrategy {
    /// 创建新的重试策略 / Create new retry strategy
    pub fn new(max_retries: usize, initial_delay: Duration) -> Self {
        Self {
            max_retries,
            initial_delay,
            max_delay: Duration::from_secs(300), // 5 minutes
            backoff_factor: 2.0,
            current_retry: 0,
            last_retry: None,
        }
    }

    /// 计算下次重试延迟 / Calculate next retry delay
    pub fn calculate_next_delay(&self) -> Duration {
        if self.current_retry == 0 {
            self.initial_delay
        } else {
            let delay = self
                .initial_delay
                .mul_f64(self.backoff_factor.powi(self.current_retry as i32));
            delay.min(self.max_delay)
        }
    }

    /// 检查是否可以重试 / Check if retry is possible
    pub fn can_retry(&self) -> bool {
        self.current_retry < self.max_retries
    }

    /// 记录重试 / Record retry
    pub fn record_retry(&mut self) {
        self.current_retry += 1;
        self.last_retry = Some(Instant::now());
    }

    /// 重置重试计数 / Reset retry count
    pub fn reset(&mut self) {
        self.current_retry = 0;
        self.last_retry = None;
    }
}

/// 错误分析器 / Error Analyzer
///
/// 提供错误分析和模式识别功能。
/// Provides error analysis and pattern recognition functionality.
pub struct ErrorAnalyzer {
    /// 错误历史 / Error history
    error_history: Vec<EnhancedError>,
    /// 错误模式 / Error patterns
    error_patterns: HashMap<String, ErrorPattern>,
    /// 分析配置 / Analysis configuration
    config: ErrorAnalysisConfig,
}

/// 错误模式 / Error Pattern
///
/// 定义了错误模式的结构和特征。
/// Defines the structure and characteristics of error patterns.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorPattern {
    /// 模式名称 / Pattern name
    pub name: String,
    /// 错误类型 / Error types
    pub error_types: Vec<String>,
    /// 发生频率 / Occurrence frequency
    pub frequency: u64,
    /// 平均严重程度 / Average severity
    pub avg_severity: ErrorSeverity,
    /// 常见原因 / Common causes
    pub common_causes: Vec<String>,
    /// 建议解决方案 / Suggested solutions
    pub suggested_solutions: Vec<String>,
    /// 首次出现时间 / First occurrence time
    #[serde(with = "timestamp_serde")]
    pub first_occurrence: Instant,
    /// 最后出现时间 / Last occurrence time
    #[serde(with = "timestamp_serde")]
    pub last_occurrence: Instant,
}

/// 错误分析配置 / Error Analysis Configuration
#[derive(Debug, Clone)]
pub struct ErrorAnalysisConfig {
    /// 历史保留时间 / History retention time
    pub history_retention: Duration,
    /// 模式识别阈值 / Pattern recognition threshold
    pub pattern_threshold: u64,
    /// 自动分析间隔 / Auto analysis interval
    pub auto_analysis_interval: Duration,
    /// 启用实时分析 / Enable real-time analysis
    pub enable_real_time_analysis: bool,
}

impl Default for ErrorAnalysisConfig {
    fn default() -> Self {
        Self {
            history_retention: Duration::from_secs(86400 * 30), // 30 days
            pattern_threshold: 5,
            auto_analysis_interval: Duration::from_secs(3600), // 1 hour
            enable_real_time_analysis: true,
        }
    }
}

impl ErrorAnalyzer {
    /// 创建新的错误分析器 / Create new error analyzer
    pub fn new() -> Self {
        Self::with_config(ErrorAnalysisConfig::default())
    }

    /// 使用配置创建错误分析器 / Create error analyzer with configuration
    pub fn with_config(config: ErrorAnalysisConfig) -> Self {
        Self {
            error_history: Vec::new(),
            error_patterns: HashMap::new(),
            config,
        }
    }

    /// 记录错误 / Record error
    pub fn record_error(&mut self, error: EnhancedError) {
        self.error_history.push(error.clone());

        // 实时模式识别 / Real-time pattern recognition
        if self.config.enable_real_time_analysis {
            self.analyze_patterns();
        }

        // 清理过期历史 / Clean expired history
        self.cleanup_old_history();
    }

    /// 分析错误模式 / Analyze error patterns
    pub fn analyze_patterns(&mut self) {
        let mut pattern_groups: HashMap<String, Vec<&EnhancedError>> = HashMap::new();

        // 按错误类型分组 / Group by error type
        for error in &self.error_history {
            let error_type = format!("{:?}", error.error);
            pattern_groups
                .entry(error_type)
                .or_insert_with(Vec::new)
                .push(error);
        }

        // 识别模式 / Identify patterns
        for (error_type, errors) in pattern_groups {
            if errors.len() >= self.config.pattern_threshold as usize {
                let pattern = self.create_error_pattern(&error_type, errors);
                self.error_patterns.insert(error_type, pattern);
            }
        }
    }

    /// 创建错误模式 / Create error pattern
    fn create_error_pattern(&self, error_type: &str, errors: Vec<&EnhancedError>) -> ErrorPattern {
        let frequency = errors.len() as u64;
        let avg_severity = self.calculate_average_severity(&errors);
        let common_causes = self.extract_common_causes(&errors);
        let suggested_solutions = self.extract_suggested_solutions(&errors);

        let first_occurrence = errors
            .iter()
            .map(|e| e.context.timestamp)
            .min()
            .unwrap_or(Instant::now());
        let last_occurrence = errors
            .iter()
            .map(|e| e.context.timestamp)
            .max()
            .unwrap_or(Instant::now());

        ErrorPattern {
            name: error_type.to_string(),
            error_types: vec![error_type.to_string()],
            frequency,
            avg_severity,
            common_causes,
            suggested_solutions,
            first_occurrence,
            last_occurrence,
        }
    }

    /// 计算平均严重程度 / Calculate average severity
    fn calculate_average_severity(&self, errors: &[&EnhancedError]) -> ErrorSeverity {
        let severity_scores: Vec<u8> = errors
            .iter()
            .map(|e| match e.severity {
                ErrorSeverity::Low => 1,
                ErrorSeverity::Medium => 2,
                ErrorSeverity::High => 3,
                ErrorSeverity::Critical => 4,
            })
            .collect();

        let avg_score = severity_scores.iter().sum::<u8>() as f64 / severity_scores.len() as f64;

        match avg_score {
            s if s < 1.5 => ErrorSeverity::Low,
            s if s < 2.5 => ErrorSeverity::Medium,
            s if s < 3.5 => ErrorSeverity::High,
            _ => ErrorSeverity::Critical,
        }
    }

    /// 提取常见原因 / Extract common causes
    fn extract_common_causes(&self, _errors: &[&EnhancedError]) -> Vec<String> {
        // 这里可以实现更复杂的模式识别算法
        // Here you can implement more complex pattern recognition algorithms
        vec![
            "网络连接问题 / Network connectivity issues".to_string(),
            "资源不足 / Insufficient resources".to_string(),
            "配置错误 / Configuration errors".to_string(),
        ]
    }

    /// 提取建议解决方案 / Extract suggested solutions
    fn extract_suggested_solutions(&self, _errors: &[&EnhancedError]) -> Vec<String> {
        vec![
            "检查网络连接 / Check network connectivity".to_string(),
            "增加系统资源 / Increase system resources".to_string(),
            "验证配置参数 / Verify configuration parameters".to_string(),
        ]
    }

    /// 清理过期历史 / Cleanup old history
    fn cleanup_old_history(&mut self) {
        let cutoff_time = Instant::now() - self.config.history_retention;
        self.error_history
            .retain(|error| error.context.timestamp > cutoff_time);
    }

    /// 获取错误统计 / Get error statistics
    pub fn get_error_statistics(&self) -> ErrorStatistics {
        let total_errors = self.error_history.len();
        let severity_counts = self.calculate_severity_counts();
        let recent_errors = self.get_recent_errors(Duration::from_secs(3600)); // Last hour

        ErrorStatistics {
            total_errors,
            severity_counts,
            recent_errors,
            patterns: self.error_patterns.clone(),
        }
    }

    /// 计算严重程度计数 / Calculate severity counts
    fn calculate_severity_counts(&self) -> HashMap<ErrorSeverity, u64> {
        let mut counts = HashMap::new();
        for error in &self.error_history {
            *counts.entry(error.severity.clone()).or_insert(0) += 1;
        }
        counts
    }

    /// 获取最近错误 / Get recent errors
    fn get_recent_errors(&self, duration: Duration) -> Vec<EnhancedError> {
        let cutoff_time = Instant::now() - duration;
        self.error_history
            .iter()
            .filter(|error| error.context.timestamp > cutoff_time)
            .cloned()
            .collect()
    }
}

/// 错误统计 / Error Statistics
///
/// 提供错误统计信息的结构。
/// Structure providing error statistics information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorStatistics {
    /// 总错误数 / Total error count
    pub total_errors: usize,
    /// 严重程度分布 / Severity distribution
    pub severity_counts: HashMap<ErrorSeverity, u64>,
    /// 最近错误 / Recent errors
    pub recent_errors: Vec<EnhancedError>,
    /// 错误模式 / Error patterns
    pub patterns: HashMap<String, ErrorPattern>,
}

/// 错误处理工具 / Error Handling Utilities
///
/// 提供错误处理的工具函数。
/// Provides utility functions for error handling.
mod timestamp_serde {
    use super::*;

    pub fn serialize<S>(instant: &Instant, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_u64(instant.elapsed().as_nanos() as u64)
    }

    pub fn deserialize<'de, D>(deserializer: D) -> Result<Instant, D::Error>
    where
        D: Deserializer<'de>,
    {
        let nanos = u64::deserialize(deserializer)?;
        Ok(Instant::now() - Duration::from_nanos(nanos))
    }
}

pub mod utils {
    use super::*;

    /// 创建标准错误上下文 / Create standard error context
    pub fn create_standard_context(
        location: &str,
        additional_data: Option<HashMap<String, serde_json::Value>>,
    ) -> ErrorContext {
        let mut context = ErrorContext::new(location.to_string());

        if let Some(data) = additional_data {
            for (key, value) in data {
                context.add_context_data(key, value);
            }
        }

        context
    }

    /// 确定错误严重程度 / Determine error severity
    pub fn determine_severity(error: &WorkflowError) -> ErrorSeverity {
        match error {
            WorkflowError::WorkflowNotFound(_) => ErrorSeverity::Medium,
            WorkflowError::InstanceNotFound(_) => ErrorSeverity::Medium,
            WorkflowError::InvalidStateTransition { .. } => ErrorSeverity::High,
            WorkflowError::ExecutionTimeout(_) => ErrorSeverity::Medium,
            WorkflowError::EventChannelClosed => ErrorSeverity::Critical,
            WorkflowError::ConcurrentAccessConflict => ErrorSeverity::High,
            WorkflowError::ResourceLimitExceeded(_) => ErrorSeverity::High,
            WorkflowError::ValidationError(_) => ErrorSeverity::Medium,
            WorkflowError::SerializationError(_) => ErrorSeverity::Medium,
            WorkflowError::NetworkError(_) => ErrorSeverity::Medium,
            WorkflowError::StorageError(_) => ErrorSeverity::High,
            WorkflowError::PermissionError(_) => ErrorSeverity::High,
            WorkflowError::ConfigurationError(_) => ErrorSeverity::Medium,
            WorkflowError::InternalError(_) => ErrorSeverity::Critical,
        }
    }

    /// 生成错误代码 / Generate error code
    pub fn generate_error_code(error: &WorkflowError) -> String {
        match error {
            WorkflowError::WorkflowNotFound(_) => "WF001".to_string(),
            WorkflowError::InstanceNotFound(_) => "WF002".to_string(),
            WorkflowError::InvalidStateTransition { .. } => "WF003".to_string(),
            WorkflowError::ExecutionTimeout(_) => "WF004".to_string(),
            WorkflowError::EventChannelClosed => "WF005".to_string(),
            WorkflowError::ConcurrentAccessConflict => "WF006".to_string(),
            WorkflowError::ResourceLimitExceeded(_) => "WF007".to_string(),
            WorkflowError::ValidationError(_) => "WF008".to_string(),
            WorkflowError::SerializationError(_) => "WF009".to_string(),
            WorkflowError::NetworkError(_) => "WF010".to_string(),
            WorkflowError::StorageError(_) => "WF011".to_string(),
            WorkflowError::PermissionError(_) => "WF012".to_string(),
            WorkflowError::ConfigurationError(_) => "WF013".to_string(),
            WorkflowError::InternalError(_) => "WF014".to_string(),
        }
    }

    /// 提供建议解决方案 / Provide suggested solution
    pub fn provide_suggested_solution(error: &WorkflowError) -> Option<String> {
        match error {
            WorkflowError::WorkflowNotFound(name) => {
                Some(format!("检查工作流定义是否存在: {}", name))
            }
            WorkflowError::InstanceNotFound(id) => Some(format!("检查实例ID是否正确: {}", id)),
            WorkflowError::InvalidStateTransition { from, to } => {
                Some(format!("验证状态转换规则: {} -> {}", from, to))
            }
            WorkflowError::ExecutionTimeout(details) => {
                Some(format!("增加超时时间或优化执行逻辑: {}", details))
            }
            WorkflowError::EventChannelClosed => {
                Some("重启工作流引擎或检查事件通道状态".to_string())
            }
            WorkflowError::ConcurrentAccessConflict => {
                Some("使用适当的同步机制或重试操作".to_string())
            }
            WorkflowError::ResourceLimitExceeded(details) => {
                Some(format!("增加系统资源或优化资源使用: {}", details))
            }
            _ => None,
        }
    }
}
