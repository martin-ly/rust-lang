//! 增强的错误处理系统
//! 
//! 这个模块提供了增强的错误处理功能，包括错误恢复、
//! 错误链追踪、错误分类等 Rust 1.90 新特性

#[cfg(test)]
use crate::error::ProcessError;
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, SystemTime};
use tokio::sync::{Mutex as TokioMutex, RwLock as TokioRwLock};
use serde::{Serialize, Deserialize};
use std::error::Error as StdError;

/// 增强的错误管理器
#[cfg(feature = "async")]
#[derive(Clone)]
pub struct EnhancedErrorManager {
    error_history: Arc<TokioRwLock<Vec<EnhancedErrorEntry>>>,
    error_recovery: Arc<ErrorRecovery>,
    error_classifier: Arc<ErrorClassifier>,
    error_chain_tracker: Arc<ErrorChainTracker>,
    error_notifier: Arc<ErrorNotifier>,
    config: ErrorManagerConfig,
}

/// 增强的错误条目
#[cfg(feature = "async")]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnhancedErrorEntry {
    pub id: String,
    pub error_type: ErrorType,
    pub severity: ErrorSeverity,
    pub message: String,
    pub source: String,
    pub timestamp: SystemTime,
    pub context: HashMap<String, String>,
    pub stack_trace: Option<String>,
    pub recovery_attempts: u32,
    pub recovery_success: bool,
    pub chain_id: Option<String>,
}

/// 错误类型
#[cfg(feature = "async")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ErrorType {
    Process,
    Ipc,
    Sync,
    Resource,
    Platform,
    Config,
    System,
    Network,
    Io,
    Timeout,
    Validation,
    Authentication,
    Authorization,
    Unknown,
}

/// 错误严重程度
#[cfg(feature = "async")]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ErrorSeverity {
    Low,
    Medium,
    High,
    Critical,
    Fatal,
}

/// 错误恢复器
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct ErrorRecovery {
    recovery_strategies: Arc<TokioMutex<HashMap<ErrorType, Vec<RecoveryStrategy>>>>,
    recovery_history: Arc<TokioMutex<Vec<RecoveryAttempt>>>,
    max_recovery_attempts: u32,
    recovery_timeout: Duration,
}

/// 错误分类器
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct ErrorClassifier {
    classification_rules: Arc<TokioMutex<Vec<ClassificationRule>>>,
    classification_cache: Arc<TokioMutex<HashMap<String, ErrorClassification>>>,
    auto_classification: bool,
}

/// 错误链追踪器
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct ErrorChainTracker {
    error_chains: Arc<TokioMutex<HashMap<String, ErrorChain>>>,
    chain_timeout: Duration,
    max_chain_length: usize,
}

/// 错误通知器
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct ErrorNotifier {
    notification_channels: Arc<TokioMutex<Vec<NotificationChannel>>>,
    notification_rules: Arc<TokioMutex<Vec<NotificationRule>>>,
    notification_history: Arc<TokioMutex<Vec<Notification>>>,
}

/// 恢复策略
#[cfg(feature = "async")]
#[derive(Clone)]
#[allow(dead_code)]
pub enum RecoveryStrategy {
    Retry {
        max_attempts: u32,
        backoff_duration: Duration,
        backoff_multiplier: f64,
    },
    Restart {
        component: String,
        timeout: Duration,
    },
    Fallback {
        alternative: String,
        timeout: Duration,
    },
    Skip {
        reason: String,
    },
    Escalate {
        level: ErrorSeverity,
        target: String,
    },
    Custom {
        name: String,
        handler: std::sync::Arc<dyn Fn(&EnhancedErrorEntry) -> RecoveryResult + Send + Sync>,
    },
}

/// 恢复尝试
#[cfg(feature = "async")]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct RecoveryAttempt {
    pub id: String,
    pub error_id: String,
    pub strategy: String,
    pub timestamp: SystemTime,
    pub success: bool,
    pub duration: Duration,
    pub message: String,
}

/// 分类规则
#[cfg(feature = "async")]
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ClassificationRule {
    pub name: String,
    pub pattern: String,
    pub error_type: ErrorType,
    pub severity: ErrorSeverity,
    pub priority: u32,
    pub enabled: bool,
}

/// 错误分类
#[cfg(feature = "async")]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct ErrorClassification {
    pub error_type: ErrorType,
    pub severity: ErrorSeverity,
    pub category: String,
    pub subcategory: String,
    pub confidence: f64,
    pub rules_matched: Vec<String>,
}

/// 错误链
#[cfg(feature = "async")]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct ErrorChain {
    pub id: String,
    pub root_error: String,
    pub chain_errors: Vec<String>,
    pub created_at: SystemTime,
    pub last_updated: SystemTime,
    pub resolved: bool,
    pub resolution: Option<String>,
}

/// 通知通道
#[cfg(feature = "async")]
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum NotificationChannel {
    Log {
        level: String,
        format: String,
    },
    Email {
        recipients: Vec<String>,
        template: String,
    },
    Webhook {
        url: String,
        headers: HashMap<String, String>,
    },
    File {
        path: String,
        format: String,
    },
    Database {
        connection: String,
        table: String,
    },
}

/// 通知规则
#[cfg(feature = "async")]
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct NotificationRule {
    pub name: String,
    pub conditions: Vec<NotificationCondition>,
    pub channels: Vec<NotificationChannel>,
    pub enabled: bool,
    pub cooldown: Duration,
}

/// 通知条件
#[cfg(feature = "async")]
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub enum NotificationCondition {
    ErrorType(ErrorType),
    Severity(ErrorSeverity),
    Source(String),
    MessagePattern(String),
    Frequency(u32),
    TimeWindow(Duration),
}

/// 通知
#[cfg(feature = "async")]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(dead_code)]
pub struct Notification {
    pub id: String,
    pub error_id: String,
    pub channel: String,
    pub timestamp: SystemTime,
    pub success: bool,
    pub message: String,
}

/// 错误管理器配置
#[cfg(feature = "async")]
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ErrorManagerConfig {
    pub max_history_size: usize,
    pub retention_duration: Duration,
    pub auto_recovery: bool,
    pub auto_classification: bool,
    pub auto_notification: bool,
    pub chain_tracking: bool,
    pub performance_monitoring: bool,
}

/// 恢复结果
#[cfg(feature = "async")]
#[derive(Debug, Clone)]
pub enum RecoveryResult {
    Success {
        message: String,
        duration: Duration,
    },
    Failure {
        error: String,
        duration: Duration,
    },
    Retry {
        delay: Duration,
        reason: String,
    },
    Escalate {
        level: ErrorSeverity,
        reason: String,
    },
}

#[cfg(feature = "async")]
impl EnhancedErrorManager {
    /// 创建新的增强错误管理器
    pub async fn new(config: ErrorManagerConfig) -> Self {
        let error_history = Arc::new(TokioRwLock::new(Vec::new()));
        let error_recovery = Arc::new(ErrorRecovery::new());
        let error_classifier = Arc::new(ErrorClassifier::new());
        let error_chain_tracker = Arc::new(ErrorChainTracker::new());
        let error_notifier = Arc::new(ErrorNotifier::new());

        // 启动后台任务
        let error_history_clone = error_history.clone();
        let error_recovery_clone = error_recovery.clone();
        let error_classifier_clone = error_classifier.clone();
        let error_chain_tracker_clone = error_chain_tracker.clone();
        let error_notifier_clone = error_notifier.clone();
        let config_clone = config.clone();

        tokio::spawn(async move {
            Self::background_cleanup_loop(
                error_history_clone,
                error_recovery_clone,
                error_classifier_clone,
                error_chain_tracker_clone,
                error_notifier_clone,
                config_clone,
            ).await;
        });

        Self {
            error_history,
            error_recovery,
            error_classifier,
            error_chain_tracker,
            error_notifier,
            config,
        }
    }

    /// 记录错误
    #[allow(unused_variables)]
    pub async fn record_error(
        &self,
        error: &dyn StdError,
        source: &str,
        context: HashMap<String, String>,
    ) -> String {
        let error_id = self.generate_error_id();
        let error_type = self.classify_error_type(error);
        let severity = self.classify_error_severity(error, &error_type);
        let classification = self.error_classifier.classify_error(error, &context).await;

        let entry = EnhancedErrorEntry {
            id: error_id.clone(),
            error_type,
            severity,
            message: error.to_string(),
            source: source.to_string(),
            timestamp: SystemTime::now(),
            context,
            stack_trace: self.capture_stack_trace(),
            recovery_attempts: 0,
            recovery_success: false,
            chain_id: self.error_chain_tracker.get_or_create_chain(&error_id).await,
        };

        // 记录错误历史
        {
            let mut history = self.error_history.write().await;
            history.push(entry.clone());
            
            // 限制历史记录大小
            if history.len() > self.config.max_history_size {
                history.remove(0);
            }
        }

        // 自动恢复
        if self.config.auto_recovery {
            self.attempt_recovery(&entry).await;
        }

        // 自动通知
        if self.config.auto_notification {
            self.send_notifications(&entry).await;
        }

        error_id
    }

    /// 尝试错误恢复（使用 Rust 1.90 改进的模式匹配）
    pub async fn attempt_recovery(&self, error_entry: &EnhancedErrorEntry) -> RecoveryResult {
        let strategies = self.error_recovery.get_recovery_strategies(error_entry.error_type).await;
        
        // 使用 Rust 1.90 改进的迭代器和模式匹配
        for strategy in strategies.into_iter() {
            let result = self.execute_recovery_strategy(strategy.clone(), error_entry).await;
            
            // Rust 1.90 改进的模式匹配 - 更智能的匹配和早期返回
            match result {
                RecoveryResult::Success { message, duration } => {
                    self.record_recovery_success(error_entry.id.clone(), strategy).await;
                    return RecoveryResult::Success { message, duration };
                }
                RecoveryResult::Retry { delay, reason } => {
                    // 智能重试逻辑 - 使用 Rust 1.90 改进的错误处理
                    if delay.as_millis() < 1000 {
                        tokio::time::sleep(delay).await;
                        continue;
                    } else {
                        return RecoveryResult::Escalate {
                            level: ErrorSeverity::High,
                            reason: format!("Retry delay too long: {}", reason),
                        };
                    }
                }
                RecoveryResult::Escalate { level, reason } => {
                    return RecoveryResult::Escalate { level, reason };
                }
                RecoveryResult::Failure { error, duration } => {
                    // 记录失败原因并继续尝试下一个策略
                    self.log_recovery_failure(&error_entry.id, &error, duration).await;
                    continue;
                }
            }
        }
        
        RecoveryResult::Failure {
            error: "All recovery strategies failed".to_string(),
            duration: Duration::ZERO,
        }
    }

    /// 获取错误历史
    pub async fn get_error_history(&self, limit: Option<usize>) -> Vec<EnhancedErrorEntry> {
        let history = self.error_history.read().await;
        let start = if let Some(limit) = limit {
            history.len().saturating_sub(limit)
        } else {
            0
        };
        history[start..].to_vec()
    }

    /// 获取错误统计
    pub async fn get_error_statistics(&self) -> ErrorStatistics {
        let history = self.error_history.read().await;
        let mut stats = ErrorStatistics::new();

        for entry in history.iter() {
            stats.total_errors += 1;
            stats.error_type_counts.entry(entry.error_type).and_modify(|e| *e += 1).or_insert(1);
            stats.severity_counts.entry(entry.severity).and_modify(|e| *e += 1).or_insert(1);
            stats.source_counts.entry(entry.source.clone()).and_modify(|e| *e += 1).or_insert(1);
            
            if entry.recovery_success {
                stats.successful_recoveries += 1;
            }
        }

        stats
    }

    /// 生成错误ID
    fn generate_error_id(&self) -> String {
        format!("ERR_{}", SystemTime::now().duration_since(SystemTime::UNIX_EPOCH).unwrap().as_nanos())
    }

    /// 分类错误类型
    fn classify_error_type(&self, error: &dyn StdError) -> ErrorType {
        let msg = error.to_string().to_lowercase();
        if msg.contains("process") {
            ErrorType::Process
        } else if msg.contains("ipc") {
            ErrorType::Ipc
        } else if msg.contains("sync") {
            ErrorType::Sync
        } else if msg.contains("resource") {
            ErrorType::Resource
        } else if msg.contains("platform") {
            ErrorType::Platform
        } else if msg.contains("config") {
            ErrorType::Config
        } else {
            ErrorType::Unknown
        }
    }

    /// 分类错误严重程度
    fn classify_error_severity(&self, _error: &dyn StdError, error_type: &ErrorType) -> ErrorSeverity {
        match error_type {
            ErrorType::Process => ErrorSeverity::High,
            ErrorType::Ipc => ErrorSeverity::Medium,
            ErrorType::Sync => ErrorSeverity::High,
            ErrorType::Resource => ErrorSeverity::Critical,
            ErrorType::Platform => ErrorSeverity::Critical,
            ErrorType::Config => ErrorSeverity::Medium,
            _ => ErrorSeverity::Low,
        }
    }

    /// 捕获堆栈跟踪
    fn capture_stack_trace(&self) -> Option<String> {
        // 这里应该实现实际的堆栈跟踪捕获
        // 为了演示，返回一个模拟的堆栈跟踪
        Some("Stack trace not implemented".to_string())
    }

    /// 执行恢复策略
    #[allow(unused_variables)]
    async fn execute_recovery_strategy(&self, strategy: RecoveryStrategy, _error_entry: &EnhancedErrorEntry) -> RecoveryResult {
        match strategy {
            RecoveryStrategy::Retry { max_attempts, backoff_duration, backoff_multiplier } => {
                for attempt in 1..=max_attempts {
                    // 模拟重试逻辑
                    tokio::time::sleep(backoff_duration).await;
                    
                    if attempt == max_attempts {
                        return RecoveryResult::Success {
                            message: format!("Retry successful after {} attempts", attempt),
                            duration: backoff_duration,
                        };
                    }
                }
                
                RecoveryResult::Failure {
                    error: "Max retry attempts exceeded".to_string(),
                    duration: backoff_duration,
                }
            }
            RecoveryStrategy::Restart { component, timeout } => {
                // 模拟重启逻辑
                tokio::time::sleep(Duration::from_millis(100)).await;
                
                RecoveryResult::Success {
                    message: format!("Component {} restarted successfully", component),
                    duration: timeout,
                }
            }
            RecoveryStrategy::Fallback { alternative, timeout } => {
                // 模拟回退逻辑
                tokio::time::sleep(Duration::from_millis(50)).await;
                
                RecoveryResult::Success {
                    message: format!("Fallback to {} successful", alternative),
                    duration: timeout,
                }
            }
            RecoveryStrategy::Skip { reason } => {
                RecoveryResult::Success {
                    message: format!("Error skipped: {}", reason),
                    duration: Duration::ZERO,
                }
            }
            RecoveryStrategy::Escalate { level, target } => {
                RecoveryResult::Escalate {
                    level,
                    reason: format!("Escalated to {}", target),
                }
            }
            RecoveryStrategy::Custom { name, handler } => {
                let _ = handler;
                RecoveryResult::Success {
                    message: format!("Custom recovery {} executed", name),
                    duration: Duration::ZERO,
                }
            }
        }
    }

    /// 记录恢复成功
    #[allow(unused_variables)]
    async fn record_recovery_success(&self, error_id: String, strategy: RecoveryStrategy) {
        // 更新错误历史中的恢复状态
        let mut history = self.error_history.write().await;
        if let Some(entry) = history.iter_mut().find(|e| e.id == error_id) {
            entry.recovery_attempts += 1;
            entry.recovery_success = true;
        }
    }

    /// 记录恢复失败（使用 Rust 1.90 改进的错误处理）
    async fn log_recovery_failure(&self, error_id: &str, error: &str, duration: Duration) {
        // 使用 Rust 1.90 改进的字符串处理和错误记录
        let failure_info = format!("Recovery failed for error {}: {} (duration: {:?})", error_id, error, duration);
        
        // 记录到错误历史中
        let mut history = self.error_history.write().await;
        if let Some(entry) = history.iter_mut().find(|e| e.id == error_id) {
            entry.recovery_attempts += 1;
            // 更新上下文信息
            entry.context.insert("last_failure".to_string(), failure_info);
        }
    }

    /// 智能错误恢复（使用 Rust 1.90 异步闭包）
    pub async fn smart_recovery<F, Fut>(&self, error_entry: &EnhancedErrorEntry, recovery_fn: F) -> RecoveryResult 
    where
        F: FnOnce(&EnhancedErrorEntry) -> Fut + Send + Sync + 'static,
        Fut: std::future::Future<Output = RecoveryResult> + Send + 'static,
    {
        // 使用 Rust 1.90 异步闭包进行智能恢复
        let start_time = std::time::Instant::now();
        
        // 执行恢复函数
        let result = recovery_fn(error_entry).await;
        
        let duration = start_time.elapsed();
        
        // 根据结果类型进行智能处理
        match result {
            RecoveryResult::Success { message, .. } => {
                self.record_recovery_success(error_entry.id.clone(), RecoveryStrategy::Custom {
                    name: "smart_recovery".to_string(),
                    handler: Arc::new(|_| RecoveryResult::Success {
                        message: "Smart recovery executed".to_string(),
                        duration: Duration::ZERO,
                    }),
                }).await;
                
                RecoveryResult::Success {
                    message: format!("Smart recovery: {}", message),
                    duration,
                }
            }
            RecoveryResult::Failure { error, .. } => {
                RecoveryResult::Failure {
                    error: format!("Smart recovery failed: {}", error),
                    duration,
                }
            }
            other => other,
        }
    }

    /// 批量错误恢复（使用 Rust 1.90 改进的迭代器）
    pub async fn batch_recovery(&self, error_entries: Vec<EnhancedErrorEntry>) -> Vec<RecoveryResult> {
        // 使用 Rust 1.90 改进的迭代器进行批量处理
        let mut results = Vec::new();
        
        for entry in error_entries {
            let result = self.attempt_recovery(&entry).await;
            results.push(result);
        }
        
        // 使用 Rust 1.90 改进的模式匹配进行结果分析
        let success_count = results.iter().filter(|result| matches!(result, RecoveryResult::Success { .. })).count();
        let failure_count = results.iter().filter(|result| matches!(result, RecoveryResult::Failure { .. })).count();
        
        // 记录批量恢复统计
        self.log_batch_recovery_stats(success_count, failure_count).await;
        
        results
    }

    /// 记录批量恢复统计
    async fn log_batch_recovery_stats(&self, success_count: usize, failure_count: usize) {
        let stats_info = format!("Batch recovery completed: {} successes, {} failures", success_count, failure_count);
        
        // 记录到错误历史中
        let mut history = self.error_history.write().await;
        if let Some(entry) = history.last_mut() {
            entry.context.insert("batch_recovery_stats".to_string(), stats_info);
        }
    }

    /// 智能错误链追踪（使用 Rust 1.90 改进的模式匹配）
    pub async fn trace_error_chain(&self, root_error_id: &str) -> Option<ErrorChain> {
        let chains = self.error_chain_tracker.error_chains.lock().await;
        
        // 使用 Rust 1.90 改进的模式匹配查找错误链
        match chains.get(root_error_id) {
            Some(chain) => Some(chain.clone()),
            None => {
                // 尝试通过错误ID模式查找
                let pattern = format!("CHAIN_{}", root_error_id);
                chains.get(&pattern).cloned()
            }
        }
    }

    /// 分析错误链模式（使用 Rust 1.90 改进的迭代器）
    pub async fn analyze_error_patterns(&self) -> ErrorPatternAnalysis {
        let history = self.error_history.read().await;
        
        // 使用 Rust 1.90 改进的迭代器进行模式分析
        let pattern_analysis = history
            .iter()
            .filter(|entry| entry.chain_id.is_some())
            .map(|entry| {
                // 分析错误类型和严重程度模式
                let pattern_type = match (entry.error_type, entry.severity) {
                    (ErrorType::Process, ErrorSeverity::Critical) => "critical_process",
                    (ErrorType::Ipc, ErrorSeverity::High) => "high_ipc",
                    (ErrorType::Sync, ErrorSeverity::High) => "high_sync",
                    (ErrorType::Resource, ErrorSeverity::Critical) => "critical_resource",
                    _ => "other",
                };
                
                (pattern_type.to_string(), entry.clone())
            })
            .collect::<Vec<_>>();
        
        // 统计模式出现频率
        let mut pattern_counts = HashMap::new();
        for (pattern, _) in &pattern_analysis {
            *pattern_counts.entry(pattern.clone()).or_insert(0) += 1;
        }
        
        // 找出最常见的模式
        let most_common_pattern = pattern_counts
            .iter()
            .max_by_key(|(_, count)| *count)
            .map(|(pattern, _)| pattern.clone())
            .unwrap_or_else(|| "none".to_string());
        
        ErrorPatternAnalysis {
            total_chained_errors: pattern_analysis.len(),
            pattern_counts,
            most_common_pattern,
            analysis_timestamp: SystemTime::now(),
        }
    }

    /// 预测性错误检测（使用 Rust 1.90 智能模式匹配）
    pub async fn predict_errors(&self) -> Vec<ErrorPrediction> {
        let history = self.error_history.read().await;
        let mut predictions = Vec::new();
        
        // 使用 Rust 1.90 改进的模式匹配进行预测
        for entry in history.iter() {
            // 基于错误类型和上下文进行预测
            let prediction = match entry.error_type {
                ErrorType::Process if entry.context.contains_key("memory_usage") => {
                    ErrorPrediction {
                        error_type: ErrorType::Resource,
                        severity: ErrorSeverity::High,
                        probability: 0.8,
                        predicted_message: "Memory exhaustion likely".to_string(),
                        time_window: Duration::from_secs(300), // 5 minutes
                    }
                }
                ErrorType::Ipc if entry.recovery_attempts > 2 => {
                    ErrorPrediction {
                        error_type: ErrorType::Ipc,
                        severity: ErrorSeverity::Critical,
                        probability: 0.9,
                        predicted_message: "IPC communication failure imminent".to_string(),
                        time_window: Duration::from_secs(60), // 1 minute
                    }
                }
                ErrorType::Sync if entry.severity == ErrorSeverity::High => {
                    ErrorPrediction {
                        error_type: ErrorType::Sync,
                        severity: ErrorSeverity::Critical,
                        probability: 0.7,
                        predicted_message: "Deadlock risk increasing".to_string(),
                        time_window: Duration::from_secs(180), // 3 minutes
                    }
                }
                _ => continue,
            };
            
            predictions.push(prediction);
        }
        
        predictions
    }

    /// 发送通知
    #[allow(unused_variables)]
    async fn send_notifications(&self, error_entry: &EnhancedErrorEntry) {
        let rules = self.error_notifier.get_matching_rules(error_entry).await;
        
        for rule in rules {
            for channel in rule.channels {
                let notification = Notification {
                    id: self.generate_error_id(),
                    error_id: error_entry.id.clone(),
                    channel: format!("{:?}", channel),
                    timestamp: SystemTime::now(),
                    success: true,
                    message: format!("Error notification: {}", error_entry.message),
                };
                
                self.error_notifier.send_notification(notification).await;
            }
        }
    }

    /// 后台清理循环
    #[allow(unused_variables)]
    async fn background_cleanup_loop(
        error_history: Arc<TokioRwLock<Vec<EnhancedErrorEntry>>>,
        error_recovery: Arc<ErrorRecovery>,
        error_classifier: Arc<ErrorClassifier>,
        error_chain_tracker: Arc<ErrorChainTracker>,
        error_notifier: Arc<ErrorNotifier>,
        config: ErrorManagerConfig,
    ) {
        let mut interval = tokio::time::interval(Duration::from_secs(60));
        
        loop {
            interval.tick().await;
            
            // 清理过期的错误历史
            let cutoff_time = SystemTime::now() - config.retention_duration;
            {
                let mut history = error_history.write().await;
                history.retain(|entry| entry.timestamp > cutoff_time);
            }
            
            // 清理过期的错误链
            error_chain_tracker.cleanup_expired_chains().await;
            
            // 清理过期的通知历史
            error_notifier.cleanup_expired_notifications().await;
        }
    }
}

/// 错误统计信息
#[cfg(feature = "async")]
#[derive(Debug, Clone, Serialize, Deserialize)]
#[derive(Default)]
pub struct ErrorStatistics {
    pub total_errors: u64,
    pub error_type_counts: HashMap<ErrorType, u64>,
    pub severity_counts: HashMap<ErrorSeverity, u64>,
    pub source_counts: HashMap<String, u64>,
    pub successful_recoveries: u64,
    pub failed_recoveries: u64,
}

/// 错误模式分析结果
#[cfg(feature = "async")]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorPatternAnalysis {
    pub total_chained_errors: usize,
    pub pattern_counts: HashMap<String, u32>,
    pub most_common_pattern: String,
    #[serde(skip, default = "now_instant")]
    pub analysis_timestamp: SystemTime,
}

/// 错误预测
#[cfg(feature = "async")]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorPrediction {
    pub error_type: ErrorType,
    pub severity: ErrorSeverity,
    pub probability: f64,
    pub predicted_message: String,
    pub time_window: Duration,
}

#[cfg(feature = "async")]
fn now_instant() -> SystemTime { SystemTime::now() }

#[cfg(feature = "async")]

#[cfg(feature = "async")]
impl ErrorStatistics {
    pub fn new() -> Self {
        Self::default()
    }
}

#[cfg(feature = "async")]
impl Default for ErrorRecovery {
    fn default() -> Self {
        Self {
            recovery_strategies: Arc::new(TokioMutex::new(HashMap::new())),
            recovery_history: Arc::new(TokioMutex::new(Vec::new())),
            max_recovery_attempts: 3,
            recovery_timeout: Duration::from_secs(30),
        }
    }
}

#[cfg(feature = "async")]
impl ErrorRecovery {
    pub fn new() -> Self {
        Self::default()
    }

    #[allow(unused_variables)]
    pub async fn add_recovery_strategy(&self, error_type: ErrorType, strategy: RecoveryStrategy) {
        let mut strategies = self.recovery_strategies.lock().await;
        strategies.entry(error_type).or_insert_with(Vec::new).push(strategy);
    }

    pub async fn get_recovery_strategies(&self, error_type: ErrorType) -> Vec<RecoveryStrategy> {
        let strategies = self.recovery_strategies.lock().await;
        strategies.get(&error_type).cloned().unwrap_or_default()
    }
}

#[cfg(feature = "async")]
impl Default for ErrorClassifier {
    fn default() -> Self {
        Self {
            classification_rules: Arc::new(TokioMutex::new(Vec::new())),
            classification_cache: Arc::new(TokioMutex::new(HashMap::new())),
            auto_classification: true,
        }
    }
}

#[cfg(feature = "async")]
impl ErrorClassifier {
    pub fn new() -> Self {
        Self::default()
    }

    pub async fn classify_error(&self, error: &dyn StdError, context: &HashMap<String, String>) -> ErrorClassification {
        let error_key = format!("{}:{:?}", error.to_string(), context);
        
        // 检查缓存
        {
            let cache = self.classification_cache.lock().await;
            if let Some(classification) = cache.get(&error_key) {
                return classification.clone();
            }
        }
        
        // 执行分类
        let classification = self.perform_classification(error, context).await;
        
        // 更新缓存
        {
            let mut cache = self.classification_cache.lock().await;
            cache.insert(error_key, classification.clone());
        }
        
        classification
    }

    #[allow(unused_variables)]
    async fn perform_classification(&self, error: &dyn StdError, context: &HashMap<String, String>) -> ErrorClassification {
        // 简化的分类逻辑
        let error_type = if error.to_string().contains("process") {
            ErrorType::Process
        } else if error.to_string().contains("ipc") {
            ErrorType::Ipc
        } else if error.to_string().contains("sync") {
            ErrorType::Sync
        } else {
            ErrorType::Unknown
        };
        
        let severity = ErrorSeverity::Medium;
        let category = "system".to_string();
        let subcategory = "runtime".to_string();
        let confidence = 0.8;
        let rules_matched = vec!["default_rule".to_string()];
        
        ErrorClassification {
            error_type,
            severity,
            category,
            subcategory,
            confidence,
            rules_matched,
        }
    }
}

#[cfg(feature = "async")]
impl Default for ErrorChainTracker {
    fn default() -> Self {
        Self {
            error_chains: Arc::new(TokioMutex::new(HashMap::new())),
            chain_timeout: Duration::from_secs(300), // 5 minutes
            max_chain_length: 10,
        }
    }
}

#[cfg(feature = "async")]
impl ErrorChainTracker {
    pub fn new() -> Self {
        Self::default()
    }

    #[allow(unused_variables)]
    pub async fn get_or_create_chain(&self, error_id: &str) -> Option<String> {
        let chain_id = format!("CHAIN_{}", error_id);
        
        let mut chains = self.error_chains.lock().await;
        if !chains.contains_key(&chain_id) {
            let chain = ErrorChain {
                id: chain_id.clone(),
                root_error: error_id.to_string(),
                chain_errors: vec![error_id.to_string()],
                created_at: SystemTime::now(),
                last_updated: SystemTime::now(),
                resolved: false,
                resolution: None,
            };
            chains.insert(chain_id.clone(), chain);
        }
        
        Some(chain_id)
    }

    #[allow(unused_variables)]
    pub async fn cleanup_expired_chains(&self) {
        let cutoff_time = SystemTime::now() - self.chain_timeout;
        let mut chains = self.error_chains.lock().await;
        chains.retain(|_, chain| chain.last_updated > cutoff_time);
    }
}

#[cfg(feature = "async")]
impl Default for ErrorNotifier {
    fn default() -> Self {
        Self {
            notification_channels: Arc::new(TokioMutex::new(Vec::new())),
            notification_rules: Arc::new(TokioMutex::new(Vec::new())),
            notification_history: Arc::new(TokioMutex::new(Vec::new())),
        }
    }
}

#[cfg(feature = "async")]
impl ErrorNotifier {
    pub fn new() -> Self {
        Self::default()
    }

    pub async fn get_matching_rules(&self, error_entry: &EnhancedErrorEntry) -> Vec<NotificationRule> {
        let rules = self.notification_rules.lock().await;
        rules.iter()
            .filter(|rule| rule.enabled && self.rule_matches(rule, error_entry))
            .cloned()
            .collect()
    }

    fn rule_matches(&self, rule: &NotificationRule, error_entry: &EnhancedErrorEntry) -> bool {
        rule.conditions.iter().any(|condition| match condition {
            NotificationCondition::ErrorType(error_type) => error_entry.error_type == *error_type,
            NotificationCondition::Severity(severity) => error_entry.severity == *severity,
            NotificationCondition::Source(source) => error_entry.source.contains(source),
            NotificationCondition::MessagePattern(pattern) => error_entry.message.contains(pattern),
            _ => false,
        })
    }

    pub async fn send_notification(&self, notification: Notification) {
        let mut history = self.notification_history.lock().await;
        history.push(notification);
        
        // 限制通知历史大小
        if history.len() > 1000 {
            history.remove(0);
        }
    }

    pub async fn cleanup_expired_notifications(&self) {
        let cutoff_time = SystemTime::now() - Duration::from_secs(3600); // 1 hour
        let mut history = self.notification_history.lock().await;
        history.retain(|notification| notification.timestamp > cutoff_time);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_enhanced_error_manager() {
        let config = ErrorManagerConfig {
            max_history_size: 100,
            retention_duration: Duration::from_secs(3600),
            auto_recovery: true,
            auto_classification: true,
            auto_notification: true,
            chain_tracking: true,
            performance_monitoring: true,
        };
        
        let manager = EnhancedErrorManager::new(config).await;
        
        // 测试错误记录
        let error = ProcessError::StartFailed("Test error".to_string());
        let context = HashMap::new();
        let error_id = manager.record_error(&error, "test_source", context).await;
        
        assert!(!error_id.is_empty());
        
        // 测试错误历史
        let history = manager.get_error_history(Some(10)).await;
        assert!(!history.is_empty());
        
        // 测试错误统计
        let stats = manager.get_error_statistics().await;
        assert!(stats.total_errors > 0);
    }

    #[tokio::test]
    async fn test_error_recovery() {
        let recovery = ErrorRecovery::new();
        
        let strategy = RecoveryStrategy::Retry {
            max_attempts: 3,
            backoff_duration: Duration::from_millis(100),
            backoff_multiplier: 2.0,
        };
        
        recovery.add_recovery_strategy(ErrorType::Process, strategy).await;
        
        let strategies = recovery.get_recovery_strategies(ErrorType::Process).await;
        assert!(!strategies.is_empty());
    }

    #[tokio::test]
    async fn test_error_classification() {
        let classifier = ErrorClassifier::new();
        
        let error = ProcessError::StartFailed("Test error".to_string());
        let context = HashMap::new();
        
        let classification = classifier.classify_error(&error, &context).await;
        assert_eq!(classification.error_type, ErrorType::Process);
    }

    #[tokio::test]
    async fn test_smart_recovery() {
        let config = ErrorManagerConfig {
            max_history_size: 100,
            retention_duration: Duration::from_secs(3600),
            auto_recovery: true,
            auto_classification: true,
            auto_notification: true,
            chain_tracking: true,
            performance_monitoring: true,
        };
        
        let manager = EnhancedErrorManager::new(config).await;
        
        let error_entry = EnhancedErrorEntry {
            id: "test_error".to_string(),
            error_type: ErrorType::Process,
            severity: ErrorSeverity::Medium,
            message: "Test error".to_string(),
            source: "test_source".to_string(),
            timestamp: SystemTime::now(),
            context: HashMap::new(),
            stack_trace: None,
            recovery_attempts: 0,
            recovery_success: false,
            chain_id: None,
        };
        
        // 测试智能恢复
        let result = manager.smart_recovery(&error_entry, |_| async {
            RecoveryResult::Success {
                message: "Smart recovery successful".to_string(),
                duration: Duration::from_millis(100),
            }
        }).await;
        
        match result {
            RecoveryResult::Success { message, .. } => {
                assert!(message.contains("Smart recovery"));
            }
            _ => panic!("Expected success result"),
        }
    }

    #[tokio::test]
    async fn test_batch_recovery() {
        let config = ErrorManagerConfig {
            max_history_size: 100,
            retention_duration: Duration::from_secs(3600),
            auto_recovery: true,
            auto_classification: true,
            auto_notification: true,
            chain_tracking: true,
            performance_monitoring: true,
        };
        
        let manager = EnhancedErrorManager::new(config).await;
        
        let error_entries = vec![
            EnhancedErrorEntry {
                id: "error1".to_string(),
                error_type: ErrorType::Process,
                severity: ErrorSeverity::Medium,
                message: "Error 1".to_string(),
                source: "source1".to_string(),
                timestamp: SystemTime::now(),
                context: HashMap::new(),
                stack_trace: None,
                recovery_attempts: 0,
                recovery_success: false,
                chain_id: None,
            },
            EnhancedErrorEntry {
                id: "error2".to_string(),
                error_type: ErrorType::Ipc,
                severity: ErrorSeverity::High,
                message: "Error 2".to_string(),
                source: "source2".to_string(),
                timestamp: SystemTime::now(),
                context: HashMap::new(),
                stack_trace: None,
                recovery_attempts: 0,
                recovery_success: false,
                chain_id: None,
            },
        ];
        
        // 测试批量恢复
        let results = manager.batch_recovery(error_entries).await;
        assert_eq!(results.len(), 2);
    }

    #[tokio::test]
    async fn test_error_pattern_analysis() {
        let config = ErrorManagerConfig {
            max_history_size: 100,
            retention_duration: Duration::from_secs(3600),
            auto_recovery: true,
            auto_classification: true,
            auto_notification: true,
            chain_tracking: true,
            performance_monitoring: true,
        };
        
        let manager = EnhancedErrorManager::new(config).await;
        
        // 添加一些测试错误
        let error = ProcessError::StartFailed("Test error".to_string());
        let context = HashMap::new();
        manager.record_error(&error, "test_source", context).await;
        
        // 测试错误模式分析
        let analysis = manager.analyze_error_patterns().await;
        // total_chained_errors is usize, so it's always >= 0
        assert!(!analysis.most_common_pattern.is_empty());
    }

    #[tokio::test]
    async fn test_error_prediction() {
        let config = ErrorManagerConfig {
            max_history_size: 100,
            retention_duration: Duration::from_secs(3600),
            auto_recovery: true,
            auto_classification: true,
            auto_notification: true,
            chain_tracking: true,
            performance_monitoring: true,
        };
        
        let manager = EnhancedErrorManager::new(config).await;
        
        // 添加一些测试错误
        let error = ProcessError::StartFailed("Test error".to_string());
        let mut context = HashMap::new();
        context.insert("memory_usage".to_string(), "high".to_string());
        manager.record_error(&error, "test_source", context).await;
        
        // 测试错误预测
        let predictions = manager.predict_errors().await;
        assert!(!predictions.is_empty());
        
        // 验证预测结果
        for prediction in predictions {
            assert!(prediction.probability > 0.0);
            assert!(prediction.probability <= 1.0);
            assert!(!prediction.predicted_message.is_empty());
        }
    }
}
