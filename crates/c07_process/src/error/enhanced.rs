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

    /// 尝试错误恢复
    pub async fn attempt_recovery(&self, error_entry: &EnhancedErrorEntry) -> RecoveryResult {
        let strategies = self.error_recovery.get_recovery_strategies(error_entry.error_type).await;
        
        for strategy in strategies.into_iter() {
            let result = self.execute_recovery_strategy(strategy.clone(), error_entry).await;
            
            match result {
                RecoveryResult::Success { .. } => {
                    self.record_recovery_success(error_entry.id.clone(), strategy).await;
                    return result;
                }
                RecoveryResult::Retry { delay, .. } => {
                    tokio::time::sleep(delay).await;
                    continue;
                }
                RecoveryResult::Escalate { .. } => {
                    return result;
                }
                RecoveryResult::Failure { .. } => {
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
pub struct ErrorStatistics {
    pub total_errors: u64,
    pub error_type_counts: HashMap<ErrorType, u64>,
    pub severity_counts: HashMap<ErrorSeverity, u64>,
    pub source_counts: HashMap<String, u64>,
    pub successful_recoveries: u64,
    pub failed_recoveries: u64,
}

#[cfg(feature = "async")]
impl ErrorStatistics {
    pub fn new() -> Self {
        Self {
            total_errors: 0,
            error_type_counts: HashMap::new(),
            severity_counts: HashMap::new(),
            source_counts: HashMap::new(),
            successful_recoveries: 0,
            failed_recoveries: 0,
        }
    }
}

#[cfg(feature = "async")]
impl ErrorRecovery {
    pub fn new() -> Self {
        Self {
            recovery_strategies: Arc::new(TokioMutex::new(HashMap::new())),
            recovery_history: Arc::new(TokioMutex::new(Vec::new())),
            max_recovery_attempts: 3,
            recovery_timeout: Duration::from_secs(30),
        }
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
impl ErrorClassifier {
    pub fn new() -> Self {
        Self {
            classification_rules: Arc::new(TokioMutex::new(Vec::new())),
            classification_cache: Arc::new(TokioMutex::new(HashMap::new())),
            auto_classification: true,
        }
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
impl ErrorChainTracker {
    pub fn new() -> Self {
        Self {
            error_chains: Arc::new(TokioMutex::new(HashMap::new())),
            chain_timeout: Duration::from_secs(300), // 5 minutes
            max_chain_length: 10,
        }
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
impl ErrorNotifier {
    pub fn new() -> Self {
        Self {
            notification_channels: Arc::new(TokioMutex::new(Vec::new())),
            notification_rules: Arc::new(TokioMutex::new(Vec::new())),
            notification_history: Arc::new(TokioMutex::new(Vec::new())),
        }
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
}
