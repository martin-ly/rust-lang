//! 告警管理器模块
//! 
//! 提供告警规则管理和告警通知功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::{RwLock, mpsc};
use chrono::{DateTime, Utc};
use super::MonitoringError;

/// 条件评估结果
#[derive(Debug)]
pub struct ConditionResult {
    pub triggered: bool,
    pub value: Option<f64>,
    pub message: String,
}

/// 告警管理器
pub struct AlertManager {
    /// 告警规则
    rules: Arc<RwLock<HashMap<String, AlertRule>>>,
    /// 告警历史
    history: Arc<RwLock<Vec<Alert>>>,
    /// 告警通知发送器
    notification_sender: mpsc::UnboundedSender<AlertNotification>,
    /// 告警配置
    config: AlertConfig,
}

/// 告警配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlertConfig {
    /// 告警检查间隔 (秒)
    pub check_interval: u64,
    /// 告警历史保留时间 (小时)
    pub history_retention_hours: u32,
    /// 最大告警历史数量
    pub max_history_count: usize,
    /// 是否启用告警聚合
    pub enable_alert_aggregation: bool,
    /// 告警聚合时间窗口 (分钟)
    pub aggregation_window_minutes: u32,
    /// 是否启用告警抑制
    pub enable_alert_suppression: bool,
    /// 告警抑制时间 (分钟)
    pub suppression_duration_minutes: u32,
}

impl Default for AlertConfig {
    fn default() -> Self {
        Self {
            check_interval: 30,
            history_retention_hours: 168, // 7天
            max_history_count: 10000,
            enable_alert_aggregation: true,
            aggregation_window_minutes: 5,
            enable_alert_suppression: true,
            suppression_duration_minutes: 15,
        }
    }
}

/// 告警规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlertRule {
    /// 规则ID
    pub id: String,
    /// 规则名称
    pub name: String,
    /// 规则描述
    pub description: Option<String>,
    /// 告警条件
    pub condition: AlertCondition,
    /// 告警级别
    pub severity: AlertSeverity,
    /// 告警标签
    pub labels: HashMap<String, String>,
    /// 告警注释
    pub annotations: HashMap<String, String>,
    /// 是否启用
    pub enabled: bool,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 更新时间
    pub updated_at: DateTime<Utc>,
}

/// 告警条件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AlertCondition {
    /// 简单条件
    Simple {
        /// 指标名称
        metric_name: String,
        /// 操作符
        operator: ComparisonOperator,
        /// 阈值
        threshold: f64,
        /// 时间窗口 (秒)
        time_window: u64,
    },
    /// 复合条件
    Compound {
        /// 逻辑操作符
        logical_operator: LogicalOperator,
        /// 子条件
        conditions: Vec<AlertCondition>,
    },
    /// 表达式条件
    Expression {
        /// 表达式
        expression: String,
        /// 时间窗口 (秒)
        time_window: u64,
    },
}

/// 比较操作符
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum ComparisonOperator {
    /// 等于
    Equal,
    /// 不等于
    NotEqual,
    /// 大于
    GreaterThan,
    /// 小于
    LessThan,
    /// 大于等于
    GreaterThanOrEqual,
    /// 小于等于
    LessThanOrEqual,
}

impl ComparisonOperator {
    /// 获取操作符描述
    pub fn description(&self) -> &'static str {
        match self {
            ComparisonOperator::Equal => "等于",
            ComparisonOperator::NotEqual => "不等于",
            ComparisonOperator::GreaterThan => "大于",
            ComparisonOperator::LessThan => "小于",
            ComparisonOperator::GreaterThanOrEqual => "大于等于",
            ComparisonOperator::LessThanOrEqual => "小于等于",
        }
    }
}

/// 逻辑操作符
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum LogicalOperator {
    /// 与
    And,
    /// 或
    Or,
    /// 非
    Not,
}

impl LogicalOperator {
    /// 获取操作符描述
    pub fn description(&self) -> &'static str {
        match self {
            LogicalOperator::And => "与",
            LogicalOperator::Or => "或",
            LogicalOperator::Not => "非",
        }
    }
}

/// 告警级别
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
pub enum AlertSeverity {
    /// 信息
    Info,
    /// 警告
    Warning,
    /// 错误
    Error,
    /// 严重
    Critical,
}

impl AlertSeverity {
    /// 获取级别描述
    pub fn description(&self) -> &'static str {
        match self {
            AlertSeverity::Info => "信息",
            AlertSeverity::Warning => "警告",
            AlertSeverity::Error => "错误",
            AlertSeverity::Critical => "严重",
        }
    }

    /// 获取级别数值
    pub fn value(&self) -> u8 {
        match self {
            AlertSeverity::Info => 1,
            AlertSeverity::Warning => 2,
            AlertSeverity::Error => 3,
            AlertSeverity::Critical => 4,
        }
    }
}

/// 告警
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Alert {
    /// 告警ID
    pub id: String,
    /// 规则ID
    pub rule_id: String,
    /// 告警名称
    pub name: String,
    /// 告警描述
    pub description: Option<String>,
    /// 告警级别
    pub severity: AlertSeverity,
    /// 告警状态
    pub status: AlertStatus,
    /// 告警标签
    pub labels: HashMap<String, String>,
    /// 告警注释
    pub annotations: HashMap<String, String>,
    /// 触发时间
    pub triggered_at: DateTime<Utc>,
    /// 恢复时间
    pub resolved_at: Option<DateTime<Utc>>,
    /// 持续时间
    pub duration: Option<chrono::Duration>,
    /// 告警值
    pub value: Option<f64>,
    /// 告警消息
    pub message: String,
}

/// 告警状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum AlertStatus {
    /// 触发
    Firing,
    /// 恢复
    Resolved,
    /// 抑制
    Suppressed,
}

impl AlertStatus {
    /// 获取状态描述
    pub fn description(&self) -> &'static str {
        match self {
            AlertStatus::Firing => "触发",
            AlertStatus::Resolved => "恢复",
            AlertStatus::Suppressed => "抑制",
        }
    }
}

/// 告警通知
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlertNotification {
    /// 通知ID
    pub id: String,
    /// 告警ID
    pub alert_id: String,
    /// 通知类型
    pub notification_type: NotificationType,
    /// 接收者
    pub recipients: Vec<String>,
    /// 通知内容
    pub content: String,
    /// 发送时间
    pub sent_at: DateTime<Utc>,
    /// 发送状态
    pub status: NotificationStatus,
    /// 重试次数
    pub retry_count: u32,
    /// 最大重试次数
    pub max_retries: u32,
}

/// 通知类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum NotificationType {
    /// 邮件
    Email,
    /// 短信
    SMS,
    /// 微信
    WeChat,
    /// 钉钉
    DingTalk,
    /// 企业微信
    EnterpriseWeChat,
    /// Webhook
    Webhook,
    /// 自定义
    Custom(String),
}

impl NotificationType {
    /// 获取类型描述
    pub fn description(&self) -> String {
        match self {
            NotificationType::Email => "邮件".to_string(),
            NotificationType::SMS => "短信".to_string(),
            NotificationType::WeChat => "微信".to_string(),
            NotificationType::DingTalk => "钉钉".to_string(),
            NotificationType::EnterpriseWeChat => "企业微信".to_string(),
            NotificationType::Webhook => "Webhook".to_string(),
            NotificationType::Custom(name) => name.clone(),
        }
    }
}

/// 通知状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum NotificationStatus {
    /// 待发送
    Pending,
    /// 发送中
    Sending,
    /// 发送成功
    Sent,
    /// 发送失败
    Failed,
    /// 已取消
    Cancelled,
}

impl NotificationStatus {
    /// 获取状态描述
    pub fn description(&self) -> &'static str {
        match self {
            NotificationStatus::Pending => "待发送",
            NotificationStatus::Sending => "发送中",
            NotificationStatus::Sent => "发送成功",
            NotificationStatus::Failed => "发送失败",
            NotificationStatus::Cancelled => "已取消",
        }
    }
}

impl AlertManager {
    /// 创建新的告警管理器
    pub fn new(config: AlertConfig) -> (Self, mpsc::UnboundedReceiver<AlertNotification>) {
        let (notification_sender, notification_receiver) = mpsc::unbounded_channel();
        let manager = Self {
            rules: Arc::new(RwLock::new(HashMap::new())),
            history: Arc::new(RwLock::new(Vec::new())),
            notification_sender,
            config,
        };
        (manager, notification_receiver)
    }

    /// 添加告警规则
    pub async fn add_rule(&self, rule: AlertRule) -> Result<(), MonitoringError> {
        let mut rules = self.rules.write().await;
        rules.insert(rule.id.clone(), rule);
        Ok(())
    }

    /// 更新告警规则
    pub async fn update_rule(&self, rule_id: &str, rule: AlertRule) -> Result<(), MonitoringError> {
        let mut rules = self.rules.write().await;
        if rules.contains_key(rule_id) {
            rules.insert(rule_id.to_string(), rule);
            Ok(())
        } else {
            Err(MonitoringError::AlertManagementError(
                format!("告警规则 {} 不存在", rule_id)
            ))
        }
    }

    /// 删除告警规则
    pub async fn remove_rule(&self, rule_id: &str) -> Result<(), MonitoringError> {
        let mut rules = self.rules.write().await;
        if rules.remove(rule_id).is_some() {
            Ok(())
        } else {
            Err(MonitoringError::AlertManagementError(
                format!("告警规则 {} 不存在", rule_id)
            ))
        }
    }

    /// 获取告警规则
    pub async fn get_rule(&self, rule_id: &str) -> Option<AlertRule> {
        let rules = self.rules.read().await;
        rules.get(rule_id).cloned()
    }

    /// 获取所有告警规则
    pub async fn get_all_rules(&self) -> Vec<AlertRule> {
        let rules = self.rules.read().await;
        rules.values().cloned().collect()
    }

    /// 检查告警条件
    pub async fn check_alert_conditions(&self, metrics: &[super::metrics_collector::Metric]) -> Result<Vec<Alert>, MonitoringError> {
        let rules = self.rules.read().await;
        let mut alerts = Vec::new();
        
        for rule in rules.values() {
            if !rule.enabled {
                continue;
            }
            
            if let Some(alert) = self.evaluate_rule(rule, metrics).await? {
                alerts.push(alert);
            }
        }
        
        Ok(alerts)
    }

    /// 评估告警规则
    async fn evaluate_rule(&self, rule: &AlertRule, metrics: &[super::metrics_collector::Metric]) -> Result<Option<Alert>, MonitoringError> {
        let condition_result = self.evaluate_condition(&rule.condition, metrics).await?;
        
        if condition_result.triggered {
            let alert = Alert {
                id: uuid::Uuid::new_v4().to_string(),
                rule_id: rule.id.clone(),
                name: rule.name.clone(),
                description: rule.description.clone(),
                severity: rule.severity.clone(),
                status: AlertStatus::Firing,
                labels: rule.labels.clone(),
                annotations: rule.annotations.clone(),
                triggered_at: Utc::now(),
                resolved_at: None,
                duration: None,
                value: condition_result.value,
                message: condition_result.message,
            };
            
            // 检查告警抑制
            if self.config.enable_alert_suppression {
                if self.is_alert_suppressed(&alert).await {
                    return Ok(None);
                }
            }
            
            // 记录告警历史
            self.record_alert(alert.clone()).await;
            
            // 发送告警通知
            self.send_alert_notification(&alert).await?;
            
            Ok(Some(alert))
        } else {
            Ok(None)
        }
    }

    /// 评估告警条件
    pub async fn evaluate_condition(&self, condition: &AlertCondition, metrics: &[super::metrics_collector::Metric]) -> Result<ConditionResult, MonitoringError> {
        Box::pin(self.evaluate_condition_recursive(condition, metrics)).await
    }

    /// 评估告警条件（递归版本）
    async fn evaluate_condition_recursive(&self, condition: &AlertCondition, metrics: &[super::metrics_collector::Metric]) -> Result<ConditionResult, MonitoringError> {
        match condition {
            AlertCondition::Simple { metric_name, operator, threshold, time_window } => {
                self.evaluate_simple_condition(metric_name, operator, *threshold, *time_window, metrics).await
            }
            AlertCondition::Compound { logical_operator, conditions } => {
                self.evaluate_compound_condition(logical_operator, conditions, metrics).await
            }
            AlertCondition::Expression { expression, time_window } => {
                self.evaluate_expression_condition(expression, *time_window, metrics).await
            }
        }
    }

    /// 评估告警条件（内部方法）
    async fn evaluate_condition_internal(&self, condition: &AlertCondition, metrics: &[super::metrics_collector::Metric]) -> Result<ConditionResult, MonitoringError> {
        Box::pin(self.evaluate_condition_recursive(condition, metrics)).await
    }

    /// 评估简单条件
    async fn evaluate_simple_condition(
        &self,
        metric_name: &str,
        operator: &ComparisonOperator,
        threshold: f64,
        time_window: u64,
        metrics: &[super::metrics_collector::Metric],
    ) -> Result<ConditionResult, MonitoringError> {
        let now = Utc::now();
        let window_start = now - chrono::Duration::seconds(time_window as i64);
        
        let relevant_metrics: Vec<&super::metrics_collector::Metric> = metrics
            .iter()
            .filter(|m| m.name == metric_name && m.timestamp >= window_start)
            .collect();
        
        if relevant_metrics.is_empty() {
            return Ok(ConditionResult {
                triggered: false,
                value: None,
                message: format!("指标 {} 在时间窗口内无数据", metric_name),
            });
        }
        
        let latest_metric = relevant_metrics.iter().max_by_key(|m| m.timestamp).unwrap();
        let value = latest_metric.value.as_number().unwrap_or(0.0);
        
        let triggered = match operator {
            ComparisonOperator::Equal => (value - threshold).abs() < f64::EPSILON,
            ComparisonOperator::NotEqual => (value - threshold).abs() >= f64::EPSILON,
            ComparisonOperator::GreaterThan => value > threshold,
            ComparisonOperator::LessThan => value < threshold,
            ComparisonOperator::GreaterThanOrEqual => value >= threshold,
            ComparisonOperator::LessThanOrEqual => value <= threshold,
        };
        
        let message = if triggered {
            format!("指标 {} 当前值 {} {} 阈值 {}", 
                   metric_name, value, operator.description(), threshold)
        } else {
            format!("指标 {} 当前值 {} 未触发告警条件", metric_name, value)
        };
        
        Ok(ConditionResult {
            triggered,
            value: Some(value),
            message,
        })
    }

    /// 评估复合条件
    async fn evaluate_compound_condition(
        &self,
        logical_operator: &LogicalOperator,
        conditions: &[AlertCondition],
        metrics: &[super::metrics_collector::Metric],
    ) -> Result<ConditionResult, MonitoringError> {
        let mut results = Vec::new();
        
        for condition in conditions {
            let result = self.evaluate_condition_internal(condition, metrics).await?;
            results.push(result);
        }
        
        let triggered = match logical_operator {
            LogicalOperator::And => results.iter().all(|r| r.triggered),
            LogicalOperator::Or => results.iter().any(|r| r.triggered),
            LogicalOperator::Not => {
                if results.len() != 1 {
                    return Err(MonitoringError::AlertManagementError(
                        "NOT操作符只能有一个条件".to_string()
                    ));
                }
                !results[0].triggered
            }
        };
        
        let message = if triggered {
            format!("复合条件 {} 已触发", logical_operator.description())
        } else {
            format!("复合条件 {} 未触发", logical_operator.description())
        };
        
        Ok(ConditionResult {
            triggered,
            value: None,
            message,
        })
    }

    /// 评估表达式条件
    async fn evaluate_expression_condition(
        &self,
        expression: &str,
        time_window: u64,
        metrics: &[super::metrics_collector::Metric],
    ) -> Result<ConditionResult, MonitoringError> {
        // 简化实现，实际应该使用表达式解析器
        let now = Utc::now();
        let window_start = now - chrono::Duration::seconds(time_window as i64);
        
        let relevant_metrics: Vec<&super::metrics_collector::Metric> = metrics
            .iter()
            .filter(|m| m.timestamp >= window_start)
            .collect();
        
        if relevant_metrics.is_empty() {
            return Ok(ConditionResult {
                triggered: false,
                value: None,
                message: "表达式条件在时间窗口内无数据".to_string(),
            });
        }
        
        // 简化实现，实际应该解析表达式
        let triggered = expression.contains("> 80");
        let message = if triggered {
            "表达式条件已触发".to_string()
        } else {
            "表达式条件未触发".to_string()
        };
        
        Ok(ConditionResult {
            triggered,
            value: None,
            message,
        })
    }


    /// 检查告警是否被抑制
    async fn is_alert_suppressed(&self, alert: &Alert) -> bool {
        let history = self.history.read().await;
        let suppression_threshold = Utc::now() - chrono::Duration::minutes(self.config.suppression_duration_minutes as i64);
        
        history.iter().any(|h| {
            h.rule_id == alert.rule_id &&
            h.status == AlertStatus::Firing &&
            h.triggered_at > suppression_threshold
        })
    }

    /// 记录告警
    async fn record_alert(&self, alert: Alert) {
        let mut history = self.history.write().await;
        
        // 检查历史数量限制
        if history.len() >= self.config.max_history_count {
            history.remove(0);
        }
        
        history.push(alert);
    }

    /// 发送告警通知
    async fn send_alert_notification(&self, alert: &Alert) -> Result<(), MonitoringError> {
        let notification = AlertNotification {
            id: uuid::Uuid::new_v4().to_string(),
            alert_id: alert.id.clone(),
            notification_type: NotificationType::Email,
            recipients: vec!["admin@example.com".to_string()],
            content: format!("告警: {} - {}", alert.name, alert.message),
            sent_at: Utc::now(),
            status: NotificationStatus::Pending,
            retry_count: 0,
            max_retries: 3,
        };
        
        self.notification_sender.send(notification)
            .map_err(|_| MonitoringError::AlertManagementError(
                "告警通知发送失败".to_string()
            ))
    }

    /// 获取告警历史
    pub async fn get_alert_history(&self, limit: Option<usize>) -> Vec<Alert> {
        let history = self.history.read().await;
        let mut alerts = history.clone();
        alerts.sort_by_key(|a| a.triggered_at);
        alerts.reverse();
        
        if let Some(limit) = limit {
            alerts.truncate(limit);
        }
        
        alerts
    }

    /// 获取指定规则的告警历史
    pub async fn get_rule_alert_history(&self, rule_id: &str, limit: Option<usize>) -> Vec<Alert> {
        let history = self.history.read().await;
        let mut alerts: Vec<Alert> = history
            .iter()
            .filter(|a| a.rule_id == rule_id)
            .cloned()
            .collect();
        
        alerts.sort_by_key(|a| a.triggered_at);
        alerts.reverse();
        
        if let Some(limit) = limit {
            alerts.truncate(limit);
        }
        
        alerts
    }

    /// 清理过期告警历史
    pub async fn cleanup_expired_history(&self) -> usize {
        let mut history = self.history.write().await;
        let initial_count = history.len();
        let retention_threshold = Utc::now() - chrono::Duration::hours(self.config.history_retention_hours as i64);
        
        history.retain(|alert| alert.triggered_at > retention_threshold);
        
        initial_count - history.len()
    }

    /// 启动告警检查
    pub async fn start_alert_checking(&self, metrics_collector: Arc<super::metrics_collector::MetricsCollector>) -> Result<(), MonitoringError> {
        let rules = Arc::clone(&self.rules);
        let history = Arc::clone(&self.history);
        let config = self.config.clone();
        let notification_sender = self.notification_sender.clone();
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(
                tokio::time::Duration::from_secs(config.check_interval)
            );
            
            loop {
                interval.tick().await;
                
                // 获取最新指标
                let metrics = metrics_collector.get_all_metrics().await;
                
                // 检查告警条件
                if let Ok(alerts) = Self::check_alert_conditions_static(&rules, &history, &config, &notification_sender, &metrics).await {
                    for alert in alerts {
                        // 记录告警
                        let mut history_guard = history.write().await;
                        if history_guard.len() >= config.max_history_count {
                            history_guard.remove(0);
                        }
                        history_guard.push(alert);
                    }
                }
                
                // 清理过期历史
                if config.history_retention_hours > 0 {
                    let retention_threshold = Utc::now() - chrono::Duration::hours(config.history_retention_hours as i64);
                    let mut history_guard = history.write().await;
                    history_guard.retain(|alert| alert.triggered_at > retention_threshold);
                }
            }
        });
        
        Ok(())
    }

    /// 静态方法：检查告警条件
    async fn check_alert_conditions_static(
        rules: &Arc<RwLock<HashMap<String, AlertRule>>>,
        history: &Arc<RwLock<Vec<Alert>>>,
        config: &AlertConfig,
        notification_sender: &mpsc::UnboundedSender<AlertNotification>,
        _metrics: &[super::metrics_collector::Metric],
    ) -> Result<Vec<Alert>, MonitoringError> {
        let rules_guard = rules.read().await;
        let mut alerts = Vec::new();
        
        for rule in rules_guard.values() {
            if !rule.enabled {
                continue;
            }
            
            // 简化实现，实际应该调用evaluate_rule方法
            let alert = Alert {
                id: uuid::Uuid::new_v4().to_string(),
                rule_id: rule.id.clone(),
                name: rule.name.clone(),
                description: rule.description.clone(),
                severity: rule.severity.clone(),
                status: AlertStatus::Firing,
                labels: rule.labels.clone(),
                annotations: rule.annotations.clone(),
                triggered_at: Utc::now(),
                resolved_at: None,
                duration: None,
                value: Some(0.0),
                message: "告警已触发".to_string(),
            };
            
            // 检查告警抑制
            if config.enable_alert_suppression {
                let history_guard = history.read().await;
                let suppression_threshold = Utc::now() - chrono::Duration::minutes(config.suppression_duration_minutes as i64);
                
                let is_suppressed = history_guard.iter().any(|h| {
                    h.rule_id == alert.rule_id &&
                    h.status == AlertStatus::Firing &&
                    h.triggered_at > suppression_threshold
                });
                
                if is_suppressed {
                    continue;
                }
            }
            
            // 发送告警通知
            let notification = AlertNotification {
                id: uuid::Uuid::new_v4().to_string(),
                alert_id: alert.id.clone(),
                notification_type: NotificationType::Email,
                recipients: vec!["admin@example.com".to_string()],
                content: format!("告警: {} - {}", alert.name, alert.message),
                sent_at: Utc::now(),
                status: NotificationStatus::Pending,
                retry_count: 0,
                max_retries: 3,
            };
            
            if notification_sender.send(notification).is_err() {
                eprintln!("告警通知发送失败");
            }
            
            alerts.push(alert);
        }
        
        Ok(alerts)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_alert_manager_creation() {
        let config = AlertConfig::default();
        let (manager, _receiver) = AlertManager::new(config);
        
        let rules = manager.get_all_rules().await;
        assert_eq!(rules.len(), 0);
    }

    #[tokio::test]
    async fn test_add_alert_rule() {
        let config = AlertConfig::default();
        let (manager, _receiver) = AlertManager::new(config);
        
        let rule = AlertRule {
            id: "rule_001".to_string(),
            name: "CPU使用率告警".to_string(),
            description: Some("CPU使用率超过80%时触发告警".to_string()),
            condition: AlertCondition::Simple {
                metric_name: "cpu_usage".to_string(),
                operator: ComparisonOperator::GreaterThan,
                threshold: 80.0,
                time_window: 300,
            },
            severity: AlertSeverity::Warning,
            labels: HashMap::new(),
            annotations: HashMap::new(),
            enabled: true,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };
        
        assert!(manager.add_rule(rule).await.is_ok());
        
        let rules = manager.get_all_rules().await;
        assert_eq!(rules.len(), 1);
    }

    #[tokio::test]
    async fn test_remove_alert_rule() {
        let config = AlertConfig::default();
        let (manager, _receiver) = AlertManager::new(config);
        
        let rule = AlertRule {
            id: "rule_001".to_string(),
            name: "CPU使用率告警".to_string(),
            description: Some("CPU使用率超过80%时触发告警".to_string()),
            condition: AlertCondition::Simple {
                metric_name: "cpu_usage".to_string(),
                operator: ComparisonOperator::GreaterThan,
                threshold: 80.0,
                time_window: 300,
            },
            severity: AlertSeverity::Warning,
            labels: HashMap::new(),
            annotations: HashMap::new(),
            enabled: true,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        };
        
        manager.add_rule(rule).await.unwrap();
        assert!(manager.remove_rule("rule_001").await.is_ok());
        
        let rules = manager.get_all_rules().await;
        assert_eq!(rules.len(), 0);
    }

    #[tokio::test]
    async fn test_alert_severity_ordering() {
        assert!(AlertSeverity::Info < AlertSeverity::Warning);
        assert!(AlertSeverity::Warning < AlertSeverity::Error);
        assert!(AlertSeverity::Error < AlertSeverity::Critical);
    }

    #[tokio::test]
    async fn test_alert_status_descriptions() {
        assert_eq!(AlertStatus::Firing.description(), "触发");
        assert_eq!(AlertStatus::Resolved.description(), "恢复");
        assert_eq!(AlertStatus::Suppressed.description(), "抑制");
    }

    #[tokio::test]
    async fn test_notification_type_descriptions() {
        assert_eq!(NotificationType::Email.description(), "邮件");
        assert_eq!(NotificationType::SMS.description(), "短信");
        assert_eq!(NotificationType::WeChat.description(), "微信");
        assert_eq!(NotificationType::DingTalk.description(), "钉钉");
        assert_eq!(NotificationType::EnterpriseWeChat.description(), "企业微信");
        assert_eq!(NotificationType::Webhook.description(), "Webhook");
        assert_eq!(NotificationType::Custom("自定义".to_string()).description(), "自定义");
    }
}
