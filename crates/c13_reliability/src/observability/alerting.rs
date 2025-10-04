/// 实时告警系统
///
/// 提供规则引擎和多渠道告警功能

use crate::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Serialize, Deserialize};

/// 告警级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum AlertLevel {
    Info,
    Warning,
    Error,
    Critical,
}

/// 告警状态
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum AlertStatus {
    /// 触发
    Firing,
    /// 已解决
    Resolved,
    /// 已确认
    Acknowledged,
}

/// 告警
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Alert {
    /// 告警ID
    pub id: String,
    /// 告警名称
    pub name: String,
    /// 告警级别
    pub level: AlertLevel,
    /// 告警状态
    pub status: AlertStatus,
    /// 告警消息
    pub message: String,
    /// 来源
    pub source: String,
    /// 标签
    pub labels: HashMap<String, String>,
    /// 创建时间
    pub created_at: i64,
    /// 更新时间
    pub updated_at: i64,
    /// 解决时间
    pub resolved_at: Option<i64>,
}

impl Alert {
    /// 创建新告警
    pub fn new(
        name: impl Into<String>,
        level: AlertLevel,
        message: impl Into<String>,
        source: impl Into<String>,
    ) -> Self {
        let now = chrono::Utc::now().timestamp();
        Self {
            id: uuid::Uuid::new_v4().to_string(),
            name: name.into(),
            level,
            status: AlertStatus::Firing,
            message: message.into(),
            source: source.into(),
            labels: HashMap::new(),
            created_at: now,
            updated_at: now,
            resolved_at: None,
        }
    }
    
    /// 添加标签
    pub fn with_label(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.labels.insert(key.into(), value.into());
        self
    }
    
    /// 解决告警
    pub fn resolve(&mut self) {
        self.status = AlertStatus::Resolved;
        self.resolved_at = Some(chrono::Utc::now().timestamp());
        self.updated_at = chrono::Utc::now().timestamp();
    }
    
    /// 确认告警
    pub fn acknowledge(&mut self) {
        self.status = AlertStatus::Acknowledged;
        self.updated_at = chrono::Utc::now().timestamp();
    }
}

/// 告警规则
#[derive(Clone)]
pub struct AlertRule {
    /// 规则名称
    pub name: String,
    /// 规则条件（闭包）
    pub condition: Arc<dyn Fn(&HashMap<String, f64>) -> bool + Send + Sync>,
    /// 告警级别
    pub level: AlertLevel,
    /// 告警消息模板
    pub message_template: String,
    /// 是否启用
    pub enabled: bool,
}

impl std::fmt::Debug for AlertRule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AlertRule")
            .field("name", &self.name)
            .field("level", &self.level)
            .field("message_template", &self.message_template)
            .field("enabled", &self.enabled)
            .finish()
    }
}

/// 告警通知器 trait
#[async_trait::async_trait]
pub trait AlertNotifier: Send + Sync {
    /// 发送告警
    async fn notify(&self, alert: &Alert) -> Result<()>;
    
    /// 通知器名称
    fn name(&self) -> &str;
}

/// 控制台通知器
pub struct ConsoleNotifier;

#[async_trait::async_trait]
impl AlertNotifier for ConsoleNotifier {
    async fn notify(&self, alert: &Alert) -> Result<()> {
        println!(
            "[ALERT {:?}] {} - {} (Source: {})",
            alert.level, alert.name, alert.message, alert.source
        );
        Ok(())
    }
    
    fn name(&self) -> &str {
        "console"
    }
}

/// 日志通知器
pub struct LogNotifier;

#[async_trait::async_trait]
impl AlertNotifier for LogNotifier {
    async fn notify(&self, alert: &Alert) -> Result<()> {
        match alert.level {
            AlertLevel::Info => tracing::info!("Alert: {} - {}", alert.name, alert.message),
            AlertLevel::Warning => tracing::warn!("Alert: {} - {}", alert.name, alert.message),
            AlertLevel::Error => tracing::error!("Alert: {} - {}", alert.name, alert.message),
            AlertLevel::Critical => tracing::error!("CRITICAL Alert: {} - {}", alert.name, alert.message),
        }
        Ok(())
    }
    
    fn name(&self) -> &str {
        "log"
    }
}

/// 告警管理器
pub struct AlertManager {
    /// 活跃的告警
    active_alerts: Arc<RwLock<HashMap<String, Alert>>>,
    /// 历史告警
    alert_history: Arc<RwLock<Vec<Alert>>>,
    /// 告警规则
    rules: Arc<RwLock<Vec<AlertRule>>>,
    /// 通知器列表
    notifiers: Arc<RwLock<Vec<Arc<dyn AlertNotifier>>>>,
    /// 最大历史记录数
    max_history: usize,
}

impl AlertManager {
    /// 创建新的告警管理器
    pub fn new() -> Self {
        Self {
            active_alerts: Arc::new(RwLock::new(HashMap::new())),
            alert_history: Arc::new(RwLock::new(Vec::new())),
            rules: Arc::new(RwLock::new(Vec::new())),
            notifiers: Arc::new(RwLock::new(Vec::new())),
            max_history: 10000,
        }
    }
    
    /// 设置最大历史数
    pub fn with_max_history(mut self, max: usize) -> Self {
        self.max_history = max;
        self
    }
    
    /// 添加通知器
    pub async fn add_notifier(&self, notifier: Arc<dyn AlertNotifier>) {
        self.notifiers.write().await.push(notifier);
    }
    
    /// 添加规则
    pub async fn add_rule(&self, rule: AlertRule) {
        self.rules.write().await.push(rule);
    }
    
    /// 触发告警
    pub async fn fire_alert(&self, mut alert: Alert) -> Result<()> {
        alert.status = AlertStatus::Firing;
        alert.updated_at = chrono::Utc::now().timestamp();
        
        // 存储活跃告警
        {
            let mut alerts = self.active_alerts.write().await;
            alerts.insert(alert.id.clone(), alert.clone());
        }
        
        // 发送通知
        self.notify_alert(&alert).await?;
        
        Ok(())
    }
    
    /// 解决告警
    pub async fn resolve_alert(&self, alert_id: &str) -> Result<()> {
        let mut alerts = self.active_alerts.write().await;
        
        if let Some(alert) = alerts.get_mut(alert_id) {
            alert.resolve();
            
            // 移动到历史
            let resolved_alert = alert.clone();
            drop(alerts);
            
            self.add_to_history(resolved_alert).await;
            
            let mut alerts = self.active_alerts.write().await;
            alerts.remove(alert_id);
            
            Ok(())
        } else {
            Err(anyhow::anyhow!("Alert not found: {}", alert_id))
        }
    }
    
    /// 确认告警
    pub async fn acknowledge_alert(&self, alert_id: &str) -> Result<()> {
        let mut alerts = self.active_alerts.write().await;
        
        if let Some(alert) = alerts.get_mut(alert_id) {
            alert.acknowledge();
            Ok(())
        } else {
            Err(anyhow::anyhow!("Alert not found: {}", alert_id))
        }
    }
    
    /// 发送通知
    async fn notify_alert(&self, alert: &Alert) -> Result<()> {
        let notifiers = self.notifiers.read().await;
        
        for notifier in notifiers.iter() {
            if let Err(e) = notifier.notify(alert).await {
                tracing::error!("Failed to send alert via {}: {}", notifier.name(), e);
            }
        }
        
        Ok(())
    }
    
    /// 添加到历史
    async fn add_to_history(&self, alert: Alert) {
        let mut history = self.alert_history.write().await;
        history.push(alert);
        
        if history.len() > self.max_history {
            let to_remove = history.len() - self.max_history;
            history.drain(0..to_remove);
        }
    }
    
    /// 评估规则
    pub async fn evaluate_rules(&self, metrics: &HashMap<String, f64>) -> Result<()> {
        let rules = self.rules.read().await;
        
        for rule in rules.iter() {
            if !rule.enabled {
                continue;
            }
            
            if (rule.condition)(metrics) {
                let alert = Alert::new(
                    rule.name.clone(),
                    rule.level,
                    rule.message_template.clone(),
                    "rule_engine",
                );
                
                self.fire_alert(alert).await?;
            }
        }
        
        Ok(())
    }
    
    /// 获取活跃告警
    pub async fn get_active_alerts(&self) -> Vec<Alert> {
        self.active_alerts.read().await.values().cloned().collect()
    }
    
    /// 获取历史告警
    pub async fn get_alert_history(&self, limit: usize) -> Vec<Alert> {
        let history = self.alert_history.read().await;
        let alerts: Vec<_> = history.iter().cloned().collect();
        alerts.into_iter().rev().take(limit).collect()
    }
    
    /// 清空所有告警
    pub async fn clear(&self) {
        self.active_alerts.write().await.clear();
        self.alert_history.write().await.clear();
    }
}

impl Default for AlertManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_fire_and_resolve_alert() {
        let manager = AlertManager::new();
        manager.add_notifier(Arc::new(ConsoleNotifier)).await;
        
        let alert = Alert::new(
            "test_alert",
            AlertLevel::Warning,
            "Test message",
            "test",
        );
        let alert_id = alert.id.clone();
        
        manager.fire_alert(alert).await.unwrap();
        
        let active = manager.get_active_alerts().await;
        assert_eq!(active.len(), 1);
        
        manager.resolve_alert(&alert_id).await.unwrap();
        
        let active = manager.get_active_alerts().await;
        assert_eq!(active.len(), 0);
        
        let history = manager.get_alert_history(10).await;
        assert_eq!(history.len(), 1);
    }
    
    #[tokio::test]
    async fn test_alert_rules() {
        let manager = AlertManager::new();
        
        let rule = AlertRule {
            name: "high_cpu".to_string(),
            condition: Arc::new(|metrics: &HashMap<String, f64>| {
                metrics.get("cpu_usage").map(|&v| v > 80.0).unwrap_or(false)
            }),
            level: AlertLevel::Warning,
            message_template: "CPU usage is high".to_string(),
            enabled: true,
        };
        
        manager.add_rule(rule).await;
        manager.add_notifier(Arc::new(ConsoleNotifier)).await;
        
        let mut metrics = HashMap::new();
        metrics.insert("cpu_usage".to_string(), 85.0);
        
        manager.evaluate_rules(&metrics).await.unwrap();
        
        let active = manager.get_active_alerts().await;
        assert!(!active.is_empty());
    }
}

