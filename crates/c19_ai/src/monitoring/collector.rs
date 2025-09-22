//! 监控数据收集器
//! 
//! 提供系统监控数据的收集、聚合和存储功能

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use tokio::sync::RwLock;
use uuid::Uuid;
use chrono::{DateTime, Utc};

use super::metrics::*;
use super::logging::*;

/// 监控数据收集器
#[derive(Debug)]
pub struct MonitoringCollector {
    metrics: Arc<RwLock<HashMap<String, Metric>>>,
    logs: Arc<RwLock<Vec<LogEntry>>>,
    events: Arc<RwLock<Vec<MonitoringEvent>>>,
    alerts: Arc<RwLock<Vec<Alert>>>,
    config: MonitoringConfig,
    start_time: Instant,
}

/// 监控配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonitoringConfig {
    pub collection_interval: Duration,
    pub retention_period: Duration,
    pub max_metrics: usize,
    pub max_logs: usize,
    pub max_events: usize,
    pub max_alerts: usize,
    pub enable_metrics: bool,
    pub enable_logs: bool,
    pub enable_events: bool,
    pub enable_alerts: bool,
    pub alert_thresholds: HashMap<String, f64>,
}

impl Default for MonitoringConfig {
    fn default() -> Self {
        Self {
            collection_interval: Duration::from_secs(60),
            retention_period: Duration::from_secs(86400 * 7), // 7 days
            max_metrics: 10000,
            max_logs: 50000,
            max_events: 10000,
            max_alerts: 1000,
            enable_metrics: true,
            enable_logs: true,
            enable_events: true,
            enable_alerts: true,
            alert_thresholds: HashMap::new(),
        }
    }
}

/// 监控事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonitoringEvent {
    pub id: Uuid,
    pub event_type: EventType,
    pub severity: EventSeverity,
    pub title: String,
    pub description: String,
    pub source: String,
    pub tags: HashMap<String, String>,
    pub timestamp: DateTime<Utc>,
    pub duration: Option<Duration>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 事件类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EventType {
    SystemStart,
    SystemStop,
    ModelLoaded,
    ModelUnloaded,
    TrainingStarted,
    TrainingCompleted,
    TrainingFailed,
    InferenceStarted,
    InferenceCompleted,
    InferenceFailed,
    CacheHit,
    CacheMiss,
    DatabaseConnected,
    DatabaseDisconnected,
    ApiRequest,
    ApiResponse,
    Error,
    Warning,
    Info,
    Custom(String),
}

/// 事件严重程度
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EventSeverity {
    Critical,
    High,
    Medium,
    Low,
    Info,
}

/// 告警
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Alert {
    pub id: Uuid,
    pub name: String,
    pub description: String,
    pub severity: AlertSeverity,
    pub status: AlertStatus,
    pub source: String,
    pub metric_name: String,
    pub threshold: f64,
    pub current_value: f64,
    pub triggered_at: DateTime<Utc>,
    pub resolved_at: Option<DateTime<Utc>>,
    pub tags: HashMap<String, String>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 告警严重程度
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AlertSeverity {
    Critical,
    High,
    Medium,
    Low,
}

/// 告警状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum AlertStatus {
    Active,
    Resolved,
    Suppressed,
    Acknowledged,
}

/// 系统健康状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemHealth {
    pub overall_status: HealthStatus,
    pub components: HashMap<String, ComponentHealth>,
    pub last_check: DateTime<Utc>,
    pub uptime: Duration,
    pub version: String,
}

/// 健康状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum HealthStatus {
    Healthy,
    Degraded,
    Unhealthy,
    Unknown,
}

/// 组件健康状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ComponentHealth {
    pub name: String,
    pub status: HealthStatus,
    pub message: Option<String>,
    pub last_check: DateTime<Utc>,
    pub response_time: Option<Duration>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 性能指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMetrics {
    pub cpu_usage: f64,
    pub memory_usage: f64,
    pub disk_usage: f64,
    pub network_io: NetworkIO,
    pub request_rate: f64,
    pub response_time: Duration,
    pub error_rate: f64,
    pub timestamp: DateTime<Utc>,
}

/// 网络IO统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkIO {
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub packets_sent: u64,
    pub packets_received: u64,
}

impl MonitoringCollector {
    /// 创建新的监控收集器
    pub fn new(config: MonitoringConfig) -> Self {
        Self {
            metrics: Arc::new(RwLock::new(HashMap::new())),
            logs: Arc::new(RwLock::new(Vec::new())),
            events: Arc::new(RwLock::new(Vec::new())),
            alerts: Arc::new(RwLock::new(Vec::new())),
            config,
            start_time: Instant::now(),
        }
    }

    /// 记录指标
    pub async fn record_metric(&self, name: String, value: f64, labels: HashMap<String, String>) -> Result<()> {
        if !self.config.enable_metrics {
            return Ok(());
        }

        let metric = Metric {
            name: name.clone(),
            metric_type: MetricType::Gauge,
            value,
            labels,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)?
                .as_secs(),
        };

        {
            let mut metrics = self.metrics.write().await;
            metrics.insert(name, metric);
            
            // 清理过期指标
            if metrics.len() > self.config.max_metrics {
                self.cleanup_old_metrics(&mut metrics).await;
            }
        }

        // 检查告警阈值
        self.check_alert_thresholds(&name, value).await?;

        Ok(())
    }

    /// 记录日志
    pub async fn record_log(&self, level: LogLevel, message: String, fields: HashMap<String, String>) -> Result<()> {
        if !self.config.enable_logs {
            return Ok(());
        }

        let log_entry = LogEntry {
            level,
            message,
            timestamp: SystemTime::now()
                .duration_since(UNIX_EPOCH)?
                .as_secs(),
            fields,
        };

        {
            let mut logs = self.logs.write().await;
            logs.push(log_entry);
            
            // 清理过期日志
            if logs.len() > self.config.max_logs {
                self.cleanup_old_logs(&mut logs).await;
            }
        }

        Ok(())
    }

    /// 记录事件
    pub async fn record_event(&self, event: MonitoringEvent) -> Result<()> {
        if !self.config.enable_events {
            return Ok(());
        }

        {
            let mut events = self.events.write().await;
            events.push(event);
            
            // 清理过期事件
            if events.len() > self.config.max_events {
                self.cleanup_old_events(&mut events).await;
            }
        }

        Ok(())
    }

    /// 创建告警
    pub async fn create_alert(&self, alert: Alert) -> Result<()> {
        if !self.config.enable_alerts {
            return Ok(());
        }

        {
            let mut alerts = self.alerts.write().await;
            alerts.push(alert);
            
            // 清理过期告警
            if alerts.len() > self.config.max_alerts {
                self.cleanup_old_alerts(&mut alerts).await;
            }
        }

        Ok(())
    }

    /// 获取指标
    pub async fn get_metric(&self, name: &str) -> Option<Metric> {
        let metrics = self.metrics.read().await;
        metrics.get(name).cloned()
    }

    /// 获取所有指标
    pub async fn get_all_metrics(&self) -> HashMap<String, Metric> {
        let metrics = self.metrics.read().await;
        metrics.clone()
    }

    /// 获取日志
    pub async fn get_logs(&self, level: Option<LogLevel>, limit: Option<usize>) -> Vec<LogEntry> {
        let logs = self.logs.read().await;
        let mut filtered_logs: Vec<LogEntry> = logs.clone();

        if let Some(level) = level {
            filtered_logs.retain(|log| std::mem::discriminant(&log.level) == std::mem::discriminant(&level));
        }

        if let Some(limit) = limit {
            filtered_logs.truncate(limit);
        }

        filtered_logs
    }

    /// 获取事件
    pub async fn get_events(&self, event_type: Option<EventType>, limit: Option<usize>) -> Vec<MonitoringEvent> {
        let events = self.events.read().await;
        let mut filtered_events: Vec<MonitoringEvent> = events.clone();

        if let Some(event_type) = event_type {
            filtered_events.retain(|event| std::mem::discriminant(&event.event_type) == std::mem::discriminant(&event_type));
        }

        if let Some(limit) = limit {
            filtered_events.truncate(limit);
        }

        filtered_events
    }

    /// 获取告警
    pub async fn get_alerts(&self, status: Option<AlertStatus>, limit: Option<usize>) -> Vec<Alert> {
        let alerts = self.alerts.read().await;
        let mut filtered_alerts: Vec<Alert> = alerts.clone();

        if let Some(status) = status {
            filtered_alerts.retain(|alert| std::mem::discriminant(&alert.status) == std::mem::discriminant(&status));
        }

        if let Some(limit) = limit {
            filtered_alerts.truncate(limit);
        }

        filtered_alerts
    }

    /// 获取系统健康状态
    pub async fn get_system_health(&self) -> SystemHealth {
        let uptime = self.start_time.elapsed();
        let last_check = Utc::now();

        // 检查各个组件的健康状态
        let mut components = HashMap::new();
        
        // 检查数据库连接
        components.insert("database".to_string(), ComponentHealth {
            name: "database".to_string(),
            status: HealthStatus::Healthy, // TODO: 实际检查数据库连接
            message: None,
            last_check,
            response_time: None,
            metadata: HashMap::new(),
        });

        // 检查缓存
        components.insert("cache".to_string(), ComponentHealth {
            name: "cache".to_string(),
            status: HealthStatus::Healthy, // TODO: 实际检查缓存状态
            message: None,
            last_check,
            response_time: None,
            metadata: HashMap::new(),
        });

        // 检查存储
        components.insert("storage".to_string(), ComponentHealth {
            name: "storage".to_string(),
            status: HealthStatus::Healthy, // TODO: 实际检查存储状态
            message: None,
            last_check,
            response_time: None,
            metadata: HashMap::new(),
        });

        // 确定整体健康状态
        let overall_status = if components.values().any(|c| c.status == HealthStatus::Unhealthy) {
            HealthStatus::Unhealthy
        } else if components.values().any(|c| c.status == HealthStatus::Degraded) {
            HealthStatus::Degraded
        } else {
            HealthStatus::Healthy
        };

        SystemHealth {
            overall_status,
            components,
            last_check,
            uptime,
            version: env!("CARGO_PKG_VERSION").to_string(),
        }
    }

    /// 获取性能指标
    pub async fn get_performance_metrics(&self) -> PerformanceMetrics {
        // TODO: 实际收集系统性能指标
        PerformanceMetrics {
            cpu_usage: 0.0,
            memory_usage: 0.0,
            disk_usage: 0.0,
            network_io: NetworkIO {
                bytes_sent: 0,
                bytes_received: 0,
                packets_sent: 0,
                packets_received: 0,
            },
            request_rate: 0.0,
            response_time: Duration::from_millis(0),
            error_rate: 0.0,
            timestamp: Utc::now(),
        }
    }

    /// 检查告警阈值
    async fn check_alert_thresholds(&self, metric_name: &str, value: f64) -> Result<()> {
        if let Some(threshold) = self.config.alert_thresholds.get(metric_name) {
            if value > *threshold {
                let alert = Alert {
                    id: Uuid::new_v4(),
                    name: format!("High {} value", metric_name),
                    description: format!("{} value {} exceeds threshold {}", metric_name, value, threshold),
                    severity: AlertSeverity::High,
                    status: AlertStatus::Active,
                    source: "monitoring".to_string(),
                    metric_name: metric_name.to_string(),
                    threshold: *threshold,
                    current_value: value,
                    triggered_at: Utc::now(),
                    resolved_at: None,
                    tags: HashMap::new(),
                    metadata: HashMap::new(),
                };

                self.create_alert(alert).await?;
            }
        }

        Ok(())
    }

    /// 清理过期指标
    async fn cleanup_old_metrics(&self, metrics: &mut HashMap<String, Metric>) {
        let cutoff_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() - self.config.retention_period.as_secs();

        metrics.retain(|_, metric| metric.timestamp > cutoff_time);
    }

    /// 清理过期日志
    async fn cleanup_old_logs(&self, logs: &mut Vec<LogEntry>) {
        let cutoff_time = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap_or_default()
            .as_secs() - self.config.retention_period.as_secs();

        logs.retain(|log| log.timestamp > cutoff_time);
    }

    /// 清理过期事件
    async fn cleanup_old_events(&self, events: &mut Vec<MonitoringEvent>) {
        let cutoff_time = Utc::now() - chrono::Duration::from_std(self.config.retention_period).unwrap_or_default();
        events.retain(|event| event.timestamp > cutoff_time);
    }

    /// 清理过期告警
    async fn cleanup_old_alerts(&self, alerts: &mut Vec<Alert>) {
        let cutoff_time = Utc::now() - chrono::Duration::from_std(self.config.retention_period).unwrap_or_default();
        alerts.retain(|alert| alert.triggered_at > cutoff_time);
    }

    /// 获取监控统计信息
    pub async fn get_monitoring_stats(&self) -> MonitoringStats {
        let metrics = self.metrics.read().await;
        let logs = self.logs.read().await;
        let events = self.events.read().await;
        let alerts = self.alerts.read().await;

        MonitoringStats {
            total_metrics: metrics.len(),
            total_logs: logs.len(),
            total_events: events.len(),
            total_alerts: alerts.len(),
            active_alerts: alerts.iter().filter(|a| a.status == AlertStatus::Active).count(),
            uptime: self.start_time.elapsed(),
            last_collection: Utc::now(),
        }
    }
}

/// 监控统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonitoringStats {
    pub total_metrics: usize,
    pub total_logs: usize,
    pub total_events: usize,
    pub total_alerts: usize,
    pub active_alerts: usize,
    pub uptime: Duration,
    pub last_collection: DateTime<Utc>,
}

/// 监控数据导出器
#[derive(Debug)]
pub struct MonitoringExporter {
    collector: Arc<MonitoringCollector>,
}

impl MonitoringExporter {
    /// 创建新的监控导出器
    pub fn new(collector: Arc<MonitoringCollector>) -> Self {
        Self { collector }
    }

    /// 导出指标为Prometheus格式
    pub async fn export_prometheus_metrics(&self) -> Result<String> {
        let metrics = self.collector.get_all_metrics().await;
        let mut prometheus_output = String::new();

        for (name, metric) in metrics {
            let labels = if metric.labels.is_empty() {
                String::new()
            } else {
                let label_pairs: Vec<String> = metric.labels
                    .iter()
                    .map(|(k, v)| format!("{}=\"{}\"", k, v))
                    .collect();
                format!("{{{}}}", label_pairs.join(","))
            };

            prometheus_output.push_str(&format!("{} {} {}\n", name, labels, metric.value));
        }

        Ok(prometheus_output)
    }

    /// 导出日志为JSON格式
    pub async fn export_logs_json(&self, level: Option<LogLevel>, limit: Option<usize>) -> Result<String> {
        let logs = self.collector.get_logs(level, limit).await;
        Ok(serde_json::to_string_pretty(&logs)?)
    }

    /// 导出事件为JSON格式
    pub async fn export_events_json(&self, event_type: Option<EventType>, limit: Option<usize>) -> Result<String> {
        let events = self.collector.get_events(event_type, limit).await;
        Ok(serde_json::to_string_pretty(&events)?)
    }

    /// 导出告警为JSON格式
    pub async fn export_alerts_json(&self, status: Option<AlertStatus>, limit: Option<usize>) -> Result<String> {
        let alerts = self.collector.get_alerts(status, limit).await;
        Ok(serde_json::to_string_pretty(&alerts)?)
    }
}
