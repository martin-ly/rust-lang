//! 监控仪表板模块
//! 
//! 提供监控数据可视化和仪表板功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use chrono::{DateTime, Utc};
use super::MonitoringError;

/// 监控仪表板
#[derive(Clone)]
pub struct MonitoringDashboard {
    /// 仪表板配置
    config: DashboardConfig,
    /// 仪表板数据
    data: Arc<RwLock<DashboardData>>,
    /// 数据源
    data_sources: Arc<RwLock<HashMap<String, DataSource>>>,
}

/// 仪表板配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DashboardConfig {
    /// 刷新间隔 (秒)
    pub refresh_interval: u64,
    /// 数据保留时间 (小时)
    pub data_retention_hours: u32,
    /// 最大数据点数量
    pub max_data_points: usize,
    /// 是否启用实时更新
    pub enable_realtime: bool,
    /// 是否启用数据聚合
    pub enable_aggregation: bool,
    /// 聚合时间窗口 (分钟)
    pub aggregation_window_minutes: u32,
}

impl Default for DashboardConfig {
    fn default() -> Self {
        Self {
            refresh_interval: 30,
            data_retention_hours: 24,
            max_data_points: 10000,
            enable_realtime: true,
            enable_aggregation: true,
            aggregation_window_minutes: 5,
        }
    }
}

/// 仪表板数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DashboardData {
    /// 系统概览
    pub system_overview: SystemOverview,
    /// 指标数据
    pub metrics: Vec<MetricData>,
    /// 告警数据
    pub alerts: Vec<AlertData>,
    /// 健康检查数据
    pub health_checks: Vec<HealthCheckData>,
    /// 性能数据
    pub performance: PerformanceData,
    /// 更新时间
    pub updated_at: DateTime<Utc>,
}

/// 系统概览
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SystemOverview {
    /// 系统状态
    pub status: SystemStatus,
    /// 总设备数
    pub total_devices: u32,
    /// 在线设备数
    pub online_devices: u32,
    /// 离线设备数
    pub offline_devices: u32,
    /// 告警数量
    pub alert_count: u32,
    /// 系统负载
    pub system_load: f64,
    /// 内存使用率
    pub memory_usage: f64,
    /// 磁盘使用率
    pub disk_usage: f64,
    /// 网络流量
    pub network_traffic: NetworkTraffic,
}

/// 系统状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum SystemStatus {
    /// 正常
    Normal,
    /// 警告
    Warning,
    /// 错误
    Error,
    /// 严重
    Critical,
}

impl SystemStatus {
    /// 获取状态描述
    pub fn description(&self) -> &'static str {
        match self {
            SystemStatus::Normal => "正常",
            SystemStatus::Warning => "警告",
            SystemStatus::Error => "错误",
            SystemStatus::Critical => "严重",
        }
    }

    /// 获取状态颜色
    pub fn color(&self) -> &'static str {
        match self {
            SystemStatus::Normal => "green",
            SystemStatus::Warning => "yellow",
            SystemStatus::Error => "orange",
            SystemStatus::Critical => "red",
        }
    }
}

/// 网络流量
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkTraffic {
    /// 入站流量 (MB/s)
    pub inbound_mbps: f64,
    /// 出站流量 (MB/s)
    pub outbound_mbps: f64,
    /// 总流量 (MB/s)
    pub total_mbps: f64,
    /// 连接数
    pub connections: u32,
}

/// 指标数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricData {
    /// 指标名称
    pub name: String,
    /// 指标类型
    pub metric_type: String,
    /// 指标值
    pub value: f64,
    /// 指标单位
    pub unit: String,
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    /// 指标标签
    pub labels: HashMap<String, String>,
    /// 趋势
    pub trend: Trend,
}

/// 趋势
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Trend {
    /// 上升
    Up,
    /// 下降
    Down,
    /// 稳定
    Stable,
    /// 未知
    Unknown,
}

/// 导出格式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ExportFormat {
    /// JSON格式
    Json,
    /// CSV格式
    Csv,
    /// XML格式
    Xml,
}

/// 告警阈值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlertThresholds {
    /// CPU使用率阈值
    pub cpu_threshold: f64,
    /// 内存使用率阈值
    pub memory_threshold: f64,
    /// 磁盘使用率阈值
    pub disk_threshold: f64,
    /// 网络使用率阈值
    pub network_threshold: f64,
    /// 响应时间阈值
    pub response_time_threshold: f64,
    /// 错误率阈值
    pub error_rate_threshold: f64,
}

/// 告警统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlertStatistics {
    /// 总告警数
    pub total_alerts: usize,
    /// 严重告警数
    pub critical_alerts: usize,
    /// 警告告警数
    pub warning_alerts: usize,
    /// 已解决告警数
    pub resolved_alerts: usize,
    /// 活跃告警数
    pub active_alerts: usize,
}


impl Trend {
    /// 获取趋势描述
    pub fn description(&self) -> &'static str {
        match self {
            Trend::Up => "上升",
            Trend::Down => "下降",
            Trend::Stable => "稳定",
            Trend::Unknown => "未知",
        }
    }

    /// 获取趋势颜色
    pub fn color(&self) -> &'static str {
        match self {
            Trend::Up => "red",
            Trend::Down => "green",
            Trend::Stable => "blue",
            Trend::Unknown => "gray",
        }
    }
}

/// 告警数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AlertData {
    /// 告警ID
    pub id: String,
    /// 告警名称
    pub name: String,
    /// 告警级别
    pub severity: String,
    /// 告警状态
    pub status: String,
    /// 告警消息
    pub message: String,
    /// 触发时间
    pub triggered_at: DateTime<Utc>,
    /// 持续时间
    pub duration: Option<chrono::Duration>,
    /// 告警标签
    pub labels: HashMap<String, String>,
}

/// 健康检查数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthCheckData {
    /// 检查ID
    pub id: String,
    /// 检查名称
    pub name: String,
    /// 检查类型
    pub check_type: String,
    /// 健康状态
    pub status: String,
    /// 检查消息
    pub message: String,
    /// 响应时间 (毫秒)
    pub response_time_ms: Option<u64>,
    /// 检查时间
    pub timestamp: DateTime<Utc>,
    /// 检查详情
    pub details: HashMap<String, serde_json::Value>,
}

/// 性能数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceData {
    /// CPU使用率
    pub cpu_usage: f64,
    /// 内存使用率
    pub memory_usage: f64,
    /// 磁盘使用率
    pub disk_usage: f64,
    /// 网络使用率
    pub network_usage: f64,
    /// 响应时间 (毫秒)
    pub response_time_ms: f64,
    /// 吞吐量 (请求/秒)
    pub throughput_rps: f64,
    /// 错误率
    pub error_rate: f64,
}

/// 数据源
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataSource {
    /// 数据源ID
    pub id: String,
    /// 数据源名称
    pub name: String,
    /// 数据源类型
    pub source_type: DataSourceType,
    /// 数据源配置
    pub config: HashMap<String, serde_json::Value>,
    /// 是否启用
    pub enabled: bool,
    /// 最后更新时间
    pub last_updated: Option<DateTime<Utc>>,
}

/// 数据源类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum DataSourceType {
    /// 指标收集器
    MetricsCollector,
    /// 告警管理器
    AlertManager,
    /// 健康检查器
    HealthChecker,
    /// 外部API
    ExternalAPI,
    /// 数据库
    Database,
    /// 文件
    File,
}

impl DataSourceType {
    /// 获取类型描述
    pub fn description(&self) -> &'static str {
        match self {
            DataSourceType::MetricsCollector => "指标收集器",
            DataSourceType::AlertManager => "告警管理器",
            DataSourceType::HealthChecker => "健康检查器",
            DataSourceType::ExternalAPI => "外部API",
            DataSourceType::Database => "数据库",
            DataSourceType::File => "文件",
        }
    }
}

impl MonitoringDashboard {
    /// 创建新的监控仪表板
    pub fn new(config: DashboardConfig) -> Self {
        Self {
            config,
            data: Arc::new(RwLock::new(DashboardData {
                system_overview: SystemOverview {
                    status: SystemStatus::Normal,
                    total_devices: 0,
                    online_devices: 0,
                    offline_devices: 0,
                    alert_count: 0,
                    system_load: 0.0,
                    memory_usage: 0.0,
                    disk_usage: 0.0,
                    network_traffic: NetworkTraffic {
                        inbound_mbps: 0.0,
                        outbound_mbps: 0.0,
                        total_mbps: 0.0,
                        connections: 0,
                    },
                },
                metrics: Vec::new(),
                alerts: Vec::new(),
                health_checks: Vec::new(),
                performance: PerformanceData {
                    cpu_usage: 0.0,
                    memory_usage: 0.0,
                    disk_usage: 0.0,
                    network_usage: 0.0,
                    response_time_ms: 0.0,
                    throughput_rps: 0.0,
                    error_rate: 0.0,
                },
                updated_at: Utc::now(),
            })),
            data_sources: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 添加数据源
    pub async fn add_data_source(&self, data_source: DataSource) -> Result<(), MonitoringError> {
        let mut sources = self.data_sources.write().await;
        sources.insert(data_source.id.clone(), data_source);
        Ok(())
    }

    /// 移除数据源
    pub async fn remove_data_source(&self, source_id: &str) -> Result<(), MonitoringError> {
        let mut sources = self.data_sources.write().await;
        if sources.remove(source_id).is_some() {
            Ok(())
        } else {
            Err(MonitoringError::DashboardError(
                format!("数据源 {} 不存在", source_id)
            ))
        }
    }

    /// 获取数据源
    pub async fn get_data_source(&self, source_id: &str) -> Option<DataSource> {
        let sources = self.data_sources.read().await;
        sources.get(source_id).cloned()
    }

    /// 获取所有数据源
    pub async fn get_all_data_sources(&self) -> Vec<DataSource> {
        let sources = self.data_sources.read().await;
        sources.values().cloned().collect()
    }

    /// 更新仪表板数据
    pub async fn update_dashboard_data(&self) -> Result<(), MonitoringError> {
        let mut data = self.data.write().await;
        let sources = self.data_sources.read().await;
        
        // 更新系统概览
        self.update_system_overview(&mut data.system_overview, &sources).await;
        
        // 更新指标数据
        self.update_metrics_data(&mut data.metrics, &sources).await;
        
        // 更新告警数据
        self.update_alerts_data(&mut data.alerts, &sources).await;
        
        // 更新健康检查数据
        self.update_health_checks_data(&mut data.health_checks, &sources).await;
        
        // 更新性能数据
        self.update_performance_data(&mut data.performance, &sources).await;
        
        data.updated_at = Utc::now();
        
        Ok(())
    }

    /// 更新系统概览
    async fn update_system_overview(&self, overview: &mut SystemOverview, _sources: &HashMap<String, DataSource>) {
        // 从数据源获取实际数据
        let data = self.data.read().await;
        
        // 计算设备统计（基于健康检查数据）
        let mut total_devices = 0;
        let mut online_devices = 0;
        let mut offline_devices = 0;
        
        for health_check in &data.health_checks {
            total_devices += 1;
            match health_check.status.as_str() {
                "healthy" => online_devices += 1,
                "unhealthy" => offline_devices += 1,
                _ => {}
            }
        }
        
        // 计算告警数量
        let alert_count = data.alerts.len() as u32;
        
        // 计算系统负载（模拟）
        let system_load = (online_devices as f64) / (total_devices as f64).max(1.0);
        
        // 更新概览数据
        overview.total_devices = total_devices;
        overview.online_devices = online_devices;
        overview.offline_devices = offline_devices;
        overview.alert_count = alert_count;
        overview.system_load = system_load;
        overview.memory_usage = 0.7; // 模拟数据
        overview.disk_usage = 0.5;   // 模拟数据
        overview.network_traffic.inbound_mbps = 10.5;
        overview.network_traffic.outbound_mbps = 8.2;
        overview.network_traffic.total_mbps = 18.7;
        overview.network_traffic.connections = 150;
        
        // 根据数据确定系统状态
        if overview.alert_count > 10 || overview.system_load > 0.9 {
            overview.status = SystemStatus::Critical;
        } else if overview.alert_count > 5 || overview.system_load > 0.8 {
            overview.status = SystemStatus::Error;
        } else if overview.alert_count > 2 || overview.system_load > 0.7 {
            overview.status = SystemStatus::Warning;
        } else {
            overview.status = SystemStatus::Normal;
        }
    }

    /// 更新指标数据
    async fn update_metrics_data(&self, metrics: &mut Vec<MetricData>, _sources: &HashMap<String, DataSource>) {
        // 简化实现，实际应该从数据源获取数据
        metrics.clear();
        
        let now = Utc::now();
        let mut labels = HashMap::new();
        labels.insert("device_id".to_string(), "device_001".to_string());
        
        metrics.push(MetricData {
            name: "temperature".to_string(),
            metric_type: "gauge".to_string(),
            value: 25.5,
            unit: "°C".to_string(),
            timestamp: now,
            labels: labels.clone(),
            trend: Trend::Stable,
        });
        
        labels.insert("device_id".to_string(), "device_002".to_string());
        metrics.push(MetricData {
            name: "humidity".to_string(),
            metric_type: "gauge".to_string(),
            value: 60.0,
            unit: "%".to_string(),
            timestamp: now,
            labels,
            trend: Trend::Up,
        });
    }

    /// 更新告警数据
    async fn update_alerts_data(&self, alerts: &mut Vec<AlertData>, _sources: &HashMap<String, DataSource>) {
        // 简化实现，实际应该从数据源获取数据
        alerts.clear();
        
        let now = Utc::now();
        let mut labels = HashMap::new();
        labels.insert("device_id".to_string(), "device_001".to_string());
        
        alerts.push(AlertData {
            id: "alert_001".to_string(),
            name: "温度过高告警".to_string(),
            severity: "Warning".to_string(),
            status: "Firing".to_string(),
            message: "设备温度超过阈值".to_string(),
            triggered_at: now - chrono::Duration::minutes(5),
            duration: Some(chrono::Duration::minutes(5)),
            labels,
        });
    }

    /// 更新健康检查数据
    async fn update_health_checks_data(&self, health_checks: &mut Vec<HealthCheckData>, _sources: &HashMap<String, DataSource>) {
        // 简化实现，实际应该从数据源获取数据
        health_checks.clear();
        
        let now = Utc::now();
        let mut details = HashMap::new();
        details.insert("cpu_usage".to_string(), serde_json::Value::Number(serde_json::Number::from(50)));
        details.insert("memory_usage".to_string(), serde_json::Value::Number(serde_json::Number::from(60)));
        
        health_checks.push(HealthCheckData {
            id: "health_001".to_string(),
            name: "系统健康检查".to_string(),
            check_type: "System".to_string(),
            status: "Healthy".to_string(),
            message: "系统运行正常".to_string(),
            response_time_ms: Some(50),
            timestamp: now,
            details,
        });
    }

    /// 更新性能数据
    async fn update_performance_data(&self, performance: &mut PerformanceData, _sources: &HashMap<String, DataSource>) {
        // 简化实现，使用模拟数据
        // 在实际应用中，这里应该从数据源获取真实的性能数据
        performance.cpu_usage = 0.6;
        performance.memory_usage = 0.7;
        performance.disk_usage = 0.5;
        performance.network_usage = 0.3;
        performance.response_time_ms = 100.0;
        performance.throughput_rps = 1000.0;
        performance.error_rate = 0.01;
    }

    /// 获取仪表板数据
    pub async fn get_dashboard_data(&self) -> DashboardData {
        let data = self.data.read().await;
        data.clone()
    }

    /// 刷新数据
    pub async fn refresh_data(&self) -> Result<(), MonitoringError> {
        let mut data = self.data.write().await;
        
        // 模拟数据刷新
        data.system_overview.total_devices = 100;
        data.system_overview.online_devices = 95;
        data.system_overview.offline_devices = 5;
        data.system_overview.alert_count = 2;
        data.system_overview.system_load = 0.6;
        data.system_overview.memory_usage = 0.7;
        data.system_overview.disk_usage = 0.5;
        
        Ok(())
    }

    /// 获取实时数据流（简化版本）
    pub async fn get_realtime_data(&self) -> DashboardData {
        let data = self.data.read().await;
        data.clone()
    }

    /// 获取历史数据
    pub async fn get_historical_data(&self, start_time: DateTime<Utc>, end_time: DateTime<Utc>) -> Result<Vec<DashboardData>, MonitoringError> {
        // 这里应该从时间序列数据库获取历史数据
        // 简化实现，返回模拟数据
        let mut historical_data = Vec::new();
        let mut current_time = start_time;
        
        while current_time <= end_time {
            let data = DashboardData {
                system_overview: SystemOverview {
                    status: SystemStatus::Normal,
                    total_devices: 100,
                    online_devices: 95,
                    offline_devices: 5,
                    alert_count: 2,
                    system_load: 0.6,
                    memory_usage: 0.7,
                    disk_usage: 0.5,
                    network_traffic: NetworkTraffic {
                        inbound_mbps: 10.0,
                        outbound_mbps: 8.0,
                        total_mbps: 18.0,
                        connections: 25,
                    },
                },
                metrics: vec![],
                alerts: vec![],
                health_checks: vec![],
                performance: PerformanceData {
                    cpu_usage: 0.5 + (current_time.timestamp() % 100) as f64 / 200.0,
                    memory_usage: 0.6 + (current_time.timestamp() % 80) as f64 / 200.0,
                    disk_usage: 0.4 + (current_time.timestamp() % 60) as f64 / 200.0,
                    network_usage: 0.3 + (current_time.timestamp() % 40) as f64 / 200.0,
                    response_time_ms: 100.0 + (current_time.timestamp() % 50) as f64,
                    throughput_rps: 1000.0 + (current_time.timestamp() % 200) as f64,
                    error_rate: 0.01 + (current_time.timestamp() % 10) as f64 / 1000.0,
                },
                updated_at: current_time,
            };
            
            historical_data.push(data);
            current_time = current_time + chrono::Duration::minutes(5);
        }
        
        Ok(historical_data)
    }

    /// 导出仪表板数据
    pub async fn export_data(&self, format: ExportFormat) -> Result<Vec<u8>, MonitoringError> {
        let data = self.data.read().await;
        
        match format {
            ExportFormat::Json => {
                serde_json::to_vec(&*data)
                    .map_err(|e| MonitoringError::SerializationError(e.to_string()))
            }
            ExportFormat::Csv => {
                // 简化的CSV导出
                let mut csv_data = String::new();
                csv_data.push_str("updated_at,cpu_usage,memory_usage,disk_usage,network_usage,response_time_ms,throughput_rps,error_rate\n");
                csv_data.push_str(&format!(
                    "{},{},{},{},{},{},{},{}\n",
                    data.updated_at.to_rfc3339(),
                    data.performance.cpu_usage,
                    data.performance.memory_usage,
                    data.performance.disk_usage,
                    data.performance.network_usage,
                    data.performance.response_time_ms,
                    data.performance.throughput_rps,
                    data.performance.error_rate
                ));
                Ok(csv_data.into_bytes())
            }
            ExportFormat::Xml => {
                // 简化的XML导出
                let xml_data = format!(
                    r#"<?xml version="1.0" encoding="UTF-8"?>
<dashboard>
    <updated_at>{}</updated_at>
    <performance>
        <cpu_usage>{}</cpu_usage>
        <memory_usage>{}</memory_usage>
        <disk_usage>{}</disk_usage>
        <network_usage>{}</network_usage>
        <response_time_ms>{}</response_time_ms>
        <throughput_rps>{}</throughput_rps>
        <error_rate>{}</error_rate>
    </performance>
</dashboard>"#,
                    data.updated_at.to_rfc3339(),
                    data.performance.cpu_usage,
                    data.performance.memory_usage,
                    data.performance.disk_usage,
                    data.performance.network_usage,
                    data.performance.response_time_ms,
                    data.performance.throughput_rps,
                    data.performance.error_rate
                );
                Ok(xml_data.into_bytes())
            }
        }
    }

    /// 设置告警阈值
    pub async fn set_alert_thresholds(&mut self, _thresholds: HashMap<String, f64>) -> Result<(), MonitoringError> {
        let _data = self.data.write().await;
        // 这里应该更新告警阈值配置
        // 简化实现
        Ok(())
    }

    /// 获取告警统计
    pub async fn get_alert_statistics(&self) -> AlertStatistics {
        let data = self.data.read().await;
        
        AlertStatistics {
            total_alerts: data.alerts.len(),
            critical_alerts: data.alerts.iter().filter(|a| a.severity == "Critical").count(),
            warning_alerts: data.alerts.iter().filter(|a| a.severity == "Warning").count(),
            resolved_alerts: data.alerts.iter().filter(|a| a.status == "Resolved").count(),
            active_alerts: data.alerts.iter().filter(|a| a.status == "Active").count(),
        }
    }

    /// 获取系统概览
    pub async fn get_system_overview(&self) -> SystemOverview {
        let data = self.data.read().await;
        data.system_overview.clone()
    }

    /// 获取指标数据
    pub async fn get_metrics_data(&self, limit: Option<usize>) -> Vec<MetricData> {
        let data = self.data.read().await;
        let mut metrics = data.metrics.clone();
        
        if let Some(limit) = limit {
            metrics.truncate(limit);
        }
        
        metrics
    }

    /// 获取告警数据
    pub async fn get_alerts_data(&self, limit: Option<usize>) -> Vec<AlertData> {
        let data = self.data.read().await;
        let mut alerts = data.alerts.clone();
        
        if let Some(limit) = limit {
            alerts.truncate(limit);
        }
        
        alerts
    }

    /// 获取健康检查数据
    pub async fn get_health_checks_data(&self, limit: Option<usize>) -> Vec<HealthCheckData> {
        let data = self.data.read().await;
        let mut health_checks = data.health_checks.clone();
        
        if let Some(limit) = limit {
            health_checks.truncate(limit);
        }
        
        health_checks
    }

    /// 获取性能数据
    pub async fn get_performance_data(&self) -> PerformanceData {
        let data = self.data.read().await;
        data.performance.clone()
    }

    /// 导出仪表板数据为JSON
    pub async fn export_json(&self) -> Result<String, MonitoringError> {
        let data = self.data.read().await;
        serde_json::to_string_pretty(&*data)
            .map_err(|e| MonitoringError::DashboardError(
                format!("JSON序列化失败: {}", e)
            ))
    }

    /// 导出仪表板数据为CSV
    pub async fn export_csv(&self) -> Result<String, MonitoringError> {
        let data = self.data.read().await;
        let mut csv = String::new();
        
        // 添加系统概览
        csv.push_str("系统概览\n");
        csv.push_str(&format!("状态,{}\n", data.system_overview.status.description()));
        csv.push_str(&format!("总设备数,{}\n", data.system_overview.total_devices));
        csv.push_str(&format!("在线设备数,{}\n", data.system_overview.online_devices));
        csv.push_str(&format!("离线设备数,{}\n", data.system_overview.offline_devices));
        csv.push_str(&format!("告警数量,{}\n", data.system_overview.alert_count));
        csv.push_str(&format!("系统负载,{:.2}\n", data.system_overview.system_load));
        csv.push_str(&format!("内存使用率,{:.2}\n", data.system_overview.memory_usage));
        csv.push_str(&format!("磁盘使用率,{:.2}\n", data.system_overview.disk_usage));
        csv.push_str("\n");
        
        // 添加指标数据
        csv.push_str("指标数据\n");
        csv.push_str("名称,类型,值,单位,时间戳,趋势\n");
        for metric in &data.metrics {
            csv.push_str(&format!("{},{},{},{},{},{}\n",
                metric.name,
                metric.metric_type,
                metric.value,
                metric.unit,
                metric.timestamp.format("%Y-%m-%d %H:%M:%S"),
                metric.trend.description()
            ));
        }
        csv.push_str("\n");
        
        // 添加告警数据
        csv.push_str("告警数据\n");
        csv.push_str("ID,名称,级别,状态,消息,触发时间,持续时间\n");
        for alert in &data.alerts {
            let duration = if let Some(d) = alert.duration {
                format!("{}分钟", d.num_minutes())
            } else {
                "未知".to_string()
            };
            csv.push_str(&format!("{},{},{},{},{},{},{}\n",
                alert.id,
                alert.name,
                alert.severity,
                alert.status,
                alert.message,
                alert.triggered_at.format("%Y-%m-%d %H:%M:%S"),
                duration
            ));
        }
        csv.push_str("\n");
        
        // 添加健康检查数据
        csv.push_str("健康检查数据\n");
        csv.push_str("ID,名称,类型,状态,消息,响应时间,检查时间\n");
        for health_check in &data.health_checks {
            let response_time = if let Some(rt) = health_check.response_time_ms {
                format!("{}ms", rt)
            } else {
                "未知".to_string()
            };
            csv.push_str(&format!("{},{},{},{},{},{},{}\n",
                health_check.id,
                health_check.name,
                health_check.check_type,
                health_check.status,
                health_check.message,
                response_time,
                health_check.timestamp.format("%Y-%m-%d %H:%M:%S")
            ));
        }
        
        Ok(csv)
    }

    /// 启动仪表板更新
    pub async fn start_dashboard_updates(&self) -> Result<(), MonitoringError> {
        if !self.config.enable_realtime {
            return Ok(());
        }
        
        let config = self.config.clone();
        let data = Arc::clone(&self.data);
        let data_sources = Arc::clone(&self.data_sources);
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(
                tokio::time::Duration::from_secs(config.refresh_interval)
            );
            
            loop {
                interval.tick().await;
                
                // 更新仪表板数据
                let mut data_guard = data.write().await;
                let sources_guard = data_sources.read().await;
                
                // 更新系统概览
                Self::update_system_overview_static(&mut data_guard.system_overview, &sources_guard).await;
                
                // 更新指标数据
                Self::update_metrics_data_static(&mut data_guard.metrics, &sources_guard).await;
                
                // 更新告警数据
                Self::update_alerts_data_static(&mut data_guard.alerts, &sources_guard).await;
                
                // 更新健康检查数据
                Self::update_health_checks_data_static(&mut data_guard.health_checks, &sources_guard).await;
                
                // 更新性能数据
                Self::update_performance_data_static(&mut data_guard.performance, &sources_guard).await;
                
                data_guard.updated_at = Utc::now();
            }
        });
        
        Ok(())
    }

    /// 静态方法：更新系统概览
    async fn update_system_overview_static(overview: &mut SystemOverview, _sources: &HashMap<String, DataSource>) {
        // 简化实现，实际应该从数据源获取数据
        overview.total_devices = 100;
        overview.online_devices = 95;
        overview.offline_devices = 5;
        overview.alert_count = 3;
        overview.system_load = 0.6;
        overview.memory_usage = 0.7;
        overview.disk_usage = 0.5;
        overview.network_traffic.inbound_mbps = 10.5;
        overview.network_traffic.outbound_mbps = 8.2;
        overview.network_traffic.total_mbps = 18.7;
        overview.network_traffic.connections = 150;
        
        // 根据数据确定系统状态
        if overview.alert_count > 10 || overview.system_load > 0.9 {
            overview.status = SystemStatus::Critical;
        } else if overview.alert_count > 5 || overview.system_load > 0.8 {
            overview.status = SystemStatus::Error;
        } else if overview.alert_count > 2 || overview.system_load > 0.7 {
            overview.status = SystemStatus::Warning;
        } else {
            overview.status = SystemStatus::Normal;
        }
    }

    /// 静态方法：更新指标数据
    async fn update_metrics_data_static(metrics: &mut Vec<MetricData>, _sources: &HashMap<String, DataSource>) {
        // 简化实现，实际应该从数据源获取数据
        metrics.clear();
        
        let now = Utc::now();
        let mut labels = HashMap::new();
        labels.insert("device_id".to_string(), "device_001".to_string());
        
        metrics.push(MetricData {
            name: "temperature".to_string(),
            metric_type: "gauge".to_string(),
            value: 25.5,
            unit: "°C".to_string(),
            timestamp: now,
            labels: labels.clone(),
            trend: Trend::Stable,
        });
        
        labels.insert("device_id".to_string(), "device_002".to_string());
        metrics.push(MetricData {
            name: "humidity".to_string(),
            metric_type: "gauge".to_string(),
            value: 60.0,
            unit: "%".to_string(),
            timestamp: now,
            labels,
            trend: Trend::Up,
        });
    }

    /// 静态方法：更新告警数据
    async fn update_alerts_data_static(alerts: &mut Vec<AlertData>, _sources: &HashMap<String, DataSource>) {
        // 简化实现，实际应该从数据源获取数据
        alerts.clear();
        
        let now = Utc::now();
        let mut labels = HashMap::new();
        labels.insert("device_id".to_string(), "device_001".to_string());
        
        alerts.push(AlertData {
            id: "alert_001".to_string(),
            name: "温度过高告警".to_string(),
            severity: "Warning".to_string(),
            status: "Firing".to_string(),
            message: "设备温度超过阈值".to_string(),
            triggered_at: now - chrono::Duration::minutes(5),
            duration: Some(chrono::Duration::minutes(5)),
            labels,
        });
    }

    /// 静态方法：更新健康检查数据
    async fn update_health_checks_data_static(health_checks: &mut Vec<HealthCheckData>, _sources: &HashMap<String, DataSource>) {
        // 简化实现，实际应该从数据源获取数据
        health_checks.clear();
        
        let now = Utc::now();
        let mut details = HashMap::new();
        details.insert("cpu_usage".to_string(), serde_json::Value::Number(serde_json::Number::from(50)));
        details.insert("memory_usage".to_string(), serde_json::Value::Number(serde_json::Number::from(60)));
        
        health_checks.push(HealthCheckData {
            id: "health_001".to_string(),
            name: "系统健康检查".to_string(),
            check_type: "System".to_string(),
            status: "Healthy".to_string(),
            message: "系统运行正常".to_string(),
            response_time_ms: Some(50),
            timestamp: now,
            details,
        });
    }

    /// 静态方法：更新性能数据
    async fn update_performance_data_static(performance: &mut PerformanceData, _sources: &HashMap<String, DataSource>) {
        // 简化实现，实际应该从数据源获取数据
        performance.cpu_usage = 0.6;
        performance.memory_usage = 0.7;
        performance.disk_usage = 0.5;
        performance.network_usage = 0.3;
        performance.response_time_ms = 100.0;
        performance.throughput_rps = 1000.0;
        performance.error_rate = 0.01;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_monitoring_dashboard_creation() {
        let config = DashboardConfig::default();
        let dashboard = MonitoringDashboard::new(config);
        
        let data = dashboard.get_dashboard_data().await;
        assert_eq!(data.system_overview.total_devices, 0);
    }

    #[tokio::test]
    async fn test_add_data_source() {
        let config = DashboardConfig::default();
        let dashboard = MonitoringDashboard::new(config);
        
        let data_source = DataSource {
            id: "source_001".to_string(),
            name: "指标收集器".to_string(),
            source_type: DataSourceType::MetricsCollector,
            config: HashMap::new(),
            enabled: true,
            last_updated: None,
        };
        
        assert!(dashboard.add_data_source(data_source).await.is_ok());
        
        let sources = dashboard.get_all_data_sources().await;
        assert_eq!(sources.len(), 1);
    }

    #[tokio::test]
    async fn test_update_dashboard_data() {
        let config = DashboardConfig::default();
        let dashboard = MonitoringDashboard::new(config);
        
        assert!(dashboard.update_dashboard_data().await.is_ok());
        
        let data = dashboard.get_dashboard_data().await;
        assert_eq!(data.system_overview.total_devices, 100);
    }

    #[tokio::test]
    async fn test_export_json() {
        let config = DashboardConfig::default();
        let dashboard = MonitoringDashboard::new(config);
        
        dashboard.update_dashboard_data().await.unwrap();
        
        let json = dashboard.export_json().await.unwrap();
        assert!(json.contains("system_overview"));
    }

    #[tokio::test]
    async fn test_export_csv() {
        let config = DashboardConfig::default();
        let dashboard = MonitoringDashboard::new(config);
        
        dashboard.update_dashboard_data().await.unwrap();
        
        let csv = dashboard.export_csv().await.unwrap();
        assert!(csv.contains("系统概览"));
    }

    #[tokio::test]
    async fn test_system_status_ordering() {
        assert!(SystemStatus::Normal.description() == "正常");
        assert!(SystemStatus::Warning.description() == "警告");
        assert!(SystemStatus::Error.description() == "错误");
        assert!(SystemStatus::Critical.description() == "严重");
    }

    #[tokio::test]
    async fn test_trend_descriptions() {
        assert_eq!(Trend::Up.description(), "上升");
        assert_eq!(Trend::Down.description(), "下降");
        assert_eq!(Trend::Stable.description(), "稳定");
        assert_eq!(Trend::Unknown.description(), "未知");
    }

    #[tokio::test]
    async fn test_data_source_type_descriptions() {
        assert_eq!(DataSourceType::MetricsCollector.description(), "指标收集器");
        assert_eq!(DataSourceType::AlertManager.description(), "告警管理器");
        assert_eq!(DataSourceType::HealthChecker.description(), "健康检查器");
        assert_eq!(DataSourceType::ExternalAPI.description(), "外部API");
        assert_eq!(DataSourceType::Database.description(), "数据库");
        assert_eq!(DataSourceType::File.description(), "文件");
    }
}
