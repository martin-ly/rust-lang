//! 监控仪表板模块
//!
//! 提供实时监控数据的可视化和分析功能。

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime};
use serde::{Serialize, Deserialize};
use tokio::sync::RwLock;
use tracing::info;

use crate::error_handling::UnifiedError;
use super::{MonitoringState, HealthChecker, HealthCheckResult, ResourceMonitor, PerformanceMonitor, AnomalyDetector};

/// 监控仪表板配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DashboardConfig {
    /// 数据刷新间隔
    pub refresh_interval: Duration,
    /// 历史数据保留时间
    pub history_retention: Duration,
    /// 最大历史数据点数量
    pub max_history_points: usize,
    /// 是否启用实时更新
    pub real_time_enabled: bool,
    /// 告警阈值配置
    pub alert_thresholds: DashboardAlertThresholds,
}

impl Default for DashboardConfig {
    fn default() -> Self {
        Self {
            refresh_interval: Duration::from_secs(5),
            history_retention: Duration::from_secs(3600), // 1小时
            max_history_points: 720, // 5秒间隔，1小时数据
            real_time_enabled: true,
            alert_thresholds: DashboardAlertThresholds::default(),
        }
    }
}

/// 仪表板告警阈值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DashboardAlertThresholds {
    /// CPU使用率告警阈值
    pub cpu_alert_threshold: f64,
    /// 内存使用率告警阈值
    pub memory_alert_threshold: f64,
    /// 响应时间告警阈值
    pub response_time_alert_threshold: Duration,
    /// 错误率告警阈值
    pub error_rate_alert_threshold: f64,
    /// 异常检测告警阈值
    pub anomaly_alert_threshold: f64,
}

impl Default for DashboardAlertThresholds {
    fn default() -> Self {
        Self {
            cpu_alert_threshold: 80.0,
            memory_alert_threshold: 85.0,
            response_time_alert_threshold: Duration::from_millis(1000),
            error_rate_alert_threshold: 0.05, // 5%
            anomaly_alert_threshold: 0.7,
        }
    }
}

/// 监控数据点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonitoringDataPoint {
    /// 时间戳
    pub timestamp: SystemTime,
    /// 健康状态
    pub health_status: MonitoringState,
    /// 资源使用情况
    pub resource_usage: ResourceUsageData,
    /// 性能指标
    pub performance_metrics: PerformanceMetricsData,
    /// 异常检测结果
    pub anomaly_results: AnomalyDetectionData,
    /// 自定义指标
    pub custom_metrics: HashMap<String, f64>,
}

/// 资源使用数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceUsageData {
    /// CPU使用率百分比
    pub cpu_usage_percent: f64,
    /// 内存使用率百分比
    pub memory_usage_percent: f64,
    /// 磁盘使用率百分比
    pub disk_usage_percent: f64,
    /// 网络I/O使用率
    pub network_io_usage: f64,
    /// 活跃连接数
    pub active_connections: u32,
}

/// 性能指标数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMetricsData {
    /// 平均响应时间
    pub average_response_time: Duration,
    /// 95%分位响应时间
    pub p95_response_time: Duration,
    /// 99%分位响应时间
    pub p99_response_time: Duration,
    /// 每秒请求数
    pub requests_per_second: f64,
    /// 错误率
    pub error_rate: f64,
    /// 吞吐量
    pub throughput: f64,
}

/// 异常检测数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AnomalyDetectionData {
    /// 是否检测到异常
    pub anomalies_detected: bool,
    /// 异常数量
    pub anomaly_count: u32,
    /// 异常检测器数量
    pub total_detectors: u32,
    /// 异常评分
    pub anomaly_score: f64,
    /// 异常详情
    pub anomaly_details: HashMap<String, String>,
}

/// 仪表板状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DashboardStatus {
    /// 当前状态
    pub current_state: MonitoringState,
    /// 最后更新时间
    pub last_updated: SystemTime,
    /// 数据点数量
    pub data_points_count: usize,
    /// 是否正在运行
    pub is_running: bool,
    /// 告警数量
    pub alert_count: u32,
    /// 系统运行时间
    pub uptime: Duration,
}

/// 监控仪表板
pub struct MonitoringDashboard {
    /// 配置
    config: DashboardConfig,
    /// 历史数据
    history_data: Arc<RwLock<Vec<MonitoringDataPoint>>>,
    /// 当前状态
    current_status: Arc<RwLock<DashboardStatus>>,
    /// 健康检查器
    health_checker: Arc<HealthChecker>,
    /// 资源监控器
    _resource_monitor: Arc<ResourceMonitor>,
    /// 性能监控器
    _performance_monitor: Arc<PerformanceMonitor>,
    /// 异常检测器
    anomaly_detector: Arc<AnomalyDetector>,
    /// 启动时间
    start_time: Instant,
    /// 是否正在运行
    is_running: Arc<std::sync::atomic::AtomicBool>,
}

impl MonitoringDashboard {
    /// 创建新的监控仪表板
    pub fn new(
        config: DashboardConfig,
        health_checker: Arc<HealthChecker>,
        resource_monitor: Arc<ResourceMonitor>,
        performance_monitor: Arc<PerformanceMonitor>,
        anomaly_detector: Arc<AnomalyDetector>,
    ) -> Self {
        let start_time = Instant::now();
        let is_running = Arc::new(std::sync::atomic::AtomicBool::new(false));
        
        let current_status = Arc::new(RwLock::new(DashboardStatus {
            current_state: MonitoringState::Healthy,
            last_updated: SystemTime::now(),
            data_points_count: 0,
            is_running: false,
            alert_count: 0,
            uptime: Duration::from_secs(0),
        }));

        Self {
            config,
            history_data: Arc::new(RwLock::new(Vec::new())),
            current_status,
            health_checker,
            _resource_monitor: resource_monitor,
            _performance_monitor: performance_monitor,
            anomaly_detector,
            start_time,
            is_running,
        }
    }

    /// 启动监控仪表板
    pub async fn start(&self) -> Result<(), UnifiedError> {
        if self.is_running.load(std::sync::atomic::Ordering::Relaxed) {
            return Err(UnifiedError::new(
                "监控仪表板已经在运行",
                crate::error_handling::ErrorSeverity::Low,
                "dashboard",
                crate::error_handling::ErrorContext::new(
                    "dashboard",
                    "start",
                    file!(),
                    line!(),
                    crate::error_handling::ErrorSeverity::Low,
                    "dashboard",
                ),
            ));
        }

        self.is_running.store(true, std::sync::atomic::Ordering::Relaxed);
        
        // 更新状态
        {
            let mut status = self.current_status.write().await;
            status.is_running = true;
            status.last_updated = SystemTime::now();
        }

        info!("监控仪表板已启动");
        Ok(())
    }

    /// 停止监控仪表板
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.is_running.store(false, std::sync::atomic::Ordering::Relaxed);
        
        // 更新状态
        {
            let mut status = self.current_status.write().await;
            status.is_running = false;
            status.last_updated = SystemTime::now();
        }

        info!("监控仪表板已停止");
        Ok(())
    }

    /// 收集当前监控数据
    pub async fn collect_data(&self) -> Result<MonitoringDataPoint, UnifiedError> {
        // 收集健康状态
        let health_check_result = self.health_checker.check_health().await.unwrap_or_else(|_| {
            HealthCheckResult {
                timestamp: chrono::Utc::now(),
                state: MonitoringState::Error,
                items: Vec::new(),
                total_checks: 0,
                successful_checks: 0,
                failed_checks: 0,
                warning_checks: 0,
            }
        });
        let health_status = health_check_result.state;

        // 收集资源使用情况
        let resource_usage = self.collect_resource_usage().await?;

        // 收集性能指标
        let performance_metrics = self.collect_performance_metrics().await?;

        // 收集异常检测结果
        let anomaly_results = self.collect_anomaly_results().await?;

        // 创建数据点
        let data_point = MonitoringDataPoint {
            timestamp: SystemTime::now(),
            health_status,
            resource_usage,
            performance_metrics,
            anomaly_results,
            custom_metrics: HashMap::new(),
        };

        // 添加到历史数据
        self.add_to_history(data_point.clone()).await;

        // 更新当前状态
        self.update_current_status(&data_point).await;

        Ok(data_point)
    }

    /// 收集资源使用情况
    async fn collect_resource_usage(&self) -> Result<ResourceUsageData, UnifiedError> {
        // 这里应该从实际的资源监控器获取数据
        // 目前返回模拟数据
        Ok(ResourceUsageData {
            cpu_usage_percent: 45.0,
            memory_usage_percent: 60.0,
            disk_usage_percent: 30.0,
            network_io_usage: 25.0,
            active_connections: 150,
        })
    }

    /// 收集性能指标
    async fn collect_performance_metrics(&self) -> Result<PerformanceMetricsData, UnifiedError> {
        // 这里应该从实际的性能监控器获取数据
        // 目前返回模拟数据
        Ok(PerformanceMetricsData {
            average_response_time: Duration::from_millis(120),
            p95_response_time: Duration::from_millis(300),
            p99_response_time: Duration::from_millis(500),
            requests_per_second: 1000.0,
            error_rate: 0.02,
            throughput: 1200.0,
        })
    }

    /// 收集异常检测结果
    async fn collect_anomaly_results(&self) -> Result<AnomalyDetectionData, UnifiedError> {
        match self.anomaly_detector.detect_anomalies().await {
            Ok(result) => Ok(AnomalyDetectionData {
                anomalies_detected: result.anomalies_detected > 0,
                anomaly_count: result.anomalies_detected as u32,
                total_detectors: result.total_detectors as u32,
                anomaly_score: result.items.iter()
                    .map(|item| item.anomaly_score)
                    .sum::<f64>() / result.items.len() as f64,
                anomaly_details: result.items.iter()
                    .filter(|item| item.anomaly_detected)
                    .flat_map(|item| item.anomaly_details.clone())
                    .collect(),
            }),
            Err(_) => Ok(AnomalyDetectionData {
                anomalies_detected: false,
                anomaly_count: 0,
                total_detectors: 0,
                anomaly_score: 0.0,
                anomaly_details: HashMap::new(),
            }),
        }
    }

    /// 添加数据点到历史记录
    async fn add_to_history(&self, data_point: MonitoringDataPoint) {
        let mut history = self.history_data.write().await;
        
        // 添加新数据点
        history.push(data_point);
        
        // 清理过期数据
        let cutoff_time = SystemTime::now() - self.config.history_retention;
        history.retain(|point| point.timestamp > cutoff_time);
        
        // 限制数据点数量
        if history.len() > self.config.max_history_points {
            let excess = history.len() - self.config.max_history_points;
            history.drain(0..excess);
        }
    }

    /// 更新当前状态
    async fn update_current_status(&self, data_point: &MonitoringDataPoint) {
        let mut status = self.current_status.write().await;
        
        status.current_state = data_point.health_status.clone();
        status.last_updated = data_point.timestamp;
        status.data_points_count = self.history_data.read().await.len();
        status.uptime = self.start_time.elapsed();
        
        // 计算告警数量
        status.alert_count = self.calculate_alert_count(data_point);
    }

    /// 计算告警数量
    fn calculate_alert_count(&self, data_point: &MonitoringDataPoint) -> u32 {
        let mut alert_count = 0;
        
        // 检查资源使用告警
        if data_point.resource_usage.cpu_usage_percent > self.config.alert_thresholds.cpu_alert_threshold {
            alert_count += 1;
        }
        if data_point.resource_usage.memory_usage_percent > self.config.alert_thresholds.memory_alert_threshold {
            alert_count += 1;
        }
        
        // 检查性能告警
        if data_point.performance_metrics.average_response_time > self.config.alert_thresholds.response_time_alert_threshold {
            alert_count += 1;
        }
        if data_point.performance_metrics.error_rate > self.config.alert_thresholds.error_rate_alert_threshold {
            alert_count += 1;
        }
        
        // 检查异常告警
        if data_point.anomaly_results.anomaly_score > self.config.alert_thresholds.anomaly_alert_threshold {
            alert_count += 1;
        }
        
        alert_count
    }

    /// 获取历史数据
    pub async fn get_history_data(&self) -> Vec<MonitoringDataPoint> {
        self.history_data.read().await.clone()
    }

    /// 获取当前状态
    pub async fn get_current_status(&self) -> DashboardStatus {
        self.current_status.read().await.clone()
    }

    /// 获取指定时间范围的数据
    pub async fn get_data_in_range(&self, start: SystemTime, end: SystemTime) -> Vec<MonitoringDataPoint> {
        let history = self.history_data.read().await;
        history.iter()
            .filter(|point| point.timestamp >= start && point.timestamp <= end)
            .cloned()
            .collect()
    }

    /// 获取统计摘要
    pub async fn get_statistics_summary(&self) -> DashboardStatisticsSummary {
        let history = self.history_data.read().await;
        
        if history.is_empty() {
            return DashboardStatisticsSummary::default();
        }

        let mut cpu_usage_sum = 0.0;
        let mut memory_usage_sum = 0.0;
        let mut response_time_sum = Duration::from_secs(0);
        let mut error_rate_sum = 0.0;
        let mut anomaly_count = 0;

        for point in history.iter() {
            cpu_usage_sum += point.resource_usage.cpu_usage_percent;
            memory_usage_sum += point.resource_usage.memory_usage_percent;
            response_time_sum += point.performance_metrics.average_response_time;
            error_rate_sum += point.performance_metrics.error_rate;
            if point.anomaly_results.anomalies_detected {
                anomaly_count += 1;
            }
        }

        let count = history.len() as f64;
        
        DashboardStatisticsSummary {
            data_points_count: history.len(),
            average_cpu_usage: cpu_usage_sum / count,
            average_memory_usage: memory_usage_sum / count,
            average_response_time: Duration::from_nanos(
                (response_time_sum.as_nanos() as f64 / count) as u64
            ),
            average_error_rate: error_rate_sum / count,
            anomaly_detection_rate: anomaly_count as f64 / count,
            time_range: if let (Some(first), Some(last)) = (history.first(), history.last()) {
                last.timestamp.duration_since(first.timestamp).unwrap_or_default()
            } else {
                Duration::from_secs(0)
            },
        }
    }
}

/// 仪表板统计摘要
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DashboardStatisticsSummary {
    /// 数据点数量
    pub data_points_count: usize,
    /// 平均CPU使用率
    pub average_cpu_usage: f64,
    /// 平均内存使用率
    pub average_memory_usage: f64,
    /// 平均响应时间
    pub average_response_time: Duration,
    /// 平均错误率
    pub average_error_rate: f64,
    /// 异常检测率
    pub anomaly_detection_rate: f64,
    /// 时间范围
    pub time_range: Duration,
}

impl Default for DashboardStatisticsSummary {
    fn default() -> Self {
        Self {
            data_points_count: 0,
            average_cpu_usage: 0.0,
            average_memory_usage: 0.0,
            average_response_time: Duration::from_secs(0),
            average_error_rate: 0.0,
            anomaly_detection_rate: 0.0,
            time_range: Duration::from_secs(0),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;
    use super::super::{AnomalyDetectionConfig, HealthCheckConfig, ResourceMonitorConfig, PerformanceMonitorConfig};

    #[tokio::test]
    async fn test_dashboard_creation() {
        let config = DashboardConfig::default();
        let health_checker = Arc::new(HealthChecker::new(HealthCheckConfig::default()));
        let resource_monitor = Arc::new(ResourceMonitor::new(ResourceMonitorConfig::default()));
        let performance_monitor = Arc::new(PerformanceMonitor::new(PerformanceMonitorConfig::default()));
        let anomaly_detector = Arc::new(AnomalyDetector::new(AnomalyDetectionConfig::default()));

        let dashboard = MonitoringDashboard::new(
            config,
            health_checker,
            resource_monitor,
            performance_monitor,
            anomaly_detector,
        );

        assert!(!dashboard.is_running.load(std::sync::atomic::Ordering::Relaxed));
    }

    #[tokio::test]
    async fn test_dashboard_start_stop() {
        let config = DashboardConfig::default();
        let health_checker = Arc::new(HealthChecker::new(HealthCheckConfig::default()));
        let resource_monitor = Arc::new(ResourceMonitor::new(ResourceMonitorConfig::default()));
        let performance_monitor = Arc::new(PerformanceMonitor::new(PerformanceMonitorConfig::default()));
        let anomaly_detector = Arc::new(AnomalyDetector::new(AnomalyDetectionConfig::default()));

        let dashboard = MonitoringDashboard::new(
            config,
            health_checker,
            resource_monitor,
            performance_monitor,
            anomaly_detector,
        );

        // 启动仪表板
        assert!(dashboard.start().await.is_ok());
        assert!(dashboard.is_running.load(std::sync::atomic::Ordering::Relaxed));

        // 停止仪表板
        assert!(dashboard.stop().await.is_ok());
        assert!(!dashboard.is_running.load(std::sync::atomic::Ordering::Relaxed));
    }

    #[tokio::test]
    async fn test_data_collection() {
        let config = DashboardConfig::default();
        let health_checker = Arc::new(HealthChecker::new(HealthCheckConfig::default()));
        let resource_monitor = Arc::new(ResourceMonitor::new(ResourceMonitorConfig::default()));
        let performance_monitor = Arc::new(PerformanceMonitor::new(PerformanceMonitorConfig::default()));
        let anomaly_detector = Arc::new(AnomalyDetector::new(AnomalyDetectionConfig::default()));

        let dashboard = MonitoringDashboard::new(
            config,
            health_checker,
            resource_monitor,
            performance_monitor,
            anomaly_detector,
        );

        // 收集数据
        let data_point = dashboard.collect_data().await.unwrap();
        
        assert!(data_point.timestamp <= SystemTime::now());
        assert!(data_point.resource_usage.cpu_usage_percent >= 0.0);
        assert!(data_point.resource_usage.cpu_usage_percent <= 100.0);
    }

    #[test]
    fn test_dashboard_config_default() {
        let config = DashboardConfig::default();
        assert_eq!(config.refresh_interval, Duration::from_secs(5));
        assert_eq!(config.history_retention, Duration::from_secs(3600));
        assert_eq!(config.max_history_points, 720);
        assert!(config.real_time_enabled);
    }

    #[test]
    fn test_alert_thresholds_default() {
        let thresholds = DashboardAlertThresholds::default();
        assert_eq!(thresholds.cpu_alert_threshold, 80.0);
        assert_eq!(thresholds.memory_alert_threshold, 85.0);
        assert_eq!(thresholds.response_time_alert_threshold, Duration::from_millis(1000));
        assert_eq!(thresholds.error_rate_alert_threshold, 0.05);
        assert_eq!(thresholds.anomaly_alert_threshold, 0.7);
    }
}
