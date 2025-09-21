//! 监控系统模块
//! 
//! 提供IoT系统监控功能，包括指标收集、告警、日志等

pub mod metrics_collector;
pub mod alert_manager;
pub mod health_checker;
pub mod dashboard;
pub mod performance_monitor;

pub use metrics_collector::{MetricsCollector, Metric, MetricType, MetricValue};
pub use alert_manager::{AlertManager, Alert, AlertSeverity, AlertRule, AlertNotification};
pub use health_checker::{HealthChecker, HealthStatus, HealthCheckResult};
pub use dashboard::{MonitoringDashboard, DashboardData, SystemOverview};
pub use performance_monitor::{
    PerformanceMonitor, PerformanceMetric, PerformanceStats, PerformanceAnalysis,
    PerformanceBottleneck, OptimizationRecommendation, PerformanceMonitorConfig,
    PerformanceThresholds, PerformanceMonitorError
};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum MonitoringError {
    #[error("指标收集错误: {0}")]
    MetricsCollectionError(String),
    #[error("告警管理错误: {0}")]
    AlertManagementError(String),
    #[error("健康检查错误: {0}")]
    HealthCheckError(String),
    #[error("仪表板错误: {0}")]
    DashboardError(String),
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    #[error("序列化错误: {0}")]
    SerializationError(String),
}
