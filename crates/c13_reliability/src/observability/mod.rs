/// 高级可观测性模块
///
/// 提供企业级的监控、日志、追踪和告警功能
///
/// # 模块结构
///
/// - `metrics_aggregation` - 指标聚合和统计
/// - `log_correlation` - 日志关联和分析
/// - `alerting` - 实时告警系统
/// - `dashboards` - 可视化仪表板

pub mod metrics_aggregation;
pub mod log_correlation;
pub mod alerting;
pub mod profiler;

// 重新导出常用类型
pub use metrics_aggregation::{MetricsAggregator, MetricType, AggregatedMetric};
pub use log_correlation::{LogCorrelator, CorrelationContext};
pub use alerting::{AlertManager, Alert, AlertLevel};
pub use profiler::{Profiler, ProfileType, ProfileReport};
