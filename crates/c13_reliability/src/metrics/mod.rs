//! 指标模块
//!
//! 提供可靠性框架的指标收集、存储和分析功能。

use std::sync::Arc;
use std::collections::HashMap;
use std::time::{Duration, SystemTime};
use serde::{Serialize, Deserialize};
use tracing::{error, info};

use crate::error_handling::UnifiedError;


/// 可靠性指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReliabilityMetrics {
    /// 指标时间戳
    pub timestamp: SystemTime,
    /// 错误指标
    pub error_metrics: ErrorMetrics,
    /// 容错指标
    pub fault_tolerance_metrics: FaultToleranceMetrics,
    /// 性能指标
    pub performance_metrics: PerformanceMetrics,
    /// 资源指标
    pub resource_metrics: ResourceMetrics,
    /// 健康指标
    pub health_metrics: HealthMetrics,
    /// 自定义指标
    pub custom_metrics: HashMap<String, MetricValue>,
}

/// 错误指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorMetrics {
    /// 总错误数
    pub total_errors: u64,
    /// 错误率
    pub error_rate: f64,
    /// 按类型分组的错误数
    pub errors_by_type: HashMap<String, u64>,
    /// 按严重程度分组的错误数
    pub errors_by_severity: HashMap<String, u64>,
    /// 平均错误恢复时间
    pub average_recovery_time: Duration,
    /// 错误趋势
    pub error_trend: Vec<ErrorTrendPoint>,
}

/// 容错指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FaultToleranceMetrics {
    /// 断路器状态
    pub circuit_breaker_states: HashMap<String, String>,
    /// 重试次数
    pub retry_counts: HashMap<String, u64>,
    /// 超时次数
    pub timeout_counts: HashMap<String, u64>,
    /// 降级次数
    pub fallback_counts: HashMap<String, u64>,
    /// 容错成功率
    pub fault_tolerance_success_rate: f64,
    /// 平均恢复时间
    pub average_recovery_time: Duration,
}

/// 性能指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PerformanceMetrics {
    /// 总请求数
    pub total_requests: u64,
    /// 成功请求数
    pub successful_requests: u64,
    /// 失败请求数
    pub failed_requests: u64,
    /// 平均响应时间
    pub average_response_time: Duration,
    /// 最大响应时间
    pub max_response_time: Duration,
    /// 最小响应时间
    pub min_response_time: Duration,
    /// 吞吐量
    pub throughput: f64,
    /// 错误率
    pub error_rate: f64,
    /// 延迟分布
    pub latency_distribution: HashMap<String, u64>,
}

/// 资源指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceMetrics {
    /// CPU使用率
    pub cpu_usage: f64,
    /// 内存使用率
    pub memory_usage: f64,
    /// 磁盘使用率
    pub disk_usage: f64,
    /// 网络使用率
    pub network_usage: f64,
    /// 资源趋势
    pub resource_trend: Vec<ResourceTrendPoint>,
    /// 资源警告次数
    pub resource_warnings: u64,
    /// 资源错误次数
    pub resource_errors: u64,
}

/// 健康指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthMetrics {
    /// 整体健康状态
    pub overall_health: String,
    /// 健康检查项目
    pub health_checks: HashMap<String, String>,
    /// 健康检查次数
    pub health_check_count: u64,
    /// 健康检查成功率
    pub health_check_success_rate: f64,
    /// 健康趋势
    pub health_trend: Vec<HealthTrendPoint>,
}

/// 错误趋势点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorTrendPoint {
    /// 时间戳
    pub timestamp: SystemTime,
    /// 错误数
    pub error_count: u64,
    /// 错误率
    pub error_rate: f64,
}

/// 资源趋势点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ResourceTrendPoint {
    /// 时间戳
    pub timestamp: SystemTime,
    /// CPU使用率
    pub cpu_usage: f64,
    /// 内存使用率
    pub memory_usage: f64,
    /// 磁盘使用率
    pub disk_usage: f64,
    /// 网络使用率
    pub network_usage: f64,
}

/// 健康趋势点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HealthTrendPoint {
    /// 时间戳
    pub timestamp: SystemTime,
    /// 健康状态
    pub health_status: String,
    /// 健康分数
    pub health_score: f64,
}

/// 指标值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MetricValue {
    /// 整数值
    Integer(i64),
    /// 浮点值
    Float(f64),
    /// 字符串值
    String(String),
    /// 布尔值
    Boolean(bool),
    /// 持续时间
    Duration(Duration),
    /// 时间戳
    Timestamp(SystemTime),
}

impl MetricValue {
    /// 获取整数值
    pub fn as_integer(&self) -> Option<i64> {
        match self {
            MetricValue::Integer(value) => Some(*value),
            _ => None,
        }
    }

    /// 获取浮点值
    pub fn as_float(&self) -> Option<f64> {
        match self {
            MetricValue::Float(value) => Some(*value),
            MetricValue::Integer(value) => Some(*value as f64),
            _ => None,
        }
    }

    /// 获取字符串值
    pub fn as_string(&self) -> Option<&String> {
        match self {
            MetricValue::String(value) => Some(value),
            _ => None,
        }
    }

    /// 获取布尔值
    pub fn as_boolean(&self) -> Option<bool> {
        match self {
            MetricValue::Boolean(value) => Some(*value),
            _ => None,
        }
    }

    /// 获取持续时间
    pub fn as_duration(&self) -> Option<Duration> {
        match self {
            MetricValue::Duration(value) => Some(*value),
            _ => None,
        }
    }

    /// 获取时间戳
    pub fn as_timestamp(&self) -> Option<SystemTime> {
        match self {
            MetricValue::Timestamp(value) => Some(*value),
            _ => None,
        }
    }
}

/// 指标收集器
pub struct MetricsCollector {
    metrics: std::sync::Mutex<ReliabilityMetrics>,
    metrics_history: std::sync::Mutex<Vec<ReliabilityMetrics>>,
    collection_interval: Duration,
    is_running: std::sync::atomic::AtomicBool,
    custom_metrics: std::sync::Mutex<HashMap<String, MetricValue>>,
}

impl MetricsCollector {
    /// 创建新的指标收集器
    pub fn new(collection_interval: Duration) -> Self {
        Self {
            metrics: std::sync::Mutex::new(ReliabilityMetrics::default()),
            metrics_history: std::sync::Mutex::new(Vec::new()),
            collection_interval,
            is_running: std::sync::atomic::AtomicBool::new(false),
            custom_metrics: std::sync::Mutex::new(HashMap::new()),
        }
    }

    /// 启动指标收集
    pub async fn start(&self) -> Result<(), UnifiedError> {
        self.is_running.store(true, std::sync::atomic::Ordering::Relaxed);
        
        // 启动指标收集循环
        let collector = Arc::new(self.clone());
        tokio::spawn(async move {
            collector.run_collection_loop().await;
        });
        
        info!("指标收集器启动");
        Ok(())
    }

    /// 停止指标收集
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.is_running.store(false, std::sync::atomic::Ordering::Relaxed);
        info!("指标收集器停止");
        Ok(())
    }

    /// 收集指标
    pub async fn collect_metrics(&self) -> Result<ReliabilityMetrics, UnifiedError> {
        let timestamp = SystemTime::now();
        
        // 收集错误指标
        let error_metrics = self.collect_error_metrics().await;
        
        // 收集容错指标
        let fault_tolerance_metrics = self.collect_fault_tolerance_metrics().await;
        
        // 收集性能指标
        let performance_metrics = self.collect_performance_metrics().await;
        
        // 收集资源指标
        let resource_metrics = self.collect_resource_metrics().await;
        
        // 收集健康指标
        let health_metrics = self.collect_health_metrics().await;
        
        // 获取自定义指标
        let custom_metrics = self.custom_metrics.lock().unwrap().clone();
        
        let metrics = ReliabilityMetrics {
            timestamp,
            error_metrics,
            fault_tolerance_metrics,
            performance_metrics,
            resource_metrics,
            health_metrics,
            custom_metrics,
        };
        
        // 更新当前指标
        *self.metrics.lock().unwrap() = metrics.clone();
        
        // 添加到历史记录
        self.add_to_history(metrics.clone());
        
        Ok(metrics)
    }

    /// 收集错误指标
    async fn collect_error_metrics(&self) -> ErrorMetrics {
        // 模拟错误指标收集
        let mut errors_by_type = HashMap::new();
        errors_by_type.insert("network".to_string(), 5);
        errors_by_type.insert("database".to_string(), 3);
        errors_by_type.insert("service".to_string(), 2);
        
        let mut errors_by_severity = HashMap::new();
        errors_by_severity.insert("low".to_string(), 3);
        errors_by_severity.insert("medium".to_string(), 4);
        errors_by_severity.insert("high".to_string(), 2);
        errors_by_severity.insert("critical".to_string(), 1);
        
        let mut error_trend = Vec::new();
        for i in 0..10 {
            let timestamp = SystemTime::now() - Duration::from_secs(i * 60);
            error_trend.push(ErrorTrendPoint {
                timestamp,
                error_count: 10 - i,
                error_rate: (10 - i) as f64 / 100.0,
            });
        }
        
        ErrorMetrics {
            total_errors: 10,
            error_rate: 0.05,
            errors_by_type,
            errors_by_severity,
            average_recovery_time: Duration::from_millis(500),
            error_trend,
        }
    }

    /// 收集容错指标
    async fn collect_fault_tolerance_metrics(&self) -> FaultToleranceMetrics {
        // 模拟容错指标收集
        let mut circuit_breaker_states = HashMap::new();
        circuit_breaker_states.insert("service_a".to_string(), "closed".to_string());
        circuit_breaker_states.insert("service_b".to_string(), "open".to_string());
        circuit_breaker_states.insert("service_c".to_string(), "half_open".to_string());
        
        let mut retry_counts = HashMap::new();
        retry_counts.insert("service_a".to_string(), 5);
        retry_counts.insert("service_b".to_string(), 10);
        retry_counts.insert("service_c".to_string(), 3);
        
        let mut timeout_counts = HashMap::new();
        timeout_counts.insert("service_a".to_string(), 2);
        timeout_counts.insert("service_b".to_string(), 8);
        timeout_counts.insert("service_c".to_string(), 1);
        
        let mut fallback_counts = HashMap::new();
        fallback_counts.insert("service_a".to_string(), 1);
        fallback_counts.insert("service_b".to_string(), 5);
        fallback_counts.insert("service_c".to_string(), 0);
        
        FaultToleranceMetrics {
            circuit_breaker_states,
            retry_counts,
            timeout_counts,
            fallback_counts,
            fault_tolerance_success_rate: 0.85,
            average_recovery_time: Duration::from_millis(300),
        }
    }

    /// 收集性能指标
    async fn collect_performance_metrics(&self) -> PerformanceMetrics {
        // 模拟性能指标收集
        let mut latency_distribution = HashMap::new();
        latency_distribution.insert("0-100ms".to_string(), 1000);
        latency_distribution.insert("100-500ms".to_string(), 500);
        latency_distribution.insert("500ms-1s".to_string(), 100);
        latency_distribution.insert("1s+".to_string(), 50);
        
        PerformanceMetrics {
            total_requests: 10000,
            successful_requests: 9500,
            failed_requests: 500,
            average_response_time: Duration::from_millis(200),
            max_response_time: Duration::from_millis(2000),
            min_response_time: Duration::from_millis(50),
            throughput: 100.0,
            error_rate: 0.05,
            latency_distribution,
        }
    }

    /// 收集资源指标
    async fn collect_resource_metrics(&self) -> ResourceMetrics {
        // 模拟资源指标收集
        let mut resource_trend = Vec::new();
        for i in 0..10 {
            let timestamp = SystemTime::now() - Duration::from_secs(i * 60);
            resource_trend.push(ResourceTrendPoint {
                timestamp,
                cpu_usage: 50.0 + (i as f64 * 2.0),
                memory_usage: 60.0 + (i as f64 * 1.5),
                disk_usage: 40.0 + (i as f64 * 0.5),
                network_usage: 30.0 + (i as f64 * 1.0),
            });
        }
        
        ResourceMetrics {
            cpu_usage: 70.0,
            memory_usage: 75.0,
            disk_usage: 45.0,
            network_usage: 40.0,
            resource_trend,
            resource_warnings: 5,
            resource_errors: 1,
        }
    }

    /// 收集健康指标
    async fn collect_health_metrics(&self) -> HealthMetrics {
        // 模拟健康指标收集
        let mut health_checks = HashMap::new();
        health_checks.insert("database".to_string(), "healthy".to_string());
        health_checks.insert("cache".to_string(), "healthy".to_string());
        health_checks.insert("external_service".to_string(), "degraded".to_string());
        
        let mut health_trend = Vec::new();
        for i in 0..10 {
            let timestamp = SystemTime::now() - Duration::from_secs(i * 60);
            health_trend.push(HealthTrendPoint {
                timestamp,
                health_status: if i < 5 { "healthy".to_string() } else { "degraded".to_string() },
                health_score: 0.9 - (i as f64 * 0.02),
            });
        }
        
        HealthMetrics {
            overall_health: "healthy".to_string(),
            health_checks,
            health_check_count: 1000,
            health_check_success_rate: 0.95,
            health_trend,
        }
    }

    /// 运行指标收集循环
    async fn run_collection_loop(&self) {
        let mut interval = tokio::time::interval(self.collection_interval);
        
        while self.is_running.load(std::sync::atomic::Ordering::Relaxed) {
            interval.tick().await;
            
            if let Err(error) = self.collect_metrics().await {
                error!("指标收集失败: {}", error);
            }
        }
    }

    /// 添加到历史记录
    fn add_to_history(&self, metrics: ReliabilityMetrics) {
        let mut history = self.metrics_history.lock().unwrap();
        history.push(metrics);
        
        // 保持最近1000个指标记录
        if history.len() > 1000 {
            let len = history.len();
            history.drain(0..len - 1000);
        }
    }

    /// 获取当前指标
    pub fn get_current_metrics(&self) -> ReliabilityMetrics {
        self.metrics.lock().unwrap().clone()
    }

    /// 获取指标历史
    pub fn get_metrics_history(&self) -> Vec<ReliabilityMetrics> {
        self.metrics_history.lock().unwrap().clone()
    }

    /// 设置自定义指标
    pub fn set_custom_metric(&self, key: String, value: MetricValue) {
        let mut custom_metrics = self.custom_metrics.lock().unwrap();
        custom_metrics.insert(key, value);
    }

    /// 获取自定义指标
    pub fn get_custom_metric(&self, key: &str) -> Option<MetricValue> {
        let custom_metrics = self.custom_metrics.lock().unwrap();
        custom_metrics.get(key).cloned()
    }

    /// 获取所有自定义指标
    pub fn get_all_custom_metrics(&self) -> HashMap<String, MetricValue> {
        self.custom_metrics.lock().unwrap().clone()
    }
}

impl Clone for MetricsCollector {
    fn clone(&self) -> Self {
        Self {
            metrics: std::sync::Mutex::new(self.metrics.lock().unwrap().clone()),
            metrics_history: std::sync::Mutex::new(Vec::new()),
            collection_interval: self.collection_interval,
            is_running: std::sync::atomic::AtomicBool::new(false),
            custom_metrics: std::sync::Mutex::new(HashMap::new()),
        }
    }
}

/// 全局指标收集器
pub struct GlobalMetricsCollector {
    collector: Arc<MetricsCollector>,
}

impl GlobalMetricsCollector {
    /// 创建全局指标收集器
    pub fn new() -> Self {
        Self {
            collector: Arc::new(MetricsCollector::new(Duration::from_secs(60))),
        }
    }

    /// 获取指标收集器实例
    pub fn get_collector(&self) -> Arc<MetricsCollector> {
        self.collector.clone()
    }

    /// 启动全局指标收集
    pub async fn start(&self) -> Result<(), UnifiedError> {
        self.collector.start().await
    }

    /// 停止全局指标收集
    pub async fn stop(&self) -> Result<(), UnifiedError> {
        self.collector.stop().await
    }

    /// 收集全局指标
    pub async fn collect_metrics(&self) -> Result<ReliabilityMetrics, UnifiedError> {
        self.collector.collect_metrics().await
    }

    /// 获取当前全局指标
    pub fn get_current_metrics(&self) -> ReliabilityMetrics {
        self.collector.get_current_metrics()
    }

    /// 获取全局指标历史
    pub fn get_metrics_history(&self) -> Vec<ReliabilityMetrics> {
        self.collector.get_metrics_history()
    }
}

impl Default for GlobalMetricsCollector {
    fn default() -> Self {
        Self::new()
    }
}

impl Default for ReliabilityMetrics {
    fn default() -> Self {
        Self {
            timestamp: SystemTime::now(),
            error_metrics: ErrorMetrics::default(),
            fault_tolerance_metrics: FaultToleranceMetrics::default(),
            performance_metrics: PerformanceMetrics::default(),
            resource_metrics: ResourceMetrics::default(),
            health_metrics: HealthMetrics::default(),
            custom_metrics: HashMap::new(),
        }
    }
}

impl Default for ErrorMetrics {
    fn default() -> Self {
        Self {
            total_errors: 0,
            error_rate: 0.0,
            errors_by_type: HashMap::new(),
            errors_by_severity: HashMap::new(),
            average_recovery_time: Duration::ZERO,
            error_trend: Vec::new(),
        }
    }
}

impl Default for FaultToleranceMetrics {
    fn default() -> Self {
        Self {
            circuit_breaker_states: HashMap::new(),
            retry_counts: HashMap::new(),
            timeout_counts: HashMap::new(),
            fallback_counts: HashMap::new(),
            fault_tolerance_success_rate: 0.0,
            average_recovery_time: Duration::ZERO,
        }
    }
}

impl Default for PerformanceMetrics {
    fn default() -> Self {
        Self {
            total_requests: 0,
            successful_requests: 0,
            failed_requests: 0,
            average_response_time: Duration::ZERO,
            max_response_time: Duration::ZERO,
            min_response_time: Duration::MAX,
            throughput: 0.0,
            error_rate: 0.0,
            latency_distribution: HashMap::new(),
        }
    }
}

impl Default for ResourceMetrics {
    fn default() -> Self {
        Self {
            cpu_usage: 0.0,
            memory_usage: 0.0,
            disk_usage: 0.0,
            network_usage: 0.0,
            resource_trend: Vec::new(),
            resource_warnings: 0,
            resource_errors: 0,
        }
    }
}

impl Default for HealthMetrics {
    fn default() -> Self {
        Self {
            overall_health: "unknown".to_string(),
            health_checks: HashMap::new(),
            health_check_count: 0,
            health_check_success_rate: 0.0,
            health_trend: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reliability_metrics_default() {
        let metrics = ReliabilityMetrics::default();
        assert_eq!(metrics.error_metrics.total_errors, 0);
        assert_eq!(metrics.performance_metrics.total_requests, 0);
        assert_eq!(metrics.resource_metrics.cpu_usage, 0.0);
        assert_eq!(metrics.health_metrics.overall_health, "unknown");
    }

    #[test]
    fn test_error_metrics_default() {
        let metrics = ErrorMetrics::default();
        assert_eq!(metrics.total_errors, 0);
        assert_eq!(metrics.error_rate, 0.0);
        assert!(metrics.errors_by_type.is_empty());
        assert!(metrics.errors_by_severity.is_empty());
        assert_eq!(metrics.average_recovery_time, Duration::ZERO);
        assert!(metrics.error_trend.is_empty());
    }

    #[test]
    fn test_fault_tolerance_metrics_default() {
        let metrics = FaultToleranceMetrics::default();
        assert!(metrics.circuit_breaker_states.is_empty());
        assert!(metrics.retry_counts.is_empty());
        assert!(metrics.timeout_counts.is_empty());
        assert!(metrics.fallback_counts.is_empty());
        assert_eq!(metrics.fault_tolerance_success_rate, 0.0);
        assert_eq!(metrics.average_recovery_time, Duration::ZERO);
    }

    #[test]
    fn test_performance_metrics_default() {
        let metrics = PerformanceMetrics::default();
        assert_eq!(metrics.total_requests, 0);
        assert_eq!(metrics.successful_requests, 0);
        assert_eq!(metrics.failed_requests, 0);
        assert_eq!(metrics.average_response_time, Duration::ZERO);
        assert_eq!(metrics.max_response_time, Duration::ZERO);
        assert_eq!(metrics.min_response_time, Duration::MAX);
        assert_eq!(metrics.throughput, 0.0);
        assert_eq!(metrics.error_rate, 0.0);
        assert!(metrics.latency_distribution.is_empty());
    }

    #[test]
    fn test_resource_metrics_default() {
        let metrics = ResourceMetrics::default();
        assert_eq!(metrics.cpu_usage, 0.0);
        assert_eq!(metrics.memory_usage, 0.0);
        assert_eq!(metrics.disk_usage, 0.0);
        assert_eq!(metrics.network_usage, 0.0);
        assert!(metrics.resource_trend.is_empty());
        assert_eq!(metrics.resource_warnings, 0);
        assert_eq!(metrics.resource_errors, 0);
    }

    #[test]
    fn test_health_metrics_default() {
        let metrics = HealthMetrics::default();
        assert_eq!(metrics.overall_health, "unknown");
        assert!(metrics.health_checks.is_empty());
        assert_eq!(metrics.health_check_count, 0);
        assert_eq!(metrics.health_check_success_rate, 0.0);
        assert!(metrics.health_trend.is_empty());
    }

    #[test]
    fn test_metric_value() {
        let int_value = MetricValue::Integer(42);
        assert_eq!(int_value.as_integer(), Some(42));
        assert_eq!(int_value.as_float(), Some(42.0));
        
        let float_value = MetricValue::Float(3.14);
        assert_eq!(float_value.as_float(), Some(3.14));
        
        let string_value = MetricValue::String("test".to_string());
        assert_eq!(string_value.as_string(), Some(&"test".to_string()));
        
        let bool_value = MetricValue::Boolean(true);
        assert_eq!(bool_value.as_boolean(), Some(true));
        
        let duration_value = MetricValue::Duration(Duration::from_secs(5));
        assert_eq!(duration_value.as_duration(), Some(Duration::from_secs(5)));
        
        let timestamp_value = MetricValue::Timestamp(SystemTime::now());
        assert!(timestamp_value.as_timestamp().is_some());
    }

    #[test]
    fn test_metrics_collector_creation() {
        let collector = MetricsCollector::new(Duration::from_secs(60));
        let metrics = collector.get_current_metrics();
        assert_eq!(metrics.error_metrics.total_errors, 0);
    }

    #[test]
    fn test_global_metrics_collector() {
        let global_collector = GlobalMetricsCollector::new();
        let metrics = global_collector.get_current_metrics();
        assert_eq!(metrics.error_metrics.total_errors, 0);
    }

    #[test]
    fn test_custom_metrics() {
        let collector = MetricsCollector::new(Duration::from_secs(60));
        
        collector.set_custom_metric("test_int".to_string(), MetricValue::Integer(42));
        collector.set_custom_metric("test_float".to_string(), MetricValue::Float(3.14));
        collector.set_custom_metric("test_string".to_string(), MetricValue::String("test".to_string()));
        
        assert_eq!(collector.get_custom_metric("test_int").unwrap().as_integer(), Some(42));
        assert_eq!(collector.get_custom_metric("test_float").unwrap().as_float(), Some(3.14));
        assert_eq!(collector.get_custom_metric("test_string").unwrap().as_string(), Some(&"test".to_string()));
        
        let all_metrics = collector.get_all_custom_metrics();
        assert_eq!(all_metrics.len(), 3);
    }
}
