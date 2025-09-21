//! 指标收集器模块
//! 
//! 提供系统指标收集和监控功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use chrono::{DateTime, Utc};
use super::MonitoringError;

/// 指标收集器
#[derive(Clone)]
pub struct MetricsCollector {
    /// 指标注册表
    registry: Arc<RwLock<HashMap<String, Metric>>>,
    /// 指标配置
    config: MetricsConfig,
    /// 收集统计信息
    statistics: Arc<RwLock<CollectionStatistics>>,
}

/// 指标配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricsConfig {
    /// 收集间隔 (秒)
    pub collection_interval: u64,
    /// 指标保留时间 (小时)
    pub retention_hours: u32,
    /// 最大指标数量
    pub max_metrics: usize,
    /// 是否启用自动清理
    pub enable_auto_cleanup: bool,
    /// 是否启用指标聚合
    pub enable_aggregation: bool,
}

impl Default for MetricsConfig {
    fn default() -> Self {
        Self {
            collection_interval: 60,
            retention_hours: 24,
            max_metrics: 10000,
            enable_auto_cleanup: true,
            enable_aggregation: true,
        }
    }
}

/// 指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Metric {
    /// 指标名称
    pub name: String,
    /// 指标类型
    pub metric_type: MetricType,
    /// 指标值
    pub value: MetricValue,
    /// 指标标签
    pub labels: HashMap<String, String>,
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    /// 指标描述
    pub description: Option<String>,
    /// 指标单位
    pub unit: Option<String>,
}

impl Metric {
    /// 创建新的指标
    pub fn new(
        name: String,
        metric_type: MetricType,
        value: MetricValue,
        labels: HashMap<String, String>,
    ) -> Self {
        Self {
            name,
            metric_type,
            value,
            labels,
            timestamp: Utc::now(),
            description: None,
            unit: None,
        }
    }

    /// 设置指标描述
    pub fn with_description(mut self, description: String) -> Self {
        self.description = Some(description);
        self
    }

    /// 设置指标单位
    pub fn with_unit(mut self, unit: String) -> Self {
        self.unit = Some(unit);
        self
    }

    /// 获取指标键值
    pub fn get_key(&self) -> String {
        format!("{}:{}", self.name, self.labels.iter()
            .map(|(k, v)| format!("{}={}", k, v))
            .collect::<Vec<_>>()
            .join(","))
    }

    /// 检查指标是否过期
    pub fn is_expired(&self, retention_hours: u32) -> bool {
        let threshold = Utc::now() - chrono::Duration::hours(retention_hours as i64);
        self.timestamp < threshold
    }
}

/// 指标类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum MetricType {
    /// 计数器
    Counter,
    /// 仪表盘
    Gauge,
    /// 直方图
    Histogram,
    /// 摘要
    Summary,
}

impl MetricType {
    /// 获取类型描述
    pub fn description(&self) -> &'static str {
        match self {
            MetricType::Counter => "计数器",
            MetricType::Gauge => "仪表盘",
            MetricType::Histogram => "直方图",
            MetricType::Summary => "摘要",
        }
    }
}

/// 指标值
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum MetricValue {
    /// 整数值
    Integer(i64),
    /// 浮点值
    Float(f64),
    /// 字符串值
    String(String),
    /// 布尔值
    Boolean(bool),
}

impl MetricValue {
    /// 获取数值
    pub fn as_number(&self) -> Option<f64> {
        match self {
            MetricValue::Integer(i) => Some(*i as f64),
            MetricValue::Float(f) => Some(*f),
            MetricValue::Boolean(b) => Some(if *b { 1.0 } else { 0.0 }),
            MetricValue::String(_) => None,
        }
    }

    /// 获取字符串值
    pub fn as_string(&self) -> String {
        match self {
            MetricValue::Integer(i) => i.to_string(),
            MetricValue::Float(f) => f.to_string(),
            MetricValue::String(s) => s.clone(),
            MetricValue::Boolean(b) => b.to_string(),
        }
    }
}

/// 收集统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CollectionStatistics {
    /// 总指标数
    pub total_metrics: usize,
    /// 各类型指标数量
    pub type_counts: HashMap<String, usize>,
    /// 最后收集时间
    pub last_collection: Option<DateTime<Utc>>,
    /// 收集次数
    pub collection_count: u64,
    /// 错误次数
    pub error_count: u64,
}

impl CollectionStatistics {
    /// 创建新的统计信息
    pub fn new() -> Self {
        Self {
            total_metrics: 0,
            type_counts: HashMap::new(),
            last_collection: None,
            collection_count: 0,
            error_count: 0,
        }
    }

    /// 更新统计信息
    pub fn update(&mut self, metrics: &[Metric]) {
        self.total_metrics = metrics.len();
        self.type_counts.clear();
        
        for metric in metrics {
            let type_name = match metric.metric_type {
                MetricType::Counter => "计数器",
                MetricType::Gauge => "仪表盘",
                MetricType::Histogram => "直方图",
                MetricType::Summary => "摘要",
            };
            *self.type_counts.entry(type_name.to_string()).or_insert(0) += 1;
        }
        
        self.last_collection = Some(Utc::now());
        self.collection_count += 1;
    }
}

impl MetricsCollector {
    /// 创建新的指标收集器
    pub fn new(config: MetricsConfig) -> Self {
        Self {
            registry: Arc::new(RwLock::new(HashMap::new())),
            config,
            statistics: Arc::new(RwLock::new(CollectionStatistics::new())),
        }
    }

    /// 记录指标
    pub async fn record_metric(&self, metric: Metric) -> Result<(), MonitoringError> {
        let mut registry = self.registry.write().await;
        
        // 检查指标数量限制
        if registry.len() >= self.config.max_metrics {
            if self.config.enable_auto_cleanup {
                self.cleanup_expired_metrics_internal(&mut registry).await;
            } else {
                return Err(MonitoringError::MetricsCollectionError(
                    "指标数量已达上限".to_string()
                ));
            }
        }
        
        let key = metric.get_key();
        registry.insert(key, metric);
        
        // 更新统计信息
        let mut stats = self.statistics.write().await;
        stats.update(&registry.values().cloned().collect::<Vec<_>>());
        
        Ok(())
    }

    /// 记录计数器指标
    pub async fn record_counter(
        &self,
        name: String,
        value: i64,
        labels: HashMap<String, String>,
    ) -> Result<(), MonitoringError> {
        let metric = Metric::new(
            name,
            MetricType::Counter,
            MetricValue::Integer(value),
            labels,
        );
        self.record_metric(metric).await
    }

    /// 记录仪表盘指标
    pub async fn record_gauge(
        &self,
        name: String,
        value: f64,
        labels: HashMap<String, String>,
    ) -> Result<(), MonitoringError> {
        let metric = Metric::new(
            name,
            MetricType::Gauge,
            MetricValue::Float(value),
            labels,
        );
        self.record_metric(metric).await
    }

    /// 记录直方图指标
    pub async fn record_histogram(
        &self,
        name: String,
        value: f64,
        labels: HashMap<String, String>,
    ) -> Result<(), MonitoringError> {
        let metric = Metric::new(
            name,
            MetricType::Histogram,
            MetricValue::Float(value),
            labels,
        );
        self.record_metric(metric).await
    }

    /// 获取指标
    pub async fn get_metric(&self, name: &str, labels: &HashMap<String, String>) -> Option<Metric> {
        let registry = self.registry.read().await;
        let key = format!("{}:{}", name, labels.iter()
            .map(|(k, v)| format!("{}={}", k, v))
            .collect::<Vec<_>>()
            .join(","));
        registry.get(&key).cloned()
    }

    /// 获取所有指标
    pub async fn get_all_metrics(&self) -> Vec<Metric> {
        let registry = self.registry.read().await;
        registry.values().cloned().collect()
    }

    /// 获取指定名称的指标
    pub async fn get_metrics_by_name(&self, name: &str) -> Vec<Metric> {
        let registry = self.registry.read().await;
        registry.values()
            .filter(|metric| metric.name == name)
            .cloned()
            .collect()
    }

    /// 获取指定类型的指标
    pub async fn get_metrics_by_type(&self, metric_type: MetricType) -> Vec<Metric> {
        let registry = self.registry.read().await;
        registry.values()
            .filter(|metric| metric.metric_type == metric_type)
            .cloned()
            .collect()
    }

    /// 清理过期指标（内部方法）
    async fn cleanup_expired_metrics_internal(&self, registry: &mut HashMap<String, Metric>) {
        let retention_threshold = Utc::now() - chrono::Duration::hours(self.config.retention_hours as i64);
        
        registry.retain(|_, metric| metric.timestamp > retention_threshold);
    }

    /// 清理过期指标
    pub async fn cleanup_expired_metrics(&self) -> usize {
        let mut registry = self.registry.write().await;
        let initial_count = registry.len();
        self.cleanup_expired_metrics_internal(&mut registry).await;
        initial_count - registry.len()
    }

    /// 获取指标统计信息
    pub async fn get_statistics(&self) -> CollectionStatistics {
        let stats = self.statistics.read().await;
        stats.clone()
    }

    /// 导出指标为Prometheus格式
    pub async fn export_prometheus_format(&self) -> String {
        let registry = self.registry.read().await;
        let mut output = String::new();
        
        for metric in registry.values() {
            let metric_type = match metric.metric_type {
                MetricType::Counter => "# TYPE {} counter",
                MetricType::Gauge => "# TYPE {} gauge",
                MetricType::Histogram => "# TYPE {} histogram",
                MetricType::Summary => "# TYPE {} summary",
            };
            
            output.push_str(&format!("{}\n", metric_type.replace("{}", &metric.name)));
            
            let labels_str = if metric.labels.is_empty() {
                String::new()
            } else {
                format!("{{{}}}", metric.labels.iter()
                    .map(|(k, v)| format!("{}=\"{}\"", k, v))
                    .collect::<Vec<_>>()
                    .join(","))
            };
            
            let value = metric.value.as_number().unwrap_or(0.0);
            output.push_str(&format!("{}{} {}\n", metric.name, labels_str, value));
        }
        
        output
    }

    /// 导出指标为JSON格式
    pub async fn export_json_format(&self) -> Result<String, MonitoringError> {
        let registry = self.registry.read().await;
        let metrics: Vec<&Metric> = registry.values().collect();
        
        serde_json::to_string_pretty(&metrics)
            .map_err(|e| MonitoringError::MetricsCollectionError(
                format!("JSON序列化失败: {}", e)
            ))
    }

    /// 收集系统指标
    pub async fn collect_system_metrics(&self) -> Result<Vec<Metric>, MonitoringError> {
        let mut metrics = Vec::new();
        
        // 模拟收集系统指标
        metrics.push(Metric {
            name: "cpu_usage".to_string(),
            value: MetricValue::Float(0.5),
            metric_type: MetricType::Gauge,
            timestamp: Utc::now(),
            labels: HashMap::new(),
            unit: Some("percent".to_string()),
            description: Some("CPU使用率".to_string()),
        });
        
        metrics.push(Metric {
            name: "memory_usage".to_string(),
            value: MetricValue::Float(0.7),
            metric_type: MetricType::Gauge,
            timestamp: Utc::now(),
            labels: HashMap::new(),
            unit: Some("percent".to_string()),
            description: Some("内存使用率".to_string()),
        });
        
        Ok(metrics)
    }

    /// 收集应用指标
    pub async fn collect_application_metrics(&self) -> Result<Vec<Metric>, MonitoringError> {
        let mut metrics = Vec::new();
        
        // 模拟收集应用指标
        metrics.push(Metric {
            name: "request_count".to_string(),
            value: MetricValue::Float(100.0),
            metric_type: MetricType::Counter,
            timestamp: Utc::now(),
            labels: HashMap::new(),
            unit: Some("requests".to_string()),
            description: Some("请求总数".to_string()),
        });
        
        Ok(metrics)
    }

    /// 启动指标收集
    pub async fn start_collection(&self) -> Result<(), MonitoringError> {
        let registry = Arc::clone(&self.registry);
        let config = self.config.clone();
        let statistics = Arc::clone(&self.statistics);
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(
                tokio::time::Duration::from_secs(config.collection_interval)
            );
            
            loop {
                interval.tick().await;
                
                // 清理过期指标
                if config.enable_auto_cleanup {
                    let mut registry_guard = registry.write().await;
                    let retention_threshold = Utc::now() - chrono::Duration::hours(config.retention_hours as i64);
                    registry_guard.retain(|_, metric| metric.timestamp > retention_threshold);
                }
                
                // 更新统计信息
                let mut stats_guard = statistics.write().await;
                stats_guard.last_collection = Some(Utc::now());
                stats_guard.collection_count += 1;
            }
        });
        
        Ok(())
    }
}

/// 系统指标收集器
pub struct SystemMetricsCollector {
    /// 基础指标收集器
    collector: MetricsCollector,
}

impl SystemMetricsCollector {
    /// 创建新的系统指标收集器
    pub fn new(config: MetricsConfig) -> Self {
        Self {
            collector: MetricsCollector::new(config),
        }
    }

    /// 收集CPU使用率
    pub async fn collect_cpu_usage(&self) -> Result<(), MonitoringError> {
        let cpu_usage = self.get_cpu_usage().await;
        let mut labels = HashMap::new();
        labels.insert("metric".to_string(), "cpu_usage".to_string());
        
        self.collector.record_gauge(
            "system_cpu_usage".to_string(),
            cpu_usage,
            labels,
        ).await
    }

    /// 收集内存使用率
    pub async fn collect_memory_usage(&self) -> Result<(), MonitoringError> {
        let memory_usage = self.get_memory_usage().await;
        let mut labels = HashMap::new();
        labels.insert("metric".to_string(), "memory_usage".to_string());
        
        self.collector.record_gauge(
            "system_memory_usage".to_string(),
            memory_usage,
            labels,
        ).await
    }

    /// 收集磁盘使用率
    pub async fn collect_disk_usage(&self) -> Result<(), MonitoringError> {
        let disk_usage = self.get_disk_usage().await;
        let mut labels = HashMap::new();
        labels.insert("metric".to_string(), "disk_usage".to_string());
        
        self.collector.record_gauge(
            "system_disk_usage".to_string(),
            disk_usage,
            labels,
        ).await
    }

    /// 获取CPU使用率
    async fn get_cpu_usage(&self) -> f64 {
        // 简化实现，实际应该使用系统API
        use std::time::{SystemTime, UNIX_EPOCH};
        let timestamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
        (timestamp % 100) as f64
    }

    /// 获取内存使用率
    async fn get_memory_usage(&self) -> f64 {
        // 简化实现，实际应该使用系统API
        use std::time::{SystemTime, UNIX_EPOCH};
        let timestamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
        ((timestamp + 10) % 100) as f64
    }

    /// 获取磁盘使用率
    async fn get_disk_usage(&self) -> f64 {
        // 简化实现，实际应该使用系统API
        use std::time::{SystemTime, UNIX_EPOCH};
        let timestamp = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs();
        ((timestamp + 20) % 100) as f64
    }

    /// 获取基础收集器
    pub fn get_collector(&self) -> &MetricsCollector {
        &self.collector
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_metrics_collector_creation() {
        let config = MetricsConfig::default();
        let collector = MetricsCollector::new(config);
        
        let stats = collector.get_statistics().await;
        assert_eq!(stats.total_metrics, 0);
    }

    #[tokio::test]
    async fn test_record_metric() {
        let config = MetricsConfig::default();
        let collector = MetricsCollector::new(config);
        
        let mut labels = HashMap::new();
        labels.insert("device_id".to_string(), "device_001".to_string());
        
        let metric = Metric::new(
            "temperature".to_string(),
            MetricType::Gauge,
            MetricValue::Float(25.5),
            labels,
        );
        
        assert!(collector.record_metric(metric).await.is_ok());
        
        let stats = collector.get_statistics().await;
        assert_eq!(stats.total_metrics, 1);
    }

    #[tokio::test]
    async fn test_record_counter() {
        let config = MetricsConfig::default();
        let collector = MetricsCollector::new(config);
        
        let mut labels = HashMap::new();
        labels.insert("device_id".to_string(), "device_001".to_string());
        
        assert!(collector.record_counter(
            "request_count".to_string(),
            100,
            labels,
        ).await.is_ok());
        
        let stats = collector.get_statistics().await;
        assert_eq!(stats.total_metrics, 1);
    }

    #[tokio::test]
    async fn test_record_gauge() {
        let config = MetricsConfig::default();
        let collector = MetricsCollector::new(config);
        
        let mut labels = HashMap::new();
        labels.insert("device_id".to_string(), "device_001".to_string());
        
        assert!(collector.record_gauge(
            "temperature".to_string(),
            25.5,
            labels,
        ).await.is_ok());
        
        let stats = collector.get_statistics().await;
        assert_eq!(stats.total_metrics, 1);
    }

    #[tokio::test]
    async fn test_export_prometheus_format() {
        let config = MetricsConfig::default();
        let collector = MetricsCollector::new(config);
        
        let mut labels = HashMap::new();
        labels.insert("device_id".to_string(), "device_001".to_string());
        
        collector.record_gauge(
            "temperature".to_string(),
            25.5,
            labels,
        ).await.unwrap();
        
        let prometheus_output = collector.export_prometheus_format().await;
        assert!(prometheus_output.contains("temperature"));
        assert!(prometheus_output.contains("25.5"));
    }

    #[tokio::test]
    async fn test_system_metrics_collector() {
        let config = MetricsConfig::default();
        let collector = SystemMetricsCollector::new(config);
        
        assert!(collector.collect_cpu_usage().await.is_ok());
        assert!(collector.collect_memory_usage().await.is_ok());
        assert!(collector.collect_disk_usage().await.is_ok());
        
        let stats = collector.get_collector().get_statistics().await;
        assert_eq!(stats.total_metrics, 3);
    }
}
