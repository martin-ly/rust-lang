/// 指标聚合系统
///
/// 提供高性能的指标收集、聚合和查询功能

use crate::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Serialize, Deserialize};

/// 指标类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum MetricType {
    /// 计数器 - 只增不减
    Counter,
    /// 仪表盘 - 可增可减
    Gauge,
    /// 直方图 - 分布统计
    Histogram,
    /// 摘要 - 分位数统计
    Summary,
}

/// 聚合的指标数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AggregatedMetric {
    /// 指标名称
    pub name: String,
    /// 指标类型
    pub metric_type: MetricType,
    /// 标签
    pub labels: HashMap<String, String>,
    /// 值
    pub value: f64,
    /// 时间戳
    pub timestamp: i64,
    /// 统计信息（用于直方图和摘要）
    pub stats: Option<MetricStats>,
}

/// 指标统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricStats {
    /// 总数
    pub count: u64,
    /// 总和
    pub sum: f64,
    /// 最小值
    pub min: f64,
    /// 最大值
    pub max: f64,
    /// 平均值
    pub mean: f64,
    /// 标准差
    pub stddev: f64,
    /// 分位数
    pub percentiles: HashMap<String, f64>,
}

/// 时间窗口
#[derive(Debug, Clone, Copy)]
pub enum TimeWindow {
    /// 最近1分钟
    OneMinute,
    /// 最近5分钟
    FiveMinutes,
    /// 最近15分钟
    FifteenMinutes,
    /// 最近1小时
    OneHour,
    /// 最近24小时
    OneDay,
    /// 自定义时间窗口（秒）
    Custom(u64),
}

impl TimeWindow {
    fn as_seconds(&self) -> u64 {
        match self {
            TimeWindow::OneMinute => 60,
            TimeWindow::FiveMinutes => 300,
            TimeWindow::FifteenMinutes => 900,
            TimeWindow::OneHour => 3600,
            TimeWindow::OneDay => 86400,
            TimeWindow::Custom(secs) => *secs,
        }
    }
}

/// 指标数据点
#[derive(Debug, Clone)]
struct MetricDataPoint {
    value: f64,
    timestamp: i64,
    labels: HashMap<String, String>,
}

/// 指标聚合器
pub struct MetricsAggregator {
    /// 存储的指标数据
    metrics: Arc<RwLock<HashMap<String, Vec<MetricDataPoint>>>>,
    /// 指标类型映射
    metric_types: Arc<RwLock<HashMap<String, MetricType>>>,
    /// 最大保留数据点数
    max_data_points: usize,
}

impl MetricsAggregator {
    /// 创建新的指标聚合器
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(RwLock::new(HashMap::new())),
            metric_types: Arc::new(RwLock::new(HashMap::new())),
            max_data_points: 10000,
        }
    }
    
    /// 设置最大数据点数
    pub fn with_max_data_points(mut self, max: usize) -> Self {
        self.max_data_points = max;
        self
    }
    
    /// 记录计数器
    pub async fn record_counter(
        &self,
        name: impl Into<String>,
        value: f64,
        labels: HashMap<String, String>,
    ) -> Result<()> {
        self.record_metric(name, MetricType::Counter, value, labels).await
    }
    
    /// 记录仪表盘
    pub async fn record_gauge(
        &self,
        name: impl Into<String>,
        value: f64,
        labels: HashMap<String, String>,
    ) -> Result<()> {
        self.record_metric(name, MetricType::Gauge, value, labels).await
    }
    
    /// 记录直方图
    pub async fn record_histogram(
        &self,
        name: impl Into<String>,
        value: f64,
        labels: HashMap<String, String>,
    ) -> Result<()> {
        self.record_metric(name, MetricType::Histogram, value, labels).await
    }
    
    /// 记录摘要
    pub async fn record_summary(
        &self,
        name: impl Into<String>,
        value: f64,
        labels: HashMap<String, String>,
    ) -> Result<()> {
        self.record_metric(name, MetricType::Summary, value, labels).await
    }
    
    /// 内部记录指标方法
    async fn record_metric(
        &self,
        name: impl Into<String>,
        metric_type: MetricType,
        value: f64,
        labels: HashMap<String, String>,
    ) -> Result<()> {
        let name = name.into();
        let timestamp = chrono::Utc::now().timestamp();
        
        let data_point = MetricDataPoint {
            value,
            timestamp,
            labels,
        };
        
        // 记录指标类型
        {
            let mut types = self.metric_types.write().await;
            types.insert(name.clone(), metric_type);
        }
        
        // 存储数据点
        {
            let mut metrics = self.metrics.write().await;
            let points = metrics.entry(name).or_insert_with(Vec::new);
            points.push(data_point);
            
            // 限制数据点数量
            if points.len() > self.max_data_points {
                points.drain(0..points.len() - self.max_data_points);
            }
        }
        
        Ok(())
    }
    
    /// 聚合指标（指定时间窗口）
    pub async fn aggregate(
        &self,
        name: &str,
        window: TimeWindow,
    ) -> Result<Option<AggregatedMetric>> {
        let metrics = self.metrics.read().await;
        let types = self.metric_types.read().await;
        
        let metric_type = types.get(name).copied();
        let points = metrics.get(name);
        
        if let (Some(metric_type), Some(points)) = (metric_type, points) {
            let now = chrono::Utc::now().timestamp();
            let window_start = now - window.as_seconds() as i64;
            
            // 过滤时间窗口内的数据点
            let window_points: Vec<_> = points
                .iter()
                .filter(|p| p.timestamp >= window_start)
                .collect();
            
            if window_points.is_empty() {
                return Ok(None);
            }
            
            // 根据类型聚合
            let (value, stats) = match metric_type {
                MetricType::Counter => {
                    // 计数器：求和
                    let sum: f64 = window_points.iter().map(|p| p.value).sum();
                    (sum, None)
                }
                MetricType::Gauge => {
                    // 仪表盘：最新值
                    let last_value = window_points.last().map(|p| p.value).unwrap_or(0.0);
                    (last_value, None)
                }
                MetricType::Histogram | MetricType::Summary => {
                    // 直方图/摘要：计算统计信息
                    let values: Vec<f64> = window_points.iter().map(|p| p.value).collect();
                    let stats = self.calculate_stats(&values);
                    (stats.mean, Some(stats))
                }
            };
            
            // 合并标签（使用最新的标签）
            let labels = window_points
                .last()
                .map(|p| p.labels.clone())
                .unwrap_or_default();
            
            Ok(Some(AggregatedMetric {
                name: name.to_string(),
                metric_type,
                labels,
                value,
                timestamp: now,
                stats,
            }))
        } else {
            Ok(None)
        }
    }
    
    /// 计算统计信息
    fn calculate_stats(&self, values: &[f64]) -> MetricStats {
        if values.is_empty() {
            return MetricStats {
                count: 0,
                sum: 0.0,
                min: 0.0,
                max: 0.0,
                mean: 0.0,
                stddev: 0.0,
                percentiles: HashMap::new(),
            };
        }
        
        let count = values.len() as u64;
        let sum: f64 = values.iter().sum();
        let mean = sum / count as f64;
        
        let min = values.iter().copied().fold(f64::INFINITY, f64::min);
        let max = values.iter().copied().fold(f64::NEG_INFINITY, f64::max);
        
        // 计算标准差
        let variance: f64 = values
            .iter()
            .map(|v| {
                let diff = v - mean;
                diff * diff
            })
            .sum::<f64>()
            / count as f64;
        let stddev = variance.sqrt();
        
        // 计算分位数
        let mut sorted_values = values.to_vec();
        sorted_values.sort_by(|a, b| a.partial_cmp(b).unwrap());
        
        let mut percentiles = HashMap::new();
        for &p in &[50.0, 75.0, 90.0, 95.0, 99.0] {
            let index = ((p / 100.0) * (count - 1) as f64) as usize;
            let value = sorted_values.get(index).copied().unwrap_or(0.0);
            percentiles.insert(format!("p{}", p as u32), value);
        }
        
        MetricStats {
            count,
            sum,
            min,
            max,
            mean,
            stddev,
            percentiles,
        }
    }
    
    /// 列出所有指标名称
    pub async fn list_metrics(&self) -> Vec<String> {
        self.metrics.read().await.keys().cloned().collect()
    }
    
    /// 获取指标类型
    pub async fn get_metric_type(&self, name: &str) -> Option<MetricType> {
        self.metric_types.read().await.get(name).copied()
    }
    
    /// 清空所有指标数据
    pub async fn clear(&self) {
        self.metrics.write().await.clear();
        self.metric_types.write().await.clear();
    }
}

impl Default for MetricsAggregator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_counter() {
        let aggregator = MetricsAggregator::new();
        let labels = HashMap::new();
        
        aggregator.record_counter("requests", 1.0, labels.clone()).await.unwrap();
        aggregator.record_counter("requests", 2.0, labels.clone()).await.unwrap();
        aggregator.record_counter("requests", 3.0, labels).await.unwrap();
        
        let result = aggregator.aggregate("requests", TimeWindow::OneMinute).await.unwrap();
        assert!(result.is_some());
        
        let metric = result.unwrap();
        assert_eq!(metric.value, 6.0); // 1 + 2 + 3
    }
    
    #[tokio::test]
    async fn test_histogram() {
        let aggregator = MetricsAggregator::new();
        let labels = HashMap::new();
        
        for i in 1..=100 {
            aggregator.record_histogram("latency", i as f64, labels.clone()).await.unwrap();
        }
        
        let result = aggregator.aggregate("latency", TimeWindow::OneMinute).await.unwrap();
        assert!(result.is_some());
        
        let metric = result.unwrap();
        assert!(metric.stats.is_some());
        
        let stats = metric.stats.unwrap();
        assert_eq!(stats.count, 100);
        assert_eq!(stats.min, 1.0);
        assert_eq!(stats.max, 100.0);
        assert!(stats.percentiles.contains_key("p50"));
    }
}

