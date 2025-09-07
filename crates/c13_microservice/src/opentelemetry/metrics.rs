//! 指标收集模块

use std::collections::HashMap;
use std::sync::{Arc, RwLock};
use std::time::{SystemTime, UNIX_EPOCH, Duration};
use tracing::info;
use serde::{Serialize, Deserialize};
use anyhow::Result;

/// 带标签的指标值
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LabeledMetric {
    pub name: String,
    pub labels: HashMap<String, String>,
    pub value: MetricValue,
    pub timestamp: u64,
}

/// 指标值类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MetricValue {
    Counter(u64),
    Gauge(f64),
    Histogram(Vec<f64>),
    Timer(Vec<Duration>),
}

/// 指标收集器（增强版本）
pub struct MetricsCollector {
    counters: Arc<RwLock<HashMap<String, u64>>>,
    gauges: Arc<RwLock<HashMap<String, f64>>>,
    histograms: Arc<RwLock<HashMap<String, Vec<f64>>>>,
    timers: Arc<RwLock<HashMap<String, Vec<Duration>>>>,
    labels: Arc<RwLock<HashMap<String, HashMap<String, String>>>>,
    labeled_metrics: Arc<RwLock<Vec<LabeledMetric>>>,
    metric_buffer: Arc<RwLock<Vec<LabeledMetric>>>,
    buffer_size: usize,
    flush_interval: Duration,
    exporter: Option<Arc<dyn MetricExporter + Send + Sync>>,
}

/// 指标导出器trait
pub trait MetricExporter {
    fn export(&self, metrics: &[LabeledMetric]) -> Result<()>;
    fn get_name(&self) -> &str;
}

/// Prometheus格式导出器
#[derive(Debug)]
pub struct PrometheusExporter {
    name: String,
}

impl PrometheusExporter {
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

impl MetricExporter for PrometheusExporter {
    fn export(&self, metrics: &[LabeledMetric]) -> Result<()> {
        let mut output = String::new();
        
        for metric in metrics {
            match &metric.value {
                MetricValue::Counter(value) => {
                    output.push_str(&format!("# HELP {}_total Total count of {}\n", metric.name, metric.name));
                    output.push_str(&format!("# TYPE {}_total counter\n", metric.name));
                    
                    if metric.labels.is_empty() {
                        output.push_str(&format!("{}_total {}\n", metric.name, value));
                    } else {
                        let labels_str = metric.labels.iter()
                            .map(|(k, v)| format!("{}=\"{}\"", k, v))
                            .collect::<Vec<_>>()
                            .join(",");
                        output.push_str(&format!("{}_total{{{}}} {}\n", metric.name, labels_str, value));
                    }
                },
                MetricValue::Gauge(value) => {
                    output.push_str(&format!("# HELP {} Current value of {}\n", metric.name, metric.name));
                    output.push_str(&format!("# TYPE {} gauge\n", metric.name));
                    
                    if metric.labels.is_empty() {
                        output.push_str(&format!("{} {}\n", metric.name, value));
                    } else {
                        let labels_str = metric.labels.iter()
                            .map(|(k, v)| format!("{}=\"{}\"", k, v))
                            .collect::<Vec<_>>()
                            .join(",");
                        output.push_str(&format!("{}{{{}}} {}\n", metric.name, labels_str, value));
                    }
                },
                MetricValue::Histogram(values) => {
                    if !values.is_empty() {
                        let stats = calculate_histogram_stats(values);
                        output.push_str(&format!("# HELP {}_count Total count of {}\n", metric.name, metric.name));
                        output.push_str(&format!("# TYPE {}_count counter\n", metric.name));
                        output.push_str(&format!("{}_count {}\n", metric.name, values.len()));
                        
                        output.push_str(&format!("# HELP {}_sum Total sum of {}\n", metric.name, metric.name));
                        output.push_str(&format!("# TYPE {}_sum counter\n", metric.name));
                        output.push_str(&format!("{}_sum {}\n", metric.name, stats.sum));
                        
                        output.push_str(&format!("# HELP {}_bucket Histogram buckets for {}\n", metric.name, metric.name));
                        output.push_str(&format!("# TYPE {}_bucket histogram\n", metric.name));
                        
                        // 添加分位数
                        for (quantile, value) in [("0.5", stats.median), ("0.95", stats.p95), ("0.99", stats.p99)] {
                            output.push_str(&format!("{}{{quantile=\"{}\"}} {}\n", metric.name, quantile, value));
                        }
                    }
                },
                MetricValue::Timer(durations) => {
                    if !durations.is_empty() {
                        let stats = calculate_timer_stats(durations);
                        output.push_str(&format!("# HELP {}_duration_seconds Timer duration for {}\n", metric.name, metric.name));
                        output.push_str(&format!("# TYPE {}_duration_seconds histogram\n", metric.name));
                        
                        output.push_str(&format!("{}_duration_seconds_count {}\n", metric.name, durations.len()));
                        output.push_str(&format!("{}_duration_seconds_sum {}\n", metric.name, stats.total.as_secs_f64()));
                        
                        // 添加分位数
                        for (quantile, duration) in [("0.5", stats.median), ("0.95", Duration::from_millis((stats.median.as_millis() as f64 * 1.9) as u64)), ("0.99", Duration::from_millis((stats.median.as_millis() as f64 * 1.99) as u64))] {
                            output.push_str(&format!("{}_duration_seconds{{quantile=\"{}\"}} {}\n", metric.name, quantile, duration.as_secs_f64()));
                        }
                    }
                },
            }
        }
        
        info!("Exported {} metrics in Prometheus format", metrics.len());
        println!("{}", output);
        Ok(())
    }
    
    fn get_name(&self) -> &str {
        &self.name
    }
}

/// 计算直方图统计信息
fn calculate_histogram_stats(values: &[f64]) -> HistogramStats {
    if values.is_empty() {
        return HistogramStats::default();
    }
    
    let mut sorted_values = values.to_vec();
    sorted_values.sort_by(|a, b| a.partial_cmp(b).unwrap());
    
    let count = values.len();
    let sum: f64 = values.iter().sum();
    let mean = sum / count as f64;
    let min = sorted_values[0];
    let max = sorted_values[count - 1];
    
    let median = if count % 2 == 0 {
        (sorted_values[count / 2 - 1] + sorted_values[count / 2]) / 2.0
    } else {
        sorted_values[count / 2]
    };
    
    let p95_idx = (count as f64 * 0.95) as usize;
    let p99_idx = (count as f64 * 0.99) as usize;
    let p95 = sorted_values[p95_idx.min(count - 1)];
    let p99 = sorted_values[p99_idx.min(count - 1)];
    
    HistogramStats {
        count,
        sum,
        mean,
        min,
        max,
        median,
        p95,
        p99,
    }
}

/// 计算计时器统计信息
fn calculate_timer_stats(durations: &[Duration]) -> TimerStats {
    if durations.is_empty() {
        return TimerStats::default();
    }
    
    let mut sorted_durations = durations.to_vec();
    sorted_durations.sort();
    
    let count = durations.len();
    let total: Duration = durations.iter().sum();
    let mean = total / count as u32;
    let min = sorted_durations[0];
    let max = sorted_durations[count - 1];
    
    let median = if count % 2 == 0 {
        (sorted_durations[count / 2 - 1] + sorted_durations[count / 2]) / 2
    } else {
        sorted_durations[count / 2]
    };
    
    TimerStats {
        count,
        total,
        mean,
        min,
        max,
        median,
    }
}

impl MetricsCollector {
    pub fn new() -> Self {
        Self {
            counters: Arc::new(RwLock::new(HashMap::new())),
            gauges: Arc::new(RwLock::new(HashMap::new())),
            histograms: Arc::new(RwLock::new(HashMap::new())),
            timers: Arc::new(RwLock::new(HashMap::new())),
            labels: Arc::new(RwLock::new(HashMap::new())),
            labeled_metrics: Arc::new(RwLock::new(Vec::new())),
            metric_buffer: Arc::new(RwLock::new(Vec::new())),
            buffer_size: 1000,
            flush_interval: Duration::from_secs(30),
            exporter: None,
        }
    }
    
    /// 设置指标导出器
    pub fn set_exporter(&mut self, exporter: Arc<dyn MetricExporter + Send + Sync>) {
        self.exporter = Some(exporter);
    }
    
    /// 设置缓冲区大小
    pub fn set_buffer_size(&mut self, size: usize) {
        self.buffer_size = size;
    }
    
    /// 设置刷新间隔
    pub fn set_flush_interval(&mut self, interval: Duration) {
        self.flush_interval = interval;
    }
    
    /// 记录带标签的计数器
    pub fn increment_labeled_counter(&self, name: &str, labels: HashMap<String, String>, value: u64) {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let labeled_metric = LabeledMetric {
            name: name.to_string(),
            labels,
            value: MetricValue::Counter(value),
            timestamp,
        };
        
        // 添加到缓冲区
        if let Ok(mut buffer) = self.metric_buffer.write() {
            buffer.push(labeled_metric.clone());
            
            if buffer.len() >= self.buffer_size {
                drop(buffer);
                if let Err(e) = self.flush_buffer() {
                    eprintln!("Failed to flush metric buffer: {}", e);
                }
            }
        }
        
        // 添加到历史记录
        if let Ok(mut labeled_metrics) = self.labeled_metrics.write() {
            labeled_metrics.push(labeled_metric);
        }
        
        info!("Labeled counter '{}' incremented by {}", name, value);
    }
    
    /// 记录带标签的仪表
    pub fn set_labeled_gauge(&self, name: &str, labels: HashMap<String, String>, value: f64) {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let labeled_metric = LabeledMetric {
            name: name.to_string(),
            labels,
            value: MetricValue::Gauge(value),
            timestamp,
        };
        
        // 添加到缓冲区
        if let Ok(mut buffer) = self.metric_buffer.write() {
            buffer.push(labeled_metric.clone());
            
            if buffer.len() >= self.buffer_size {
                drop(buffer);
                if let Err(e) = self.flush_buffer() {
                    eprintln!("Failed to flush metric buffer: {}", e);
                }
            }
        }
        
        // 添加到历史记录
        if let Ok(mut labeled_metrics) = self.labeled_metrics.write() {
            labeled_metrics.push(labeled_metric);
        }
        
        info!("Labeled gauge '{}' set to {}", name, value);
    }
    
    /// 记录带标签的直方图
    pub fn record_labeled_histogram(&self, name: &str, labels: HashMap<String, String>, value: f64) {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let labeled_metric = LabeledMetric {
            name: name.to_string(),
            labels,
            value: MetricValue::Histogram(vec![value]),
            timestamp,
        };
        
        // 添加到缓冲区
        if let Ok(mut buffer) = self.metric_buffer.write() {
            buffer.push(labeled_metric.clone());
            
            if buffer.len() >= self.buffer_size {
                drop(buffer);
                if let Err(e) = self.flush_buffer() {
                    eprintln!("Failed to flush metric buffer: {}", e);
                }
            }
        }
        
        // 添加到历史记录
        if let Ok(mut labeled_metrics) = self.labeled_metrics.write() {
            labeled_metrics.push(labeled_metric);
        }
        
        info!("Labeled histogram '{}' recorded value {}", name, value);
    }
    
    /// 记录带标签的计时器
    pub fn record_labeled_timer(&self, name: &str, labels: HashMap<String, String>, duration: Duration) {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let labeled_metric = LabeledMetric {
            name: name.to_string(),
            labels,
            value: MetricValue::Timer(vec![duration]),
            timestamp,
        };
        
        // 添加到缓冲区
        if let Ok(mut buffer) = self.metric_buffer.write() {
            buffer.push(labeled_metric.clone());
            
            if buffer.len() >= self.buffer_size {
                drop(buffer);
                if let Err(e) = self.flush_buffer() {
                    eprintln!("Failed to flush metric buffer: {}", e);
                }
            }
        }
        
        // 添加到历史记录
        if let Ok(mut labeled_metrics) = self.labeled_metrics.write() {
            labeled_metrics.push(labeled_metric);
        }
        
        info!("Labeled timer '{}' recorded duration {:?}", name, duration);
    }
    
    /// 刷新指标缓冲区
    pub fn flush_buffer(&self) -> Result<()> {
        if let Some(exporter) = &self.exporter {
            if let Ok(mut buffer) = self.metric_buffer.write() {
                if !buffer.is_empty() {
                    exporter.export(&buffer)?;
                    buffer.clear();
                }
            }
        }
        Ok(())
    }
    
    /// 获取带标签的指标
    pub fn get_labeled_metrics(&self, name: &str) -> Vec<LabeledMetric> {
        if let Ok(labeled_metrics) = self.labeled_metrics.read() {
            labeled_metrics.iter()
                .filter(|metric| metric.name == name)
                .cloned()
                .collect()
        } else {
            Vec::new()
        }
    }
    
    /// 获取指定时间范围内的指标
    pub fn get_metrics_by_time_range(&self, start_time: u64, end_time: u64) -> Vec<LabeledMetric> {
        if let Ok(labeled_metrics) = self.labeled_metrics.read() {
            labeled_metrics.iter()
                .filter(|metric| metric.timestamp >= start_time && metric.timestamp <= end_time)
                .cloned()
                .collect()
        } else {
            Vec::new()
        }
    }
    
    /// 获取缓冲区大小
    pub fn get_buffer_size(&self) -> usize {
        if let Ok(buffer) = self.metric_buffer.read() {
            buffer.len()
        } else {
            0
        }
    }
    
    /// 清理旧的指标数据
    pub fn cleanup_old_metrics(&self, cutoff_time: u64) -> usize {
        if let Ok(mut labeled_metrics) = self.labeled_metrics.write() {
            let initial_count = labeled_metrics.len();
            labeled_metrics.retain(|metric| metric.timestamp >= cutoff_time);
            initial_count - labeled_metrics.len()
        } else {
            0
        }
    }
    
    /// 增加计数器
    pub fn increment_counter(&self, name: &str, value: u64) {
        if let Ok(mut counters) = self.counters.write() {
            *counters.entry(name.to_string()).or_insert(0) += value;
            info!("Counter '{}' incremented by {}", name, value);
        }
    }
    
    /// 设置仪表值
    pub fn set_gauge(&self, name: &str, value: f64) {
        if let Ok(mut gauges) = self.gauges.write() {
            gauges.insert(name.to_string(), value);
            info!("Gauge '{}' set to {}", name, value);
        }
    }
    
    /// 记录直方图值
    pub fn record_histogram(&self, name: &str, value: f64) {
        if let Ok(mut histograms) = self.histograms.write() {
            histograms.entry(name.to_string()).or_insert_with(Vec::new).push(value);
            info!("Histogram '{}' recorded value {}", name, value);
        }
    }
    
    /// 记录计时器值
    pub fn record_timer(&self, name: &str, duration: Duration) {
        if let Ok(mut timers) = self.timers.write() {
            timers.entry(name.to_string()).or_insert_with(Vec::new).push(duration);
            info!("Timer '{}' recorded duration {:?}", name, duration);
        }
    }
    
    /// 设置指标标签
    pub fn set_labels(&self, name: &str, labels: HashMap<String, String>) {
        if let Ok(mut label_map) = self.labels.write() {
            label_map.insert(name.to_string(), labels);
        }
    }
    
    /// 获取计数器值
    pub fn get_counter(&self, name: &str) -> Option<u64> {
        if let Ok(counters) = self.counters.read() {
            counters.get(name).copied()
        } else {
            None
        }
    }
    
    /// 获取仪表值
    pub fn get_gauge(&self, name: &str) -> Option<f64> {
        if let Ok(gauges) = self.gauges.read() {
            gauges.get(name).copied()
        } else {
            None
        }
    }
    
    /// 获取直方图统计
    pub fn get_histogram_stats(&self, name: &str) -> Option<HistogramStats> {
        if let Ok(histograms) = self.histograms.read() {
            histograms.get(name).map(|values| {
                if values.is_empty() {
                    return HistogramStats::default();
                }
                
                let mut sorted_values = values.clone();
                sorted_values.sort_by(|a, b| a.partial_cmp(b).unwrap());
                
                let count = values.len();
                let sum: f64 = values.iter().sum();
                let mean = sum / count as f64;
                let min = sorted_values[0];
                let max = sorted_values[count - 1];
                
                // 计算中位数
                let median = if count % 2 == 0 {
                    (sorted_values[count / 2 - 1] + sorted_values[count / 2]) / 2.0
                } else {
                    sorted_values[count / 2]
                };
                
                // 计算P95和P99
                let p95_idx = (count as f64 * 0.95) as usize;
                let p99_idx = (count as f64 * 0.99) as usize;
                let p95 = sorted_values[p95_idx.min(count - 1)];
                let p99 = sorted_values[p99_idx.min(count - 1)];
                
                HistogramStats {
                    count,
                    sum,
                    mean,
                    min,
                    max,
                    median,
                    p95,
                    p99,
                }
            })
        } else {
            None
        }
    }
    
    /// 获取计时器统计
    pub fn get_timer_stats(&self, name: &str) -> Option<TimerStats> {
        if let Ok(timers) = self.timers.read() {
            timers.get(name).map(|durations| {
                if durations.is_empty() {
                    return TimerStats::default();
                }
                
                let mut sorted_durations = durations.clone();
                sorted_durations.sort();
                
                let count = durations.len();
                let total: Duration = durations.iter().sum();
                let mean = total / count as u32;
                let min = sorted_durations[0];
                let max = sorted_durations[count - 1];
                
                // 计算中位数
                let median = if count % 2 == 0 {
                    (sorted_durations[count / 2 - 1] + sorted_durations[count / 2]) / 2
                } else {
                    sorted_durations[count / 2]
                };
                
                TimerStats {
                    count,
                    total,
                    mean,
                    min,
                    max,
                    median,
                }
            })
        } else {
            None
        }
    }
    
    /// 获取所有计数器
    pub fn get_all_counters(&self) -> HashMap<String, u64> {
        if let Ok(counters) = self.counters.read() {
            counters.clone()
        } else {
            HashMap::new()
        }
    }
    
    /// 获取所有仪表
    pub fn get_all_gauges(&self) -> HashMap<String, f64> {
        if let Ok(gauges) = self.gauges.read() {
            gauges.clone()
        } else {
            HashMap::new()
        }
    }
    
    /// 获取所有直方图名称
    pub fn get_histogram_names(&self) -> Vec<String> {
        if let Ok(histograms) = self.histograms.read() {
            histograms.keys().cloned().collect()
        } else {
            Vec::new()
        }
    }
    
    /// 获取所有计时器名称
    pub fn get_timer_names(&self) -> Vec<String> {
        if let Ok(timers) = self.timers.read() {
            timers.keys().cloned().collect()
        } else {
            Vec::new()
        }
    }
    
    /// 重置所有指标
    pub fn reset(&self) {
        if let Ok(mut counters) = self.counters.write() {
            counters.clear();
        }
        if let Ok(mut gauges) = self.gauges.write() {
            gauges.clear();
        }
        if let Ok(mut histograms) = self.histograms.write() {
            histograms.clear();
        }
        if let Ok(mut timers) = self.timers.write() {
            timers.clear();
        }
        if let Ok(mut labels) = self.labels.write() {
            labels.clear();
        }
        
        info!("All metrics have been reset");
    }
    
    /// 导出所有指标为JSON格式
    pub fn export_metrics(&self) -> Result<String, Box<dyn std::error::Error>> {
        use serde_json::Value;
        let mut metrics_data = serde_json::Map::new();
        
        if let Ok(counters) = self.counters.read() {
            let counters_json: Value = serde_json::to_value(counters.clone())?;
            metrics_data.insert("counters".to_string(), counters_json);
        }
        if let Ok(gauges) = self.gauges.read() {
            let gauges_json: Value = serde_json::to_value(gauges.clone())?;
            metrics_data.insert("gauges".to_string(), gauges_json);
        }
        if let Ok(histograms) = self.histograms.read() {
            let histograms_json: Value = serde_json::to_value(histograms.clone())?;
            metrics_data.insert("histograms".to_string(), histograms_json);
        }
        if let Ok(timers) = self.timers.read() {
            let timer_data: HashMap<String, Vec<u64>> = timers.iter()
                .map(|(k, v)| (k.clone(), v.iter().map(|d| d.as_millis() as u64).collect()))
                .collect();
            let timers_json: Value = serde_json::to_value(timer_data)?;
            metrics_data.insert("timers".to_string(), timers_json);
        }
        
        Ok(serde_json::to_string_pretty(&metrics_data)?)
    }
}

/// 直方图统计信息
#[derive(Debug, Clone, Default)]
pub struct HistogramStats {
    pub count: usize,
    pub sum: f64,
    pub mean: f64,
    pub min: f64,
    pub max: f64,
    pub median: f64,
    pub p95: f64,
    pub p99: f64,
}

/// 计时器统计信息
#[derive(Debug, Clone, Default)]
pub struct TimerStats {
    pub count: usize,
    pub total: Duration,
    pub mean: Duration,
    pub min: Duration,
    pub max: Duration,
    pub median: Duration,
}

impl HistogramStats {
    /// 获取统计信息的字符串表示
    pub fn to_string(&self) -> String {
        format!(
            "count={}, sum={:.2}, mean={:.2}, min={:.2}, max={:.2}, median={:.2}, p95={:.2}, p99={:.2}",
            self.count, self.sum, self.mean, self.min, self.max, self.median, self.p95, self.p99
        )
    }
}

impl TimerStats {
    /// 获取统计信息的字符串表示
    pub fn to_string(&self) -> String {
        format!(
            "count={}, total={:?}, mean={:?}, min={:?}, max={:?}, median={:?}",
            self.count, self.total, self.mean, self.min, self.max, self.median
        )
    }
}

/// 预定义的指标名称
pub mod metric_names {
    pub const HTTP_REQUESTS_TOTAL: &str = "http_requests_total";
    pub const HTTP_REQUEST_DURATION: &str = "http_request_duration_seconds";
    pub const HTTP_REQUEST_SIZE: &str = "http_request_size_bytes";
    pub const HTTP_RESPONSE_SIZE: &str = "http_response_size_bytes";
    pub const ACTIVE_CONNECTIONS: &str = "active_connections";
    pub const CPU_USAGE: &str = "cpu_usage_percent";
    pub const MEMORY_USAGE: &str = "memory_usage_bytes";
    pub const DATABASE_QUERIES_TOTAL: &str = "database_queries_total";
    pub const DATABASE_QUERY_DURATION: &str = "database_query_duration_seconds";
    pub const CACHE_HITS_TOTAL: &str = "cache_hits_total";
    pub const CACHE_MISSES_TOTAL: &str = "cache_misses_total";
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_metrics_collector() {
        let metrics = MetricsCollector::new();
        
        metrics.increment_counter("requests", 1);
        metrics.set_gauge("cpu_usage", 75.5);
        metrics.record_histogram("response_time", 0.1);
        
        assert_eq!(metrics.get_counter("requests"), Some(1));
        assert_eq!(metrics.get_gauge("cpu_usage"), Some(75.5));
        
        let stats = metrics.get_histogram_stats("response_time");
        assert!(stats.is_some());
        let stats = stats.unwrap();
        assert_eq!(stats.count, 1);
        assert_eq!(stats.sum, 0.1);
    }
    
    #[test]
    fn test_histogram_stats() {
        let metrics = MetricsCollector::new();
        
        // 添加多个值
        metrics.record_histogram("test_histogram", 1.0);
        metrics.record_histogram("test_histogram", 2.0);
        metrics.record_histogram("test_histogram", 3.0);
        metrics.record_histogram("test_histogram", 4.0);
        metrics.record_histogram("test_histogram", 5.0);
        
        let stats = metrics.get_histogram_stats("test_histogram").unwrap();
        assert_eq!(stats.count, 5);
        assert_eq!(stats.sum, 15.0);
        assert_eq!(stats.mean, 3.0);
        assert_eq!(stats.min, 1.0);
        assert_eq!(stats.max, 5.0);
        assert_eq!(stats.median, 3.0);
    }
    
    #[test]
    fn test_metric_names() {
        assert_eq!(metric_names::HTTP_REQUESTS_TOTAL, "http_requests_total");
        assert_eq!(metric_names::CPU_USAGE, "cpu_usage_percent");
    }
}
