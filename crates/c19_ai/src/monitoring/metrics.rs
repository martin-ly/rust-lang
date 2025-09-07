//! 监控指标
//! 
//! 提供 AI 系统的监控和指标收集功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::{Duration, Instant};

/// 指标类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MetricType {
    /// 计数器
    Counter,
    /// 直方图
    Histogram,
    /// 仪表盘
    Gauge,
    /// 计时器
    Timer,
}

/// 监控指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Metric {
    pub name: String,
    pub metric_type: MetricType,
    pub value: f64,
    pub labels: HashMap<String, String>,
    pub timestamp: u64,
}

/// 指标收集器
pub struct MetricsCollector {
    metrics: HashMap<String, Metric>,
    start_time: Instant,
}

impl MetricsCollector {
    /// 创建新的指标收集器
    pub fn new() -> Self {
        Self {
            metrics: HashMap::new(),
            start_time: Instant::now(),
        }
    }
    
    /// 记录指标
    pub fn record(&mut self, name: String, value: f64, labels: HashMap<String, String>) {
        let metric = Metric {
            name: name.clone(),
            metric_type: MetricType::Gauge,
            value,
            labels,
            timestamp: self.start_time.elapsed().as_secs(),
        };
        self.metrics.insert(name, metric);
    }
    
    /// 获取指标
    pub fn get_metric(&self, name: &str) -> Option<&Metric> {
        self.metrics.get(name)
    }
    
    /// 获取所有指标
    pub fn get_all_metrics(&self) -> &HashMap<String, Metric> {
        &self.metrics
    }
}

impl Default for MetricsCollector {
    fn default() -> Self {
        Self::new()
    }
}
