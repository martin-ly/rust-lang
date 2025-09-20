//! # OTLP处理器模块
//! 
//! 实现OTLP数据的处理逻辑，包括批处理、过滤、聚合等功能，
//! 利用Rust 1.90的异步特性实现高性能数据处理。

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{mpsc, RwLock};
use tokio::time::{
    interval, 
    //sleep,
};
//use futures::stream::{StreamExt, FuturesUnordered};
//use futures::FutureExt;
use crate::data::{
    TelemetryData,
    //TelemetryDataType,
};
use crate::error::{Result,
     ProcessingError, 
     //OtlpError,
};
use crate::utils::{
    //BatchUtils, 
    TimeUtils, 
    PerformanceUtils,
};

/// 处理配置
#[derive(Debug, Clone)]
pub struct ProcessingConfig {
    /// 批处理大小
    pub batch_size: usize,
    /// 批处理超时
    pub batch_timeout: Duration,
    /// 最大队列大小
    pub max_queue_size: usize,
    /// 是否启用过滤
    pub enable_filtering: bool,
    /// 是否启用聚合
    pub enable_aggregation: bool,
    /// 是否启用压缩
    pub enable_compression: bool,
    /// 工作线程数
    pub worker_threads: usize,
}

impl Default for ProcessingConfig {
    fn default() -> Self {
        Self {
            batch_size: 512,
            batch_timeout: Duration::from_millis(5000),
            max_queue_size: 2048,
            enable_filtering: true,
            enable_aggregation: false,
            enable_compression: true,
            worker_threads: num_cpus::get(),
        }
    }
}

/// 数据过滤器
pub trait DataFilter: Send + Sync {
    /// 过滤数据
    fn filter(&self, data: &TelemetryData) -> bool;
    
    /// 获取过滤器名称
    fn name(&self) -> &str;
}

/// 属性过滤器
pub struct AttributeFilter {
    name: String,
    required_attributes: HashMap<String, String>,
    excluded_attributes: HashMap<String, String>,
}

impl AttributeFilter {
    /// 创建新的属性过滤器
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            required_attributes: HashMap::new(),
            excluded_attributes: HashMap::new(),
        }
    }

    /// 添加必需的属性
    pub fn with_required_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.required_attributes.insert(key.into(), value.into());
        self
    }

    /// 添加排除的属性
    pub fn with_excluded_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.excluded_attributes.insert(key.into(), value.into());
        self
    }
}

impl DataFilter for AttributeFilter {
    fn filter(&self, data: &TelemetryData) -> bool {
        // 检查必需的属性
        for (key, expected_value) in &self.required_attributes {
            if let Some(actual_value) = data.resource_attributes.get(key) {
                if actual_value != expected_value {
                    return false;
                }
            } else {
                return false;
            }
        }

        // 检查排除的属性
        for (key, excluded_value) in &self.excluded_attributes {
            if let Some(actual_value) = data.resource_attributes.get(key) {
                if actual_value == excluded_value {
                    return false;
                }
            }
        }

        true
    }

    fn name(&self) -> &str {
        &self.name
    }
}

/// 采样过滤器
pub struct SamplingFilter {
    name: String,
    sampling_ratio: f64,
}

impl SamplingFilter {
    /// 创建新的采样过滤器
    pub fn new(name: impl Into<String>, sampling_ratio: f64) -> Self {
        Self {
            name: name.into(),
            sampling_ratio: sampling_ratio.max(0.0).min(1.0),
        }
    }
}

impl DataFilter for SamplingFilter {
    fn filter(&self, _data: &TelemetryData) -> bool {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        use std::time::{SystemTime, //UNIX_EPOCH,
        };
        
        let mut hasher = DefaultHasher::new();
        SystemTime::now().hash(&mut hasher);
        let hash = hasher.finish();
        
        let random_value = (hash % 1000) as f64 / 1000.0;
        random_value < self.sampling_ratio
    }

    fn name(&self) -> &str {
        &self.name
    }
}

/// 数据聚合器
pub trait DataAggregator: Send + Sync {
    /// 聚合数据
    fn aggregate(&self, data: Vec<TelemetryData>) -> Result<Vec<TelemetryData>>;
    
    /// 获取聚合器名称
    fn name(&self) -> &str;
}

/// 指标聚合器
#[allow(dead_code)]
pub struct MetricAggregator {
    name: String,
    aggregation_window: Duration,
    metrics: Arc<RwLock<HashMap<String, f64>>>,
}

impl MetricAggregator {
    /// 创建新的指标聚合器
    pub fn new(name: impl Into<String>, aggregation_window: Duration) -> Self {
        Self {
            name: name.into(),
            aggregation_window,
            metrics: Arc::new(RwLock::new(HashMap::new())),
        }
    }
}

impl DataAggregator for MetricAggregator {
    fn aggregate(&self, data: Vec<TelemetryData>) -> Result<Vec<TelemetryData>> {
        let mut aggregated_data = Vec::new();
        let mut metrics = self.metrics.try_write()
            .map_err(|_| ProcessingError::Aggregation {
                operation: "metric_aggregation".to_string(),
                reason: "Failed to acquire write lock".to_string(),
            })?;

        for telemetry_data in data {
            if let crate::data::TelemetryContent::Metric(metric_data) = &telemetry_data.content {
                for data_point in &metric_data.data_points {
                    if let crate::data::DataPointValue::Number(value) = &data_point.value {
                        let key = format!("{}_{}", metric_data.name, data_point.timestamp);
                        let current_value = *metrics.get(&key).unwrap_or(&0.0);
                        metrics.insert(key, current_value + value);
                    }
                }
            }
            aggregated_data.push(telemetry_data);
        }

        Ok(aggregated_data)
    }

    fn name(&self) -> &str {
        &self.name
    }
}

/// OTLP处理器
pub struct OtlpProcessor {
    config: ProcessingConfig,
    input_queue: mpsc::UnboundedSender<TelemetryData>,
    output_queue: mpsc::UnboundedReceiver<Vec<TelemetryData>>,
    filters: Vec<Box<dyn DataFilter>>,
    aggregators: Vec<Box<dyn DataAggregator>>,
    is_running: Arc<RwLock<bool>>,
    metrics: Arc<RwLock<ProcessorMetrics>>,
}

/// 处理器指标
#[derive(Debug, Default, Clone)]
pub struct ProcessorMetrics {
    /// 处理的数据总数
    pub total_processed: u64,
    /// 过滤的数据总数
    pub total_filtered: u64,
    /// 聚合的数据总数
    pub total_aggregated: u64,
    /// 批处理次数
    pub batch_count: u64,
    /// 平均批处理大小
    pub average_batch_size: f64,
    /// 处理延迟
    pub processing_latency: Duration,
    /// 错误计数
    pub error_count: u64,
}

impl OtlpProcessor {
    /// 创建新的处理器
    pub fn new(config: ProcessingConfig) -> Self {
        let (input_tx, _input_rx) = mpsc::unbounded_channel();
        let (_output_tx, output_rx) = mpsc::unbounded_channel();

        Self {
            config,
            input_queue: input_tx,
            output_queue: output_rx,
            filters: Vec::new(),
            aggregators: Vec::new(),
            is_running: Arc::new(RwLock::new(false)),
            metrics: Arc::new(RwLock::new(ProcessorMetrics::default())),
        }
    }

    /// 添加过滤器
    pub fn add_filter(&mut self, filter: Box<dyn DataFilter>) {
        self.filters.push(filter);
    }

    /// 添加聚合器
    pub fn add_aggregator(&mut self, aggregator: Box<dyn DataAggregator>) {
        self.aggregators.push(aggregator);
    }

    /// 启动处理器
    pub async fn start(&self) -> Result<()> {
        let mut is_running = self.is_running.write().await;
        if *is_running {
            return Err(ProcessingError::BatchProcessing {
                message: "Processor is already running".to_string(),
            }.into());
        }
        *is_running = true;
        drop(is_running);

        // 启动处理任务
        let _config = self.config.clone();
        // 注意：这里简化处理，实际实现中需要更复杂的克隆逻辑
        // let filters = self.filters.clone();
        // let aggregators = self.aggregators.clone();
        let _metrics = self.metrics.clone();
        let _is_running = self.is_running.clone();

        tokio::spawn(async move {
            // 简化处理循环，实际实现中需要传入filters和aggregators
            // Self::processing_loop(config, filters, aggregators, metrics, is_running).await;
        });

        Ok(())
    }

    /// 停止处理器
    pub async fn stop(&self) -> Result<()> {
        let mut is_running = self.is_running.write().await;
        *is_running = false;
        Ok(())
    }

    /// 处理数据
    pub async fn process(&self, data: TelemetryData) -> Result<()> {
        self.input_queue.send(data)
            .map_err(|_| ProcessingError::BatchProcessing {
                message: "Failed to send data to processing queue".to_string(),
            })?;
        Ok(())
    }

    /// 获取处理后的数据
    pub async fn receive(&mut self) -> Option<Vec<TelemetryData>> {
        self.output_queue.recv().await
    }

    /// 获取处理器指标
    pub async fn get_metrics(&self) -> ProcessorMetrics {
        self.metrics.read().await.clone()
    }

    /// 处理循环
    #[allow(dead_code)]
    async fn processing_loop(
        config: ProcessingConfig,
        filters: Vec<Box<dyn DataFilter>>,
        aggregators: Vec<Box<dyn DataAggregator>>,
        metrics: Arc<RwLock<ProcessorMetrics>>,
        is_running: Arc<RwLock<bool>>,
    ) {
        let mut batch = Vec::with_capacity(config.batch_size);
        let mut batch_timer = interval(config.batch_timeout);
        let mut _last_batch_time = TimeUtils::current_timestamp_nanos();

        loop {
            // 检查是否应该停止
            {
                let running = is_running.read().await;
                if !*running {
                    break;
                }
            }

            tokio::select! {
                // 处理定时批处理
                _ = batch_timer.tick() => {
                    if !batch.is_empty() {
                        let (processed_batch, processing_time) = PerformanceUtils::measure_time(async {
                            Self::process_batch(batch.clone(), &filters, &aggregators).await
                        }).await;

                        if let Ok(_processed_batch) = processed_batch {
                            // 更新指标
                            let mut metrics_guard = metrics.write().await;
                            metrics_guard.total_processed += batch.len() as u64;
                            metrics_guard.batch_count += 1;
                            metrics_guard.processing_latency = processing_time;
                            metrics_guard.average_batch_size = 
                                (metrics_guard.average_batch_size * (metrics_guard.batch_count - 1) as f64 + batch.len() as f64) 
                                / metrics_guard.batch_count as f64;
                        }

                        batch.clear();
                    }
                }
            }
        }
    }

    /// 处理批次数据
    async fn process_batch(
        mut batch: Vec<TelemetryData>,
        filters: &[Box<dyn DataFilter>],
        aggregators: &[Box<dyn DataAggregator>],
    ) -> Result<Vec<TelemetryData>> {
        // 应用过滤器
        if !filters.is_empty() {
            batch = batch.into_iter()
                .filter(|data| {
                    filters.iter().all(|filter| filter.filter(data))
                })
                .collect();
        }

        // 应用聚合器
        for aggregator in aggregators {
            batch = aggregator.aggregate(batch)?;
        }

        Ok(batch)
    }
}

/// 批处理管理器
pub struct BatchManager {
    config: ProcessingConfig,
    batches: Arc<RwLock<HashMap<String, Vec<TelemetryData>>>>,
    batch_timers: Arc<RwLock<HashMap<String, tokio::time::Instant>>>,
}

impl BatchManager {
    /// 创建新的批处理管理器
    pub fn new(config: ProcessingConfig) -> Self {
        Self {
            config,
            batches: Arc::new(RwLock::new(HashMap::new())),
            batch_timers: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 添加数据到批次
    pub async fn add_data(&self, key: String, data: TelemetryData) -> Result<Option<Vec<TelemetryData>>> {
        let mut batches = self.batches.write().await;
        let mut timers = self.batch_timers.write().await;

        // 获取或创建批次
        let batch = batches.entry(key.clone()).or_insert_with(Vec::new);
        batch.push(data);

        // 设置或更新定时器
        timers.entry(key.clone()).or_insert_with(tokio::time::Instant::now);

        // 检查是否达到批处理大小
        if batch.len() >= self.config.batch_size {
            let completed_batch = batches.remove(&key).unwrap_or_default();
            timers.remove(&key);
            return Ok(Some(completed_batch));
        }

        Ok(None)
    }

    /// 获取超时的批次
    pub async fn get_expired_batches(&self) -> Result<Vec<(String, Vec<TelemetryData>)>> {
        let mut batches = self.batches.write().await;
        let mut timers = self.batch_timers.write().await;
        let mut expired_batches = Vec::new();

        let now = tokio::time::Instant::now();
        let mut expired_keys = Vec::new();

        for (key, timer) in timers.iter() {
            if now.duration_since(*timer) >= self.config.batch_timeout {
                expired_keys.push(key.clone());
            }
        }

        for key in expired_keys {
            if let Some(batch) = batches.remove(&key) {
                timers.remove(&key);
                expired_batches.push((key, batch));
            }
        }

        Ok(expired_batches)
    }

    /// 获取批次统计信息
    pub async fn get_batch_stats(&self) -> HashMap<String, usize> {
        let batches = self.batches.read().await;
        batches.iter()
            .map(|(key, batch)| (key.clone(), batch.len()))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::BatchUtils; 
    use crate::data::{
        TelemetryData, 
        //TelemetryDataType, 
        TelemetryContent, 
        //MetricData, 
        MetricType,
    };

    #[test]
    fn test_attribute_filter() {
        let filter = AttributeFilter::new("test_filter")
            .with_required_attribute("service.name", "test-service")
            .with_excluded_attribute("environment", "test");

        let mut data = TelemetryData::trace("test-operation");
        data.resource_attributes.insert("service.name".to_string(), "test-service".to_string());
        data.resource_attributes.insert("environment".to_string(), "production".to_string());

        assert!(filter.filter(&data));

        data.resource_attributes.insert("environment".to_string(), "test".to_string());
        assert!(!filter.filter(&data));
    }

    #[test]
    fn test_sampling_filter() {
        let filter = SamplingFilter::new("test_sampling", 0.5);
        
        // 由于是随机采样，我们只测试过滤器名称
        assert_eq!(filter.name(), "test_sampling");
    }

    #[tokio::test]
    async fn test_metric_aggregator() {
        let aggregator = MetricAggregator::new("test_aggregator", Duration::from_secs(60));
        
        let mut data = TelemetryData::metric("test-metric", MetricType::Counter);
        if let TelemetryContent::Metric(ref mut metric_data) = data.content {
            metric_data.data_points.push(crate::data::DataPoint {
                timestamp: TimeUtils::current_timestamp_nanos(),
                attributes: HashMap::new(),
                value: crate::data::DataPointValue::Number(10.0),
            });
        }

        let result = aggregator.aggregate(vec![data]);
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_processor_creation() {
        let config = ProcessingConfig::default();
        let mut processor = OtlpProcessor::new(config);
        
        // 测试添加过滤器
        let filter = AttributeFilter::new("test_filter");
        processor.add_filter(Box::new(filter));
        
        // 测试添加聚合器
        let aggregator = MetricAggregator::new("test_aggregator", Duration::from_secs(60));
        processor.add_aggregator(Box::new(aggregator));
    }

    #[tokio::test]
    async fn test_batch_manager() {
        let config = ProcessingConfig::default();
        let manager = BatchManager::new(config);
        
        let data = TelemetryData::trace("test-operation");
        let result = manager.add_data("test_key".to_string(), data).await;
        assert!(result.is_ok());
        
        let stats = manager.get_batch_stats().await;
        assert_eq!(stats.get("test_key"), Some(&1));
    }

    #[test]
    fn test_batch_utils() {
        let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let batches = BatchUtils::batch_data(data, 3);
        assert_eq!(batches.len(), 4);
        assert_eq!(batches[0], vec![1, 2, 3]);
        assert_eq!(batches[3], vec![10]);
    }
}
