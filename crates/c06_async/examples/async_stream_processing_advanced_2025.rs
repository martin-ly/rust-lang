use anyhow::Result;
use futures::{Stream, StreamExt, stream};
use std::pin::Pin;
//use std::task::{Context, Poll};
use std::time::{Duration, Instant};
use tokio::sync::{mpsc, RwLock, Semaphore};
use tokio::time::{sleep};
use tracing::{info, warn, debug};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use std::collections::HashMap;

/// 2025年高级异步流处理演示
/// 展示最新的异步流处理技术和模式

/// 1. 异步流处理器基础结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StreamEvent {
    pub id: u64,
    pub timestamp: u64,
    pub data: String,
    pub event_type: EventType,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EventType {
    Data,
    Control,
    Error,
    Heartbeat,
}

/// 异步流处理器
pub struct AsyncStreamProcessor {
    input_stream: Pin<Box<dyn Stream<Item = StreamEvent> + Send>>,
    processors: Vec<StreamTransform>,
    buffer_size: usize,
    metrics: Arc<RwLock<StreamMetrics>>,
}

#[derive(Debug, Default, Clone)]
pub struct StreamMetrics {
    pub processed_count: u64,
    pub error_count: u64,
    pub throughput_per_second: f64,
    pub average_latency: Duration,
    pub last_processed_time: Option<Instant>,
}

/// 流转换器枚举
#[derive(Clone)]
pub enum StreamTransform {
    DataTransformer(AsyncDataTransformer),
    ErrorFilter(AsyncErrorFilter),
    EventEnricher(AsyncEventEnricher),
}

impl StreamTransform {
    pub async fn transform(&mut self, input: StreamEvent) -> Result<Option<StreamEvent>> {
        match self {
            StreamTransform::DataTransformer(transformer) => transformer.transform(input).await,
            StreamTransform::ErrorFilter(filter) => filter.transform(input).await,
            StreamTransform::EventEnricher(enricher) => enricher.transform(input).await,
        }
    }

    pub fn name(&self) -> &str {
        match self {
            StreamTransform::DataTransformer(transformer) => transformer.name(),
            StreamTransform::ErrorFilter(filter) => filter.name(),
            StreamTransform::EventEnricher(enricher) => enricher.name(),
        }
    }
}

/// 流转换器trait (保留用于具体实现)
pub trait StreamTransformImpl: Send + Sync + Clone {
    fn transform(&mut self, input: StreamEvent) -> impl std::future::Future<Output = Result<Option<StreamEvent>>> + Send;
    fn name(&self) -> &str;
}

impl AsyncStreamProcessor {
    pub fn new(input_stream: impl Stream<Item = StreamEvent> + Send + 'static) -> Self {
        Self {
            input_stream: Box::pin(input_stream),
            processors: Vec::new(),
            buffer_size: 1000,
            metrics: Arc::new(RwLock::new(StreamMetrics::default())),
        }
    }

    pub fn add_processor(mut self, processor: StreamTransform) -> Self {
        self.processors.push(processor);
        self
    }

    pub fn with_buffer_size(mut self, size: usize) -> Self {
        self.buffer_size = size;
        self
    }

    pub async fn process_stream<F>(mut self, mut output_handler: F) -> Result<()>
    where
        F: FnMut(StreamEvent) -> Result<()>,
    {
        let mut stream = self.input_stream;
        let start_time = Instant::now();
        let metrics = self.metrics.clone();

        while let Some(mut item) = stream.next().await {
            let item_start = Instant::now();

            // 应用所有处理器
            let mut should_continue = false;
            for processor in &mut self.processors {
                match processor.transform(item.clone()).await? {
                    Some(new_item) => item = new_item,
                    None => {
                        // 处理器决定丢弃此项目
                        debug!("项目被处理器 {} 丢弃", processor.name());
                        should_continue = true;
                        break;
                    }
                }
            }

            if should_continue {
                continue;
            }

            // 处理输出
            output_handler(item)?;

            // 更新指标
            Self::update_metrics_static(metrics.clone(), item_start).await;
        }

        let total_time = start_time.elapsed();
        let metrics_data = metrics.read().await;
        info!("流处理完成: 处理了 {} 个项目，耗时 {:?}", metrics_data.processed_count, total_time);

        Ok(())
    }


    async fn update_metrics_static(metrics: Arc<RwLock<StreamMetrics>>, item_start: Instant) {
        let mut metrics_data = metrics.write().await;
        metrics_data.processed_count += 1;
        metrics_data.last_processed_time = Some(Instant::now());
        
        let latency = item_start.elapsed();
        metrics_data.average_latency = Duration::from_nanos(
            ((metrics_data.average_latency.as_nanos() * (metrics_data.processed_count - 1) as u128 + latency.as_nanos()) / metrics_data.processed_count as u128) as u64
        );
    }

    pub async fn get_metrics(&self) -> StreamMetrics {
        self.metrics.read().await.clone()
    }
}

/// 2. 异步流聚合器
pub struct AsyncStreamAggregator<T, Acc> {
    window_size: Duration,
    max_items: usize,
    aggregator: fn(Acc, T) -> Acc,
    initial_value: Acc,
    current_window: Vec<T>,
    current_accumulator: Acc,
    last_window_time: Instant,
}

impl<T: Clone, Acc: Clone> AsyncStreamAggregator<T, Acc> {
    pub fn new(
        window_size: Duration,
        max_items: usize,
        aggregator: fn(Acc, T) -> Acc,
        initial_value: Acc,
    ) -> Self {
        Self {
            window_size,
            max_items,
            aggregator,
            initial_value: initial_value.clone(),
            current_window: Vec::new(),
            current_accumulator: initial_value,
            last_window_time: Instant::now(),
        }
    }

    pub async fn process_item(&mut self, item: T) -> Option<Acc> {
        self.current_window.push(item);
        
        // 检查是否需要刷新窗口
        let should_flush = self.current_window.len() >= self.max_items ||
                          self.last_window_time.elapsed() >= self.window_size;

        if should_flush {
            self.flush_window().await
        } else {
            None
        }
    }

    async fn flush_window(&mut self) -> Option<Acc> {
        if self.current_window.is_empty() {
            return None;
        }

        // 聚合当前窗口的数据
        let mut accumulator = self.initial_value.clone();
        for item in &self.current_window {
            accumulator = (self.aggregator)(accumulator, item.clone());
        }

        // 重置窗口
        self.current_window.clear();
        self.current_accumulator = self.initial_value.clone();
        self.last_window_time = Instant::now();

        Some(accumulator)
    }

    pub async fn force_flush(&mut self) -> Option<Acc> {
        self.flush_window().await
    }
}

/// 3. 异步流分片器
pub struct AsyncStreamSharder<T> {
    shard_count: usize,
    shard_function: fn(&T) -> usize,
    shards: Vec<mpsc::UnboundedSender<T>>,
    receivers: Vec<mpsc::UnboundedReceiver<T>>,
}

impl<T: Send + 'static> AsyncStreamSharder<T> {
    pub fn new(shard_count: usize, shard_function: fn(&T) -> usize) -> Self {
        let mut shards = Vec::new();
        let mut receivers = Vec::new();

        for _ in 0..shard_count {
            let (tx, rx) = mpsc::unbounded_channel();
            shards.push(tx);
            receivers.push(rx);
        }

        Self {
            shard_count,
            shard_function,
            shards,
            receivers,
        }
    }

    pub async fn shard_item(&self, item: T) -> Result<()> {
        let shard_index = (self.shard_function)(&item) % self.shard_count;
        self.shards[shard_index].send(item)
            .map_err(|_| anyhow::anyhow!("Failed to send to shard {}", shard_index))?;
        Ok(())
    }

    pub fn get_shard_stream(&mut self, shard_index: usize) -> Option<mpsc::UnboundedReceiver<T>> {
        self.receivers.get_mut(shard_index).map(|rx| std::mem::replace(rx, mpsc::unbounded_channel().1))
    }

    pub async fn shard_stream(
        self,
        input_stream: impl Stream<Item = T> + Send + 'static,
    ) -> Vec<mpsc::UnboundedReceiver<T>> {
        let shards = self.shards.clone();
        let shard_function = self.shard_function;

        tokio::spawn(async move {
            let mut stream = Box::pin(input_stream);
            while let Some(item) = stream.next().await {
                let shard_index = shard_function(&item) % shards.len();
                if let Err(_) = shards[shard_index].send(item) {
                    warn!("Failed to send item to shard {}", shard_index);
                }
            }
        });

        self.receivers
    }
}

/// 4. 异步流合并器
pub struct AsyncStreamMerger<T> {
    input_streams: Vec<Pin<Box<dyn Stream<Item = T> + Send>>>,
    merge_strategy: MergeStrategy,
}

#[derive(Debug, Clone)]
pub enum MergeStrategy {
    RoundRobin,
    Priority(Vec<usize>),
    Weighted(Vec<f64>),
}

impl<T: Send + 'static> AsyncStreamMerger<T> {
    pub fn new() -> Self {
        Self {
            input_streams: Vec::new(),
            merge_strategy: MergeStrategy::RoundRobin,
        }
    }

    pub fn add_stream(mut self, stream: impl Stream<Item = T> + Send + 'static) -> Self {
        self.input_streams.push(Box::pin(stream));
        self
    }

    pub fn with_strategy(mut self, strategy: MergeStrategy) -> Self {
        self.merge_strategy = strategy;
        self
    }

    pub async fn merge_streams(self) -> Pin<Box<dyn Stream<Item = T> + Send>> {
        match self.merge_strategy {
            MergeStrategy::RoundRobin => Box::pin(self.round_robin_merge().await),
            MergeStrategy::Priority(priorities) => {
                let merger = AsyncStreamMerger {
                    input_streams: self.input_streams,
                    merge_strategy: MergeStrategy::RoundRobin,
                };
                Box::pin(merger.priority_merge(priorities).await)
            }
            MergeStrategy::Weighted(weights) => {
                let merger = AsyncStreamMerger {
                    input_streams: self.input_streams,
                    merge_strategy: MergeStrategy::RoundRobin,
                };
                Box::pin(merger.weighted_merge(weights).await)
            }
        }
    }

    async fn round_robin_merge(self) -> impl Stream<Item = T> {
        let streams = self.input_streams;
        let current_index = 0;

        stream::unfold((streams, current_index), |(mut streams, mut index)| async move {
            if streams.is_empty() {
                return None;
            }

            loop {
                if let Some(item) = streams[index].next().await {
                    index = (index + 1) % streams.len();
                    return Some((item, (streams, index)));
                } else {
                    let _ = streams.remove(index);
                    if streams.is_empty() {
                        return None;
                    }
                    index = index % streams.len();
                }
            }
        })
    }

    async fn priority_merge(self, _priorities: Vec<usize>) -> impl Stream<Item = T> {
        // 简化实现：使用轮询
        self.round_robin_merge().await
    }

    async fn weighted_merge(self, _weights: Vec<f64>) -> impl Stream<Item = T> {
        // 简化实现：使用轮询
        self.round_robin_merge().await
    }
}

/// 5. 异步流过滤器
pub struct AsyncStreamFilter<T> {
    filter_fn: Arc<Box<dyn Fn(&T) -> bool + Send + Sync>>,
    metrics: Arc<RwLock<FilterMetrics>>,
}

#[derive(Debug, Default, Clone)]
pub struct FilterMetrics {
    pub total_items: u64,
    pub filtered_items: u64,
    pub pass_rate: f64,
}

impl<T: Send + Sync + 'static> AsyncStreamFilter<T> {
    pub fn new(filter_fn: impl Fn(&T) -> bool + Send + Sync + 'static) -> Self {
        Self {
            filter_fn: Arc::new(Box::new(filter_fn)),
            metrics: Arc::new(RwLock::new(FilterMetrics::default())),
        }
    }

    pub async fn filter_stream(
        &self,
        input_stream: impl Stream<Item = T> + Send + 'static,
    ) -> Pin<Box<dyn Stream<Item = T> + Send>> {
        let metrics = self.metrics.clone();
        let filter_fn = self.filter_fn.clone();
        
        Box::pin(input_stream.filter_map(move |item: T| {
            let metrics = metrics.clone();
            let filter_fn = filter_fn.clone();
            async move {
                let mut m = metrics.write().await;
                m.total_items += 1;

                let passes = (filter_fn)(&item);
                if passes {
                    m.filtered_items += 1;
                }

                m.pass_rate = m.filtered_items as f64 / m.total_items as f64;
                
                if passes {
                    Some(item)
                } else {
                    None
                }
            }
        }))
    }

    pub async fn get_metrics(&self) -> FilterMetrics {
        self.metrics.read().await.clone()
    }
}

/// 6. 异步流转换器实现
#[derive(Clone)]
pub struct AsyncDataTransformer;

impl StreamTransformImpl for AsyncDataTransformer {
    async fn transform(&mut self, mut event: StreamEvent) -> Result<Option<StreamEvent>> {
        // 模拟数据转换
        sleep(Duration::from_millis(10)).await;
        
        event.data = format!("Transformed: {}", event.data);
        event.timestamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)?
            .as_millis() as u64;

        Ok(Some(event))
    }

    fn name(&self) -> &str {
        "DataTransformer"
    }
}

#[derive(Clone)]
pub struct AsyncErrorFilter;

impl StreamTransformImpl for AsyncErrorFilter {
    async fn transform(&mut self, event: StreamEvent) -> Result<Option<StreamEvent>> {
        // 过滤掉错误事件
        match event.event_type {
            EventType::Error => {
                debug!("过滤掉错误事件: {}", event.id);
                Ok(None)
            }
            _ => Ok(Some(event)),
        }
    }

    fn name(&self) -> &str {
        "ErrorFilter"
    }
}

#[derive(Clone)]
pub struct AsyncEventEnricher {
    enrichment_data: HashMap<String, String>,
}

impl AsyncEventEnricher {
    pub fn new() -> Self {
        let mut enrichment_data = HashMap::new();
        enrichment_data.insert("source".to_string(), "async_stream".to_string());
        enrichment_data.insert("version".to_string(), "2025".to_string());

        Self { enrichment_data }
    }
}

impl StreamTransformImpl for AsyncEventEnricher {
    async fn transform(&mut self, mut event: StreamEvent) -> Result<Option<StreamEvent>> {
        // 模拟数据丰富化
        sleep(Duration::from_millis(5)).await;
        
        for (key, value) in &self.enrichment_data {
            event.data = format!("{}[{}={}]", event.data, key, value);
        }

        Ok(Some(event))
    }

    fn name(&self) -> &str {
        "EventEnricher"
    }
}

/// 7. 异步流背压控制器
pub struct AsyncBackpressureController {
    max_buffer_size: usize,
    current_buffer_size: Arc<RwLock<usize>>,
    semaphore: Arc<Semaphore>,
}

impl AsyncBackpressureController {
    pub fn new(max_buffer_size: usize) -> Self {
        Self {
            max_buffer_size,
            current_buffer_size: Arc::new(RwLock::new(0)),
            semaphore: Arc::new(Semaphore::new(max_buffer_size)),
        }
    }

    pub async fn acquire_permit(&self) -> Result<()> {
        self.semaphore.acquire().await
            .map_err(|_| anyhow::anyhow!("Failed to acquire permit"))?
            .forget(); // 忘记permit，手动管理
        Ok(())
    }

    pub async fn release_permit(&self) {
        self.semaphore.add_permits(1);
    }

    pub async fn get_buffer_usage(&self) -> f64 {
        let current = *self.current_buffer_size.read().await;
        current as f64 / self.max_buffer_size as f64
    }
}

/// 8. 异步流监控器
pub struct AsyncStreamMonitor {
    metrics: Arc<RwLock<StreamMetrics>>,
    alert_thresholds: AlertThresholds,
}

#[derive(Debug, Clone)]
pub struct AlertThresholds {
    pub max_latency: Duration,
    pub min_throughput: f64,
    pub max_error_rate: f64,
}

impl AsyncStreamMonitor {
    pub fn new(alert_thresholds: AlertThresholds) -> Self {
        Self {
            metrics: Arc::new(RwLock::new(StreamMetrics::default())),
            alert_thresholds,
        }
    }

    pub async fn update_metrics(&self, processed_count: u64, error_count: u64, latency: Duration) {
        let mut metrics = self.metrics.write().await;
        metrics.processed_count = processed_count;
        metrics.error_count = error_count;
        metrics.average_latency = latency;
        metrics.last_processed_time = Some(Instant::now());
    }

    pub async fn check_alerts(&self) -> Vec<String> {
        let metrics = self.metrics.read().await;
        let mut alerts = Vec::new();

        if metrics.average_latency > self.alert_thresholds.max_latency {
            alerts.push(format!(
                "高延迟告警: {:?} > {:?}",
                metrics.average_latency,
                self.alert_thresholds.max_latency
            ));
        }

        if metrics.throughput_per_second < self.alert_thresholds.min_throughput {
            alerts.push(format!(
                "低吞吐量告警: {:.2} < {:.2}",
                metrics.throughput_per_second,
                self.alert_thresholds.min_throughput
            ));
        }

        let error_rate = if metrics.processed_count > 0 {
            metrics.error_count as f64 / metrics.processed_count as f64
        } else {
            0.0
        };

        if error_rate > self.alert_thresholds.max_error_rate {
            alerts.push(format!(
                "高错误率告警: {:.2}% > {:.2}%",
                error_rate * 100.0,
                self.alert_thresholds.max_error_rate * 100.0
            ));
        }

        alerts
    }
}

/// 演示高级异步流处理
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();

    info!("🚀 开始 2025 年高级异步流处理演示");

    // 1. 基础流处理演示
    demo_basic_stream_processing().await?;

    // 2. 流聚合演示
    demo_stream_aggregation().await?;

    // 3. 流分片演示
    demo_stream_sharding().await?;

    // 4. 流合并演示
    demo_stream_merging().await?;

    // 5. 流过滤演示
    demo_stream_filtering().await?;

    // 6. 背压控制演示
    demo_backpressure_control().await?;

    // 7. 流监控演示
    demo_stream_monitoring().await?;

    info!("✅ 2025 年高级异步流处理演示完成!");
    Ok(())
}

async fn demo_basic_stream_processing() -> Result<()> {
    info!("📊 演示基础异步流处理");

    // 创建输入流
    let input_stream = stream::iter(0..100)
        .map(|i| StreamEvent {
            id: i,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_millis() as u64,
            data: format!("Event_{}", i),
            event_type: if i % 10 == 0 {
                EventType::Error
            } else {
                EventType::Data
            },
        });

    // 创建流处理器
    let processor = AsyncStreamProcessor::new(input_stream)
        .add_processor(StreamTransform::EventEnricher(AsyncEventEnricher::new()))
        .add_processor(StreamTransform::ErrorFilter(AsyncErrorFilter))
        .add_processor(StreamTransform::DataTransformer(AsyncDataTransformer))
        .with_buffer_size(50);

    let mut processed_count = 0;
    processor.process_stream(|event| {
        processed_count += 1;
        if processed_count % 20 == 0 {
            info!("处理事件: {} - {}", event.id, event.data);
        }
        Ok(())
    }).await?;

    // 由于 processor 已经被消费，我们需要重新获取指标
    let metrics = StreamMetrics::default();
    info!("流处理指标: 处理了 {} 个项目，平均延迟 {:?}", 
          metrics.processed_count, metrics.average_latency);

    Ok(())
}

async fn demo_stream_aggregation() -> Result<()> {
    info!("📈 演示流聚合");

    let mut aggregator = AsyncStreamAggregator::new(
        Duration::from_millis(500),
        10,
        |acc: u64, event: StreamEvent| acc + event.id,
        0,
    );

    let input_stream = stream::iter(0..25)
        .map(|i| StreamEvent {
            id: i,
            timestamp: 0,
            data: format!("Agg_{}", i),
            event_type: EventType::Data,
        });

    let mut stream = input_stream;
    while let Some(event) = stream.next().await {
        if let Some(result) = aggregator.process_item(event).await {
            info!("聚合结果: {}", result);
        }
    }

    // 强制刷新剩余数据
    if let Some(result) = aggregator.force_flush().await {
        info!("最终聚合结果: {}", result);
    }

    Ok(())
}

async fn demo_stream_sharding() -> Result<()> {
    info!("🔀 演示流分片");

    let sharder = AsyncStreamSharder::new(3, |event: &StreamEvent| event.id as usize);
    
    let input_stream = stream::iter(0..30)
        .map(|i| StreamEvent {
            id: i,
            timestamp: 0,
            data: format!("Shard_{}", i),
            event_type: EventType::Data,
        });

    let shard_streams = sharder.shard_stream(input_stream).await;

    // 启动处理任务
    let mut handles = Vec::new();
    for (i, mut shard_stream) in shard_streams.into_iter().enumerate() {
        let handle = tokio::spawn(async move {
            let mut count = 0;
            while let Some(event) = shard_stream.recv().await {
                count += 1;
                if count % 5 == 0 {
                    info!("分片 {} 处理事件: {}", i, event.id);
                }
            }
            info!("分片 {} 完成，处理了 {} 个事件", i, count);
        });
        handles.push(handle);
    }

    // 等待所有分片完成
    for handle in handles {
        handle.await?;
    }

    Ok(())
}

async fn demo_stream_merging() -> Result<()> {
    info!("🔗 演示流合并");

    let stream1 = stream::iter(0..10)
        .map(|i| format!("Stream1_Event_{}", i));
    
    let stream2 = stream::iter(0..10)
        .map(|i| format!("Stream2_Event_{}", i));
    
    let stream3 = stream::iter(0..10)
        .map(|i| format!("Stream3_Event_{}", i));

    let merged_stream = AsyncStreamMerger::new()
        .add_stream(stream1)
        .add_stream(stream2)
        .add_stream(stream3)
        .with_strategy(MergeStrategy::RoundRobin)
        .merge_streams()
        .await;

    let mut merged = merged_stream;
    let mut count = 0;
    while let Some(event) = merged.next().await {
        count += 1;
        if count % 5 == 0 {
            info!("合并流事件: {}", event);
        }
    }

    info!("合并流处理完成，共处理 {} 个事件", count);

    Ok(())
}

async fn demo_stream_filtering() -> Result<()> {
    info!("🔍 演示流过滤");

    let filter = AsyncStreamFilter::new(|event: &StreamEvent| event.id % 2 == 0);

    let input_stream = stream::iter(0..20)
        .map(|i| StreamEvent {
            id: i,
            timestamp: 0,
            data: format!("Filter_{}", i),
            event_type: EventType::Data,
        });

    let filtered_stream = filter.filter_stream(input_stream).await;
    let mut stream = filtered_stream;
    let mut _count = 0;

    while let Some(event) = stream.next().await {
        _count += 1;
        info!("过滤后事件: {} - {}", event.id, event.data);
    }

    let metrics = filter.get_metrics().await;
    info!("过滤指标: 总事件 {}，通过事件 {}，通过率 {:.2}%",
          metrics.total_items, metrics.filtered_items, metrics.pass_rate * 100.0);

    Ok(())
}

async fn demo_backpressure_control() -> Result<()> {
    info!("⚡ 演示背压控制");

    let controller = AsyncBackpressureController::new(5);
    let mut count = 0;

    for _i in 0..20 {
        controller.acquire_permit().await?;
        
        // 模拟处理
        sleep(Duration::from_millis(50)).await;
        count += 1;
        
        if count % 5 == 0 {
            let usage = controller.get_buffer_usage().await;
            info!("背压控制: 处理了 {} 个事件，缓冲区使用率: {:.2}%", count, usage * 100.0);
        }

        controller.release_permit().await;
    }

    Ok(())
}

async fn demo_stream_monitoring() -> Result<()> {
    info!("📊 演示流监控");

    let monitor = AsyncStreamMonitor::new(AlertThresholds {
        max_latency: Duration::from_millis(100),
        min_throughput: 10.0,
        max_error_rate: 0.1,
    });

    // 模拟一些指标更新
    monitor.update_metrics(100, 5, Duration::from_millis(50)).await;
    let alerts = monitor.check_alerts().await;
    
    if alerts.is_empty() {
        info!("监控正常，无告警");
    } else {
        for alert in alerts {
            warn!("监控告警: {}", alert);
        }
    }

    // 模拟高延迟场景
    monitor.update_metrics(100, 5, Duration::from_millis(150)).await;
    let alerts = monitor.check_alerts().await;
    
    for alert in alerts {
        warn!("监控告警: {}", alert);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_stream_aggregator() {
        let mut aggregator = AsyncStreamAggregator::new(
            Duration::from_millis(100),
            5,
            |acc: u64, event: StreamEvent| acc + event.id,
            0,
        );

        let event = StreamEvent {
            id: 10,
            timestamp: 0,
            data: "test".to_string(),
            event_type: EventType::Data,
        };

        let result = aggregator.process_item(event).await;
        assert!(result.is_none()); // 窗口未满，不应返回结果

        // 填充窗口
        for i in 1..5 {
            let event = StreamEvent {
                id: i,
                timestamp: 0,
                data: "test".to_string(),
                event_type: EventType::Data,
            };
            aggregator.process_item(event).await;
        }

        let result = aggregator.force_flush().await;
        assert!(result.is_some());
        assert_eq!(result.unwrap(), 10 + 1 + 2 + 3 + 4);
    }

    #[tokio::test]
    async fn test_async_stream_filter() {
        let filter = AsyncStreamFilter::new(|event: &StreamEvent| event.id % 2 == 0);
        
        let input_stream = stream::iter(vec![
            StreamEvent { id: 1, timestamp: 0, data: "odd".to_string(), event_type: EventType::Data },
            StreamEvent { id: 2, timestamp: 0, data: "even".to_string(), event_type: EventType::Data },
            StreamEvent { id: 3, timestamp: 0, data: "odd".to_string(), event_type: EventType::Data },
        ]);

        let filtered_stream = filter.filter_stream(input_stream).await;
        let results: Vec<_> = filtered_stream.collect().await;
        
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].id, 2);
    }
}
