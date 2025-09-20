# OTLP算法与设计模式深度分析

## 概述

本文档深入分析OpenTelemetry Protocol (OTLP)相关的核心算法和设计模式，结合Rust 1.90语言特性，探讨如何构建高效、可扩展的遥测数据处理系统。

## 1. 核心算法分析

### 1.1 数据采样算法

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};
use rand::Rng;

/// 自适应采样算法
pub struct AdaptiveSamplingAlgorithm {
    // 采样率控制
    base_sampling_rate: f64,
    current_sampling_rate: AtomicU64,
    
    // 性能指标
    target_latency: Duration,
    current_latency: AtomicU64,
    error_rate: AtomicU64,
    
    // 历史数据
    latency_history: VecDeque<Duration>,
    throughput_history: VecDeque<u64>,
    
    // 调整参数
    adjustment_factor: f64,
    min_sampling_rate: f64,
    max_sampling_rate: f64,
}

impl AdaptiveSamplingAlgorithm {
    pub fn new(
        base_rate: f64,
        target_latency: Duration,
        min_rate: f64,
        max_rate: f64,
    ) -> Self {
        Self {
            base_sampling_rate: base_rate,
            current_sampling_rate: AtomicU64::new((base_rate * 1000.0) as u64),
            target_latency,
            current_latency: AtomicU64::new(target_latency.as_millis() as u64),
            error_rate: AtomicU64::new(0),
            latency_history: VecDeque::with_capacity(100),
            throughput_history: VecDeque::with_capacity(100),
            adjustment_factor: 0.1,
            min_sampling_rate: min_rate,
            max_sampling_rate: max_rate,
        }
    }
    
    /// 决定是否采样
    pub fn should_sample(&self, trace_id: &str) -> bool {
        let current_rate = self.current_sampling_rate.load(Ordering::Acquire) as f64 / 1000.0;
        
        // 基于trace_id的确定性采样
        let hash = self.hash_trace_id(trace_id);
        let threshold = (hash % 1000) as f64 / 1000.0;
        
        threshold < current_rate
    }
    
    /// 更新性能指标并调整采样率
    pub fn update_metrics(&mut self, latency: Duration, success: bool) {
        // 更新延迟历史
        self.latency_history.push_back(latency);
        if self.latency_history.len() > 100 {
            self.latency_history.pop_front();
        }
        
        // 更新错误率
        if !success {
            self.error_rate.fetch_add(1, Ordering::Relaxed);
        }
        
        // 计算平均延迟
        let avg_latency = self.calculate_average_latency();
        
        // 自适应调整采样率
        self.adjust_sampling_rate(avg_latency);
    }
    
    fn adjust_sampling_rate(&self, avg_latency: Duration) {
        let current_rate = self.current_sampling_rate.load(Ordering::Acquire) as f64 / 1000.0;
        let target_latency_ms = self.target_latency.as_millis() as f64;
        let avg_latency_ms = avg_latency.as_millis() as f64;
        
        let ratio = avg_latency_ms / target_latency_ms;
        let adjustment = if ratio > 1.2 {
            // 延迟过高，降低采样率
            -self.adjustment_factor
        } else if ratio < 0.8 {
            // 延迟较低，提高采样率
            self.adjustment_factor
        } else {
            0.0
        };
        
        let new_rate = (current_rate + adjustment)
            .max(self.min_sampling_rate)
            .min(self.max_sampling_rate);
        
        self.current_sampling_rate.store(
            (new_rate * 1000.0) as u64,
            Ordering::Release
        );
    }
    
    fn hash_trace_id(&self, trace_id: &str) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        trace_id.hash(&mut hasher);
        hasher.finish()
    }
    
    fn calculate_average_latency(&self) -> Duration {
        if self.latency_history.is_empty() {
            return self.target_latency;
        }
        
        let total: Duration = self.latency_history.iter().sum();
        total / self.latency_history.len() as u32
    }
}
```

### 1.2 数据聚合算法

```rust
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 时间窗口聚合算法
pub struct TimeWindowAggregator {
    window_size: Duration,
    windows: Arc<RwLock<HashMap<u64, AggregationWindow>>>,
    current_window: Arc<RwLock<u64>>,
}

#[derive(Debug, Clone)]
pub struct AggregationWindow {
    pub start_time: Instant,
    pub end_time: Instant,
    pub metrics: HashMap<String, MetricValue>,
    pub trace_count: u64,
    pub error_count: u64,
}

#[derive(Debug, Clone)]
pub enum MetricValue {
    Counter(u64),
    Gauge(f64),
    Histogram(Vec<u64>),
    Summary { count: u64, sum: f64 },
}

impl TimeWindowAggregator {
    pub fn new(window_size: Duration) -> Self {
        Self {
            window_size,
            windows: Arc::new(RwLock::new(HashMap::new())),
            current_window: Arc::new(RwLock::new(0)),
        }
    }
    
    /// 添加数据到当前窗口
    pub async fn add_data(&self, data: &TelemetryData) -> Result<(), OtlpError> {
        let window_id = self.get_current_window_id().await;
        let mut windows = self.windows.write().await;
        
        let window = windows.entry(window_id).or_insert_with(|| {
            let now = Instant::now();
            AggregationWindow {
                start_time: now,
                end_time: now + self.window_size,
                metrics: HashMap::new(),
                trace_count: 0,
                error_count: 0,
            }
        });
        
        // 更新窗口数据
        window.trace_count += 1;
        if data.is_error() {
            window.error_count += 1;
        }
        
        // 更新指标
        self.update_metrics(window, data).await;
        
        Ok(())
    }
    
    /// 获取聚合结果
    pub async fn get_aggregated_data(&self, window_id: u64) -> Option<AggregationWindow> {
        let windows = self.windows.read().await;
        windows.get(&window_id).cloned()
    }
    
    /// 清理过期窗口
    pub async fn cleanup_expired_windows(&self) {
        let now = Instant::now();
        let mut windows = self.windows.write().await;
        
        windows.retain(|_, window| {
            window.end_time > now
        });
    }
    
    async fn get_current_window_id(&self) -> u64 {
        let now = Instant::now();
        let window_start = now.duration_since(Instant::now() - self.window_size);
        (window_start.as_secs() / self.window_size.as_secs()) as u64
    }
    
    async fn update_metrics(&self, window: &mut AggregationWindow, data: &TelemetryData) {
        // 更新延迟指标
        if let Some(latency) = data.get_latency() {
            let latency_key = "request_latency".to_string();
            match window.metrics.get_mut(&latency_key) {
                Some(MetricValue::Histogram(buckets)) => {
                    let bucket_index = self.get_histogram_bucket(latency);
                    if bucket_index < buckets.len() {
                        buckets[bucket_index] += 1;
                    }
                }
                _ => {
                    let mut buckets = vec![0; 10];
                    let bucket_index = self.get_histogram_bucket(latency);
                    if bucket_index < buckets.len() {
                        buckets[bucket_index] = 1;
                    }
                    window.metrics.insert(latency_key, MetricValue::Histogram(buckets));
                }
            }
        }
        
        // 更新错误率指标
        let error_rate_key = "error_rate".to_string();
        let error_rate = if window.trace_count > 0 {
            window.error_count as f64 / window.trace_count as f64
        } else {
            0.0
        };
        window.metrics.insert(error_rate_key, MetricValue::Gauge(error_rate));
    }
    
    fn get_histogram_bucket(&self, latency: Duration) -> usize {
        let ms = latency.as_millis() as usize;
        match ms {
            0..=10 => 0,
            11..=50 => 1,
            51..=100 => 2,
            101..=200 => 3,
            201..=500 => 4,
            501..=1000 => 5,
            1001..=2000 => 6,
            2001..=5000 => 7,
            5001..=10000 => 8,
            _ => 9,
        }
    }
}
```

### 1.3 负载均衡算法

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

/// 加权轮询负载均衡算法
pub struct WeightedRoundRobinBalancer {
    endpoints: Vec<LoadBalancerEndpoint>,
    current_index: AtomicUsize,
    weights: Vec<u32>,
    current_weight: AtomicUsize,
}

#[derive(Debug, Clone)]
pub struct LoadBalancerEndpoint {
    pub url: String,
    pub weight: u32,
    pub health_status: HealthStatus,
    pub response_time: Duration,
    pub error_count: u64,
    pub success_count: u64,
}

#[derive(Debug, Clone)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Degraded,
}

impl WeightedRoundRobinBalancer {
    pub fn new(endpoints: Vec<LoadBalancerEndpoint>) -> Self {
        let weights: Vec<u32> = endpoints.iter().map(|e| e.weight).collect();
        
        Self {
            endpoints,
            current_index: AtomicUsize::new(0),
            weights,
            current_weight: AtomicUsize::new(0),
        }
    }
    
    /// 选择下一个端点
    pub fn select_endpoint(&self) -> Option<&LoadBalancerEndpoint> {
        let mut attempts = 0;
        let max_attempts = self.endpoints.len();
        
        while attempts < max_attempts {
            let index = self.get_next_index();
            let endpoint = &self.endpoints[index];
            
            // 检查端点健康状态
            if matches!(endpoint.health_status, HealthStatus::Healthy) {
                return Some(endpoint);
            }
            
            attempts += 1;
        }
        
        // 如果没有健康端点，返回第一个
        self.endpoints.first()
    }
    
    /// 更新端点健康状态
    pub fn update_endpoint_health(&mut self, index: usize, success: bool, response_time: Duration) {
        if let Some(endpoint) = self.endpoints.get_mut(index) {
            if success {
                endpoint.success_count += 1;
                endpoint.response_time = response_time;
                
                // 根据响应时间调整健康状态
                if response_time < Duration::from_millis(100) {
                    endpoint.health_status = HealthStatus::Healthy;
                } else if response_time < Duration::from_millis(500) {
                    endpoint.health_status = HealthStatus::Degraded;
                } else {
                    endpoint.health_status = HealthStatus::Unhealthy;
                }
            } else {
                endpoint.error_count += 1;
                
                // 错误率过高标记为不健康
                let total_requests = endpoint.success_count + endpoint.error_count;
                if total_requests > 10 {
                    let error_rate = endpoint.error_count as f64 / total_requests as f64;
                    if error_rate > 0.5 {
                        endpoint.health_status = HealthStatus::Unhealthy;
                    }
                }
            }
        }
    }
    
    fn get_next_index(&self) -> usize {
        let current = self.current_index.load(Ordering::Acquire);
        let next = (current + 1) % self.endpoints.len();
        self.current_index.store(next, Ordering::Release);
        next
    }
}

/// 一致性哈希负载均衡算法
pub struct ConsistentHashBalancer {
    ring: Vec<HashRingNode>,
    virtual_nodes: u32,
}

#[derive(Debug, Clone)]
pub struct HashRingNode {
    pub hash: u64,
    pub endpoint: LoadBalancerEndpoint,
    pub virtual_id: u32,
}

impl ConsistentHashBalancer {
    pub fn new(endpoints: Vec<LoadBalancerEndpoint>, virtual_nodes: u32) -> Self {
        let mut ring = Vec::new();
        
        for (i, endpoint) in endpoints.iter().enumerate() {
            for j in 0..virtual_nodes {
                let virtual_id = i as u32 * virtual_nodes + j;
                let hash = self.hash(&format!("{}:{}", endpoint.url, virtual_id));
                
                ring.push(HashRingNode {
                    hash,
                    endpoint: endpoint.clone(),
                    virtual_id,
                });
            }
        }
        
        ring.sort_by_key(|node| node.hash);
        
        Self { ring, virtual_nodes }
    }
    
    /// 根据键选择端点
    pub fn select_endpoint(&self, key: &str) -> Option<&LoadBalancerEndpoint> {
        let hash = self.hash(key);
        
        // 找到第一个hash值大于等于key hash的节点
        for node in &self.ring {
            if node.hash >= hash && matches!(node.endpoint.health_status, HealthStatus::Healthy) {
                return Some(&node.endpoint);
            }
        }
        
        // 如果没有找到，返回第一个健康节点
        self.ring.iter()
            .find(|node| matches!(node.endpoint.health_status, HealthStatus::Healthy))
            .map(|node| &node.endpoint)
    }
    
    fn hash(&self, input: &str) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        input.hash(&mut hasher);
        hasher.finish()
    }
}
```

## 2. 设计模式分析

### 2.1 策略模式

```rust
use std::sync::Arc;

/// 数据处理策略trait
#[async_trait]
pub trait DataProcessingStrategy: Send + Sync {
    async fn process(&self, data: TelemetryData) -> Result<TelemetryData, OtlpError>;
    fn get_name(&self) -> &str;
    fn get_priority(&self) -> u32;
}

/// 策略管理器
pub struct DataProcessingStrategyManager {
    strategies: Vec<Arc<dyn DataProcessingStrategy>>,
}

impl DataProcessingStrategyManager {
    pub fn new() -> Self {
        Self {
            strategies: Vec::new(),
        }
    }
    
    pub fn add_strategy(&mut self, strategy: Arc<dyn DataProcessingStrategy>) {
        self.strategies.push(strategy);
        // 按优先级排序
        self.strategies.sort_by_key(|s| s.get_priority());
    }
    
    pub async fn process_data(&self, mut data: TelemetryData) -> Result<TelemetryData, OtlpError> {
        for strategy in &self.strategies {
            data = strategy.process(data).await?;
        }
        Ok(data)
    }
}

/// 数据验证策略
pub struct DataValidationStrategy {
    rules: Vec<ValidationRule>,
}

impl DataValidationStrategy {
    pub fn new() -> Self {
        Self {
            rules: vec![
                ValidationRule::RequiredField("trace_id".to_string()),
                ValidationRule::TimestampRange,
                ValidationRule::AttributeLimit(100),
            ],
        }
    }
}

#[async_trait]
impl DataProcessingStrategy for DataValidationStrategy {
    async fn process(&self, data: TelemetryData) -> Result<TelemetryData, OtlpError> {
        for rule in &self.rules {
            rule.validate(&data)?;
        }
        Ok(data)
    }
    
    fn get_name(&self) -> &str {
        "DataValidationStrategy"
    }
    
    fn get_priority(&self) -> u32 {
        1 // 最高优先级
    }
}

/// 数据压缩策略
pub struct DataCompressionStrategy {
    algorithm: CompressionAlgorithm,
}

impl DataCompressionStrategy {
    pub fn new(algorithm: CompressionAlgorithm) -> Self {
        Self { algorithm }
    }
}

#[async_trait]
impl DataProcessingStrategy for DataCompressionStrategy {
    async fn process(&self, data: TelemetryData) -> Result<TelemetryData, OtlpError> {
        match self.algorithm {
            CompressionAlgorithm::Gzip => self.compress_gzip(data).await,
            CompressionAlgorithm::Brotli => self.compress_brotli(data).await,
            CompressionAlgorithm::Zstd => self.compress_zstd(data).await,
        }
    }
    
    fn get_name(&self) -> &str {
        "DataCompressionStrategy"
    }
    
    fn get_priority(&self) -> u32 {
        3 // 较低优先级
    }
}

impl DataCompressionStrategy {
    async fn compress_gzip(&self, data: TelemetryData) -> Result<TelemetryData, OtlpError> {
        // 实现gzip压缩
        Ok(data)
    }
    
    async fn compress_brotli(&self, data: TelemetryData) -> Result<TelemetryData, OtlpError> {
        // 实现brotli压缩
        Ok(data)
    }
    
    async fn compress_zstd(&self, data: TelemetryData) -> Result<TelemetryData, OtlpError> {
        // 实现zstd压缩
        Ok(data)
    }
}
```

### 2.2 观察者模式

```rust
use tokio::sync::broadcast;
use std::sync::Arc;

/// 事件观察者trait
#[async_trait]
pub trait OtlpEventListener: Send + Sync {
    async fn on_trace_created(&self, trace: &TraceData);
    async fn on_metric_updated(&self, metric: &MetricData);
    async fn on_log_generated(&self, log: &LogData);
    async fn on_error_occurred(&self, error: &OtlpError);
}

/// 事件总线
pub struct OtlpEventBus {
    trace_sender: broadcast::Sender<TraceData>,
    metric_sender: broadcast::Sender<MetricData>,
    log_sender: broadcast::Sender<LogData>,
    error_sender: broadcast::Sender<OtlpError>,
    listeners: Vec<Arc<dyn OtlpEventListener>>,
}

impl OtlpEventBus {
    pub fn new() -> Self {
        Self {
            trace_sender: broadcast::channel(1000).0,
            metric_sender: broadcast::channel(1000).0,
            log_sender: broadcast::channel(1000).0,
            error_sender: broadcast::channel(100).0,
            listeners: Vec::new(),
        }
    }
    
    pub fn subscribe(&mut self, listener: Arc<dyn OtlpEventListener>) {
        self.listeners.push(listener);
    }
    
    pub async fn publish_trace(&self, trace: TraceData) {
        let _ = self.trace_sender.send(trace.clone());
        
        // 通知所有监听器
        for listener in &self.listeners {
            listener.on_trace_created(&trace).await;
        }
    }
    
    pub async fn publish_metric(&self, metric: MetricData) {
        let _ = self.metric_sender.send(metric.clone());
        
        for listener in &self.listeners {
            listener.on_metric_updated(&metric).await;
        }
    }
    
    pub async fn publish_log(&self, log: LogData) {
        let _ = self.log_sender.send(log.clone());
        
        for listener in &self.listeners {
            listener.on_log_generated(&log).await;
        }
    }
    
    pub async fn publish_error(&self, error: OtlpError) {
        let _ = self.error_sender.send(error.clone());
        
        for listener in &self.listeners {
            listener.on_error_occurred(&error).await;
        }
    }
}

/// 性能监控监听器
pub struct PerformanceMonitoringListener {
    metrics: Arc<PerformanceMetrics>,
}

impl PerformanceMonitoringListener {
    pub fn new(metrics: Arc<PerformanceMetrics>) -> Self {
        Self { metrics }
    }
}

#[async_trait]
impl OtlpEventListener for PerformanceMonitoringListener {
    async fn on_trace_created(&self, trace: &TraceData) {
        // 记录追踪创建事件
        self.metrics.record_trace_created();
    }
    
    async fn on_metric_updated(&self, metric: &MetricData) {
        // 记录指标更新事件
        self.metrics.record_metric_updated();
    }
    
    async fn on_log_generated(&self, log: &LogData) {
        // 记录日志生成事件
        self.metrics.record_log_generated();
    }
    
    async fn on_error_occurred(&self, error: &OtlpError) {
        // 记录错误事件
        self.metrics.record_error();
    }
}
```

### 2.3 工厂模式

```rust
/// 传输协议工厂
pub struct TransportFactory;

impl TransportFactory {
    pub fn create_transport(
        protocol: TransportProtocol,
        config: TransportConfig,
    ) -> Result<Box<dyn Transport>, OtlpError> {
        match protocol {
            TransportProtocol::Grpc => {
                Ok(Box::new(GrpcTransport::new(config)?))
            }
            TransportProtocol::Http => {
                Ok(Box::new(HttpTransport::new(config)?))
            }
            TransportProtocol::Udp => {
                Ok(Box::new(UdpTransport::new(config)?))
            }
        }
    }
}

/// 数据处理器工厂
pub struct DataProcessorFactory;

impl DataProcessorFactory {
    pub fn create_processor(
        processor_type: ProcessorType,
        config: ProcessorConfig,
    ) -> Result<Box<dyn DataProcessor>, OtlpError> {
        match processor_type {
            ProcessorType::Validation => {
                Ok(Box::new(ValidationProcessor::new(config)))
            }
            ProcessorType::Transformation => {
                Ok(Box::new(TransformationProcessor::new(config)))
            }
            ProcessorType::Compression => {
                Ok(Box::new(CompressionProcessor::new(config)))
            }
            ProcessorType::Filtering => {
                Ok(Box::new(FilteringProcessor::new(config)))
            }
        }
    }
}

/// 导出器工厂
pub struct ExporterFactory;

impl ExporterFactory {
    pub fn create_exporter(
        exporter_type: ExporterType,
        config: ExporterConfig,
    ) -> Result<Box<dyn DataExporter>, OtlpError> {
        match exporter_type {
            ExporterType::Jaeger => {
                Ok(Box::new(JaegerExporter::new(config)?))
            }
            ExporterType::Zipkin => {
                Ok(Box::new(ZipkinExporter::new(config)?))
            }
            ExporterType::Prometheus => {
                Ok(Box::new(PrometheusExporter::new(config)?))
            }
            ExporterType::Custom => {
                Ok(Box::new(CustomExporter::new(config)?))
            }
        }
    }
}
```

## 3. 算法优化策略

### 3.1 内存优化算法

```rust
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering};

/// 内存池分配器
pub struct MemoryPoolAllocator {
    pool_size: usize,
    block_size: usize,
    free_blocks: Vec<*mut u8>,
    allocated_blocks: AtomicUsize,
    total_blocks: usize,
}

impl MemoryPoolAllocator {
    pub fn new(pool_size: usize, block_size: usize) -> Self {
        let total_blocks = pool_size / block_size;
        let mut free_blocks = Vec::with_capacity(total_blocks);
        
        // 预分配内存块
        unsafe {
            let layout = Layout::from_size_align(block_size, 8).unwrap();
            for _ in 0..total_blocks {
                let ptr = System.alloc(layout);
                if !ptr.is_null() {
                    free_blocks.push(ptr);
                }
            }
        }
        
        Self {
            pool_size,
            block_size,
            free_blocks,
            allocated_blocks: AtomicUsize::new(0),
            total_blocks,
        }
    }
    
    pub fn allocate(&mut self) -> Option<*mut u8> {
        if let Some(ptr) = self.free_blocks.pop() {
            self.allocated_blocks.fetch_add(1, Ordering::Relaxed);
            Some(ptr)
        } else {
            None
        }
    }
    
    pub fn deallocate(&mut self, ptr: *mut u8) {
        self.free_blocks.push(ptr);
        self.allocated_blocks.fetch_sub(1, Ordering::Relaxed);
    }
    
    pub fn get_usage_stats(&self) -> MemoryUsageStats {
        let allocated = self.allocated_blocks.load(Ordering::Relaxed);
        let free = self.total_blocks - allocated;
        
        MemoryUsageStats {
            total_blocks: self.total_blocks,
            allocated_blocks: allocated,
            free_blocks: free,
            usage_percentage: (allocated as f64 / self.total_blocks as f64) * 100.0,
        }
    }
}

#[derive(Debug)]
pub struct MemoryUsageStats {
    pub total_blocks: usize,
    pub allocated_blocks: usize,
    pub free_blocks: usize,
    pub usage_percentage: f64,
}
```

### 3.2 缓存优化算法

```rust
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

/// LRU缓存实现
pub struct LruCache<K, V> {
    capacity: usize,
    cache: Arc<RwLock<HashMap<K, CacheEntry<V>>>>>,
    access_order: Arc<RwLock<Vec<K>>>,
}

#[derive(Debug, Clone)]
pub struct CacheEntry<V> {
    pub value: V,
    pub created_at: Instant,
    pub last_accessed: Instant,
    pub access_count: u64,
}

impl<K, V> LruCache<K, V>
where
    K: Clone + std::hash::Hash + Eq + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            cache: Arc::new(RwLock::new(HashMap::new())),
            access_order: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    pub async fn get(&self, key: &K) -> Option<V> {
        let mut cache = self.cache.write().await;
        let mut access_order = self.access_order.write().await;
        
        if let Some(entry) = cache.get_mut(key) {
            // 更新访问信息
            entry.last_accessed = Instant::now();
            entry.access_count += 1;
            
            // 更新访问顺序
            access_order.retain(|k| k != key);
            access_order.push(key.clone());
            
            Some(entry.value.clone())
        } else {
            None
        }
    }
    
    pub async fn put(&self, key: K, value: V) {
        let mut cache = self.cache.write().await;
        let mut access_order = self.access_order.write().await;
        
        // 如果缓存已满，移除最久未使用的项
        if cache.len() >= self.capacity {
            if let Some(oldest_key) = access_order.first().cloned() {
                cache.remove(&oldest_key);
                access_order.remove(0);
            }
        }
        
        // 添加新项
        let entry = CacheEntry {
            value,
            created_at: Instant::now(),
            last_accessed: Instant::now(),
            access_count: 1,
        };
        
        cache.insert(key.clone(), entry);
        access_order.push(key);
    }
    
    pub async fn remove(&self, key: &K) -> Option<V> {
        let mut cache = self.cache.write().await;
        let mut access_order = self.access_order.write().await;
        
        if let Some(entry) = cache.remove(key) {
            access_order.retain(|k| k != key);
            Some(entry.value)
        } else {
            None
        }
    }
    
    pub async fn clear(&self) {
        let mut cache = self.cache.write().await;
        let mut access_order = self.access_order.write().await;
        
        cache.clear();
        access_order.clear();
    }
    
    pub async fn size(&self) -> usize {
        let cache = self.cache.read().await;
        cache.len()
    }
    
    pub async fn get_stats(&self) -> CacheStats {
        let cache = self.cache.read().await;
        let access_order = self.access_order.read().await;
        
        let total_accesses: u64 = cache.values().map(|entry| entry.access_count).sum();
        let avg_access_count = if cache.is_empty() {
            0.0
        } else {
            total_accesses as f64 / cache.len() as f64
        };
        
        CacheStats {
            size: cache.len(),
            capacity: self.capacity,
            total_accesses,
            avg_access_count,
            hit_rate: 0.0, // 需要额外统计
        }
    }
}

#[derive(Debug)]
pub struct CacheStats {
    pub size: usize,
    pub capacity: usize,
    pub total_accesses: u64,
    pub avg_access_count: f64,
    pub hit_rate: f64,
}
```

## 4. 实际应用示例

### 4.1 完整的OTLP处理系统

```rust
use tokio::sync::mpsc;
use std::sync::Arc;

/// 完整的OTLP处理系统
pub struct OtlpProcessingSystem {
    // 组件
    strategy_manager: DataProcessingStrategyManager,
    event_bus: OtlpEventBus,
    load_balancer: WeightedRoundRobinBalancer,
    aggregator: TimeWindowAggregator,
    cache: LruCache<String, TelemetryData>,
    
    // 通道
    input_receiver: mpsc::UnboundedReceiver<TelemetryData>,
    output_sender: mpsc::UnboundedSender<ProcessedData>,
    
    // 配置
    config: SystemConfig,
}

#[derive(Debug, Clone)]
pub struct SystemConfig {
    pub max_concurrent_requests: usize,
    pub batch_size: usize,
    pub processing_timeout: Duration,
    pub cache_capacity: usize,
    pub aggregation_window: Duration,
}

impl OtlpProcessingSystem {
    pub async fn new(config: SystemConfig) -> Result<Self, OtlpError> {
        // 创建通道
        let (input_sender, input_receiver) = mpsc::unbounded_channel();
        let (output_sender, output_receiver) = mpsc::unbounded_channel();
        
        // 创建策略管理器
        let mut strategy_manager = DataProcessingStrategyManager::new();
        strategy_manager.add_strategy(Arc::new(DataValidationStrategy::new()));
        strategy_manager.add_strategy(Arc::new(DataCompressionStrategy::new(
            CompressionAlgorithm::Gzip
        )));
        
        // 创建事件总线
        let event_bus = OtlpEventBus::new();
        
        // 创建负载均衡器
        let endpoints = vec![
            LoadBalancerEndpoint {
                url: "http://localhost:4317".to_string(),
                weight: 1,
                health_status: HealthStatus::Healthy,
                response_time: Duration::from_millis(50),
                error_count: 0,
                success_count: 0,
            },
        ];
        let load_balancer = WeightedRoundRobinBalancer::new(endpoints);
        
        // 创建聚合器
        let aggregator = TimeWindowAggregator::new(config.aggregation_window);
        
        // 创建缓存
        let cache = LruCache::new(config.cache_capacity);
        
        Ok(Self {
            strategy_manager,
            event_bus,
            load_balancer,
            aggregator,
            cache,
            input_receiver,
            output_sender,
            config,
        })
    }
    
    /// 启动处理系统
    pub async fn start(&mut self) -> Result<(), OtlpError> {
        let mut receiver = std::mem::replace(&mut self.input_receiver, mpsc::unbounded_channel().1);
        let sender = self.output_sender.clone();
        let strategy_manager = self.strategy_manager.clone();
        let event_bus = self.event_bus.clone();
        let aggregator = self.aggregator.clone();
        let cache = self.cache.clone();
        let config = self.config.clone();
        
        // 启动处理协程
        tokio::spawn(async move {
            while let Some(data) = receiver.recv().await {
                // 处理数据
                match strategy_manager.process_data(data.clone()).await {
                    Ok(processed_data) => {
                        // 发布事件
                        event_bus.publish_trace(processed_data.clone().into()).await;
                        
                        // 添加到聚合器
                        aggregator.add_data(&processed_data).await.unwrap();
                        
                        // 缓存结果
                        cache.put(processed_data.get_id(), processed_data.clone()).await;
                        
                        // 发送到输出
                        let result = ProcessedData {
                            data: processed_data,
                            processed_at: Instant::now(),
                        };
                        let _ = sender.send(result);
                    }
                    Err(e) => {
                        event_bus.publish_error(e).await;
                    }
                }
            }
        });
        
        Ok(())
    }
    
    /// 发送数据到系统
    pub async fn send_data(&self, data: TelemetryData) -> Result<(), OtlpError> {
        // 这里需要重新获取sender，为了简化示例，我们假设有全局访问
        // 在实际实现中，需要更好的设计
        Ok(())
    }
}
```

## 5. 总结

本文档深入分析了OTLP相关的核心算法和设计模式，包括：

1. **核心算法**:
   - 自适应采样算法
   - 时间窗口聚合算法
   - 负载均衡算法
   - 内存优化算法
   - 缓存优化算法

2. **设计模式**:
   - 策略模式：灵活的数据处理策略
   - 观察者模式：事件驱动的架构
   - 工厂模式：组件创建和管理

3. **优化策略**:
   - 内存池管理
   - LRU缓存实现
   - 性能监控和调优

这些算法和设计模式为构建高性能、可扩展的OTLP处理系统提供了坚实的基础，充分利用了Rust 1.90的语言特性，实现了类型安全、内存安全和并发安全。

---

*本文档为OTLP算法与设计模式提供了全面的技术分析和实践指导，适用于构建企业级的可观测性系统。*
