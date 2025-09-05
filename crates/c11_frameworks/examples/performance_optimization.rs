//! 性能优化示例
//! 
//! 展示Rust应用性能优化的各种技术和最佳实践，包括：
//! - 内存池和对象池
//! - 连接池管理
//! - 缓存策略和实现
//! - 零拷贝优化
//! - 并行计算
//! - 内存映射文件
//! - 性能分析和基准测试

use std::{
    collections::{HashMap, VecDeque},
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, Mutex, RwLock,
    },
    time::{Duration, Instant},
    thread,
    mem,
    slice,
};
use tokio::{
    sync::{Semaphore, Mutex as AsyncMutex},
    time::{sleep, timeout},
    task::JoinHandle,
};
use serde::{Deserialize, Serialize};
use tracing::{info, warn, error, debug};
use memmap2::{Mmap, MmapOptions};
use rayon::prelude::*;
use dashmap::DashMap;
use lru::LruCache;
use crossbeam::{
    channel::{bounded, unbounded, Receiver, Sender},
    queue::SegQueue,
};
use parking_lot::{Mutex as ParkingMutex, RwLock as ParkingRwLock};

/// 对象池
pub struct ObjectPool<T> {
    objects: SegQueue<T>,
    factory: Box<dyn Fn() -> T + Send + Sync>,
    max_size: usize,
    current_size: AtomicUsize,
}

/// 连接池
pub struct ConnectionPool<T> {
    connections: SegQueue<T>,
    factory: Box<dyn Fn() -> Result<T, String> + Send + Sync>,
    max_connections: usize,
    current_connections: AtomicUsize,
    semaphore: Semaphore,
}

/// 多级缓存
pub struct MultiLevelCache<K, V> {
    l1_cache: Arc<ParkingMutex<LruCache<K, V>>>,
    l2_cache: Arc<DashMap<K, V>>,
    l3_cache: Arc<DashMap<K, V>>,
    hit_counts: Arc<DashMap<K, AtomicUsize>>,
}

/// 内存池
pub struct MemoryPool {
    pools: Vec<Arc<SegQueue<Vec<u8>>>>,
    pool_sizes: Vec<usize>,
    max_pools: usize,
}

/// 零拷贝缓冲区
pub struct ZeroCopyBuffer {
    data: Vec<u8>,
    position: AtomicUsize,
    capacity: usize,
}

/// 并行计算器
pub struct ParallelComputer {
    thread_pool: rayon::ThreadPool,
    max_threads: usize,
}

/// 内存映射文件管理器
pub struct MmapFileManager {
    files: Arc<DashMap<String, Arc<Mmap>>>,
    cache_size: usize,
}

/// 性能分析器
pub struct PerformanceProfiler {
    metrics: Arc<DashMap<String, PerformanceMetric>>,
    start_time: Instant,
}

/// 性能指标
#[derive(Debug, Clone)]
pub struct PerformanceMetric {
    pub name: String,
    pub count: AtomicUsize,
    pub total_time: AtomicUsize,
    pub min_time: AtomicUsize,
    pub max_time: AtomicUsize,
    pub avg_time: f64,
}

/// 基准测试结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkResult {
    pub name: String,
    pub iterations: usize,
    pub total_time: Duration,
    pub avg_time: Duration,
    pub min_time: Duration,
    pub max_time: Duration,
    pub throughput: f64,
}

/// 缓存策略
#[derive(Debug, Clone)]
pub enum CacheStrategy {
    LRU,
    LFU,
    FIFO,
    TTL(Duration),
}

/// 连接池配置
#[derive(Debug, Clone)]
pub struct ConnectionPoolConfig {
    pub max_connections: usize,
    pub min_connections: usize,
    pub connection_timeout: Duration,
    pub idle_timeout: Duration,
    pub health_check_interval: Duration,
}

impl<T> ObjectPool<T>
where
    T: Send + 'static,
{
    pub fn new<F>(factory: F, max_size: usize) -> Self
    where
        F: Fn() -> T + Send + Sync + 'static,
    {
        Self {
            objects: SegQueue::new(),
            factory: Box::new(factory),
            max_size,
            current_size: AtomicUsize::new(0),
        }
    }
    
    /// 获取对象
    pub fn get(&self) -> Option<T> {
        self.objects.pop()
    }
    
    /// 返回对象
    pub fn put(&self, obj: T) {
        if self.current_size.load(Ordering::Relaxed) < self.max_size {
            self.objects.push(obj);
            self.current_size.fetch_add(1, Ordering::Relaxed);
        }
    }
    
    /// 创建新对象
    pub fn create(&self) -> T {
        (self.factory)()
    }
    
    /// 获取当前大小
    pub fn size(&self) -> usize {
        self.current_size.load(Ordering::Relaxed)
    }
}

impl<T> ConnectionPool<T>
where
    T: Send + 'static,
{
    pub fn new<F>(factory: F, max_connections: usize) -> Self
    where
        F: Fn() -> Result<T, String> + Send + Sync + 'static,
    {
        Self {
            connections: SegQueue::new(),
            factory: Box::new(factory),
            max_connections,
            current_connections: AtomicUsize::new(0),
            semaphore: Semaphore::new(max_connections),
        }
    }
    
    /// 获取连接
    pub async fn get_connection(&self) -> Result<PooledConnection<T>, String> {
        let _permit = self.semaphore.acquire().await.map_err(|e| e.to_string())?;
        
        if let Some(connection) = self.connections.pop() {
            Ok(PooledConnection {
                connection: Some(connection),
                pool: self,
            })
        } else {
            let connection = (self.factory)()?;
            self.current_connections.fetch_add(1, Ordering::Relaxed);
            Ok(PooledConnection {
                connection: Some(connection),
                pool: self,
            })
        }
    }
    
    /// 返回连接
    fn return_connection(&self, connection: T) {
        if self.current_connections.load(Ordering::Relaxed) <= self.max_connections {
            self.connections.push(connection);
        }
    }
    
    /// 获取当前连接数
    pub fn current_connections(&self) -> usize {
        self.current_connections.load(Ordering::Relaxed)
    }
}

/// 池化连接
pub struct PooledConnection<'a, T> {
    connection: Option<T>,
    pool: &'a ConnectionPool<T>,
}

impl<'a, T> Drop for PooledConnection<'a, T> {
    fn drop(&mut self) {
        if let Some(connection) = self.connection.take() {
            self.pool.return_connection(connection);
        }
    }
}

impl<'a, T> std::ops::Deref for PooledConnection<'a, T> {
    type Target = T;
    
    fn deref(&self) -> &Self::Target {
        self.connection.as_ref().unwrap()
    }
}

impl<'a, T> std::ops::DerefMut for PooledConnection<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.connection.as_mut().unwrap()
    }
}

impl<K, V> MultiLevelCache<K, V>
where
    K: Clone + std::hash::Hash + Eq + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    pub fn new(l1_size: usize) -> Self {
        Self {
            l1_cache: Arc::new(ParkingMutex::new(LruCache::new(l1_size))),
            l2_cache: Arc::new(DashMap::new()),
            l3_cache: Arc::new(DashMap::new()),
            hit_counts: Arc::new(DashMap::new()),
        }
    }
    
    /// 获取值
    pub fn get(&self, key: &K) -> Option<V> {
        // L1缓存查找
        {
            let mut l1 = self.l1_cache.lock();
            if let Some(value) = l1.get(key) {
                self.hit_counts.entry(key.clone()).or_insert(AtomicUsize::new(0)).fetch_add(1, Ordering::Relaxed);
                return Some(value.clone());
            }
        }
        
        // L2缓存查找
        if let Some(value) = self.l2_cache.get(key) {
            let mut l1 = self.l1_cache.lock();
            l1.put(key.clone(), value.clone());
            self.hit_counts.entry(key.clone()).or_insert(AtomicUsize::new(0)).fetch_add(1, Ordering::Relaxed);
            return Some(value.clone());
        }
        
        // L3缓存查找
        if let Some(value) = self.l3_cache.get(key) {
            let mut l1 = self.l1_cache.lock();
            l1.put(key.clone(), value.clone());
            self.l2_cache.insert(key.clone(), value.clone());
            self.hit_counts.entry(key.clone()).or_insert(AtomicUsize::new(0)).fetch_add(1, Ordering::Relaxed);
            return Some(value.clone());
        }
        
        None
    }
    
    /// 设置值
    pub fn set(&self, key: K, value: V) {
        let mut l1 = self.l1_cache.lock();
        l1.put(key.clone(), value.clone());
        self.l2_cache.insert(key.clone(), value.clone());
        self.l3_cache.insert(key, value);
    }
    
    /// 获取命中率
    pub fn hit_rate(&self) -> f64 {
        let total_hits: usize = self.hit_counts.iter().map(|entry| entry.value().load(Ordering::Relaxed)).sum();
        let total_requests = self.l1_cache.lock().len() + self.l2_cache.len() + self.l3_cache.len();
        
        if total_requests == 0 {
            0.0
        } else {
            total_hits as f64 / total_requests as f64
        }
    }
}

impl MemoryPool {
    pub fn new(max_pools: usize) -> Self {
        let mut pools = Vec::new();
        let mut pool_sizes = Vec::new();
        
        // 创建不同大小的内存池
        for i in 0..max_pools {
            let size = 2usize.pow(i as u32 + 4); // 16, 32, 64, 128, ...
            pools.push(Arc::new(SegQueue::new()));
            pool_sizes.push(size);
        }
        
        Self {
            pools,
            pool_sizes,
            max_pools,
        }
    }
    
    /// 分配内存
    pub fn allocate(&self, size: usize) -> Vec<u8> {
        // 找到合适的内存池
        for (i, &pool_size) in self.pool_sizes.iter().enumerate() {
            if size <= pool_size {
                if let Some(mut buffer) = self.pools[i].pop() {
                    buffer.clear();
                    buffer.reserve(size);
                    return buffer;
                }
            }
        }
        
        // 如果没有找到合适的池，创建新的缓冲区
        Vec::with_capacity(size)
    }
    
    /// 释放内存
    pub fn deallocate(&self, mut buffer: Vec<u8>) {
        let size = buffer.capacity();
        
        // 找到合适的内存池
        for (i, &pool_size) in self.pool_sizes.iter().enumerate() {
            if size <= pool_size {
                self.pools[i].push(buffer);
                return;
            }
        }
        
        // 如果缓冲区太大，直接丢弃
    }
}

impl ZeroCopyBuffer {
    pub fn new(capacity: usize) -> Self {
        Self {
            data: vec![0u8; capacity],
            position: AtomicUsize::new(0),
            capacity,
        }
    }
    
    /// 写入数据
    pub fn write(&self, data: &[u8]) -> Result<usize, String> {
        let pos = self.position.load(Ordering::Relaxed);
        let remaining = self.capacity - pos;
        
        if data.len() > remaining {
            return Err("缓冲区空间不足".to_string());
        }
        
        unsafe {
            let ptr = self.data.as_ptr().add(pos);
            std::ptr::copy_nonoverlapping(data.as_ptr(), ptr, data.len());
        }
        
        self.position.fetch_add(data.len(), Ordering::Relaxed);
        Ok(data.len())
    }
    
    /// 读取数据
    pub fn read(&self, buffer: &mut [u8]) -> Result<usize, String> {
        let pos = self.position.load(Ordering::Relaxed);
        let remaining = self.capacity - pos;
        
        if buffer.len() > remaining {
            return Err("没有足够的数据可读".to_string());
        }
        
        unsafe {
            let ptr = self.data.as_ptr().add(pos);
            std::ptr::copy_nonoverlapping(ptr, buffer.as_mut_ptr(), buffer.len());
        }
        
        self.position.fetch_add(buffer.len(), Ordering::Relaxed);
        Ok(buffer.len())
    }
    
    /// 获取当前位置
    pub fn position(&self) -> usize {
        self.position.load(Ordering::Relaxed)
    }
    
    /// 重置位置
    pub fn reset(&self) {
        self.position.store(0, Ordering::Relaxed);
    }
}

impl ParallelComputer {
    pub fn new(max_threads: usize) -> Self {
        let thread_pool = rayon::ThreadPoolBuilder::new()
            .num_threads(max_threads)
            .build()
            .expect("创建线程池失败");
        
        Self {
            thread_pool,
            max_threads,
        }
    }
    
    /// 并行处理数据
    pub fn parallel_map<T, R, F>(&self, data: Vec<T>, mapper: F) -> Vec<R>
    where
        T: Send,
        R: Send,
        F: Fn(T) -> R + Sync + Send,
    {
        data.into_par_iter().map(mapper).collect()
    }
    
    /// 并行归约
    pub fn parallel_reduce<T, F>(&self, data: Vec<T>, reducer: F) -> T
    where
        T: Send + Sync + Clone,
        F: Fn(T, T) -> T + Sync + Send,
    {
        data.into_par_iter().reduce(|| data[0].clone(), reducer)
    }
    
    /// 并行过滤
    pub fn parallel_filter<T, F>(&self, data: Vec<T>, predicate: F) -> Vec<T>
    where
        T: Send,
        F: Fn(&T) -> bool + Sync + Send,
    {
        data.into_par_iter().filter(predicate).collect()
    }
}

impl MmapFileManager {
    pub fn new(cache_size: usize) -> Self {
        Self {
            files: Arc::new(DashMap::new()),
            cache_size,
        }
    }
    
    /// 打开文件
    pub fn open_file(&self, path: &str) -> Result<Arc<Mmap>, String> {
        if let Some(mmap) = self.files.get(path) {
            return Ok(mmap.clone());
        }
        
        let file = std::fs::File::open(path)
            .map_err(|e| format!("打开文件失败: {}", e))?;
        
        let mmap = unsafe {
            MmapOptions::new()
                .map(&file)
                .map_err(|e| format!("内存映射失败: {}", e))?
        };
        
        let mmap = Arc::new(mmap);
        self.files.insert(path.to_string(), mmap.clone());
        
        Ok(mmap)
    }
    
    /// 关闭文件
    pub fn close_file(&self, path: &str) {
        self.files.remove(path);
    }
    
    /// 清理缓存
    pub fn cleanup(&self) {
        if self.files.len() > self.cache_size {
            // 简单的LRU清理策略
            let keys_to_remove: Vec<String> = self.files
                .iter()
                .take(self.files.len() - self.cache_size)
                .map(|entry| entry.key().clone())
                .collect();
            
            for key in keys_to_remove {
                self.files.remove(&key);
            }
        }
    }
}

impl PerformanceProfiler {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(DashMap::new()),
            start_time: Instant::now(),
        }
    }
    
    /// 开始计时
    pub fn start_timer(&self, name: &str) -> PerformanceTimer {
        PerformanceTimer {
            profiler: self.clone(),
            name: name.to_string(),
            start_time: Instant::now(),
        }
    }
    
    /// 记录指标
    pub fn record_metric(&self, name: &str, duration: Duration) {
        let metric = self.metrics.entry(name.to_string()).or_insert(PerformanceMetric {
            name: name.to_string(),
            count: AtomicUsize::new(0),
            total_time: AtomicUsize::new(0),
            min_time: AtomicUsize::new(u64::MAX as usize),
            max_time: AtomicUsize::new(0),
            avg_time: 0.0,
        });
        
        let duration_ns = duration.as_nanos() as usize;
        metric.count.fetch_add(1, Ordering::Relaxed);
        metric.total_time.fetch_add(duration_ns, Ordering::Relaxed);
        
        let mut min_time = metric.min_time.load(Ordering::Relaxed);
        while min_time > duration_ns {
            match metric.min_time.compare_exchange_weak(
                min_time,
                duration_ns,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(x) => min_time = x,
            }
        }
        
        let mut max_time = metric.max_time.load(Ordering::Relaxed);
        while max_time < duration_ns {
            match metric.max_time.compare_exchange_weak(
                max_time,
                duration_ns,
                Ordering::Relaxed,
                Ordering::Relaxed,
            ) {
                Ok(_) => break,
                Err(x) => max_time = x,
            }
        }
        
        // 更新平均值
        let count = metric.count.load(Ordering::Relaxed);
        let total_time = metric.total_time.load(Ordering::Relaxed);
        metric.avg_time = total_time as f64 / count as f64;
    }
    
    /// 获取指标
    pub fn get_metrics(&self) -> HashMap<String, PerformanceMetric> {
        self.metrics.iter().map(|entry| (entry.key().clone(), entry.value().clone())).collect()
    }
    
    /// 重置指标
    pub fn reset(&self) {
        self.metrics.clear();
    }
}

impl Clone for PerformanceProfiler {
    fn clone(&self) -> Self {
        Self {
            metrics: self.metrics.clone(),
            start_time: self.start_time,
        }
    }
}

/// 性能计时器
pub struct PerformanceTimer {
    profiler: PerformanceProfiler,
    name: String,
    start_time: Instant,
}

impl Drop for PerformanceTimer {
    fn drop(&mut self) {
        let duration = self.start_time.elapsed();
        self.profiler.record_metric(&self.name, duration);
    }
}

/// 基准测试
pub struct Benchmark {
    name: String,
    iterations: usize,
    warmup_iterations: usize,
}

impl Benchmark {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            iterations: 1000,
            warmup_iterations: 100,
        }
    }
    
    pub fn iterations(mut self, iterations: usize) -> Self {
        self.iterations = iterations;
        self
    }
    
    pub fn warmup_iterations(mut self, warmup_iterations: usize) -> Self {
        self.warmup_iterations = warmup_iterations;
        self
    }
    
    /// 运行基准测试
    pub fn run<F>(&self, mut function: F) -> BenchmarkResult
    where
        F: FnMut() -> Result<(), String>,
    {
        // 预热
        for _ in 0..self.warmup_iterations {
            let _ = function();
        }
        
        // 运行测试
        let mut times = Vec::with_capacity(self.iterations);
        
        for _ in 0..self.iterations {
            let start = Instant::now();
            let _ = function();
            let duration = start.elapsed();
            times.push(duration);
        }
        
        // 计算统计信息
        let total_time: Duration = times.iter().sum();
        let avg_time = total_time / times.len() as u32;
        let min_time = times.iter().min().copied().unwrap_or_default();
        let max_time = times.iter().max().copied().unwrap_or_default();
        let throughput = self.iterations as f64 / total_time.as_secs_f64();
        
        BenchmarkResult {
            name: self.name.clone(),
            iterations: self.iterations,
            total_time,
            avg_time,
            min_time,
            max_time,
            throughput,
        }
    }
}

/// 内存使用统计
pub struct MemoryStats {
    pub allocated: usize,
    pub deallocated: usize,
    pub peak: usize,
    pub current: usize,
}

impl MemoryStats {
    pub fn new() -> Self {
        Self {
            allocated: 0,
            deallocated: 0,
            peak: 0,
            current: 0,
        }
    }
    
    pub fn allocate(&mut self, size: usize) {
        self.allocated += size;
        self.current += size;
        if self.current > self.peak {
            self.peak = self.current;
        }
    }
    
    pub fn deallocate(&mut self, size: usize) {
        self.deallocated += size;
        self.current = self.current.saturating_sub(size);
    }
}

/// 性能优化示例
async fn object_pool_example() -> Result<(), String> {
    info!("开始对象池示例");
    
    let pool = ObjectPool::new(|| String::new(), 100);
    
    // 使用对象池
    for i in 0..1000 {
        let mut obj = pool.get().unwrap_or_else(|| pool.create());
        obj.push_str(&format!("Item {}", i));
        
        // 模拟使用对象
        sleep(Duration::from_micros(1)).await;
        
        pool.put(obj);
    }
    
    info!("对象池大小: {}", pool.size());
    Ok(())
}

/// 连接池示例
async fn connection_pool_example() -> Result<(), String> {
    info!("开始连接池示例");
    
    let pool = ConnectionPool::new(
        || {
            // 模拟创建连接
            Ok(format!("Connection-{}", uuid::Uuid::new_v4()))
        },
        10,
    );
    
    // 并发使用连接
    let mut handles = Vec::new();
    for i in 0..50 {
        let pool = pool.clone();
        let handle = tokio::spawn(async move {
            let connection = pool.get_connection().await.unwrap();
            // 模拟使用连接
            sleep(Duration::from_millis(10)).await;
            info!("使用连接: {}", *connection);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.await.unwrap();
    }
    
    info!("当前连接数: {}", pool.current_connections());
    Ok(())
}

/// 多级缓存示例
async fn multi_level_cache_example() -> Result<(), String> {
    info!("开始多级缓存示例");
    
    let cache = MultiLevelCache::new(100);
    
    // 填充缓存
    for i in 0..1000 {
        cache.set(i, format!("Value-{}", i));
    }
    
    // 测试缓存命中
    for i in 0..100 {
        let value = cache.get(&i);
        assert!(value.is_some());
    }
    
    info!("缓存命中率: {:.2}%", cache.hit_rate() * 100.0);
    Ok(())
}

/// 内存池示例
async fn memory_pool_example() -> Result<(), String> {
    info!("开始内存池示例");
    
    let pool = MemoryPool::new(10);
    
    // 分配和释放内存
    for i in 0..1000 {
        let buffer = pool.allocate(1024);
        // 模拟使用内存
        sleep(Duration::from_micros(1)).await;
        pool.deallocate(buffer);
    }
    
    Ok(())
}

/// 零拷贝示例
async fn zero_copy_example() -> Result<(), String> {
    info!("开始零拷贝示例");
    
    let buffer = ZeroCopyBuffer::new(1024);
    
    // 写入数据
    let data = b"Hello, World!";
    buffer.write(data)?;
    
    // 读取数据
    let mut read_buffer = vec![0u8; data.len()];
    buffer.read(&mut read_buffer)?;
    
    assert_eq!(data, read_buffer.as_slice());
    Ok(())
}

/// 并行计算示例
async fn parallel_computation_example() -> Result<(), String> {
    info!("开始并行计算示例");
    
    let computer = ParallelComputer::new(4);
    
    // 并行处理数据
    let data: Vec<i32> = (0..1000000).collect();
    let results = computer.parallel_map(data, |x| x * x);
    
    info!("处理了 {} 个数据项", results.len());
    
    // 并行归约
    let sum = computer.parallel_reduce(results, |a, b| a + b);
    info!("平方和: {}", sum);
    
    Ok(())
}

/// 内存映射文件示例
async fn mmap_file_example() -> Result<(), String> {
    info!("开始内存映射文件示例");
    
    let manager = MmapFileManager::new(10);
    
    // 创建测试文件
    let test_data = "Hello, Memory Mapped File!".repeat(1000);
    std::fs::write("test.txt", &test_data)?;
    
    // 打开文件
    let mmap = manager.open_file("test.txt")?;
    
    // 读取数据
    let data = &mmap[..100];
    info!("读取数据: {}", String::from_utf8_lossy(data));
    
    // 清理
    std::fs::remove_file("test.txt")?;
    Ok(())
}

/// 性能分析示例
async fn performance_profiling_example() -> Result<(), String> {
    info!("开始性能分析示例");
    
    let profiler = PerformanceProfiler::new();
    
    // 模拟一些操作
    for i in 0..100 {
        let _timer = profiler.start_timer("operation");
        sleep(Duration::from_millis(1)).await;
    }
    
    // 获取指标
    let metrics = profiler.get_metrics();
    for (name, metric) in metrics {
        info!("指标 {}: 调用次数={}, 平均时间={:.2}ns", 
              name, metric.count.load(Ordering::Relaxed), metric.avg_time);
    }
    
    Ok(())
}

/// 基准测试示例
async fn benchmark_example() -> Result<(), String> {
    info!("开始基准测试示例");
    
    let benchmark = Benchmark::new("string_concatenation")
        .iterations(10000)
        .warmup_iterations(100);
    
    let result = benchmark.run(|| {
        let mut s = String::new();
        for i in 0..100 {
            s.push_str(&format!("{}", i));
        }
        Ok(())
    });
    
    info!("基准测试结果: {:?}", result);
    Ok(())
}

/// 内存统计示例
async fn memory_stats_example() -> Result<(), String> {
    info!("开始内存统计示例");
    
    let mut stats = MemoryStats::new();
    
    // 模拟内存分配
    for i in 0..1000 {
        let size = (i % 100) + 1;
        stats.allocate(size);
        
        if i % 100 == 0 {
            info!("分配了 {} 字节内存", size);
        }
    }
    
    // 模拟内存释放
    for i in 0..500 {
        let size = (i % 100) + 1;
        stats.deallocate(size);
    }
    
    info!("内存统计: 分配={}, 释放={}, 峰值={}, 当前={}", 
          stats.allocated, stats.deallocated, stats.peak, stats.current);
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    info!("开始性能优化示例");
    
    // 运行各种示例
    object_pool_example().await?;
    connection_pool_example().await?;
    multi_level_cache_example().await?;
    memory_pool_example().await?;
    zero_copy_example().await?;
    parallel_computation_example().await?;
    mmap_file_example().await?;
    performance_profiling_example().await?;
    benchmark_example().await?;
    memory_stats_example().await?;
    
    info!("所有性能优化示例完成");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_object_pool() {
        let pool = ObjectPool::new(|| String::new(), 10);
        
        let obj1 = pool.get().unwrap_or_else(|| pool.create());
        let obj2 = pool.get().unwrap_or_else(|| pool.create());
        
        pool.put(obj1);
        pool.put(obj2);
        
        assert_eq!(pool.size(), 2);
    }
    
    #[test]
    fn test_multi_level_cache() {
        let cache = MultiLevelCache::new(10);
        
        cache.set("key1", "value1");
        assert_eq!(cache.get(&"key1"), Some("value1".to_string()));
        assert_eq!(cache.get(&"key2"), None);
    }
    
    #[test]
    fn test_zero_copy_buffer() {
        let buffer = ZeroCopyBuffer::new(100);
        
        let data = b"test data";
        buffer.write(data).unwrap();
        
        let mut read_buffer = vec![0u8; data.len()];
        buffer.read(&mut read_buffer).unwrap();
        
        assert_eq!(data, read_buffer.as_slice());
    }
    
    #[test]
    fn test_benchmark() {
        let benchmark = Benchmark::new("test")
            .iterations(100)
            .warmup_iterations(10);
        
        let result = benchmark.run(|| {
            let _ = 1 + 1;
            Ok(())
        });
        
        assert_eq!(result.iterations, 100);
        assert!(result.throughput > 0.0);
    }
    
    #[test]
    fn test_memory_stats() {
        let mut stats = MemoryStats::new();
        
        stats.allocate(100);
        stats.allocate(200);
        stats.deallocate(50);
        
        assert_eq!(stats.allocated, 300);
        assert_eq!(stats.deallocated, 50);
        assert_eq!(stats.current, 250);
        assert_eq!(stats.peak, 300);
    }
}
