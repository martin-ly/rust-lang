# C10 Networks 性能优化指南

> 适用范围：Rust 1.90+，Tokio 1.35+。文档风格遵循 [`STYLE.md`](STYLE.md)。

## 📋 目录

- [C10 Networks 性能优化指南](#c10-networks-性能优化指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [⚡ 异步I/O优化](#-异步io优化)
    - [Tokio运行时优化](#tokio运行时优化)
    - [零拷贝优化](#零拷贝优化)
    - [异步流优化](#异步流优化)
  - [💾 内存管理优化](#-内存管理优化)
    - [内存池管理](#内存池管理)
    - [内存映射优化](#内存映射优化)
    - [缓存优化](#缓存优化)
  - [🌐 网络协议优化](#-网络协议优化)
    - [TCP优化](#tcp优化)
    - [HTTP/2优化](#http2优化)
    - [WebSocket优化](#websocket优化)
  - [🔄 并发处理优化](#-并发处理优化)
    - [工作窃取调度](#工作窃取调度)
    - [无锁数据结构](#无锁数据结构)
  - [📊 性能监控](#-性能监控)
    - [性能指标收集](#性能指标收集)
    - [实时监控](#实时监控)
  - [🧪 基准测试](#-基准测试)
    - [基准测试框架](#基准测试框架)
    - [压力测试](#压力测试)
  - [🔧 调优工具](#-调优工具)
    - [性能分析器](#性能分析器)
  - [📈 性能指标](#-性能指标)
    - [关键性能指标](#关键性能指标)

## 🎯 概述

本指南提供了C10 Networks性能优化的全面方法，包括异步I/O、内存管理、网络协议、并发处理等方面的优化策略。

## ⚡ 异步I/O优化

### Tokio运行时优化

```rust
// 自定义Tokio运行时配置
pub fn create_optimized_runtime() -> tokio::runtime::Runtime {
    tokio::runtime::Builder::new_multi_thread()
        .worker_threads(num_cpus::get())
        .max_blocking_threads(512)
        .thread_stack_size(3 * 1024 * 1024) // 3MB
        .enable_all()
        .build()
        .unwrap()
}

// 异步任务调度优化
pub struct OptimizedTaskScheduler {
    cpu_intensive_pool: ThreadPool,
    io_intensive_pool: ThreadPool,
    blocking_pool: ThreadPool,
}

impl OptimizedTaskScheduler {
    pub fn new() -> Self {
        Self {
            cpu_intensive_pool: ThreadPool::new(num_cpus::get()),
            io_intensive_pool: ThreadPool::new(num_cpus::get() * 2),
            blocking_pool: ThreadPool::new(512),
        }
    }
    
    pub async fn spawn_cpu_intensive<F, T>(&self, task: F) -> JoinHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        self.cpu_intensive_pool.spawn(task)
    }
    
    pub async fn spawn_io_intensive<F, T>(&self, task: F) -> JoinHandle<T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static,
    {
        self.io_intensive_pool.spawn(task)
    }
}
```

### 零拷贝优化

```rust
// 零拷贝缓冲区
pub struct ZeroCopyBuffer {
    data: Vec<u8>,
    read_pos: usize,
    write_pos: usize,
    capacity: usize,
}

impl ZeroCopyBuffer {
    pub fn new(capacity: usize) -> Self {
        Self {
            data: vec![0; capacity],
            read_pos: 0,
            write_pos: 0,
            capacity,
        }
    }
    
    // 使用IoSlice进行零拷贝写入
    pub fn write_vectored(&mut self, slices: &[IoSlice]) -> NetworkResult<usize> {
        let mut total_written = 0;
        
        for slice in slices {
            let available = self.capacity - self.write_pos;
            let to_write = slice.len().min(available);
            
            if to_write > 0 {
                self.data[self.write_pos..self.write_pos + to_write]
                    .copy_from_slice(&slice[..to_write]);
                self.write_pos += to_write;
                total_written += to_write;
            }
            
            if to_write < slice.len() {
                break;
            }
        }
        
        Ok(total_written)
    }
    
    // 使用Bytes进行零拷贝读取
    pub fn read_bytes(&mut self, len: usize) -> NetworkResult<Bytes> {
        let available = self.write_pos - self.read_pos;
        let to_read = len.min(available);
        
        if to_read > 0 {
            let data = Bytes::copy_from_slice(&self.data[self.read_pos..self.read_pos + to_read]);
            self.read_pos += to_read;
            Ok(data)
        } else {
            Ok(Bytes::new())
        }
    }
}
```

### 异步流优化

```rust
// 高性能异步流
pub struct OptimizedAsyncStream {
    buffer: Arc<Mutex<VecDeque<Bytes>>>,
    sender: mpsc::UnboundedSender<Bytes>,
    receiver: mpsc::UnboundedReceiver<Bytes>,
    batch_size: usize,
    flush_interval: Duration,
}

impl OptimizedAsyncStream {
    pub fn new(batch_size: usize, flush_interval: Duration) -> Self {
        let (sender, receiver) = mpsc::unbounded_channel();
        
        Self {
            buffer: Arc::new(Mutex::new(VecDeque::new())),
            sender,
            receiver,
            batch_size,
            flush_interval,
        }
    }
    
    // 批量处理消息
    pub async fn process_batch(&mut self) -> NetworkResult<Vec<Bytes>> {
        let mut batch = Vec::with_capacity(self.batch_size);
        let timeout = tokio::time::sleep(self.flush_interval);
        
        tokio::select! {
            _ = timeout => {
                // 超时，处理当前批次
            }
            message = self.receiver.recv() => {
                if let Some(msg) = message {
                    batch.push(msg);
                    
                    // 继续收集直到批次满
                    while batch.len() < self.batch_size {
                        match self.receiver.try_recv() {
                            Ok(msg) => batch.push(msg),
                            Err(_) => break,
                        }
                    }
                }
            }
        }
        
        Ok(batch)
    }
}
```

## 💾 内存管理优化

### 内存池管理

```rust
// 对象池
pub struct ObjectPool<T> {
    objects: Arc<Mutex<Vec<T>>>,
    factory: Arc<dyn Fn() -> T + Send + Sync>,
    max_size: usize,
}

impl<T> ObjectPool<T> {
    pub fn new<F>(factory: F, max_size: usize) -> Self
    where
        F: Fn() -> T + Send + Sync + 'static,
    {
        Self {
            objects: Arc::new(Mutex::new(Vec::new())),
            factory: Arc::new(factory),
            max_size,
        }
    }
    
    pub fn get(&self) -> PooledObject<T> {
        let mut objects = self.objects.lock().unwrap();
        
        if let Some(obj) = objects.pop() {
            PooledObject::new(obj, self.objects.clone())
        } else {
            PooledObject::new((self.factory)(), self.objects.clone())
        }
    }
}

// 池化对象
pub struct PooledObject<T> {
    object: Option<T>,
    pool: Arc<Mutex<Vec<T>>>,
}

impl<T> PooledObject<T> {
    fn new(object: T, pool: Arc<Mutex<Vec<T>>>) -> Self {
        Self {
            object: Some(object),
            pool,
        }
    }
    
    pub fn as_ref(&self) -> &T {
        self.object.as_ref().unwrap()
    }
    
    pub fn as_mut(&mut self) -> &mut T {
        self.object.as_mut().unwrap()
    }
}

impl<T> Drop for PooledObject<T> {
    fn drop(&mut self) {
        if let Some(obj) = self.object.take() {
            let mut pool = self.pool.lock().unwrap();
            if pool.len() < 1000 { // 限制池大小
                pool.push(obj);
            }
        }
    }
}
```

### 内存映射优化

```rust
// 内存映射文件
pub struct MemoryMappedFile {
    file: File,
    mapping: MmapMut,
    size: usize,
}

impl MemoryMappedFile {
    pub fn new(path: &Path, size: usize) -> NetworkResult<Self> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(path)?;
        
        file.set_len(size as u64)?;
        
        let mapping = unsafe { MmapOptions::new().map_mut(&file)? };
        
        Ok(Self {
            file,
            mapping,
            size,
        })
    }
    
    pub fn as_slice(&self) -> &[u8] {
        &self.mapping[..]
    }
    
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.mapping[..]
    }
    
    // 异步刷新
    pub async fn flush_async(&self) -> NetworkResult<()> {
        let mapping = self.mapping.clone();
        tokio::task::spawn_blocking(move || {
            mapping.flush()
        }).await??;
        Ok(())
    }
}
```

### 缓存优化

```rust
// LRU缓存
pub struct LRUCache<K, V> {
    cache: LinkedHashMap<K, V>,
    capacity: usize,
    hits: AtomicUsize,
    misses: AtomicUsize,
}

impl<K, V> LRUCache<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    pub fn new(capacity: usize) -> Self {
        Self {
            cache: LinkedHashMap::new(),
            capacity,
            hits: AtomicUsize::new(0),
            misses: AtomicUsize::new(0),
        }
    }
    
    pub fn get(&mut self, key: &K) -> Option<&V> {
        if let Some(value) = self.cache.remove(key) {
            self.cache.insert(key.clone(), value);
            self.hits.fetch_add(1, Ordering::Relaxed);
            self.cache.get(key)
        } else {
            self.misses.fetch_add(1, Ordering::Relaxed);
            None
        }
    }
    
    pub fn put(&mut self, key: K, value: V) {
        if self.cache.contains_key(&key) {
            self.cache.remove(&key);
        } else if self.cache.len() >= self.capacity {
            self.cache.pop_front();
        }
        
        self.cache.insert(key, value);
    }
    
    pub fn hit_rate(&self) -> f64 {
        let hits = self.hits.load(Ordering::Relaxed);
        let misses = self.misses.load(Ordering::Relaxed);
        let total = hits + misses;
        
        if total == 0 {
            0.0
        } else {
            hits as f64 / total as f64
        }
    }
}
```

## 🌐 网络协议优化

### TCP优化

```rust
// TCP优化配置
pub struct TcpOptimization {
    nagle_algorithm: bool,
    tcp_nodelay: bool,
    keep_alive: bool,
    window_scaling: bool,
    congestion_control: CongestionControl,
}

pub enum CongestionControl {
    Reno,
    Cubic,
    BBR,
}

impl TcpOptimization {
    pub fn apply_to_socket(&self, socket: &TcpStream) -> NetworkResult<()> {
        // 禁用Nagle算法
        if self.tcp_nodelay {
            socket.set_nodelay(true)?;
        }
        
        // 启用keep-alive
        if self.keep_alive {
            socket.set_keepalive(true)?;
        }
        
        // 设置缓冲区大小
        socket.set_send_buffer_size(1024 * 1024)?; // 1MB
        socket.set_recv_buffer_size(1024 * 1024)?;  // 1MB
        
        Ok(())
    }
}
```

### HTTP/2优化

```rust
// HTTP/2优化
pub struct Http2Optimization {
    max_concurrent_streams: u32,
    initial_window_size: u32,
    max_frame_size: u32,
    header_table_size: u32,
    enable_push: bool,
}

impl Http2Optimization {
    pub fn new() -> Self {
        Self {
            max_concurrent_streams: 100,
            initial_window_size: 64 * 1024, // 64KB
            max_frame_size: 16 * 1024,      // 16KB
            header_table_size: 4 * 1024,    // 4KB
            enable_push: false,
        }
    }
    
    pub fn apply_to_client(&self, client: &mut HttpClient) {
        client.set_max_concurrent_streams(self.max_concurrent_streams);
        client.set_initial_window_size(self.initial_window_size);
        client.set_max_frame_size(self.max_frame_size);
        client.set_header_table_size(self.header_table_size);
        client.set_enable_push(self.enable_push);
    }
}
```

### WebSocket优化

```rust
// WebSocket优化
pub struct WebSocketOptimization {
    compression_enabled: bool,
    max_message_size: usize,
    ping_interval: Duration,
    pong_timeout: Duration,
    close_timeout: Duration,
}

impl WebSocketOptimization {
    pub fn new() -> Self {
        Self {
            compression_enabled: true,
            max_message_size: 16 * 1024 * 1024, // 16MB
            ping_interval: Duration::from_secs(30),
            pong_timeout: Duration::from_secs(10),
            close_timeout: Duration::from_secs(5),
        }
    }
    
    pub fn apply_to_server(&self, server: &mut WebSocketServer) {
        server.set_compression_enabled(self.compression_enabled);
        server.set_max_message_size(self.max_message_size);
        server.set_ping_interval(self.ping_interval);
        server.set_pong_timeout(self.pong_timeout);
        server.set_close_timeout(self.close_timeout);
    }
}
```

## 🔄 并发处理优化

### 工作窃取调度

```rust
// 工作窃取调度器
pub struct WorkStealingScheduler {
    workers: Vec<Worker>,
    global_queue: Arc<Mutex<VecDeque<Task>>>,
}

struct Worker {
    id: usize,
    local_queue: VecDeque<Task>,
    steal_count: AtomicUsize,
}

impl WorkStealingScheduler {
    pub fn new(num_workers: usize) -> Self {
        let workers = (0..num_workers)
            .map(|id| Worker {
                id,
                local_queue: VecDeque::new(),
                steal_count: AtomicUsize::new(0),
            })
            .collect();
        
        Self {
            workers,
            global_queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }
    
    pub fn schedule(&self, task: Task) {
        // 尝试放入本地队列
        let worker_id = thread_id::get() % self.workers.len();
        let worker = &self.workers[worker_id];
        
        if worker.local_queue.len() < 1000 {
            worker.local_queue.push_back(task);
        } else {
            // 放入全局队列
            self.global_queue.lock().unwrap().push_back(task);
        }
    }
    
    pub fn steal(&self, worker_id: usize) -> Option<Task> {
        let worker = &self.workers[worker_id];
        
        // 尝试从其他worker窃取
        for i in 0..self.workers.len() {
            if i != worker_id {
                let other_worker = &self.workers[i];
                if let Some(task) = other_worker.local_queue.pop_back() {
                    worker.steal_count.fetch_add(1, Ordering::Relaxed);
                    return Some(task);
                }
            }
        }
        
        // 尝试从全局队列获取
        self.global_queue.lock().unwrap().pop_front()
    }
}
```

### 无锁数据结构

```rust
// 无锁队列
pub struct LockFreeQueue<T> {
    head: AtomicPtr<Node<T>>,
    tail: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: Option<T>,
    next: AtomicPtr<Node<T>>,
}

impl<T> LockFreeQueue<T> {
    pub fn new() -> Self {
        let dummy = Box::new(Node {
            data: None,
            next: AtomicPtr::new(ptr::null_mut()),
        });
        let dummy_ptr = Box::into_raw(dummy);
        
        Self {
            head: AtomicPtr::new(dummy_ptr),
            tail: AtomicPtr::new(dummy_ptr),
        }
    }
    
    pub fn enqueue(&self, value: T) {
        let new_node = Box::new(Node {
            data: Some(value),
            next: AtomicPtr::new(ptr::null_mut()),
        });
        let new_ptr = Box::into_raw(new_node);
        
        loop {
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*tail).next.load(Ordering::Acquire) };
            
            if next.is_null() {
                if unsafe { (*tail).next.compare_exchange_weak(
                    ptr::null_mut(),
                    new_ptr,
                    Ordering::Release,
                    Ordering::Relaxed,
                ).is_ok() } {
                    self.tail.compare_exchange_weak(
                        tail,
                        new_ptr,
                        Ordering::Release,
                        Ordering::Relaxed,
                    ).ok();
                    break;
                }
            } else {
                self.tail.compare_exchange_weak(
                    tail,
                    next,
                    Ordering::Release,
                    Ordering::Relaxed,
                ).ok();
            }
        }
    }
    
    pub fn dequeue(&self) -> Option<T> {
        loop {
            let head = self.head.load(Ordering::Acquire);
            let tail = self.tail.load(Ordering::Acquire);
            let next = unsafe { (*head).next.load(Ordering::Acquire) };
            
            if head == tail {
                if next.is_null() {
                    return None;
                }
                self.tail.compare_exchange_weak(
                    tail,
                    next,
                    Ordering::Release,
                    Ordering::Relaxed,
                ).ok();
            } else {
                if let Some(next) = NonNull::new(next) {
                    let data = unsafe { (*next.as_ptr()).data.take() };
                    self.head.compare_exchange_weak(
                        head,
                        next.as_ptr(),
                        Ordering::Release,
                        Ordering::Relaxed,
                    ).ok();
                    return data;
                }
            }
        }
    }
}
```

## 📊 性能监控

### 性能指标收集

```rust
// 性能指标
pub struct PerformanceMetrics {
    request_count: AtomicUsize,
    response_time: AtomicU64,
    error_count: AtomicUsize,
    throughput: AtomicU64,
    memory_usage: AtomicUsize,
    cpu_usage: AtomicF64,
}

impl PerformanceMetrics {
    pub fn new() -> Self {
        Self {
            request_count: AtomicUsize::new(0),
            response_time: AtomicU64::new(0),
            error_count: AtomicUsize::new(0),
            throughput: AtomicU64::new(0),
            memory_usage: AtomicUsize::new(0),
            cpu_usage: AtomicF64::new(0.0),
        }
    }
    
    pub fn record_request(&self, response_time: Duration) {
        self.request_count.fetch_add(1, Ordering::Relaxed);
        self.response_time.fetch_add(response_time.as_nanos() as u64, Ordering::Relaxed);
    }
    
    pub fn record_error(&self) {
        self.error_count.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn update_throughput(&self, bytes: u64) {
        self.throughput.fetch_add(bytes, Ordering::Relaxed);
    }
    
    pub fn get_average_response_time(&self) -> Duration {
        let count = self.request_count.load(Ordering::Relaxed);
        if count > 0 {
            let total_nanos = self.response_time.load(Ordering::Relaxed);
            Duration::from_nanos(total_nanos / count as u64)
        } else {
            Duration::ZERO
        }
    }
    
    pub fn get_error_rate(&self) -> f64 {
        let errors = self.error_count.load(Ordering::Relaxed);
        let requests = self.request_count.load(Ordering::Relaxed);
        
        if requests > 0 {
            errors as f64 / requests as f64
        } else {
            0.0
        }
    }
}
```

### 实时监控

```rust
// 实时监控器
pub struct RealTimeMonitor {
    metrics: Arc<PerformanceMetrics>,
    interval: Duration,
}

impl RealTimeMonitor {
    pub fn new(metrics: Arc<PerformanceMetrics>, interval: Duration) -> Self {
        Self { metrics, interval }
    }
    
    pub async fn start(&self) -> NetworkResult<()> {
        let mut interval = tokio::time::interval(self.interval);
        
        loop {
            interval.tick().await;
            
            // 收集系统指标
            let memory_usage = self.get_memory_usage();
            let cpu_usage = self.get_cpu_usage();
            
            // 更新指标
            self.metrics.memory_usage.store(memory_usage, Ordering::Relaxed);
            self.metrics.cpu_usage.store(cpu_usage, Ordering::Relaxed);
            
            // 输出监控信息
            self.print_metrics();
        }
    }
    
    fn print_metrics(&self) {
        println!("=== 性能监控报告 ===");
        println!("请求数: {}", self.metrics.request_count.load(Ordering::Relaxed));
        println!("平均响应时间: {:?}", self.metrics.get_average_response_time());
        println!("错误率: {:.2}%", self.metrics.get_error_rate() * 100.0);
        println!("吞吐量: {} bytes/s", self.metrics.throughput.load(Ordering::Relaxed));
        println!("内存使用: {} MB", self.metrics.memory_usage.load(Ordering::Relaxed) / 1024 / 1024);
        println!("CPU使用率: {:.2}%", self.metrics.cpu_usage.load(Ordering::Relaxed) * 100.0);
    }
}
```

## 🧪 基准测试

### 基准测试框架

```rust
// 基准测试
pub struct Benchmark {
    name: String,
    iterations: usize,
    warmup_iterations: usize,
}

impl Benchmark {
    pub fn new(name: String) -> Self {
        Self {
            name,
            iterations: 1000,
            warmup_iterations: 100,
        }
    }
    
    pub async fn run<F, Fut>(&self, test_fn: F) -> BenchmarkResult
    where
        F: Fn() -> Fut,
        Fut: Future<Output = NetworkResult<()>>,
    {
        let mut times = Vec::new();
        
        // 预热
        for _ in 0..self.warmup_iterations {
            let _ = test_fn().await;
        }
        
        // 正式测试
        for _ in 0..self.iterations {
            let start = Instant::now();
            let _ = test_fn().await;
            let duration = start.elapsed();
            times.push(duration);
        }
        
        // 计算统计信息
        times.sort();
        let min = times[0];
        let max = times[times.len() - 1];
        let median = times[times.len() / 2];
        let mean = times.iter().sum::<Duration>() / times.len() as u32;
        
        BenchmarkResult {
            name: self.name.clone(),
            min,
            max,
            median,
            mean,
            iterations: self.iterations,
        }
    }
}

pub struct BenchmarkResult {
    name: String,
    min: Duration,
    max: Duration,
    median: Duration,
    mean: Duration,
    iterations: usize,
}
```

### 压力测试

```rust
// 压力测试
pub struct StressTest {
    concurrent_users: usize,
    duration: Duration,
    ramp_up_time: Duration,
}

impl StressTest {
    pub fn new(concurrent_users: usize, duration: Duration) -> Self {
        Self {
            concurrent_users,
            duration,
            ramp_up_time: Duration::from_secs(10),
        }
    }
    
    pub async fn run<F, Fut>(&self, test_fn: F) -> StressTestResult
    where
        F: Fn() -> Fut + Send + Sync + 'static,
        Fut: Future<Output = NetworkResult<()>> + Send,
    {
        let start_time = Instant::now();
        let mut handles = Vec::new();
        let metrics = Arc::new(PerformanceMetrics::new());
        
        // 逐步增加并发用户
        let ramp_up_interval = self.ramp_up_time / self.concurrent_users as u32;
        
        for user_id in 0..self.concurrent_users {
            let metrics = metrics.clone();
            let test_fn = &test_fn;
            
            let handle = tokio::spawn(async move {
                // 等待轮到该用户启动
                tokio::time::sleep(ramp_up_interval * user_id as u32).await;
                
                let mut request_count = 0;
                let mut error_count = 0;
                
                while start_time.elapsed() < self.duration {
                    let request_start = Instant::now();
                    
                    match test_fn().await {
                        Ok(_) => {
                            request_count += 1;
                            metrics.record_request(request_start.elapsed());
                        }
                        Err(_) => {
                            error_count += 1;
                            metrics.record_error();
                        }
                    }
                }
                
                (request_count, error_count)
            });
            
            handles.push(handle);
        }
        
        // 等待所有任务完成
        let mut total_requests = 0;
        let mut total_errors = 0;
        
        for handle in handles {
            let (requests, errors) = handle.await.unwrap();
            total_requests += requests;
            total_errors += errors;
        }
        
        StressTestResult {
            duration: self.duration,
            concurrent_users: self.concurrent_users,
            total_requests,
            total_errors,
            average_response_time: metrics.get_average_response_time(),
            error_rate: metrics.get_error_rate(),
            throughput: metrics.throughput.load(Ordering::Relaxed),
        }
    }
}
```

## 🔧 调优工具

### 性能分析器

```rust
// 性能分析器
pub struct Profiler {
    samples: Arc<Mutex<Vec<Sample>>>,
    enabled: AtomicBool,
}

struct Sample {
    timestamp: Instant,
    function: String,
    duration: Duration,
}

impl Profiler {
    pub fn new() -> Self {
        Self {
            samples: Arc::new(Mutex::new(Vec::new())),
            enabled: AtomicBool::new(false),
        }
    }
    
    pub fn enable(&self) {
        self.enabled.store(true, Ordering::Relaxed);
    }
    
    pub fn disable(&self) {
        self.enabled.store(false, Ordering::Relaxed);
    }
    
    pub fn record_sample(&self, function: String, duration: Duration) {
        if self.enabled.load(Ordering::Relaxed) {
            let sample = Sample {
                timestamp: Instant::now(),
                function,
                duration,
            };
            
            self.samples.lock().unwrap().push(sample);
        }
    }
    
    pub fn generate_report(&self) -> String {
        let samples = self.samples.lock().unwrap();
        let mut function_stats: HashMap<String, Vec<Duration>> = HashMap::new();
        
        for sample in samples.iter() {
            function_stats
                .entry(sample.function.clone())
                .or_insert_with(Vec::new)
                .push(sample.duration);
        }
        
        let mut report = String::new();
        report.push_str("=== 性能分析报告 ===\n");
        
        for (function, durations) in function_stats {
            let total_time: Duration = durations.iter().sum();
            let average_time = total_time / durations.len() as u32;
            let min_time = durations.iter().min().unwrap();
            let max_time = durations.iter().max().unwrap();
            
            report.push_str(&format!(
                "函数: {}\n  调用次数: {}\n  总时间: {:?}\n  平均时间: {:?}\n  最小时间: {:?}\n  最大时间: {:?}\n\n",
                function, durations.len(), total_time, average_time, min_time, max_time
            ));
        }
        
        report
    }
}
```

## 📈 性能指标

### 关键性能指标

```rust
// 关键性能指标
pub struct KeyPerformanceIndicators {
    // 延迟指标
    p50_latency: Duration,
    p95_latency: Duration,
    p99_latency: Duration,
    
    // 吞吐量指标
    requests_per_second: f64,
    bytes_per_second: u64,
    
    // 错误指标
    error_rate: f64,
    timeout_rate: f64,
    
    // 资源指标
    cpu_usage: f64,
    memory_usage: usize,
    connection_count: usize,
}

impl KeyPerformanceIndicators {
    pub fn calculate(&self, samples: &[Duration]) -> Self {
        let mut sorted_samples = samples.to_vec();
        sorted_samples.sort();
        
        let len = sorted_samples.len();
        let p50_index = (len as f64 * 0.5) as usize;
        let p95_index = (len as f64 * 0.95) as usize;
        let p99_index = (len as f64 * 0.99) as usize;
        
        Self {
            p50_latency: sorted_samples[p50_index.min(len - 1)],
            p95_latency: sorted_samples[p95_index.min(len - 1)],
            p99_latency: sorted_samples[p99_index.min(len - 1)],
            requests_per_second: 0.0, // 需要根据实际测试计算
            bytes_per_second: 0,     // 需要根据实际测试计算
            error_rate: 0.0,         // 需要根据实际测试计算
            timeout_rate: 0.0,        // 需要根据实际测试计算
            cpu_usage: 0.0,          // 需要根据实际测试计算
            memory_usage: 0,         // 需要根据实际测试计算
            connection_count: 0,     // 需要根据实际测试计算
        }
    }
}
```

---

**性能优化指南版本**: v1.0  
**最后更新**: 2025年1月  
**维护者**: C10 Networks 性能团队
