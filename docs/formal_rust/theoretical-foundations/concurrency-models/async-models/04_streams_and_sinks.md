# 异步流 (Streams)

## 概述

异步流是Rust异步编程中处理连续数据序列的核心抽象，类似于同步的Iterator，但支持异步操作。
本章深入探讨Stream Trait、异步迭代器、背压处理、流组合以及相关的工程实践。

## Stream Trait 理论基础

### 1. Stream定义

```rust
use std::pin::Pin;
use std::task::{Context, Poll};

pub trait Stream {
    type Item;
    
    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>>;
}
```

### 2. Stream语义

```rust
// Stream的三种状态
pub enum StreamPoll<T> {
    // 有数据可用
    Ready(Some(T)),
    // 暂无数据，但流未结束
    Pending,
    // 流已结束
    Ready(None),
}

// Stream状态机示例
enum FileStream {
    Initial { path: String },
    Reading { file: File, buffer: [u8; 1024] },
    Complete,
}

impl Stream for FileStream {
    type Item = Vec<u8>;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        match self.as_mut().get_mut() {
            FileStream::Initial { path } => {
                let file = File::open(path.clone())?;
                *self.as_mut().get_mut() = FileStream::Reading { 
                    file, 
                    buffer: [0; 1024] 
                };
                Poll::Pending
            }
            FileStream::Reading { file, buffer } => {
                match file.read(buffer) {
                    Ok(0) => {
                        *self.as_mut().get_mut() = FileStream::Complete;
                        Poll::Ready(None) // 流结束
                    }
                    Ok(n) => {
                        let data = buffer[..n].to_vec();
                        Poll::Ready(Some(data)) // 有数据
                    }
                    Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                        cx.waker().wake_by_ref();
                        Poll::Pending // 等待I/O
                    }
                    Err(_) => {
                        *self.as_mut().get_mut() = FileStream::Complete;
                        Poll::Ready(None) // 错误时结束流
                    }
                }
            }
            FileStream::Complete => Poll::Ready(None),
        }
    }
}
```

### 3. 数学基础

**定义 4.1** (异步流)
设 $S$ 为Stream，其定义为：

- 状态集合：$\{Initial, Active, Complete\}$
- 输出序列：$[T_0, T_1, T_2, \ldots, T_n]$
- 转换函数：$\delta: State \times Event \rightarrow State \times Option<T>$

**定理 4.1** (Stream单调性)
对于任意Stream $S$，若 $poll\_next(S) = Pending$，则后续调用 $poll\_next(S)$ 仍返回 $Pending$，直到外部事件触发或流结束。

## 异步迭代器

### 1. 异步迭代器接口

```rust
// 异步迭代器trait
pub trait AsyncIterator {
    type Item;
    
    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>>;
}

// 为Stream实现AsyncIterator
impl<S: Stream> AsyncIterator for S {
    type Item = S::Item;
    
    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        Stream::poll_next(self, cx)
    }
}
```

### 2. 异步for循环

```rust
// 异步for循环语法（实验性）
async fn process_stream<S: Stream>(mut stream: S) 
where
    S: Unpin,
{
    // 语法糖：async for
    async for item in &mut stream {
        println!("Received: {:?}", item);
        process_item(item).await;
    }
}

// 手动实现异步迭代
async fn manual_iteration<S: Stream>(mut stream: S) 
where
    S: Unpin,
{
    use futures::stream::StreamExt;
    
    while let Some(item) = stream.next().await {
        println!("Received: {:?}", item);
        process_item(item).await;
    }
}
```

### 3. 迭代器适配器

```rust
// 流适配器示例
pub struct MapStream<S, F> {
    stream: S,
    f: F,
}

impl<S, F, B> Stream for MapStream<S, F>
where
    S: Stream,
    F: FnMut(S::Item) -> B,
{
    type Item = B;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        match self.as_mut().stream().poll_next(cx) {
            Poll::Ready(Some(item)) => {
                let mapped = (self.as_mut().f())(item);
                Poll::Ready(Some(mapped))
            }
            Poll::Ready(None) => Poll::Ready(None),
            Poll::Pending => Poll::Pending,
        }
    }
}

// 过滤器适配器
pub struct FilterStream<S, F> {
    stream: S,
    predicate: F,
}

impl<S, F> Stream for FilterStream<S, F>
where
    S: Stream,
    F: FnMut(&S::Item) -> bool,
{
    type Item = S::Item;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        loop {
            match self.as_mut().stream().poll_next(cx) {
                Poll::Ready(Some(item)) => {
                    if (self.as_mut().predicate())(&item) {
                        return Poll::Ready(Some(item));
                    }
                    // 继续循环，寻找下一个匹配项
                }
                Poll::Ready(None) => return Poll::Ready(None),
                Poll::Pending => return Poll::Pending,
            }
        }
    }
}
```

## 背压处理

### 1. 背压概念

```rust
// 背压：生产者速度超过消费者速度时的处理机制
pub struct BackpressureStream<S> {
    stream: S,
    buffer: VecDeque<S::Item>,
    max_buffer_size: usize,
    backpressure_strategy: BackpressureStrategy,
}

enum BackpressureStrategy {
    // 丢弃新数据
    DropNew,
    // 丢弃旧数据
    DropOld,
    // 阻塞生产者
    Block,
    // 自适应调整
    Adaptive,
}

impl<S> Stream for BackpressureStream<S>
where
    S: Stream,
{
    type Item = S::Item;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        // 首先尝试从缓冲区获取数据
        if let Some(item) = self.as_mut().buffer.pop_front() {
            return Poll::Ready(Some(item));
        }
        
        // 缓冲区为空，从底层流获取数据
        match self.as_mut().stream().poll_next(cx) {
            Poll::Ready(Some(item)) => {
                // 检查缓冲区大小
                if self.as_mut().buffer.len() >= self.as_mut().max_buffer_size {
                    match self.as_mut().backpressure_strategy {
                        BackpressureStrategy::DropNew => {
                            // 丢弃新数据
                            Poll::Ready(None)
                        }
                        BackpressureStrategy::DropOld => {
                            // 丢弃最旧的数据
                            self.as_mut().buffer.pop_back();
                            self.as_mut().buffer.push_back(item);
                            Poll::Ready(Some(item))
                        }
                        BackpressureStrategy::Block => {
                            // 阻塞，等待缓冲区有空间
                            cx.waker().wake_by_ref();
                            Poll::Pending
                        }
                        BackpressureStrategy::Adaptive => {
                            // 自适应调整缓冲区大小
                            self.as_mut().max_buffer_size *= 2;
                            self.as_mut().buffer.push_back(item);
                            Poll::Ready(Some(item))
                        }
                    }
                } else {
                    self.as_mut().buffer.push_back(item);
                    Poll::Ready(Some(item))
                }
            }
            Poll::Ready(None) => Poll::Ready(None),
            Poll::Pending => Poll::Pending,
        }
    }
}
```

### 2. 背压策略

```rust
// 令牌桶背压控制
pub struct TokenBucketBackpressure {
    tokens: AtomicUsize,
    capacity: usize,
    refill_rate: f64, // tokens per second
    last_refill: AtomicU64,
}

impl TokenBucketBackpressure {
    pub fn new(capacity: usize, refill_rate: f64) -> Self {
        Self {
            tokens: AtomicUsize::new(capacity),
            capacity,
            refill_rate,
            last_refill: AtomicU64::new(0),
        }
    }
    
    pub fn try_acquire(&self) -> bool {
        self.refill_tokens();
        
        let current = self.tokens.load(Ordering::Acquire);
        if current > 0 {
            self.tokens.fetch_sub(1, Ordering::Release);
            true
        } else {
            false
        }
    }
    
    fn refill_tokens(&self) {
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let last = self.last_refill.load(Ordering::Acquire);
        let elapsed = now - last;
        
        if elapsed > 0 {
            let new_tokens = (elapsed as f64 * self.refill_rate) as usize;
            let current = self.tokens.load(Ordering::Acquire);
            let new_total = (current + new_tokens).min(self.capacity);
            
            self.tokens.store(new_total, Ordering::Release);
            self.last_refill.store(now, Ordering::Release);
        }
    }
}
```

### 3. 自适应背压

```rust
// 自适应背压控制器
pub struct AdaptiveBackpressure {
    current_rate: AtomicF64,
    target_latency: Duration,
    window_size: usize,
    measurements: Arc<Mutex<VecDeque<Duration>>>,
}

impl AdaptiveBackpressure {
    pub fn new(target_latency: Duration, window_size: usize) -> Self {
        Self {
            current_rate: AtomicF64::new(1000.0), // 初始速率
            target_latency,
            window_size,
            measurements: Arc::new(Mutex::new(VecDeque::new())),
        }
    }
    
    pub fn record_measurement(&self, latency: Duration) {
        let mut measurements = self.measurements.lock().unwrap();
        measurements.push_back(latency);
        
        if measurements.len() > self.window_size {
            measurements.pop_front();
        }
        
        self.adjust_rate();
    }
    
    fn adjust_rate(&self) {
        let measurements = self.measurements.lock().unwrap();
        if measurements.len() < self.window_size / 2 {
            return;
        }
        
        let avg_latency = measurements.iter()
            .map(|d| d.as_millis() as f64)
            .sum::<f64>() / measurements.len() as f64;
        
        let target_ms = self.target_latency.as_millis() as f64;
        let current_rate = self.current_rate.load(Ordering::Acquire);
        
        // 简单的PID控制器
        let error = target_ms - avg_latency;
        let new_rate = current_rate * (1.0 + error * 0.1);
        
        self.current_rate.store(new_rate.max(1.0), Ordering::Release);
    }
}
```

## 流组合

### 1. 基本组合操作

```rust
// 流组合trait
pub trait StreamExt: Stream {
    // 映射
    fn map<F, B>(self, f: F) -> MapStream<Self, F>
    where
        F: FnMut(Self::Item) -> B,
        Self: Sized,
    {
        MapStream { stream: self, f }
    }
    
    // 过滤
    fn filter<F>(self, predicate: F) -> FilterStream<Self, F>
    where
        F: FnMut(&Self::Item) -> bool,
        Self: Sized,
    {
        FilterStream { stream: self, predicate }
    }
    
    // 合并
    fn merge<S>(self, other: S) -> MergeStream<Self, S>
    where
        S: Stream<Item = Self::Item>,
        Self: Sized,
    {
        MergeStream { left: self, right: other }
    }
    
    // 连接
    fn chain<S>(self, other: S) -> ChainStream<Self, S>
    where
        S: Stream<Item = Self::Item>,
        Self: Sized,
    {
        ChainStream { first: self, second: other, state: ChainState::First }
    }
}

// 为所有Stream实现StreamExt
impl<S: Stream> StreamExt for S {}
```

### 2. 高级组合

```rust
// 窗口化流
pub struct WindowStream<S> {
    stream: S,
    window_size: usize,
    buffer: VecDeque<S::Item>,
}

impl<S> Stream for WindowStream<S>
where
    S: Stream,
    S::Item: Clone,
{
    type Item = Vec<S::Item>;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        // 填充缓冲区
        while self.as_mut().buffer.len() < self.as_mut().window_size {
            match self.as_mut().stream().poll_next(cx) {
                Poll::Ready(Some(item)) => {
                    self.as_mut().buffer.push_back(item);
                }
                Poll::Ready(None) => {
                    // 流结束，返回剩余数据
                    if !self.as_mut().buffer.is_empty() {
                        let window = self.as_mut().buffer.drain(..).collect();
                        return Poll::Ready(Some(window));
                    } else {
                        return Poll::Ready(None);
                    }
                }
                Poll::Pending => return Poll::Pending,
            }
        }
        
        // 返回完整窗口
        let window = self.as_mut().buffer.drain(..self.as_mut().window_size).collect();
        Poll::Ready(Some(window))
    }
}

// 分组流
pub struct GroupByStream<S, F, K> {
    stream: S,
    key_fn: F,
    groups: HashMap<K, Vec<S::Item>>,
}

impl<S, F, K> Stream for GroupByStream<S, F, K>
where
    S: Stream,
    F: FnMut(&S::Item) -> K,
    K: Eq + Hash + Clone,
{
    type Item = (K, Vec<S::Item>);
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        // 从底层流获取数据并分组
        match self.as_mut().stream().poll_next(cx) {
            Poll::Ready(Some(item)) => {
                let key = (self.as_mut().key_fn())(&item);
                self.as_mut().groups.entry(key.clone())
                    .or_insert_with(Vec::new)
                    .push(item);
                Poll::Pending // 继续收集
            }
            Poll::Ready(None) => {
                // 流结束，返回所有分组
                if let Some((key, items)) = self.as_mut().groups.drain().next() {
                    Poll::Ready(Some((key, items)))
                } else {
                    Poll::Ready(None)
                }
            }
            Poll::Pending => Poll::Pending,
        }
    }
}
```

### 3. 错误处理组合

```rust
// 错误处理流
pub struct ErrorHandlingStream<S, E> {
    stream: S,
    error_handler: E,
    retry_count: usize,
    max_retries: usize,
}

impl<S, E> Stream for ErrorHandlingStream<S, E>
where
    S: Stream<Item = Result<S::Item, S::Error>>,
    E: FnMut(S::Error) -> bool, // 是否应该重试
{
    type Item = S::Item;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        loop {
            match self.as_mut().stream().poll_next(cx) {
                Poll::Ready(Some(Ok(item))) => {
                    self.as_mut().retry_count = 0; // 重置重试计数
                    return Poll::Ready(Some(item));
                }
                Poll::Ready(Some(Err(error))) => {
                    if self.as_mut().retry_count < self.as_mut().max_retries 
                        && (self.as_mut().error_handler())(error) {
                        self.as_mut().retry_count += 1;
                        continue; // 重试
                    } else {
                        return Poll::Ready(None); // 放弃
                    }
                }
                Poll::Ready(None) => return Poll::Ready(None),
                Poll::Pending => return Poll::Pending,
            }
        }
    }
}
```

## 工程实践

### 1. 流处理管道

```rust
// 流处理管道
pub struct StreamPipeline<I, O> {
    input: I,
    processors: Vec<Box<dyn StreamProcessor<I::Item, O>>>,
}

trait StreamProcessor<I, O> {
    fn process(&mut self, input: I) -> Result<O, Box<dyn std::error::Error>>;
}

impl<I, O> Stream for StreamPipeline<I, O>
where
    I: Stream,
    O: 'static,
{
    type Item = O;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        // 从输入流获取数据
        match self.as_mut().input().poll_next(cx) {
            Poll::Ready(Some(input)) => {
                // 通过所有处理器处理数据
                let mut current = input;
                for processor in &mut self.as_mut().processors {
                    match processor.process(current) {
                        Ok(output) => current = output,
                        Err(_) => return Poll::Ready(None), // 错误时结束流
                    }
                }
                Poll::Ready(Some(current))
            }
            Poll::Ready(None) => Poll::Ready(None),
            Poll::Pending => Poll::Pending,
        }
    }
}
```

### 2. 性能优化

```rust
// 批量处理流
pub struct BatchStream<S> {
    stream: S,
    batch_size: usize,
    buffer: Vec<S::Item>,
}

impl<S> Stream for BatchStream<S>
where
    S: Stream,
{
    type Item = Vec<S::Item>;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        // 收集批次
        while self.as_mut().buffer.len() < self.as_mut().batch_size {
            match self.as_mut().stream().poll_next(cx) {
                Poll::Ready(Some(item)) => {
                    self.as_mut().buffer.push(item);
                }
                Poll::Ready(None) => {
                    // 流结束，返回剩余数据
                    if !self.as_mut().buffer.is_empty() {
                        let batch = std::mem::take(&mut self.as_mut().buffer);
                        return Poll::Ready(Some(batch));
                    } else {
                        return Poll::Ready(None);
                    }
                }
                Poll::Pending => return Poll::Pending,
            }
        }
        
        // 返回完整批次
        let batch = std::mem::take(&mut self.as_mut().buffer);
        Poll::Ready(Some(batch))
    }
}

// 并行处理流
pub struct ParallelStream<S, F> {
    stream: S,
    processor: F,
    workers: Vec<JoinHandle<()>>,
    result_queue: Arc<Mutex<VecDeque<S::Item>>>,
}

impl<S, F> Stream for ParallelStream<S, F>
where
    S: Stream + Send + 'static,
    S::Item: Send + 'static,
    F: Fn(S::Item) -> S::Item + Send + Sync + 'static,
{
    type Item = S::Item;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        // 检查结果队列
        if let Some(result) = self.as_mut().result_queue.lock().unwrap().pop_front() {
            return Poll::Ready(Some(result));
        }
        
        // 从输入流获取数据并启动工作线程
        match self.as_mut().stream().poll_next(cx) {
            Poll::Ready(Some(item)) => {
                let processor = &self.as_mut().processor;
                let result_queue = self.as_mut().result_queue.clone();
                
                let handle = std::thread::spawn(move || {
                    let processed = processor(item);
                    result_queue.lock().unwrap().push_back(processed);
                });
                
                self.as_mut().workers.push(handle);
                Poll::Pending
            }
            Poll::Ready(None) => {
                // 等待所有工作线程完成
                for worker in &mut self.as_mut().workers {
                    if let Ok(_) = worker.join() {
                        // 工作线程已完成
                    }
                }
                
                // 返回剩余结果
                if let Some(result) = self.as_mut().result_queue.lock().unwrap().pop_front() {
                    Poll::Ready(Some(result))
                } else {
                    Poll::Ready(None)
                }
            }
            Poll::Pending => Poll::Pending,
        }
    }
}
```

### 3. 监控与诊断

```rust
// 流监控
pub struct StreamMonitor<S> {
    stream: S,
    metrics: Arc<Mutex<StreamMetrics>>,
}

#[derive(Default)]
struct StreamMetrics {
    items_processed: usize,
    items_dropped: usize,
    average_latency: Duration,
    throughput: f64,
    errors: Vec<Box<dyn std::error::Error>>,
}

impl<S> Stream for StreamMonitor<S>
where
    S: Stream,
{
    type Item = S::Item;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let start = std::time::Instant::now();
        
        match self.as_mut().stream().poll_next(cx) {
            Poll::Ready(Some(item)) => {
                let latency = start.elapsed();
                let mut metrics = self.as_mut().metrics.lock().unwrap();
                metrics.items_processed += 1;
                metrics.average_latency = (metrics.average_latency + latency) / 2;
                Poll::Ready(Some(item))
            }
            Poll::Ready(None) => Poll::Ready(None),
            Poll::Pending => Poll::Pending,
        }
    }
}
```

## 总结

异步流是Rust异步编程中处理连续数据序列的强大抽象，通过Stream Trait、异步迭代器、背压处理等机制，实现了高效、安全的数据流处理。理解流组合、背压控制以及相关的工程实践，对于构建高性能的异步数据处理系统至关重要。

## 交叉引用

- [异步编程导论与哲学](./01_introduction_and_philosophy.md)
- [运行时与执行模型](./02_runtime_and_execution_model.md)
- [Pinning与Unsafe基础](./03_pinning_and_unsafe_foundations.md)
- [异步Trait与生态](./05_async_in_traits_and_ecosystem.md)
- [并发与同步原语](../05_concurrency/)
- [性能优化](../performance_optimization/)
