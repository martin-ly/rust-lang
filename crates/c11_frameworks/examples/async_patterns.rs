//! 异步编程模式示例
//!
//! 展示Rust异步编程的高级模式和最佳实践，包括：
//! - 并发处理和任务管理
//! - 流处理和背压控制
//! - 异步迭代器和生成器
//! - 异步锁和同步原语
//! - 错误处理和重试机制
//! - 性能优化技巧

use futures::{
    future::{self, FutureExt, TryFutureExt},
    sink::SinkExt,
    stream::{self, Stream, StreamExt},
};
use serde::{Deserialize, Serialize};
use std::{
    collections::HashMap,
    future::Future,
    pin::Pin,
    sync::Arc,
    task::{Context, Poll},
    time::SystemTime,
};
use tokio::{
    io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt},
    sync::{Barrier, Mutex, Notify, RwLock, Semaphore, broadcast, mpsc, oneshot, watch},
    task::{JoinHandle, spawn_blocking},
    time::{Duration, Instant, interval, sleep, timeout},
};
use tracing::{debug, error, info, instrument, warn};

/// 异步任务管理器
#[derive(Debug, Clone)]
pub struct TaskManager {
    tasks: Arc<RwLock<HashMap<String, JoinHandle<()>>>>,
    shutdown_tx: Arc<Mutex<Option<oneshot::Sender<()>>>>,
}

/// 流处理器
pub struct StreamProcessor<T> {
    buffer_size: usize,
    concurrency: usize,
    _phantom: std::marker::PhantomData<T>,
}

/// 背压控制器
pub struct BackpressureController {
    max_pending: usize,
    current_pending: Arc<Mutex<usize>>,
    semaphore: Arc<Semaphore>,
}

/// 异步缓存
pub struct AsyncCache<K, V> {
    data: Arc<RwLock<HashMap<K, CacheEntry<V>>>>,
    ttl: Duration,
    max_size: usize,
}

/// 缓存条目
#[derive(Debug, Clone)]
struct CacheEntry<V> {
    value: V,
    expires_at: Instant,
}

/// 重试策略
#[derive(Debug, Clone)]
pub enum RetryStrategy {
    Fixed(Duration),
    Exponential {
        base: Duration,
        max: Duration,
        multiplier: f64,
    },
    Linear {
        base: Duration,
        increment: Duration,
        max: Duration,
    },
}

/// 异步迭代器
pub struct AsyncIterator<T> {
    items: Vec<T>,
    index: usize,
}

/// 异步生成器
pub struct AsyncGenerator<T> {
    generator: Box<dyn Fn() -> Pin<Box<dyn Future<Output = Option<T>> + Send>> + Send + Sync>,
}

/// 并发限制器
pub struct ConcurrencyLimiter {
    semaphore: Arc<Semaphore>,
    max_concurrent: usize,
}

/// 异步批处理器
pub struct BatchProcessor<T> {
    batch_size: usize,
    flush_interval: Duration,
    items: Arc<Mutex<Vec<T>>>,
    processor: Arc<
        dyn Fn(Vec<T>) -> Pin<Box<dyn Future<Output = Result<(), String>> + Send>> + Send + Sync,
    >,
}

/// 异步事件总线
pub struct AsyncEventBus<T> {
    subscribers: Arc<RwLock<HashMap<String, mpsc::UnboundedSender<T>>>>,
}

/// 异步工作池
pub struct AsyncWorkerPool<T, R> {
    workers: Vec<JoinHandle<()>>,
    task_sender: mpsc::UnboundedSender<T>,
    result_receiver: mpsc::UnboundedReceiver<R>,
    worker_count: usize,
}

impl TaskManager {
    pub fn new() -> Self {
        Self {
            tasks: Arc::new(RwLock::new(HashMap::new())),
            shutdown_tx: Arc::new(Mutex::new(None)),
        }
    }

    /// 启动任务
    pub async fn spawn_task<F>(&self, name: String, task: F) -> Result<(), String>
    where
        F: Future<Output = ()> + Send + 'static,
    {
        let handle = tokio::spawn(task);
        let mut tasks = self.tasks.write().await;
        tasks.insert(name, handle);
        Ok(())
    }

    /// 停止任务
    pub async fn stop_task(&self, name: &str) -> Result<(), String> {
        let mut tasks = self.tasks.write().await;
        if let Some(handle) = tasks.remove(name) {
            handle.abort();
        }
        Ok(())
    }

    /// 等待所有任务完成
    pub async fn wait_for_all(&self) -> Result<(), String> {
        let tasks = self.tasks.read().await;
        for (name, handle) in tasks.iter() {
            if let Err(e) = handle.await {
                error!("任务 {} 执行失败: {:?}", name, e);
            }
        }
        Ok(())
    }

    /// 优雅关闭
    pub async fn shutdown(&self) -> Result<(), String> {
        let mut shutdown_tx = self.shutdown_tx.lock().await;
        if let Some(tx) = shutdown_tx.take() {
            let _ = tx.send(());
        }

        let tasks = self.tasks.read().await;
        for (name, handle) in tasks.iter() {
            handle.abort();
            info!("任务 {} 已停止", name);
        }

        Ok(())
    }
}

impl<T> StreamProcessor<T> {
    pub fn new(buffer_size: usize, concurrency: usize) -> Self {
        Self {
            buffer_size,
            concurrency,
            _phantom: std::marker::PhantomData,
        }
    }

    /// 处理流
    pub async fn process_stream<F, R>(
        &self,
        mut stream: impl Stream<Item = T> + Unpin,
        processor: F,
    ) -> Result<Vec<R>, String>
    where
        F: Fn(T) -> Pin<Box<dyn Future<Output = Result<R, String>> + Send>> + Send + Sync + Clone,
        T: Send + 'static,
        R: Send + 'static,
    {
        let semaphore = Arc::new(Semaphore::new(self.concurrency));
        let results = Arc::new(Mutex::new(Vec::new()));

        let mut handles = Vec::new();

        while let Some(item) = stream.next().await {
            let permit = semaphore.acquire().await.map_err(|e| e.to_string())?;
            let processor = processor.clone();
            let results = results.clone();

            let handle = tokio::spawn(async move {
                let result = processor(item).await;
                drop(permit);

                if let Ok(value) = result {
                    let mut results = results.lock().await;
                    results.push(value);
                }
            });

            handles.push(handle);
        }

        // 等待所有任务完成
        for handle in handles {
            handle.await.map_err(|e| e.to_string())?;
        }

        let results = results.lock().await;
        Ok(results.clone())
    }
}

impl BackpressureController {
    pub fn new(max_pending: usize) -> Self {
        Self {
            max_pending,
            current_pending: Arc::new(Mutex::new(0)),
            semaphore: Arc::new(Semaphore::new(max_pending)),
        }
    }

    /// 获取许可
    pub async fn acquire(&self) -> Result<BackpressurePermit, String> {
        let permit = self.semaphore.acquire().await.map_err(|e| e.to_string())?;
        let mut current = self.current_pending.lock().await;
        *current += 1;

        Ok(BackpressurePermit {
            controller: self.clone(),
            _permit: permit,
        })
    }

    /// 获取当前待处理数量
    pub async fn current_pending(&self) -> usize {
        let current = self.current_pending.lock().await;
        *current
    }
}

/// 背压许可
pub struct BackpressurePermit {
    controller: BackpressureController,
    _permit: tokio::sync::SemaphorePermit<'_>,
}

impl Drop for BackpressurePermit {
    fn drop(&mut self) {
        let controller = self.controller.clone();
        tokio::spawn(async move {
            let mut current = controller.current_pending.lock().await;
            *current = current.saturating_sub(1);
        });
    }
}

impl<K, V> AsyncCache<K, V>
where
    K: Clone + std::hash::Hash + Eq + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    pub fn new(ttl: Duration, max_size: usize) -> Self {
        Self {
            data: Arc::new(RwLock::new(HashMap::new())),
            ttl,
            max_size,
        }
    }

    /// 获取值
    pub async fn get(&self, key: &K) -> Option<V> {
        let data = self.data.read().await;
        if let Some(entry) = data.get(key) {
            if entry.expires_at > Instant::now() {
                return Some(entry.value.clone());
            }
        }
        None
    }

    /// 设置值
    pub async fn set(&self, key: K, value: V) -> Result<(), String> {
        let mut data = self.data.write().await;

        // 检查缓存大小限制
        if data.len() >= self.max_size {
            self.evict_expired(&mut data).await;

            if data.len() >= self.max_size {
                // 移除最旧的条目
                let oldest_key = data.keys().next().cloned();
                if let Some(key) = oldest_key {
                    data.remove(&key);
                }
            }
        }

        let entry = CacheEntry {
            value,
            expires_at: Instant::now() + self.ttl,
        };

        data.insert(key, entry);
        Ok(())
    }

    /// 移除过期条目
    async fn evict_expired(&self, data: &mut HashMap<K, CacheEntry<V>>) {
        let now = Instant::now();
        data.retain(|_, entry| entry.expires_at > now);
    }

    /// 清理过期条目
    pub async fn cleanup(&self) {
        let mut data = self.data.write().await;
        self.evict_expired(&mut data).await;
    }
}

impl RetryStrategy {
    /// 获取重试延迟
    pub fn get_delay(&self, attempt: u32) -> Duration {
        match self {
            RetryStrategy::Fixed(delay) => *delay,
            RetryStrategy::Exponential {
                base,
                max,
                multiplier,
            } => {
                let delay = base.as_millis() as f64 * multiplier.powi(attempt as i32);
                let delay_ms = delay.min(max.as_millis() as f64) as u64;
                Duration::from_millis(delay_ms)
            }
            RetryStrategy::Linear {
                base,
                increment,
                max,
            } => {
                let delay = base + *increment * attempt;
                delay.min(*max)
            }
        }
    }
}

/// 带重试的异步操作
pub async fn retry_async<F, T>(
    operation: F,
    strategy: RetryStrategy,
    max_attempts: u32,
) -> Result<T, String>
where
    F: Fn() -> Pin<Box<dyn Future<Output = Result<T, String>> + Send>> + Send + Sync,
{
    let mut last_error = String::new();

    for attempt in 0..max_attempts {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                last_error = e;
                if attempt < max_attempts - 1 {
                    let delay = strategy.get_delay(attempt);
                    sleep(delay).await;
                }
            }
        }
    }

    Err(last_error)
}

impl<T> AsyncIterator<T> {
    pub fn new(items: Vec<T>) -> Self {
        Self { items, index: 0 }
    }

    /// 异步迭代
    pub async fn next(&mut self) -> Option<T> {
        if self.index < self.items.len() {
            let item = self.items[self.index].clone();
            self.index += 1;
            Some(item)
        } else {
            None
        }
    }

    /// 转换为流
    pub fn into_stream(self) -> impl Stream<Item = T> {
        stream::iter(self.items)
    }
}

impl<T> AsyncGenerator<T> {
    pub fn new<F>(generator: F) -> Self
    where
        F: Fn() -> Pin<Box<dyn Future<Output = Option<T>> + Send>> + Send + Sync + 'static,
    {
        Self {
            generator: Box::new(generator),
        }
    }

    /// 生成下一个值
    pub async fn next(&self) -> Option<T> {
        (self.generator)().await
    }
}

impl ConcurrencyLimiter {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            max_concurrent,
        }
    }

    /// 执行任务
    pub async fn execute<F, T>(&self, task: F) -> Result<T, String>
    where
        F: Future<Output = Result<T, String>> + Send + 'static,
        T: Send + 'static,
    {
        let permit = self.semaphore.acquire().await.map_err(|e| e.to_string())?;

        let result = task.await;
        drop(permit);

        result
    }

    /// 获取当前并发数
    pub fn available_permits(&self) -> usize {
        self.semaphore.available_permits()
    }
}

impl<T> BatchProcessor<T>
where
    T: Send + 'static,
{
    pub fn new<F>(batch_size: usize, flush_interval: Duration, processor: F) -> Self
    where
        F: Fn(Vec<T>) -> Pin<Box<dyn Future<Output = Result<(), String>> + Send>>
            + Send
            + Sync
            + 'static,
    {
        Self {
            batch_size,
            flush_interval,
            items: Arc::new(Mutex::new(Vec::new())),
            processor: Arc::new(processor),
        }
    }

    /// 添加项目
    pub async fn add(&self, item: T) -> Result<(), String> {
        let mut items = self.items.lock().await;
        items.push(item);

        if items.len() >= self.batch_size {
            let batch = items.drain(..).collect();
            drop(items);

            let processor = self.processor.clone();
            tokio::spawn(async move {
                if let Err(e) = processor(batch).await {
                    error!("批处理失败: {}", e);
                }
            });
        }

        Ok(())
    }

    /// 启动定时刷新
    pub async fn start_flush_timer(&self) -> JoinHandle<()> {
        let items = self.items.clone();
        let processor = self.processor.clone();
        let flush_interval = self.flush_interval;

        tokio::spawn(async move {
            let mut interval = interval(flush_interval);

            loop {
                interval.tick().await;

                let batch = {
                    let mut items = items.lock().await;
                    if items.is_empty() {
                        continue;
                    }
                    items.drain(..).collect()
                };

                if let Err(e) = processor(batch).await {
                    error!("定时批处理失败: {}", e);
                }
            }
        })
    }
}

impl<T> AsyncEventBus<T>
where
    T: Clone + Send + 'static,
{
    pub fn new() -> Self {
        Self {
            subscribers: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 订阅事件
    pub async fn subscribe(&self, topic: String) -> mpsc::UnboundedReceiver<T> {
        let (tx, rx) = mpsc::unbounded_channel();
        let mut subscribers = self.subscribers.write().await;
        subscribers.insert(topic, tx);
        rx
    }

    /// 发布事件
    pub async fn publish(&self, topic: &str, event: T) -> Result<(), String> {
        let subscribers = self.subscribers.read().await;
        if let Some(sender) = subscribers.get(topic) {
            sender.send(event).map_err(|e| e.to_string())?;
        }
        Ok(())
    }

    /// 取消订阅
    pub async fn unsubscribe(&self, topic: &str) {
        let mut subscribers = self.subscribers.write().await;
        subscribers.remove(topic);
    }
}

impl<T, R> AsyncWorkerPool<T, R>
where
    T: Send + 'static,
    R: Send + 'static,
{
    pub fn new<F>(worker_count: usize, worker: F) -> Self
    where
        F: Fn(T) -> Pin<Box<dyn Future<Output = R> + Send>> + Send + Sync + Clone + 'static,
    {
        let (task_sender, task_receiver) = mpsc::unbounded_channel();
        let (result_sender, result_receiver) = mpsc::unbounded_channel();

        let task_receiver = Arc::new(Mutex::new(task_receiver));
        let result_sender = Arc::new(result_sender);

        let mut workers = Vec::new();

        for _ in 0..worker_count {
            let task_receiver = task_receiver.clone();
            let result_sender = result_sender.clone();
            let worker = worker.clone();

            let handle = tokio::spawn(async move {
                loop {
                    let task = {
                        let mut receiver = task_receiver.lock().await;
                        receiver.recv().await
                    };

                    match task {
                        Some(task) => {
                            let result = worker(task).await;
                            let _ = result_sender.send(result);
                        }
                        None => break,
                    }
                }
            });

            workers.push(handle);
        }

        Self {
            workers,
            task_sender,
            result_receiver,
            worker_count,
        }
    }

    /// 提交任务
    pub async fn submit(&self, task: T) -> Result<(), String> {
        self.task_sender.send(task).map_err(|e| e.to_string())
    }

    /// 获取结果
    pub async fn get_result(&mut self) -> Option<R> {
        self.result_receiver.recv().await
    }

    /// 关闭工作池
    pub async fn shutdown(self) {
        drop(self.task_sender);

        for worker in self.workers {
            let _ = worker.await;
        }
    }
}

/// 异步管道
pub struct AsyncPipeline<T> {
    stages: Vec<Box<dyn Fn(T) -> Pin<Box<dyn Future<Output = T> + Send>> + Send + Sync>>,
}

impl<T> AsyncPipeline<T>
where
    T: Send + 'static,
{
    pub fn new() -> Self {
        Self { stages: Vec::new() }
    }

    /// 添加处理阶段
    pub fn add_stage<F>(&mut self, stage: F)
    where
        F: Fn(T) -> Pin<Box<dyn Future<Output = T> + Send>> + Send + Sync + 'static,
    {
        self.stages.push(Box::new(stage));
    }

    /// 处理数据
    pub async fn process(&self, mut data: T) -> T {
        for stage in &self.stages {
            data = stage(data).await;
        }
        data
    }
}

/// 异步屏障
pub struct AsyncBarrier {
    barrier: Arc<Barrier>,
    count: usize,
}

impl AsyncBarrier {
    pub fn new(count: usize) -> Self {
        Self {
            barrier: Arc::new(Barrier::new(count)),
            count,
        }
    }

    /// 等待所有参与者到达
    pub async fn wait(&self) -> bool {
        self.barrier.wait().await.is_leader()
    }
}

/// 异步通知
pub struct AsyncNotifier {
    notify: Arc<Notify>,
}

impl AsyncNotifier {
    pub fn new() -> Self {
        Self {
            notify: Arc::new(Notify::new()),
        }
    }

    /// 等待通知
    pub async fn wait(&self) {
        self.notify.notified().await;
    }

    /// 发送通知
    pub fn notify(&self) {
        self.notify.notify_one();
    }

    /// 通知所有等待者
    pub fn notify_all(&self) {
        self.notify.notify_waiters();
    }
}

/// 异步观察者模式
pub struct AsyncObserver<T> {
    observers: Arc<RwLock<Vec<mpsc::UnboundedSender<T>>>>,
}

impl<T> AsyncObserver<T>
where
    T: Clone + Send + 'static,
{
    pub fn new() -> Self {
        Self {
            observers: Arc::new(RwLock::new(Vec::new())),
        }
    }

    /// 添加观察者
    pub async fn add_observer(&self) -> mpsc::UnboundedReceiver<T> {
        let (tx, rx) = mpsc::unbounded_channel();
        let mut observers = self.observers.write().await;
        observers.push(tx);
        rx
    }

    /// 通知所有观察者
    pub async fn notify(&self, data: T) {
        let observers = self.observers.read().await;
        for observer in observers.iter() {
            let _ = observer.send(data.clone());
        }
    }
}

/// 异步限流器
pub struct AsyncRateLimiter {
    tokens: Arc<Mutex<usize>>,
    max_tokens: usize,
    refill_interval: Duration,
    refill_amount: usize,
}

impl AsyncRateLimiter {
    pub fn new(max_tokens: usize, refill_interval: Duration, refill_amount: usize) -> Self {
        let limiter = Self {
            tokens: Arc::new(Mutex::new(max_tokens)),
            max_tokens,
            refill_interval,
            refill_amount,
        };

        // 启动令牌补充任务
        limiter.start_refill_task();

        limiter
    }

    /// 获取令牌
    pub async fn acquire(&self) -> bool {
        let mut tokens = self.tokens.lock().await;
        if *tokens > 0 {
            *tokens -= 1;
            true
        } else {
            false
        }
    }

    /// 启动令牌补充任务
    fn start_refill_task(&self) {
        let tokens = self.tokens.clone();
        let max_tokens = self.max_tokens;
        let refill_interval = self.refill_interval;
        let refill_amount = self.refill_amount;

        tokio::spawn(async move {
            let mut interval = interval(refill_interval);

            loop {
                interval.tick().await;

                let mut tokens = tokens.lock().await;
                *tokens = (*tokens + refill_amount).min(max_tokens);
            }
        });
    }
}

/// 异步超时包装器
pub struct AsyncTimeout<T> {
    future: T,
    timeout: Duration,
}

impl<T> AsyncTimeout<T> {
    pub fn new(future: T, timeout: Duration) -> Self {
        Self { future, timeout }
    }
}

impl<T> Future for AsyncTimeout<T>
where
    T: Future,
{
    type Output = Result<T::Output, String>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match timeout(self.timeout, &mut self.future).poll(cx) {
            Poll::Ready(Ok(result)) => Poll::Ready(Ok(result)),
            Poll::Ready(Err(_)) => Poll::Ready(Err("操作超时".to_string())),
            Poll::Pending => Poll::Pending,
        }
    }
}

/// 异步重试包装器
pub struct AsyncRetry<T> {
    future: T,
    strategy: RetryStrategy,
    max_attempts: u32,
}

impl<T> AsyncRetry<T> {
    pub fn new(future: T, strategy: RetryStrategy, max_attempts: u32) -> Self {
        Self {
            future,
            strategy,
            max_attempts,
        }
    }
}

impl<T> Future for AsyncRetry<T>
where
    T: Future<Output = Result<T::Output, String>> + Clone,
{
    type Output = Result<T::Output, String>;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // 简化实现，实际应用中需要更复杂的重试逻辑
        self.get_mut().future.poll(cx)
    }
}

/// 异步批处理示例
async fn batch_processing_example() -> Result<(), String> {
    info!("开始批处理示例");

    let processor = BatchProcessor::new(
        10,                     // 批大小
        Duration::from_secs(5), // 刷新间隔
        |batch: Vec<i32>| {
            Box::pin(async move {
                info!("处理批次: {:?}", batch);
                // 模拟处理时间
                sleep(Duration::from_millis(100)).await;
                Ok(())
            })
        },
    );

    // 添加数据
    for i in 0..25 {
        processor.add(i).await?;
    }

    // 启动定时刷新
    let _flush_handle = processor.start_flush_timer().await;

    // 等待处理完成
    sleep(Duration::from_secs(2)).await;

    Ok(())
}

/// 异步流处理示例
async fn stream_processing_example() -> Result<(), String> {
    info!("开始流处理示例");

    let data = (0..100).collect::<Vec<i32>>();
    let stream = stream::iter(data);

    let processor = StreamProcessor::new(10, 5);

    let results = processor
        .process_stream(stream, |item| {
            Box::pin(async move {
                // 模拟异步处理
                sleep(Duration::from_millis(10)).await;
                Ok(item * 2)
            })
        })
        .await?;

    info!("流处理完成，处理了 {} 个项目", results.len());
    Ok(())
}

/// 异步缓存示例
async fn cache_example() -> Result<(), String> {
    info!("开始缓存示例");

    let cache = AsyncCache::new(Duration::from_secs(5), 100);

    // 设置值
    cache.set("key1".to_string(), "value1".to_string()).await?;
    cache.set("key2".to_string(), "value2".to_string()).await?;

    // 获取值
    let value1 = cache.get(&"key1".to_string()).await;
    let value2 = cache.get(&"key2".to_string()).await;

    info!("缓存值: {:?}, {:?}", value1, value2);

    // 等待过期
    sleep(Duration::from_secs(6)).await;

    // 再次获取
    let value1_expired = cache.get(&"key1".to_string()).await;
    info!("过期后的值: {:?}", value1_expired);

    Ok(())
}

/// 异步工作池示例
async fn worker_pool_example() -> Result<(), String> {
    info!("开始工作池示例");

    let mut pool = AsyncWorkerPool::new(
        4, // 工作线程数
        |task: i32| {
            Box::pin(async move {
                // 模拟工作
                sleep(Duration::from_millis(100)).await;
                task * 2
            })
        },
    );

    // 提交任务
    for i in 0..10 {
        pool.submit(i).await?;
    }

    // 收集结果
    let mut results = Vec::new();
    for _ in 0..10 {
        if let Some(result) = pool.get_result().await {
            results.push(result);
        }
    }

    info!("工作池结果: {:?}", results);

    pool.shutdown().await;
    Ok(())
}

/// 异步事件总线示例
async fn event_bus_example() -> Result<(), String> {
    info!("开始事件总线示例");

    let event_bus = AsyncEventBus::new();

    // 订阅事件
    let mut subscriber1 = event_bus.subscribe("test".to_string()).await;
    let mut subscriber2 = event_bus.subscribe("test".to_string()).await;

    // 发布事件
    event_bus
        .publish("test", "Hello, World!".to_string())
        .await?;

    // 接收事件
    if let Some(event) = subscriber1.recv().await {
        info!("订阅者1收到事件: {}", event);
    }

    if let Some(event) = subscriber2.recv().await {
        info!("订阅者2收到事件: {}", event);
    }

    Ok(())
}

/// 异步管道示例
async fn pipeline_example() -> Result<(), String> {
    info!("开始管道示例");

    let mut pipeline = AsyncPipeline::new();

    // 添加处理阶段
    pipeline.add_stage(|x: i32| {
        Box::pin(async move {
            sleep(Duration::from_millis(10)).await;
            x + 1
        })
    });

    pipeline.add_stage(|x: i32| {
        Box::pin(async move {
            sleep(Duration::from_millis(10)).await;
            x * 2
        })
    });

    pipeline.add_stage(|x: i32| {
        Box::pin(async move {
            sleep(Duration::from_millis(10)).await;
            x - 1
        })
    });

    // 处理数据
    let result = pipeline.process(5).await;
    info!("管道处理结果: {}", result);

    Ok(())
}

/// 异步限流示例
async fn rate_limiter_example() -> Result<(), String> {
    info!("开始限流示例");

    let limiter = AsyncRateLimiter::new(5, Duration::from_secs(1), 2);

    // 尝试获取令牌
    for i in 0..10 {
        if limiter.acquire().await {
            info!("请求 {} 获得令牌", i);
        } else {
            info!("请求 {} 被限流", i);
        }
        sleep(Duration::from_millis(100)).await;
    }

    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();

    info!("开始异步编程模式示例");

    // 运行各种示例
    batch_processing_example().await?;
    stream_processing_example().await?;
    cache_example().await?;
    worker_pool_example().await?;
    event_bus_example().await?;
    pipeline_example().await?;
    rate_limiter_example().await?;

    info!("所有示例完成");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_task_manager() {
        let manager = TaskManager::new();

        manager
            .spawn_task("test".to_string(), async {
                sleep(Duration::from_millis(100)).await;
            })
            .await
            .unwrap();

        sleep(Duration::from_millis(200)).await;
        manager.stop_task("test").await.unwrap();
    }

    #[tokio::test]
    async fn test_backpressure_controller() {
        let controller = BackpressureController::new(5);

        let permit1 = controller.acquire().await.unwrap();
        let permit2 = controller.acquire().await.unwrap();

        assert_eq!(controller.current_pending().await, 2);

        drop(permit1);
        drop(permit2);

        sleep(Duration::from_millis(10)).await;
        assert_eq!(controller.current_pending().await, 0);
    }

    #[tokio::test]
    async fn test_async_cache() {
        let cache = AsyncCache::new(Duration::from_secs(1), 10);

        cache
            .set("key".to_string(), "value".to_string())
            .await
            .unwrap();
        assert_eq!(
            cache.get(&"key".to_string()).await,
            Some("value".to_string())
        );

        sleep(Duration::from_secs(2)).await;
        assert_eq!(cache.get(&"key".to_string()).await, None);
    }

    #[tokio::test]
    async fn test_retry_strategy() {
        let strategy = RetryStrategy::Exponential {
            base: Duration::from_millis(100),
            max: Duration::from_secs(1),
            multiplier: 2.0,
        };

        assert_eq!(strategy.get_delay(0), Duration::from_millis(100));
        assert_eq!(strategy.get_delay(1), Duration::from_millis(200));
        assert_eq!(strategy.get_delay(2), Duration::from_millis(400));
    }

    #[tokio::test]
    async fn test_concurrency_limiter() {
        let limiter = ConcurrencyLimiter::new(2);

        let result = limiter.execute(async { Ok("success") }).await;
        assert_eq!(result, Ok("success"));
    }

    #[tokio::test]
    async fn test_async_barrier() {
        let barrier = AsyncBarrier::new(2);

        let barrier_clone = barrier.clone();
        let handle = tokio::spawn(async move { barrier_clone.wait().await });

        let is_leader = barrier.wait().await;
        let handle_result = handle.await.unwrap();

        assert!(is_leader || handle_result);
    }

    #[tokio::test]
    async fn test_async_notifier() {
        let notifier = AsyncNotifier::new();

        let notifier_clone = notifier.clone();
        let handle = tokio::spawn(async move { notifier_clone.wait().await });

        sleep(Duration::from_millis(100)).await;
        notifier.notify();

        handle.await.unwrap();
    }

    #[tokio::test]
    async fn test_async_observer() {
        let observer = AsyncObserver::new();

        let mut receiver = observer.add_observer().await;

        observer.notify("test".to_string()).await;

        let message = receiver.recv().await.unwrap();
        assert_eq!(message, "test");
    }

    #[tokio::test]
    async fn test_async_rate_limiter() {
        let limiter = AsyncRateLimiter::new(2, Duration::from_millis(100), 1);

        assert!(limiter.acquire().await);
        assert!(limiter.acquire().await);
        assert!(!limiter.acquire().await);

        sleep(Duration::from_millis(150)).await;
        assert!(limiter.acquire().await);
    }
}
