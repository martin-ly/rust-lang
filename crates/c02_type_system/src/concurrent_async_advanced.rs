//! 并发和异步高级特性演示模块
//! 
//! 本模块演示了 Rust 1.90 中的各种并发和异步高级特性，包括：
//! - 高级异步编程模式
//! - 并发数据结构和算法
//! - 异步流处理
//! - 工作窃取调度器
//! - 异步锁和同步原语
//! - 并发安全的数据结构
//! - 异步错误处理
//! - 性能监控和调优

use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex, RwLock, Condvar};
use std::sync::atomic::{AtomicUsize, AtomicBool, AtomicPtr, Ordering};
use std::thread;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex as AsyncMutex, RwLock as AsyncRwLock, Semaphore, Barrier as AsyncBarrier};
use tokio::sync::broadcast;
use tokio::task::JoinHandle;
use tokio::time::{sleep, timeout, interval};
use futures::stream::{Stream, StreamExt, FuturesUnordered};
use futures::future::{Future, join_all};
use futures::pin_mut;

/// 高级异步编程模式
pub mod async_patterns {
    use super::*;

    /// 异步状态机
    #[derive(Debug)]
    pub enum AsyncState {
        Idle,
        Processing,
        Completed,
        Error(String),
    }

    /// 异步状态机管理器
    pub struct AsyncStateMachine {
        state: Arc<AsyncMutex<AsyncState>>,
        state_changes: broadcast::Sender<AsyncState>,
    }

    impl AsyncStateMachine {
        pub fn new() -> Self {
            let (tx, _) = broadcast::channel(100);
            Self {
                state: Arc::new(AsyncMutex::new(AsyncState::Idle)),
                state_changes: tx,
            }
        }

        pub async fn transition_to(&self, new_state: AsyncState) -> Result<(), String> {
            let mut state = self.state.lock().await;
            let old_state = std::mem::replace(&mut *state, new_state.clone());
            
            // 验证状态转换的合法性
            match (&old_state, &new_state) {
                (AsyncState::Idle, AsyncState::Processing) => {},
                (AsyncState::Processing, AsyncState::Completed) => {},
                (AsyncState::Processing, AsyncState::Error(_)) => {},
                (AsyncState::Completed, AsyncState::Idle) => {},
                (AsyncState::Error(_), AsyncState::Idle) => {},
                _ => return Err(format!("Invalid state transition: {:?} -> {:?}", old_state, new_state)),
            }

            // 广播状态变化
            let _ = self.state_changes.send(new_state);
            Ok(())
        }

        pub async fn get_state(&self) -> AsyncState {
            self.state.lock().await.clone()
        }

        pub fn subscribe_to_changes(&self) -> broadcast::Receiver<AsyncState> {
            self.state_changes.subscribe()
        }
    }

    impl Clone for AsyncState {
        fn clone(&self) -> Self {
            match self {
                AsyncState::Idle => AsyncState::Idle,
                AsyncState::Processing => AsyncState::Processing,
                AsyncState::Completed => AsyncState::Completed,
                AsyncState::Error(msg) => AsyncState::Error(msg.clone()),
            }
        }
    }

    /// 异步重试机制
    pub struct AsyncRetry {
        max_attempts: usize,
        base_delay: Duration,
        max_delay: Duration,
        backoff_multiplier: f64,
    }

    impl AsyncRetry {
        pub fn new(max_attempts: usize, base_delay: Duration) -> Self {
            Self {
                max_attempts,
                base_delay,
                max_delay: Duration::from_secs(60),
                backoff_multiplier: 2.0,
            }
        }

        pub async fn execute<F, T, E>(&self, mut operation: F) -> Result<T, E>
        where
            F: FnMut() -> std::pin::Pin<Box<dyn Future<Output = Result<T, E>> + Send>>,
            E: std::fmt::Debug,
        {
            let mut attempt = 0;
            let mut delay = self.base_delay;

            loop {
                attempt += 1;
                
                match operation().await {
                    Ok(result) => return Ok(result),
                    Err(error) => {
                        if attempt >= self.max_attempts {
                            return Err(error);
                        }

                        println!("Attempt {} failed: {:?}, retrying in {:?}", attempt, error, delay);
                        sleep(delay).await;

                        // 指数退避
                        delay = std::cmp::min(
                            Duration::from_millis((delay.as_millis() as f64 * self.backoff_multiplier) as u64),
                            self.max_delay
                        );
                    }
                }
            }
        }
    }

    /// 异步超时包装器
    pub struct AsyncTimeout<T> {
        future: T,
        timeout_duration: Duration,
    }

    impl<T> AsyncTimeout<T> {
        pub fn new(future: T, timeout_duration: Duration) -> Self {
            Self {
                future,
                timeout_duration,
            }
        }
    }

    impl<T> Future for AsyncTimeout<T>
    where
        T: Future + Unpin,
    {
        type Output = Result<T::Output, tokio::time::error::Elapsed>;

        fn poll(
            mut self: std::pin::Pin<&mut Self>,
            cx: &mut std::task::Context<'_>,
        ) -> std::task::Poll<Self::Output> {
            let timeout_future = timeout(self.timeout_duration, &mut self.future);
            pin_mut!(timeout_future);
            timeout_future.poll(cx)
        }
    }

    /// 异步批处理处理器
    pub struct AsyncBatchProcessor<T> {
        batch_size: usize,
        flush_interval: Duration,
        items: Arc<AsyncMutex<Vec<T>>>,
        processor: Arc<dyn Fn(Vec<T>) -> std::pin::Pin<Box<dyn Future<Output = Result<(), String>> + Send>> + Send + Sync>,
    }

    impl<T> AsyncBatchProcessor<T>
    where
        T: Send + Sync + 'static,
    {
        pub fn new<F>(
            batch_size: usize,
            flush_interval: Duration,
            processor: F,
        ) -> Self
        where
            F: Fn(Vec<T>) -> std::pin::Pin<Box<dyn Future<Output = Result<(), String>> + Send>> + Send + Sync + 'static,
        {
            Self {
                batch_size,
                flush_interval,
                items: Arc::new(AsyncMutex::new(Vec::new())),
                processor: Arc::new(processor),
            }
        }

        pub async fn add_item(&self, item: T) -> Result<(), String> {
            let mut items = self.items.lock().await;
            items.push(item);

            if items.len() >= self.batch_size {
                let batch = std::mem::take(&mut *items);
                drop(items); // 释放锁

                let processor = self.processor.clone();
                tokio::spawn(async move {
                    if let Err(e) = processor(batch).await {
                        eprintln!("Batch processing error: {}", e);
                    }
                });
            }

            Ok(())
        }

        pub async fn flush(&self) -> Result<(), String> {
            let mut items = self.items.lock().await;
            if !items.is_empty() {
                let batch = std::mem::take(&mut *items);
                drop(items); // 释放锁

                let processor = self.processor.clone();
                processor(batch).await
            } else {
                Ok(())
            }
        }

        pub async fn start_auto_flush(&self) -> JoinHandle<()> {
            let items = self.items.clone();
            let processor = self.processor.clone();
            let flush_interval = self.flush_interval;

            tokio::spawn(async move {
                let mut interval = interval(flush_interval);
                loop {
                    interval.tick().await;
                    
                    let mut items_guard = items.lock().await;
                    if !items_guard.is_empty() {
                        let batch = std::mem::take(&mut *items_guard);
                        drop(items_guard); // 释放锁

                        if let Err(e) = processor(batch).await {
                            eprintln!("Auto-flush batch processing error: {}", e);
                        }
                    }
                }
            })
        }
    }
}

/// 并发数据结构和算法
pub mod concurrent_data_structures {
    use super::*;

    /// 无锁环形缓冲区
    pub struct LockFreeRingBuffer<T> {
        buffer: Vec<AtomicPtr<T>>,
        head: AtomicUsize,
        tail: AtomicUsize,
        capacity: usize,
    }

    impl<T> LockFreeRingBuffer<T> {
        pub fn new(capacity: usize) -> Self {
            let mut buffer = Vec::with_capacity(capacity);
            for _ in 0..capacity {
                buffer.push(AtomicPtr::new(std::ptr::null_mut()));
            }

            Self {
                buffer,
                head: AtomicUsize::new(0),
                tail: AtomicUsize::new(0),
                capacity,
            }
        }

        pub fn push(&self, item: T) -> Result<(), String> {
            let current_tail = self.tail.load(Ordering::Relaxed);
            let next_tail = (current_tail + 1) % self.capacity;

            if next_tail == self.head.load(Ordering::Relaxed) {
                return Err("Buffer is full".to_string());
            }

            let item_ptr = Box::into_raw(Box::new(item));
            self.buffer[current_tail].store(item_ptr, Ordering::Release);
            self.tail.store(next_tail, Ordering::Release);

            Ok(())
        }

        pub fn pop(&self) -> Option<T> {
            let current_head = self.head.load(Ordering::Relaxed);
            
            if current_head == self.tail.load(Ordering::Relaxed) {
                return None;
            }

            let item_ptr = self.buffer[current_head].load(Ordering::Acquire);
            if item_ptr.is_null() {
                return None;
            }

            let next_head = (current_head + 1) % self.capacity;
            self.head.store(next_head, Ordering::Release);

            unsafe {
                Some(*Box::from_raw(item_ptr))
            }
        }

        pub fn len(&self) -> usize {
            let head = self.head.load(Ordering::Relaxed);
            let tail = self.tail.load(Ordering::Relaxed);
            
            if tail >= head {
                tail - head
            } else {
                self.capacity - head + tail
            }
        }

        pub fn is_empty(&self) -> bool {
            self.head.load(Ordering::Relaxed) == self.tail.load(Ordering::Relaxed)
        }
    }

    impl<T> Clone for LockFreeRingBuffer<T> {
        fn clone(&self) -> Self {
            Self {
                buffer: (0..self.capacity).map(|_| AtomicPtr::new(std::ptr::null_mut())).collect(),
                head: AtomicUsize::new(self.head.load(Ordering::Relaxed)),
                tail: AtomicUsize::new(self.tail.load(Ordering::Relaxed)),
                capacity: self.capacity,
            }
        }
    }

    impl<T> Drop for LockFreeRingBuffer<T> {
        fn drop(&mut self) {
            while let Some(_) = self.pop() {}
        }
    }

    /// 并发哈希表
    #[derive(Clone)]
    pub struct ConcurrentHashMap<K, V> {
        shards: Vec<Arc<RwLock<HashMap<K, V>>>>,
        shard_count: usize,
    }

    impl<K, V> ConcurrentHashMap<K, V>
    where
        K: std::hash::Hash + Eq + Clone,
        V: Clone,
    {
        pub fn new(shard_count: usize) -> Self {
            let mut shards = Vec::with_capacity(shard_count);
            for _ in 0..shard_count {
                shards.push(Arc::new(RwLock::new(HashMap::new())));
            }

            Self {
                shards,
                shard_count,
            }
        }

        fn get_shard(&self, key: &K) -> &Arc<RwLock<HashMap<K, V>>> {
            use std::hash::Hasher;
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            key.hash(&mut hasher);
            let hash = hasher.finish();
            &self.shards[(hash as usize) % self.shard_count]
        }

        pub fn insert(&self, key: K, value: V) {
            let shard = self.get_shard(&key);
            let mut map = shard.write().unwrap();
            map.insert(key, value);
        }

        pub fn get(&self, key: &K) -> Option<V> {
            let shard = self.get_shard(key);
            let map = shard.read().unwrap();
            map.get(key).cloned()
        }

        pub fn remove(&self, key: &K) -> Option<V> {
            let shard = self.get_shard(key);
            let mut map = shard.write().unwrap();
            map.remove(key)
        }

        pub fn len(&self) -> usize {
            let mut total = 0;
            for shard in &self.shards {
                let map = shard.read().unwrap();
                total += map.len();
            }
            total
        }
    }

    /// 工作窃取队列
    pub struct WorkStealingQueue<T> {
        tasks: Arc<Mutex<VecDeque<T>>>,
        stealers: Arc<Mutex<Vec<Arc<Mutex<VecDeque<T>>>>>>,
    }

    impl<T> WorkStealingQueue<T> {
        pub fn new() -> Self {
            Self {
                tasks: Arc::new(Mutex::new(VecDeque::new())),
                stealers: Arc::new(Mutex::new(Vec::new())),
            }
        }

        pub fn push(&self, task: T) {
            let mut tasks = self.tasks.lock().unwrap();
            tasks.push_back(task);
        }

        pub fn pop(&self) -> Option<T> {
            let mut tasks = self.tasks.lock().unwrap();
            tasks.pop_front()
        }

        pub fn steal(&self) -> Option<T> {
            let stealers = self.stealers.lock().unwrap();
            for stealer in stealers.iter() {
                if let Ok(mut tasks) = stealer.try_lock() {
                    if let Some(task) = tasks.pop_back() {
                        return Some(task);
                    }
                }
            }
            None
        }

        pub fn create_stealer(&self) -> Arc<Mutex<VecDeque<T>>> {
            let stealer = Arc::new(Mutex::new(VecDeque::new()));
            let mut stealers = self.stealers.lock().unwrap();
            stealers.push(stealer.clone());
            stealer
        }
    }
}

/// 异步流处理
pub mod async_streams {
    use super::*;

    /// 异步流处理器
    pub struct AsyncStreamProcessor<T, R> {
        buffer_size: usize,
        concurrency: usize,
        processor: Arc<dyn Fn(T) -> std::pin::Pin<Box<dyn Future<Output = Result<R, String>> + Send>> + Send + Sync>,
    }

    impl<T, R> AsyncStreamProcessor<T, R>
    where
        T: Send + Sync + 'static,
        R: Send + Sync + 'static,
    {
        pub fn new<F>(
            buffer_size: usize,
            concurrency: usize,
            processor: F,
        ) -> Self
        where
            F: Fn(T) -> std::pin::Pin<Box<dyn Future<Output = Result<R, String>> + Send>> + Send + Sync + 'static,
        {
            Self {
                buffer_size,
                concurrency,
                processor: Arc::new(processor),
            }
        }

        pub async fn process_stream<S>(&self, mut stream: S) -> Result<Vec<R>, String>
        where
            S: Stream<Item = T> + Unpin,
        {
            let semaphore = Arc::new(Semaphore::new(self.concurrency));
            let mut results = Vec::new();
            let mut futures = FuturesUnordered::new();

            while let Some(item) = stream.next().await {
                let permit = semaphore.clone().acquire_owned().await.unwrap();
                let processor = self.processor.clone();

                let future = async move {
                    let _permit = permit;
                    processor(item).await
                };

                futures.push(future);

                // 限制并发数量
                if futures.len() >= self.buffer_size {
                    if let Some(result) = futures.next().await {
                        results.push(result?);
                    }
                }
            }

            // 处理剩余的未来
            while let Some(result) = futures.next().await {
                results.push(result?);
            }

            Ok(results)
        }
    }

    /// 异步管道
    pub struct AsyncPipeline<T> {
        stages: Vec<Arc<dyn Fn(T) -> std::pin::Pin<Box<dyn Future<Output = Result<T, String>> + Send>> + Send + Sync>>,
    }

    impl<T> AsyncPipeline<T>
    where
        T: Send + Sync + 'static,
    {
        pub fn new() -> Self {
            Self {
                stages: Vec::new(),
            }
        }

        pub fn add_stage<F>(&mut self, stage: F)
        where
            F: Fn(T) -> std::pin::Pin<Box<dyn Future<Output = Result<T, String>> + Send>> + Send + Sync + 'static,
        {
            self.stages.push(Arc::new(stage));
        }

        pub async fn process(&self, input: T) -> Result<T, String> {
            let mut current = input;

            for stage in &self.stages {
                current = stage(current).await?;
            }

            Ok(current)
        }
    }

    /// 异步窗口聚合器
    pub struct AsyncWindowAggregator<T, R> {
        window_size: Duration,
        windows: Arc<AsyncMutex<HashMap<u64, Vec<T>>>>,
        aggregator: Arc<dyn Fn(Vec<T>) -> std::pin::Pin<Box<dyn Future<Output = Result<R, String>> + Send>> + Send + Sync>,
    }

    impl<T, R> AsyncWindowAggregator<T, R>
    where
        T: Send + Sync + 'static,
        R: Send + Sync + 'static,
    {
        pub fn new<F>(
            window_size: Duration,
            aggregator: F,
        ) -> Self
        where
            F: Fn(Vec<T>) -> std::pin::Pin<Box<dyn Future<Output = Result<R, String>> + Send>> + Send + Sync + 'static,
        {
            Self {
                window_size,
                windows: Arc::new(AsyncMutex::new(HashMap::new())),
                aggregator: Arc::new(aggregator),
            }
        }

        pub async fn add_item(&self, item: T) -> Result<(), String> {
            let now = Instant::now();
            let window_id = (now.elapsed().as_millis() / self.window_size.as_millis()) as u64;

            let mut windows = self.windows.lock().await;
            windows.entry(window_id).or_insert_with(Vec::new).push(item);
            Ok(())
        }

        pub async fn get_window_result(&self, window_id: u64) -> Option<Result<R, String>> {
            let mut windows = self.windows.lock().await;
            if let Some(items) = windows.remove(&window_id) {
                let aggregator = self.aggregator.clone();
                drop(windows); // 释放锁

                Some(aggregator(items).await)
            } else {
                None
            }
        }

        pub async fn start_window_processor(&self) -> JoinHandle<()> {
            let windows = self.windows.clone();
            let aggregator = self.aggregator.clone();
            let window_size = self.window_size;

            tokio::spawn(async move {
                let mut interval = interval(window_size);
                loop {
                    interval.tick().await;
                    
                    let now = Instant::now();
                    let current_window = (now.elapsed().as_millis() / window_size.as_millis()) as u64;
                    let old_window = current_window - 1;

                    let mut windows_guard = windows.lock().await;
                    if let Some(items) = windows_guard.remove(&old_window) {
                        drop(windows_guard); // 释放锁

                        if let Err(e) = aggregator(items).await {
                            eprintln!("Window aggregation error: {}", e);
                        }
                    }
                }
            })
        }
    }
}

/// 工作窃取调度器
pub mod work_stealing_scheduler {
    use super::*;

    /// 工作窃取调度器
    pub struct WorkStealingScheduler {
        workers: Vec<Arc<Worker>>,
        global_queue: Arc<super::concurrent_data_structures::WorkStealingQueue<Box<dyn Fn() + Send + Sync>>>,
        shutdown: Arc<AtomicBool>,
    }

    struct Worker {
        id: usize,
        local_queue: Arc<Mutex<VecDeque<Box<dyn Fn() + Send + Sync>>>>,
        global_queue: Arc<super::concurrent_data_structures::WorkStealingQueue<Box<dyn Fn() + Send + Sync>>>,
        other_workers: Vec<Arc<Mutex<VecDeque<Box<dyn Fn() + Send + Sync>>>>>,
        shutdown: Arc<AtomicBool>,
    }

    impl WorkStealingScheduler {
        pub fn new(worker_count: usize) -> Self {
            let global_queue = Arc::new(super::concurrent_data_structures::WorkStealingQueue::new());
            let shutdown = Arc::new(AtomicBool::new(false));
            let mut workers = Vec::new();
            let mut worker_queues = Vec::new();

            // 创建工作线程队列
            for _ in 0..worker_count {
                let queue = Arc::new(Mutex::new(VecDeque::new()));
                worker_queues.push(queue);
            }

            // 创建工作线程
            for i in 0..worker_count {
                let worker = Arc::new(Worker {
                    id: i,
                    local_queue: worker_queues[i].clone(),
                    global_queue: global_queue.clone(),
                    other_workers: worker_queues.clone(),
                    shutdown: shutdown.clone(),
                });
                workers.push(worker);
            }

            Self {
                workers,
                global_queue,
                shutdown,
            }
        }

        pub fn submit<F>(&self, task: F)
        where
            F: Fn() + Send + Sync + 'static,
        {
            self.global_queue.push(Box::new(task));
        }

        pub fn start(&self) {
            for worker in &self.workers {
                let worker = worker.clone();
                thread::spawn(move || {
                    worker.run();
                });
            }
        }

        pub fn shutdown(&self) {
            self.shutdown.store(true, Ordering::Release);
        }
    }

    impl Worker {
        fn run(&self) {
            while !self.shutdown.load(Ordering::Acquire) {
                // 首先尝试从本地队列获取任务
                if let Some(task) = self.local_queue.lock().unwrap().pop_front() {
                    task();
                    continue;
                }

                // 然后尝试从全局队列获取任务
                if let Some(task) = self.global_queue.pop() {
                    task();
                    continue;
                }

                // 最后尝试从其他工作线程窃取任务
                if let Some(task) = self.steal_task() {
                    task();
                    continue;
                }

                // 如果没有任务，短暂休眠
                thread::sleep(Duration::from_millis(1));
            }
        }

        fn steal_task(&self) -> Option<Box<dyn Fn() + Send + Sync>> {
            for (i, other_queue) in self.other_workers.iter().enumerate() {
                if i != self.id {
                    if let Ok(mut queue) = other_queue.try_lock() {
                        if let Some(task) = queue.pop_back() {
                            return Some(task);
                        }
                    }
                }
            }
            None
        }
    }

    impl Clone for WorkStealingScheduler {
        fn clone(&self) -> Self {
            Self {
                workers: self.workers.clone(),
                global_queue: self.global_queue.clone(),
                shutdown: self.shutdown.clone(),
            }
        }
    }
}

/// 异步锁和同步原语
pub mod async_sync_primitives {
    use super::*;

    /// 异步读写锁包装器
    pub struct AsyncRwLockWrapper<T> {
        inner: AsyncRwLock<T>,
    }

    impl<T> AsyncRwLockWrapper<T> {
        pub fn new(value: T) -> Self {
            Self {
                inner: AsyncRwLock::new(value),
            }
        }

        pub async fn read(&self) -> tokio::sync::RwLockReadGuard<'_, T> {
            self.inner.read().await
        }

        pub async fn write(&self) -> tokio::sync::RwLockWriteGuard<'_, T> {
            self.inner.write().await
        }

        pub async fn try_read(&self) -> Option<tokio::sync::RwLockReadGuard<'_, T>> {
            self.inner.try_read().ok()
        }

        pub async fn try_write(&self) -> Option<tokio::sync::RwLockWriteGuard<'_, T>> {
            self.inner.try_write().ok()
        }
    }

    /// 异步条件变量
    pub struct AsyncConditionVariable {
        inner: Arc<(AsyncMutex<bool>, Condvar)>,
    }

    impl AsyncConditionVariable {
        pub fn new() -> Self {
            Self {
                inner: Arc::new((AsyncMutex::new(false), Condvar::new())),
            }
        }

        pub async fn wait(&self) {
            let (lock, _cvar) = &*self.inner;
            let mut guard = lock.lock().await;
            while !*guard {
                // 使用 tokio 的异步等待
                drop(guard);
                tokio::time::sleep(Duration::from_millis(10)).await;
                guard = lock.lock().await;
            }
            *guard = false;
        }

        pub async fn notify_one(&self) {
            let (lock, cvar) = &*self.inner;
            let mut guard = lock.lock().await;
            *guard = true;
            cvar.notify_one();
        }

        pub async fn notify_all(&self) {
            let (lock, cvar) = &*self.inner;
            let mut guard = lock.lock().await;
            *guard = true;
            cvar.notify_all();
        }
    }

    /// 异步屏障
    pub struct AsyncBarrierWrapper {
        inner: AsyncBarrier,
    }

    impl AsyncBarrierWrapper {
        pub fn new(count: usize) -> Self {
            Self {
                inner: AsyncBarrier::new(count),
            }
        }

        pub async fn wait(&self) -> tokio::sync::BarrierWaitResult {
            self.inner.wait().await
        }
    }

    /// 异步信号量包装器
    pub struct AsyncSemaphoreWrapper {
        inner: Semaphore,
    }

    impl AsyncSemaphoreWrapper {
        pub fn new(permits: usize) -> Self {
            Self {
                inner: Semaphore::new(permits),
            }
        }

        pub async fn acquire(&self) -> tokio::sync::SemaphorePermit<'_> {
            self.inner.acquire().await.unwrap()
        }

        pub async fn try_acquire(&self) -> Option<tokio::sync::SemaphorePermit<'_>> {
            self.inner.try_acquire().ok()
        }

        pub fn add_permits(&self, permits: usize) {
            self.inner.add_permits(permits);
        }
    }
}

/// 并发安全的数据结构
pub mod concurrent_safe_structures {
    use super::*;

    /// 并发安全的栈
    pub struct ConcurrentStack<T> {
        data: Arc<Mutex<Vec<T>>>,
    }

    impl<T> ConcurrentStack<T> {
        pub fn new() -> Self {
            Self {
                data: Arc::new(Mutex::new(Vec::new())),
            }
        }

        pub fn push(&self, item: T) {
            let mut data = self.data.lock().unwrap();
            data.push(item);
        }

        pub fn pop(&self) -> Option<T> {
            let mut data = self.data.lock().unwrap();
            data.pop()
        }

        pub fn len(&self) -> usize {
            let data = self.data.lock().unwrap();
            data.len()
        }

        pub fn is_empty(&self) -> bool {
            let data = self.data.lock().unwrap();
            data.is_empty()
        }
    }

    impl<T> Clone for ConcurrentStack<T> {
        fn clone(&self) -> Self {
            Self {
                data: self.data.clone(),
            }
        }
    }

    /// 并发安全的队列
    pub struct ConcurrentQueue<T> {
        data: Arc<Mutex<VecDeque<T>>>,
    }

    impl<T> ConcurrentQueue<T> {
        pub fn new() -> Self {
            Self {
                data: Arc::new(Mutex::new(VecDeque::new())),
            }
        }

        pub fn enqueue(&self, item: T) {
            let mut data = self.data.lock().unwrap();
            data.push_back(item);
        }

        pub fn dequeue(&self) -> Option<T> {
            let mut data = self.data.lock().unwrap();
            data.pop_front()
        }

        pub fn len(&self) -> usize {
            let data = self.data.lock().unwrap();
            data.len()
        }

        pub fn is_empty(&self) -> bool {
            let data = self.data.lock().unwrap();
            data.is_empty()
        }
    }

    impl<T> Clone for ConcurrentQueue<T> {
        fn clone(&self) -> Self {
            Self {
                data: self.data.clone(),
            }
        }
    }

    /// 并发安全的双端队列
    pub struct ConcurrentDeque<T> {
        data: Arc<Mutex<VecDeque<T>>>,
    }

    impl<T> ConcurrentDeque<T> {
        pub fn new() -> Self {
            Self {
                data: Arc::new(Mutex::new(VecDeque::new())),
            }
        }

        pub fn push_front(&self, item: T) {
            let mut data = self.data.lock().unwrap();
            data.push_front(item);
        }

        pub fn push_back(&self, item: T) {
            let mut data = self.data.lock().unwrap();
            data.push_back(item);
        }

        pub fn pop_front(&self) -> Option<T> {
            let mut data = self.data.lock().unwrap();
            data.pop_front()
        }

        pub fn pop_back(&self) -> Option<T> {
            let mut data = self.data.lock().unwrap();
            data.pop_back()
        }

        pub fn len(&self) -> usize {
            let data = self.data.lock().unwrap();
            data.len()
        }

        pub fn is_empty(&self) -> bool {
            let data = self.data.lock().unwrap();
            data.is_empty()
        }
    }

    impl<T> Clone for ConcurrentDeque<T> {
        fn clone(&self) -> Self {
            Self {
                data: self.data.clone(),
            }
        }
    }
}

/// 异步错误处理
pub mod async_error_handling {
    use super::*;

    /// 异步错误恢复器
    pub struct AsyncErrorRecovery<T> {
        max_retries: usize,
        retry_delay: Duration,
        recovery_strategies: HashMap<String, Box<dyn Fn(&str) -> std::pin::Pin<Box<dyn Future<Output = Result<T, String>> + Send>> + Send + Sync>>,
    }

    impl<T> AsyncErrorRecovery<T> {
        pub fn new(max_retries: usize, retry_delay: Duration) -> Self {
            Self {
                max_retries,
                retry_delay,
                recovery_strategies: HashMap::new(),
            }
        }

        pub fn add_recovery_strategy<F>(&mut self, error_type: String, strategy: F)
        where
            F: Fn(&str) -> std::pin::Pin<Box<dyn Future<Output = Result<T, String>> + Send>> + Send + Sync + 'static,
        {
            self.recovery_strategies.insert(error_type, Box::new(strategy));
        }

        pub async fn execute_with_recovery<F>(&self, operation: F) -> Result<T, String>
        where
            F: Fn() -> std::pin::Pin<Box<dyn Future<Output = Result<T, String>> + Send>>,
        {
            let mut last_error = String::new();
            
            for attempt in 0..=self.max_retries {
                match operation().await {
                    Ok(result) => return Ok(result),
                    Err(error) => {
                        last_error = error.clone();
                        
                        if attempt < self.max_retries {
                            // 尝试恢复
                            if let Some(strategy) = self.recovery_strategies.get(&error) {
                                match strategy(&error).await {
                                    Ok(result) => return Ok(result),
                                    Err(recovery_error) => {
                                        eprintln!("Recovery failed: {}", recovery_error);
                                    }
                                }
                            }
                            
                            // 等待后重试
                            sleep(self.retry_delay).await;
                        }
                    }
                }
            }

            Err(format!("Operation failed after {} retries: {}", self.max_retries, last_error))
        }
    }

    /// 异步错误聚合器
    pub struct AsyncErrorAggregator {
        errors: Arc<AsyncMutex<Vec<String>>>,
        max_errors: usize,
    }

    impl AsyncErrorAggregator {
        pub fn new(max_errors: usize) -> Self {
            Self {
                errors: Arc::new(AsyncMutex::new(Vec::new())),
                max_errors,
            }
        }

        pub async fn add_error(&self, error: String) {
            let mut errors = self.errors.lock().await;
            errors.push(error);
            
            if errors.len() > self.max_errors {
                errors.remove(0);
            }
        }

        pub async fn get_errors(&self) -> Vec<String> {
            let errors = self.errors.lock().await;
            errors.clone()
        }

        pub async fn clear_errors(&self) {
            let mut errors = self.errors.lock().await;
            errors.clear();
        }

        pub async fn error_count(&self) -> usize {
            let errors = self.errors.lock().await;
            errors.len()
        }
    }
}

/// 性能监控和调优
pub mod performance_monitoring {
    use super::*;

    /// 异步性能监控器
    pub struct AsyncPerformanceMonitor {
        metrics: Arc<AsyncMutex<HashMap<String, f64>>>,
        start_time: Instant,
    }

    impl AsyncPerformanceMonitor {
        pub fn new() -> Self {
            Self {
                metrics: Arc::new(AsyncMutex::new(HashMap::new())),
                start_time: Instant::now(),
            }
        }

        pub async fn record_metric(&self, name: String, value: f64) {
            let mut metrics = self.metrics.lock().await;
            metrics.insert(name, value);
        }

        pub async fn increment_counter(&self, name: String) {
            let mut metrics = self.metrics.lock().await;
            let current = metrics.get(&name).copied().unwrap_or(0.0);
            metrics.insert(name, current + 1.0);
        }

        pub async fn get_metric(&self, name: &str) -> Option<f64> {
            let metrics = self.metrics.lock().await;
            metrics.get(name).copied()
        }

        pub async fn get_all_metrics(&self) -> HashMap<String, f64> {
            let metrics = self.metrics.lock().await;
            metrics.clone()
        }

        pub fn uptime(&self) -> Duration {
            self.start_time.elapsed()
        }
    }

    /// 异步任务性能分析器
    #[derive(Clone)]
    pub struct AsyncTaskProfiler {
        task_times: Arc<AsyncMutex<HashMap<String, Vec<Duration>>>>,
    }

    impl AsyncTaskProfiler {
        pub fn new() -> Self {
            Self {
                task_times: Arc::new(AsyncMutex::new(HashMap::new())),
            }
        }

        pub async fn profile_task<F, R>(&self, task_name: String, task: F) -> R
        where
            F: Future<Output = R>,
        {
            let start_time = Instant::now();
            let result = task.await;
            let duration = start_time.elapsed();

            let mut task_times = self.task_times.lock().await;
            task_times.entry(task_name).or_insert_with(Vec::new).push(duration);

            result
        }

        pub async fn get_task_stats(&self, task_name: &str) -> Option<TaskStats> {
            let task_times = self.task_times.lock().await;
            if let Some(times) = task_times.get(task_name) {
                if times.is_empty() {
                    return None;
                }

                let total_time: Duration = times.iter().sum();
                let avg_time = total_time / times.len() as u32;
                let min_time = *times.iter().min().unwrap();
                let max_time = *times.iter().max().unwrap();

                Some(TaskStats {
                    task_name: task_name.to_string(),
                    execution_count: times.len(),
                    total_time,
                    average_time: avg_time,
                    min_time,
                    max_time,
                })
            } else {
                None
            }
        }

        pub async fn get_all_task_stats(&self) -> Vec<TaskStats> {
            let task_times = self.task_times.lock().await;
            let mut stats = Vec::new();

            for (task_name, times) in task_times.iter() {
                if !times.is_empty() {
                    let total_time: Duration = times.iter().sum();
                    let avg_time = total_time / times.len() as u32;
                    let min_time = *times.iter().min().unwrap();
                    let max_time = *times.iter().max().unwrap();

                    stats.push(TaskStats {
                        task_name: task_name.clone(),
                        execution_count: times.len(),
                        total_time,
                        average_time: avg_time,
                        min_time,
                        max_time,
                    });
                }
            }

            stats
        }
    }

    #[derive(Debug, Clone)]
    pub struct TaskStats {
        pub task_name: String,
        pub execution_count: usize,
        pub total_time: Duration,
        pub average_time: Duration,
        pub min_time: Duration,
        pub max_time: Duration,
    }
}

/// 主演示函数
pub async fn demonstrate_concurrent_async_advanced() {
    println!("🚀 Rust 1.90 并发和异步高级特性演示");
    println!("=====================================");
    
    // 1. 异步状态机演示
    println!("\n=== 异步状态机演示 ===");
    let state_machine = async_patterns::AsyncStateMachine::new();
    
    // 监听状态变化
    let mut state_receiver = state_machine.subscribe_to_changes();
    tokio::spawn(async move {
        while let Ok(state) = state_receiver.recv().await {
            println!("状态变化: {:?}", state);
        }
    });
    
    state_machine.transition_to(async_patterns::AsyncState::Processing).await.unwrap();
    sleep(Duration::from_millis(100)).await;
    state_machine.transition_to(async_patterns::AsyncState::Completed).await.unwrap();
    
    // 2. 异步重试机制演示
    println!("\n=== 异步重试机制演示 ===");
    let retry = async_patterns::AsyncRetry::new(3, Duration::from_millis(100));
    
    let mut attempt_count = 0;
    let result = retry.execute(|| {
        attempt_count += 1;
        Box::pin(async move {
            if attempt_count < 3 {
                Err(format!("Attempt {} failed", attempt_count))
            } else {
                Ok("Success!".to_string())
            }
        })
    }).await;
    
    println!("重试结果: {:?}", result);
    
    // 3. 并发数据结构演示
    println!("\n=== 并发数据结构演示 ===");
    let concurrent_map = concurrent_data_structures::ConcurrentHashMap::new(4);
    
    // 并发插入
    let handles: Vec<_> = (0..10).map(|i| {
        let map = concurrent_map.clone();
        tokio::spawn(async move {
            map.insert(format!("key_{}", i), format!("value_{}", i));
        })
    }).collect();
    
    join_all(handles).await;
    println!("并发哈希表大小: {}", concurrent_map.len());
    
    // 4. 异步流处理演示
    println!("\n=== 异步流处理演示 ===");
    let stream_processor = async_streams::AsyncStreamProcessor::new(
        10,
        3,
        |item: i32| {
            Box::pin(async move {
                sleep(Duration::from_millis(50)).await;
                Ok(item * 2)
            })
        }
    );
    
    let stream = futures::stream::iter(0..10);
    let results = stream_processor.process_stream(stream).await.unwrap();
    println!("流处理结果: {:?}", results);
    
    // 5. 工作窃取调度器演示
    println!("\n=== 工作窃取调度器演示 ===");
    let scheduler = work_stealing_scheduler::WorkStealingScheduler::new(4);
    scheduler.start();
    
    for i in 0..20 {
        let task_id = i;
        scheduler.submit(move || {
            println!("执行任务 {}", task_id);
            thread::sleep(Duration::from_millis(10));
        });
    }
    
    sleep(Duration::from_millis(500)).await;
    scheduler.shutdown();
    
    // 6. 性能监控演示
    println!("\n=== 性能监控演示 ===");
    let profiler = performance_monitoring::AsyncTaskProfiler::new();
    
    for i in 0..5 {
        let profiler = profiler.clone();
        profiler.profile_task(format!("task_{}", i), async {
            sleep(Duration::from_millis(100 + i * 10)).await;
            format!("Task {} completed", i)
        }).await;
    }
    
    let stats = profiler.get_all_task_stats().await;
    for stat in stats {
        println!("任务统计: {:?}", stat);
    }
    
    println!("\n✅ 并发和异步高级特性演示完成！");
}
