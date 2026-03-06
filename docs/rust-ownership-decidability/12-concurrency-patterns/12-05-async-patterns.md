# Rust 异步并发模式

> **Rust版本**: 1.94
> **覆盖范围**: async/await原理、任务调度、背压控制、超时处理
> **权威参考**: The Rust Async Book, Tokio Documentation

---

## 目录

- [Rust 异步并发模式](#rust-异步并发模式)
  - [目录](#目录)
  - [1. 异步编程基础](#1-异步编程基础)
    - [1.1 Future 与异步状态机](#11-future-与异步状态机)
    - [1.2 async/await 原理](#12-asyncawait-原理)
    - [1.3 Pin 与自引用](#13-pin-与自引用)
  - [2. 任务调度](#2-任务调度)
    - [2.1 运行时架构](#21-运行时架构)
    - [2.2 Work-Stealing 调度器](#22-work-stealing-调度器)
    - [2.3 优先级调度](#23-优先级调度)
    - [2.4 任务局部存储](#24-任务局部存储)
  - [3. 并发原语](#3-并发原语)
    - [3.1 异步 Mutex](#31-异步-mutex)
    - [3.2 异步 Channel](#32-异步-channel)
    - [Rust 1.94 Peekable::next\_if\_map 在异步流中的应用](#rust-194-peekablenext_if_map-在异步流中的应用)
    - [异步延迟初始化 (Rust 1.94)](#异步延迟初始化-rust-194)

---

## 1. 异步编程基础

### 1.1 Future 与异步状态机

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

/// Future 是 Rust 异步编程的核心抽象
/// 本质是一个可能尚未完成的计算

/// 手动实现 Future
pub struct TimerFuture {
    duration: std::time::Duration,
    started: Option<std::time::Instant>,
}

impl TimerFuture {
    pub fn new(duration: std::time::Duration) -> Self {
        Self { duration, started: None }
    }
}

impl Future for TimerFuture {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.started {
            None => {
                self.started = Some(std::time::Instant::now());
                cx.waker().wake_by_ref();
                Poll::Pending
            }
            Some(started) => {
                if started.elapsed() >= self.duration {
                    Poll::Ready(())
                } else {
                    cx.waker().wake_by_ref();
                    Poll::Pending
                }
            }
        }
    }
}

/// 异步状态机转换
///
/// async fn 会被编译器转换为状态机
///
/// async fn example() {
///     step1().await;
///     step2().await;
///     step3().await;
/// }
///
/// 大致转换为：
/// enum ExampleStateMachine {
///     Start,
///     Waiting1(/* 上下文 */),
///     Waiting2(/* 上下文 */),
///     Waiting3(/* 上下文 */),
///     Done,
/// }

/// 手动状态机示例
pub enum DownloadStateMachine {
    Start { url: String },
    Connecting { url: String },
    Downloading { url: String, bytes_received: usize },
    Complete { data: Vec<u8> },
    Error { error: String },
}

impl Future for DownloadStateMachine {
    type Output = Result<Vec<u8>, String>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        use DownloadStateMachine::*;

        match *self {
            Start { ref url } => {
                // 开始连接
                *self = Connecting { url: url.clone() };
                cx.waker().wake_by_ref();
                Poll::Pending
            }
            Connecting { ref url } => {
                // 检查连接状态
                // 简化：直接开始下载
                *self = Downloading {
                    url: url.clone(),
                    bytes_received: 0
                };
                cx.waker().wake_by_ref();
                Poll::Pending
            }
            Downloading { ref url, ref mut bytes_received } => {
                // 模拟下载进度
                *bytes_received += 1024;

                if *bytes_received >= 10240 {
                    *self = Complete {
                        data: vec![0u8; *bytes_received]
                    };
                }

                cx.waker().wake_by_ref();
                Poll::Pending
            }
            Complete { ref data } => {
                Poll::Ready(Ok(data.clone()))
            }
            Error { ref error } => {
                Poll::Ready(Err(error.clone()))
            }
        }
    }
}
```

### 1.2 async/await 原理

```rust
/// async/await 的零成本抽象
///
/// 编译器优化：
/// 1. 状态机枚举占用空间 = 最大变体的大小 + 判别式
/// 2. 没有运行时分配（除非使用 Box::pin）
/// 3. 可以被内联优化

/// 基础 async 函数
pub async fn basic_async() -> i32 {
    42
}

/// 组合多个 async 操作
pub async fn combined_operations() -> Result<String, Box<dyn std::error::Error>> {
    // 顺序执行
    let result1 = async_operation1().await?;
    let result2 = async_operation2().await?;

    Ok(format!("{} {}", result1, result2))
}

async fn async_operation1() -> Result<&'static str, Box<dyn std::error::Error>> {
    Ok("Hello")
}

async fn async_operation2() -> Result<&'static str, Box<dyn std::error::Error>> {
    Ok("World")
}

/// 递归 async 函数
/// 需要 Box::pin 因为递归类型大小不确定
pub fn recursive_async(n: u32) -> std::pin::Pin<Box<dyn std::future::Future<Output = u32>>> {
    Box::pin(async move {
        if n <= 1 {
            1
        } else {
            n * recursive_async(n - 1).await
        }
    })
}

/// async 块
pub fn async_blocks() -> impl std::future::Future<Output = i32> {
    async {
        let x = async { 1 }.await;
        let y = async { 2 }.await;
        x + y
    }
}

/// async move 块 - 捕获所有权
pub fn async_move_block(data: Vec<u8>) -> impl std::future::Future<Output = usize> {
    async move {
        data.len()
    }
}
```

### 1.3 Pin 与自引用

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

/// 为什么需要 Pin：
/// 异步状态机可能包含自引用（例如引用局部变量）
/// Pin 保证值在内存中不会被移动

/// 自引用结构示例
pub struct SelfReferential {
    data: String,
    // 指向 data 的指针
    ptr_to_data: *const String,
    // 标记为固定
    _pin: PhantomPinned,
}

impl SelfReferential {
    pub fn new(data: String) -> Self {
        let mut this = Self {
            data,
            ptr_to_data: std::ptr::null(),
            _pin: PhantomPinned,
        };

        // 创建指针
        let ptr = &this.data as *const String;
        this.ptr_to_data = ptr;

        this
    }

    /// 安全访问需要 Pin
    pub fn get_data(self: Pin<&Self>) -> &str {
        &self.data
    }

    /// 通过指针访问
    pub unsafe fn get_via_ptr(self: Pin<&Self>) -> &str {
        &*self.ptr_to_data
    }
}

/// 使用 Box::pin 创建 Pin<Box<T>>
pub fn create_pinned() -> Pin<Box<SelfReferential>> {
    let data = "Hello".to_string();
    Box::pin(SelfReferential::new(data))
}

/// Pin 投影（安全地获取内部字段的 Pin）
pub struct AsyncFileReader {
    file: tokio::fs::File,
    buffer: Vec<u8>,
    _pin: PhantomPinned,
}

impl AsyncFileReader {
    /// 投影 file 字段
    fn file(self: Pin<&mut Self>) -> Pin<&mut tokio::fs::File> {
        unsafe { self.map_unchecked_mut(|s| &mut s.file) }
    }

    /// 投影 buffer 字段（不需要 Pin，因为 Vec 是 Unpin）
    fn buffer(self: Pin<&mut Self>) -> &mut Vec<u8> {
        unsafe { &mut self.get_unchecked_mut().buffer }
    }
}
```

---

## 2. 任务调度

### 2.1 运行时架构

```rust
use tokio::runtime::{Builder, Runtime};

/// 自定义 Tokio 运行时配置
pub fn create_optimized_runtime() -> Runtime {
    Builder::new_multi_thread()
        .worker_threads(num_cpus::get())
        .max_blocking_threads(512)
        .thread_stack_size(2 * 1024 * 1024) // 2MB
        .thread_name("tokio-worker")
        .enable_all()
        .event_interval(61) // 减少调度频率，提高吞吐量
        .global_queue_interval(61)
        .max_io_events_per_tick(1024)
        .build()
        .expect("Failed to create runtime")
}

/// 专用运行时示例
pub struct DedicatedRuntimes {
    /// IO 密集型任务
    io_runtime: Runtime,
    /// CPU 密集型任务
    cpu_runtime: Runtime,
    /// 定时任务
    timer_runtime: Runtime,
}

impl DedicatedRuntimes {
    pub fn new() -> Self {
        Self {
            io_runtime: Builder::new_multi_thread()
                .worker_threads(4)
                .enable_io()
                .thread_name("io-worker")
                .build()
                .unwrap(),

            cpu_runtime: Builder::new_multi_thread()
                .worker_threads(num_cpus::get())
                .enable_time()
                .thread_name("cpu-worker")
                .build()
                .unwrap(),

            timer_runtime: Builder::new_current_thread()
                .enable_time()
                .thread_name("timer")
                .build()
                .unwrap(),
        }
    }

    pub fn spawn_io<F>(&self, future: F) -> tokio::task::JoinHandle<F::Output>
    where
        F: std::future::Future + Send + 'static,
        F::Output: Send + 'static,
    {
        self.io_runtime.spawn(future)
    }

    pub fn spawn_cpu<F>(&self, future: F) -> tokio::task::JoinHandle<F::Output>
    where
        F: std::future::Future + Send + 'static,
        F::Output: Send + 'static,
    {
        self.cpu_runtime.spawn(future)
    }
}
```

### 2.2 Work-Stealing 调度器

```rust
use tokio::task::{JoinSet, spawn_local, LocalSet};

/// Work-Stealing 原理：
/// 1. 每个 worker 线程有自己的任务队列
/// 2. 当队列为空时，从其他线程"窃取"任务
/// 3. 减少锁竞争，提高缓存局部性

/// 批量任务处理
pub async fn batch_processing<T, F>(items: Vec<T>, processor: F) -> Vec<F::Output>
where
    F: Fn(T) -> tokio::task::JoinHandle<F::Output> + Clone,
    F::Output: Send + 'static,
{
    let mut set = JoinSet::new();

    for item in items {
        let proc = processor.clone();
        set.spawn(async move { proc(item).await.unwrap() });
    }

    let mut results = vec![];
    while let Some(result) = set.join_next().await {
        results.push(result.unwrap());
    }

    results
}

/// 任务亲和性（绑定到特定线程）
pub async fn spawn_with_affinity<F>(affinity: usize, future: F)
where
    F: std::future::Future + Send + 'static,
    F::Output: Send + 'static,
{
    // 使用 spawn_blocking 模拟线程亲和性
    tokio::task::spawn_blocking(move || {
        // 设置 CPU 亲和性（平台相关）
        #[cfg(target_os = "linux")]
        unsafe {
            let mut set = libc::cpu_set_t::default();
            libc::CPU_SET(affinity, &mut set);
            libc::sched_setaffinity(0, std::mem::size_of::<libc::cpu_set_t>(), &set);
        }

        // 在当前线程执行 future
        // 需要使用 LocalPool 或类似机制
    }).await.unwrap();
}

/// 本地任务集（!Send 任务）
pub async fn local_tasks_example() {
    let local = LocalSet::new();

    let rc = std::rc::Rc::new(42);

    local.run_until(async move {
        // Rc 不是 Send，只能在本地任务使用
        let task = spawn_local(async move {
            println!("Value: {}", *rc);
        });

        task.await.unwrap();
    }).await;
}
```

### 2.3 优先级调度

```rust
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use tokio::sync::Semaphore;

/// 优先级任务定义
#[derive(Debug)]
pub struct PriorityTask<T> {
    priority: u8,
    sequence: u64,
    task: T,
}

impl<T> PartialEq for PriorityTask<T> {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority && self.sequence == other.sequence
    }
}

impl<T> Eq for PriorityTask<T> {}

impl<T> PartialOrd for PriorityTask<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for PriorityTask<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // 高优先级 = 小数值
        // 同优先级 = 按序号 FIFO
        self.priority.cmp(&other.priority)
            .reverse()
            .then_with(|| self.sequence.cmp(&other.sequence))
    }
}

/// 优先级任务调度器
pub struct PriorityScheduler<T> {
    queue: tokio::sync::Mutex<BinaryHeap<PriorityTask<T>>>,
    semaphore: Semaphore,
    sequence: std::sync::atomic::AtomicU64,
}

impl<T> PriorityScheduler<T> {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            queue: tokio::sync::Mutex::new(BinaryHeap::new()),
            semaphore: Semaphore::new(max_concurrent),
            sequence: std::sync::atomic::AtomicU64::new(0),
        }
    }

    pub async fn submit(&self, priority: u8, task: T) {
        let sequence = self.sequence.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        let priority_task = PriorityTask {
            priority,
            sequence,
            task,
        };

        let mut queue = self.queue.lock().await;
        queue.push(priority_task);
    }

    pub async fn run<F, Fut>(&self, processor: F)
    where
        F: Fn(T) -> Fut + Clone + Send + 'static,
        Fut: std::future::Future<Output = ()> + Send + 'static,
        T: Send + 'static,
    {
        loop {
            let permit = self.semaphore.acquire().await.unwrap();

            let task = {
                let mut queue = self.queue.lock().await;
                queue.pop().map(|pt| pt.task)
            };

            if let Some(task) = task {
                let proc = processor.clone();
                tokio::spawn(async move {
                    let _permit = permit;
                    proc(task).await;
                });
            } else {
                drop(permit);
                tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
            }
        }
    }
}
```

### 2.4 任务局部存储

```rust
use tokio::task_local;

/// 任务局部存储（类似线程局部存储，但是 per-task）
task_local! {
    static REQUEST_ID: String;
    static USER_ID: u64;
    static START_TIME: std::time::Instant;
}

/// 在请求处理中使用
pub async fn handle_request(request_id: String, user_id: u64) {
    REQUEST_ID.scope(request_id.clone(), async {
        USER_ID.scope(user_id, async {
            START_TIME.scope(std::time::Instant::now(), async {
                // 可以在任何异步函数中访问这些值
                process_data().await;
                log_request().await;
            }).await;
        }).await;
    }).await;
}

async fn process_data() {
    let request_id = REQUEST_ID.with(|id| id.clone());
    let user_id = USER_ID.with(|id| *id);

    println!("Processing request {} for user {}", request_id, user_id);

    // 异步操作可以跨越 await 点保持上下文
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;

    let request_id2 = REQUEST_ID.with(|id| id.clone());
    assert_eq!(request_id, request_id2); // 仍然相同
}

async fn log_request() {
    let start = START_TIME.with(|t| *t);
    let elapsed = start.elapsed();
    let request_id = REQUEST_ID.with(|id| id.clone());

    println!("Request {} completed in {:?}", request_id, elapsed);
}
```

---

## 3. 并发原语

### 3.1 异步 Mutex

```rustn
use tokio::sync::{Mutex, RwLock};
use std::sync::Arc;

/// 异步 Mutex vs 标准库 Mutex
///
/// 标准库 Mutex：阻塞线程
/// 异步 Mutex：阻塞任务，让出线程

/// 共享状态管理
pub struct SharedState<T> {
    data: Arc<Mutex<T>>,
}

impl<T> Clone for SharedState<T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
        }
    }
}

impl<T> SharedState<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(Mutex::new(data)),
        }
    }

    /// 异步修改数据
    pub async fn modify<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let mut guard = self.data.lock().await;
        f(&mut *guard)
    }

    /// 异步读取数据
    pub async fn read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        let guard = self.data.lock().await;
        f(&*guard)
    }

    /// 尝试获取锁
    pub async fn try_modify<F, R>(&self, f: F) -> Option<R>
    where
        F: FnOnce(&mut T) -> R,
    {
        match self.data.try_lock() {
            Ok(mut guard) => Some(f(&mut *guard)),
            Err(_) => None,
        }
    }
}

/// 避免持有锁跨越 await
/// ❌ 错误示例
async fn bad_example(state: Arc<Mutex<Vec<i32>>>) {
    let mut guard = state.lock().await;
    guard.push(1);

    // 锁在这里仍然被持有，阻塞其他任务！
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;

    guard.push(2);
}

/// ✅ 正确示例
async fn good_example(state: Arc<Mutex<Vec<i32>>>) {
    {
        let mut guard = state.lock().await;
        guard.push(1);
    } // 锁在这里释放

    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;

    {
        let mut guard = state.lock().await;
        guard.push(2);
    }
}

/// 使用 RwLock 提高读性能
pub struct Cache<K, V> {
    data: Arc<RwLock<std::collections::HashMap<K, V>>>,
}

impl<K: Eq + std::hash::Hash + Clone, V: Clone> Cache<K, V> {
    pub fn new() -> Self {
        Self {
            data: Arc::new(RwLock::new(std::collections::HashMap::new())),
        }
    }

    pub async fn get(&self, key: &K) -> Option<V> {
        let guard = self.data.read().await;
        guard.get(key).cloned()
    }

    pub async fn insert(&self, key: K, value: V) {
        let mut guard = self.data.write().await;
        guard.insert(key, value);
    }

    /// 读多写少场景下的批量读取
    pub async fn get_batch(&self, keys: &[K]) -> Vec<Option<V>> {
        let guard = self.data.read().await;
        keys.iter().map(|k| guard.get(k).cloned()).collect()
    }
}
```

### 3.2 异步 Channel

### Rust 1.94 Peekable::next_if_map 在异步流中的应用

Rust 1.94 引入了 `Peekable::next_if_map` 方法，在处理异步流时特别有用，可以实现条件消费和转换：

```rust
use std::iter::Peekable;

/// 条件消费异步消息流
pub struct ConditionalConsumer<I: Iterator> {
    inner: Peekable<I>,
}

impl<I: Iterator> ConditionalConsumer<I> {
    pub fn new(iter: I) -> Self {
        Self {
            inner: iter.peekable(),
        }
    }

    /// 消费并转换符合条件的下一个元素（Rust 1.94）
    pub fn next_if_valid<F, T>(&mut self, transformer: F) -> Option<T>
    where
        F: FnOnce(I::Item) -> Option<T>,
    {
        // Rust 1.94: next_if_map 允许条件映射消费
        self.inner.next_if_map(transformer)
    }

    /// 异步流处理中的条件消费模式
    pub async fn process_conditional<F, Fut, T>(
        &mut self,
        predicate: impl Fn(&I::Item) -> bool,
        processor: F,
    ) -> Option<T>
    where
        F: FnOnce(I::Item) -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        // 检查下一个元素
        if let Some(item) = self.inner.peek() {
            if predicate(item) {
                // 符合条件，消费并处理
                let item = self.inner.next()?;
                Some(processor(item).await)
            } else {
                None
            }
        } else {
            None
        }
    }
}

/// 异步消息处理器 - 使用条件消费
pub struct MessageProcessor {
    // 在实际应用中，这可能是 tokio::sync::mpsc::Receiver 的包装
    buffer: Peekable<std::vec::IntoIter<Message>>,
}

#[derive(Debug, Clone)]
pub enum Message {
    HighPriority(String),
    NormalPriority(String),
    LowPriority(String),
}

impl MessageProcessor {
    pub fn new(messages: Vec<Message>) -> Self {
        Self {
            buffer: messages.into_iter().peekable(),
        }
    }

    /// 仅处理高优先级消息（Rust 1.94 风格）
    pub fn process_high_priority(&mut self) -> Option<String> {
        // Rust 1.94: 使用 next_if_map 进行条件消费和转换
        self.buffer.next_if_map(|msg| match msg {
            Message::HighPriority(content) => Some(content),
            _ => None,
        })
    }

    /// 优先级调度处理
    pub async fn priority_scheduled_process(&mut self) -> Vec<String> {
        let mut results = vec![];

        // 先处理所有高优先级消息
        while let Some(content) = self.process_high_priority() {
            results.push(format!("[HIGH] {}", content));
        }

        // 然后处理普通优先级
        while let Some(msg) = self.buffer.next() {
            match msg {
                Message::NormalPriority(content) => {
                    results.push(format!("[NORMAL] {}", content));
                }
                Message::LowPriority(content) => {
                    // 低优先级可以延迟处理
                    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
                    results.push(format!("[LOW] {}", content));
                }
                _ => {}
            }
        }

        results
    }
}

/// 与 Tokio Stream 结合使用
#[cfg(feature = "tokio-stream")]
pub mod stream_extensions {
    use tokio_stream::Stream;
    use std::pin::Pin;
    use std::task::{Context, Poll};

    /// 条件消费 Stream 包装器
    pub struct ConditionalStream<S> {
        inner: S,
    }

    impl<S: Stream + Unpin> Stream for ConditionalStream<S> {
        type Item = S::Item;

        fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
            self.inner.poll_next_unpin(cx)
        }
    }
}
```

### 异步延迟初始化 (Rust 1.94)

```rust
use std::sync::LazyLock;
use tokio::sync::RwLock;

/// 异步上下文中的延迟初始化
static ASYNC_CONFIG: LazyLock<AsyncConfig> = LazyLock::new(|| {
    // 注意：LazyLock 的初始化是同步的
    // 对于真正的异步初始化，需要使用其他模式
    AsyncConfig::blocking_load()
});

pub struct AsyncConfig {
    database_url: String,
    api_keys: RwLock<std::collections::HashMap<String, String>>,
}

impl AsyncConfig {
    fn blocking_load() -> Self {
        Self {
            database_url: std::env::var("DATABASE_URL").unwrap_or_default(),
            api_keys: RwLock::new(std::collections::HashMap::new()),
        }
    }

    pub async fn add_api_key(&self, service: String, key: String) {
        let mut keys = self.api_keys.write().await;
        keys.insert(service, key);
    }

    pub async fn get_api_key(&self, service: &str) -> Option<String> {
        let keys = self.api_keys.read().await;
        keys.get(service).cloned()
    }
}

/// 获取配置（Rust 1.94）
pub fn get_async_config() -> &'static AsyncConfig {
    ASYNC_CONFIG.get()
}

/// 在异步任务中使用延迟初始化
async fn use_lazy_config() {
    // 安全地在异步上下文中访问延迟初始化的配置
    let config = ASYNC_CONFIG.get();

    // 异步操作
    if let Some(key) = config.get_api_key("stripe").await {
        println!("Using Stripe API key: {}...", &key[..8]);
    }
}
```

```rust
use tokio::sync::{mpsc, oneshot};
use std::time::Duration;

/// MPSC Channel（多生产者单消费者）
pub struct TaskQueue<T> {
    sender: mpsc::Sender<T>,
    receiver: Option<mpsc::Receiver<T>>,
}

impl<T> TaskQueue<T> {
    pub fn new(capacity: usize) -> Self {
        let (sender, receiver) = mpsc::channel(capacity);
        Self {
            sender,
            receiver: Some(receiver),
        }
    }

    pub fn sender(&self) -> mpsc::Sender<T> {
        self.sender.clone()
    }

    pub fn take_receiver(&mut self) -> Option<mpsc::Receiver<T>> {
        self.receiver.take()
    }
}

/// 带超时的发送
pub async fn send_with_timeout<T>(
    sender: &mpsc::Sender<T>,
    value: T,
    timeout: Duration,
) -> Result<(), SendError<T>> {
    match tokio::time::timeout(timeout, sender.send(value)).await {
        Ok(Ok(())) => Ok(()),
        Ok(Err(_)) => Err(SendError::ChannelClosed),
        Err(_) => Err(SendError::Timeout),
    }
}

pub enum SendError<T> {
    ChannelClosed,
    Timeout,
}

/// Oneshot Channel（单次通信）
pub async fn request_response<Req, Resp>(
    sender: mpsc::Sender<(Req, oneshot::Sender<Resp>)>,
    request: Req,
    timeout: Duration,
) -> Result<Resp, RequestError> {
    let (tx, rx) = oneshot::channel();

    sender.send((request, tx)).await
        .map_err(|_| RequestError::SendFailed)?;

    match tokio::time::timeout(timeout, rx).await {
        Ok(Ok(response)) => Ok(response),
        Ok(Err(_)) => Err(RequestError::ChannelClosed),
        Err(_) => Err(RequestError::Timeout),
    }
}

pub enum RequestError {
    SendFailed,
    ChannelClosed,
    Timeout,
}

/// Broadcast Channel（广播）
use tokio::sync::broadcast;

pub struct EventBus<T: Clone> {
    sender: broadcast::Sender<T>,
}

impl<T: Clone + Send + 'static> EventBus<T> {
    pub fn new(capacity: usize) -> Self {
        let (sender, _) = broadcast::channel(capacity);
        Self { sender }
    }

    pub fn subscribe(&self) -> broadcast::Receiver<T> {
        self.sender.subscribe()
    }

    pub fn publish(&self, event: T) -> Result<usize, broadcast::error::SendError<T>> {
        self.sender.send(event)
    }

    /// 获取活跃订阅者数量
    pub fn receiver_count(&self) -> usize {
        self.sender.receiver_count()
    }
}

/// Watch Channel（状态订阅）
use tokio::sync::watch;

pub struct StateMonitor<T: Clone> {
    sender: watch::Sender<T>,
}

impl<T: Clone + Send + Sync + 'static> StateMonitor<T> {
    pub fn new(initial: T) -> Self {
        let (sender, _) = watch::channel(initial);
        Self { sender }
    }

    pub fn subscribe(&self) -> watch::Receiver<T> {
        self.sender.subscribe()
    }

    pub fn update(&self, value: T) -> Result<(), watch::error::SendError<T>> {
        self.sender.send(value)
    }

    /// 等待状态变化
    pub async fn wait_for<F>(&self, predicate: F) -> Result<T, watch::error::RecvError>
    where
        F: Fn(&T) -> bool,
    {
        let mut rx = self.subscribe();
        rx.wait_for(predicate).await.map(|_| rx.borrow().clone())
    }
}
```

（继续...）
