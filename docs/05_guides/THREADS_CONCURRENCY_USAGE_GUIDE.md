# 线程与并发使用指南

**模块**: C05 Threads
**创建日期**: 2025-12-11
**最后更新**: 2026-02-15
**Rust 版本**: 1.93.1+ (Edition 2024)
**状态**: ✅ 已完成

---

## 📋 目录 {#-目录}

- [线程与并发使用指南](#线程与并发使用指南)
  - [📋 目录 {#-目录}](#-目录--目录)
  - [📋 概述 {#-概述}](#-概述--概述)
  - [🚀 快速开始 {#-快速开始}](#-快速开始--快速开始)
    - [基本线程创建](#基本线程创建)
    - [作用域线程（Rust 1.89+）](#作用域线程rust-189)
  - [📊 核心功能 {#-核心功能}](#-核心功能--核心功能)
    - [1. 线程管理](#1-线程管理)
      - [线程池](#线程池)
      - [线程属性](#线程属性)
    - [2. 消息传递](#2-消息传递)
      - [通道（Channel）](#通道channel)
      - [多生产者单消费者](#多生产者单消费者)
    - [3. 共享状态](#3-共享状态)
      - [Mutex（互斥锁）](#mutex互斥锁)
      - [RwLock（读写锁）](#rwlock读写锁)
    - [4. 同步原语](#4-同步原语)
      - [信号量（Semaphore）](#信号量semaphore)
      - [屏障（Barrier）](#屏障barrier)
    - [5. 无锁数据结构](#5-无锁数据结构)
      - [无锁队列](#无锁队列)
  - [⚡ 性能优化 {#-性能优化}](#-性能优化--性能优化)
    - [1. 减少锁竞争](#1-减少锁竞争)
    - [2. 使用无锁数据结构](#2-使用无锁数据结构)
    - [3. 工作窃取](#3-工作窃取)
  - [🛡️ 并发安全代码示例（5+ 模式） {#️-并发安全代码示例5-模式}](#️-并发安全代码示例5-模式-️-并发安全代码示例5-模式)
    - [模式 1: 读写锁分离模式](#模式-1-读写锁分离模式)
    - [模式 2: 无锁计数器与统计](#模式-2-无锁计数器与统计)
    - [模式 3: 线程安全的工作队列](#模式-3-线程安全的工作队列)
    - [模式 4: 多阶段流水线并行](#模式-4-多阶段流水线并行)
    - [模式 5: 并发安全缓存](#模式-5-并发安全缓存)
  - [⚠️ 数据竞争案例与解决方案 {#️-数据竞争案例与解决方案}](#️-数据竞争案例与解决方案-️-数据竞争案例与解决方案)
    - [案例 1: 未同步的共享可变状态](#案例-1-未同步的共享可变状态)
    - [案例 2: Send/Sync 违规](#案例-2-sendsync-违规)
    - [案例 3: 死锁](#案例-3-死锁)
    - [案例 4: 优先级反转](#案例-4-优先级反转)
    - [案例 5: 条件变量误用](#案例-5-条件变量误用)
  - [🐛 常见问题 {#-常见问题}](#-常见问题--常见问题)
    - [死锁](#死锁)
    - [数据竞争](#数据竞争)
  - [📚 相关文档 {#-相关文档}](#-相关文档--相关文档)

---

## 📋 概述 {#-概述}

本指南介绍如何使用 C05 线程与并发模块的功能，包括线程管理、并发控制、同步原语、无锁数据结构等。

**形式化引用**：SEND-T1 (Send 安全)、SYNC-T1 (Sync 安全)、T-BR1 (数据竞争自由)。详见 [send_sync_formalization](../research_notes/formal_methods/send_sync_formalization.md)、[THEOREM_RUST_EXAMPLE_MAPPING](../research_notes/THEOREM_RUST_EXAMPLE_MAPPING.md)。

---

## 🚀 快速开始 {#-快速开始}

### 基本线程创建

```rust
use std::thread;
use std::time::Duration;

// 创建新线程
let handle = thread::spawn(|| {
    for i in 1..10 {
        println!("线程中的数字: {}", i);
        thread::sleep(Duration::from_millis(1));
    }
});

// 等待线程完成
handle.join().unwrap();
```

### 作用域线程（Rust 1.89+）

```rust
use std::thread;

let mut data = vec![1, 2, 3, 4, 5];

thread::scope(|s| {
    // 在作用域内创建线程，可以借用局部变量
    s.spawn(|| {
        println!("数据长度: {}", data.len());
    });

    s.spawn(|| {
        data.push(6);
    });
}); // 所有线程在这里自动等待完成
```

---

## 📊 核心功能 {#-核心功能}

### 1. 线程管理

#### 线程池

```rust
use c05_threads::threads::ThreadPool;

let pool = ThreadPool::new(4);

for i in 0..10 {
    pool.execute(move || {
        println!("任务 {} 在线程中执行", i);
    });
}

pool.join(); // 等待所有任务完成
```

#### 线程属性

```rust
use std::thread;

let builder = thread::Builder::new()
    .name("worker".into())
    .stack_size(32 * 1024 * 1024); // 32MB 栈

let handle = builder.spawn(|| {
    println!("线程名称: {:?}", thread::current().name());
}).unwrap();
```

### 2. 消息传递

#### 通道（Channel）

```rust
use std::sync::mpsc;

let (tx, rx) = mpsc::channel();

// 发送线程
thread::spawn(move || {
    tx.send("Hello".to_string()).unwrap();
    tx.send("World".to_string()).unwrap();
});

// 接收线程
for received in rx {
    println!("收到: {}", received);
}
```

#### 多生产者单消费者

```rust
use std::sync::mpsc;

let (tx, rx) = mpsc::channel();
let tx1 = tx.clone();
let tx2 = tx.clone();

thread::spawn(move || {
    tx1.send(1).unwrap();
});

thread::spawn(move || {
    tx2.send(2).unwrap();
});

drop(tx); // 关闭原始发送端

for received in rx {
    println!("收到: {}", received);
}
```

### 3. 共享状态

#### Mutex（互斥锁）

```rust
use std::sync::{Arc, Mutex};
use std::thread;

let counter = Arc::new(Mutex::new(0));
let mut handles = vec![];

for _ in 0..10 {
    let counter = Arc::clone(&counter);
    let handle = thread::spawn(move || {
        let mut num = counter.lock().unwrap();
        *num += 1;
    });
    handles.push(handle);
}

for handle in handles {
    handle.join().unwrap();
}

println!("结果: {}", *counter.lock().unwrap());
```

#### RwLock（读写锁）

```rust
use std::sync::{Arc, RwLock};
use std::thread;

let data = Arc::new(RwLock::new(0));

// 多个读线程
for i in 0..5 {
    let data = Arc::clone(&data);
    thread::spawn(move || {
        let value = data.read().unwrap();
        println!("读线程 {}: {}", i, *value);
    });
}

// 写线程
let data = Arc::clone(&data);
thread::spawn(move || {
    let mut value = data.write().unwrap();
    *value += 1;
});
```

### 4. 同步原语

#### 信号量（Semaphore）

```rust
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

struct Semaphore {
    count: AtomicUsize,
    max: usize,
}

impl Semaphore {
    fn new(max: usize) -> Self {
        Self {
            count: AtomicUsize::new(max),
            max,
        }
    }

    fn acquire(&self) {
        while self.count.load(Ordering::Acquire) == 0 {
            std::hint::spin_loop();
        }
        self.count.fetch_sub(1, Ordering::AcqRel);
    }

    fn release(&self) {
        self.count.fetch_add(1, Ordering::AcqRel);
    }
}
```

#### 屏障（Barrier）

```rust
use std::sync::{Arc, Barrier};
use std::thread;

let barrier = Arc::new(Barrier::new(3));
let mut handles = vec![];

for i in 0..3 {
    let barrier = Arc::clone(&barrier);
    let handle = thread::spawn(move || {
        println!("线程 {} 到达屏障前", i);
        barrier.wait(); // 等待所有线程到达
        println!("线程 {} 通过屏障", i);
    });
    handles.push(handle);
}

for handle in handles {
    handle.join().unwrap();
}
```

### 5. 无锁数据结构

#### 无锁队列

```rust
use c05_threads::lockfree::lockfree_queue::LockFreeQueue;
use std::sync::Arc;
use std::thread;

let queue = Arc::new(LockFreeQueue::new());

// 生产者线程
let queue_clone = Arc::clone(&queue);
thread::spawn(move || {
    for i in 0..10 {
        queue_clone.push(i);
    }
});

// 消费者线程
let queue_clone = Arc::clone(&queue);
thread::spawn(move || {
    loop {
        if let Some(value) = queue_clone.pop() {
            println!("消费: {}", value);
        } else {
            break;
        }
    }
});
```

---

## ⚡ 性能优化 {#-性能优化}

### 1. 减少锁竞争

```rust
// ❌ 不好的做法：锁住整个操作
let mutex = Arc::new(Mutex::new(data));
let guard = mutex.lock().unwrap();
// 长时间操作
drop(guard);

// ✅ 好的做法：最小化锁的持有时间
let mutex = Arc::new(Mutex::new(data));
{
    let mut guard = mutex.lock().unwrap();
    // 快速操作
}
// 锁已释放，可以进行其他操作
```

### 2. 使用无锁数据结构

```rust
// 对于高并发场景，使用无锁数据结构
use c05_threads::lockfree::*;

let queue = Arc::new(LockFreeQueue::new());
// 无锁操作，性能更好
```

### 3. 工作窃取

```rust
use c05_threads::concurrency::work_stealing::WorkStealingQueue;

let queue = WorkStealingQueue::new();
// 工作窃取调度器可以自动平衡负载
```

---

## 🛡️ 并发安全代码示例（5+ 模式） {#️-并发安全代码示例5-模式}

### 模式 1: 读写锁分离模式

```rust
use std::sync::{Arc, RwLock};
use std::thread;
use std::time::Duration;

// 配置管理：多读单写
struct ConfigManager {
    config: Arc<RwLock<AppConfig>>,
}

#[derive(Clone, Debug)]
struct AppConfig {
    database_url: String,
    max_connections: usize,
    timeout: Duration,
}

impl ConfigManager {
    fn new(initial_config: AppConfig) -> Self {
        Self {
            config: Arc::new(RwLock::new(initial_config)),
        }
    }

    // 读取配置 - 多个读取者可以同时访问
    fn get_config(&self) -> AppConfig {
        self.config.read().unwrap().clone()
    }

    // 更新配置 - 独占访问
    fn update_config<F>(&self, updater: F)
    where
        F: FnOnce(&mut AppConfig),
    {
        let mut config = self.config.write().unwrap();
        updater(&mut *config);
        println!("配置已更新: {:?}", *config);
    }

    // 并发读取示例
    fn start_readers(&self, count: usize) {
        for i in 0..count {
            let config = Arc::clone(&self.config);
            thread::spawn(move || {
                loop {
                    let cfg = config.read().unwrap();
                    println!("读取者 {}: timeout = {:?}", i, cfg.timeout);
                    drop(cfg); // 显式释放读锁
                    thread::sleep(Duration::from_millis(100));
                }
            });
        }
    }
}
```

### 模式 2: 无锁计数器与统计

```rust
use std::sync::atomic::{AtomicU64, AtomicI64, Ordering};
use std::sync::Arc;

// 高性能统计收集器
struct LockFreeStats {
    total_requests: AtomicU64,
    active_connections: AtomicI64,
    bytes_transferred: AtomicU64,
    error_count: AtomicU64,
}

impl LockFreeStats {
    fn new() -> Self {
        Self {
            total_requests: AtomicU64::new(0),
            active_connections: AtomicI64::new(0),
            bytes_transferred: AtomicU64::new(0),
            error_count: AtomicU64::new(0),
        }
    }

    // 记录请求 - Relaxed 排序足够，因为不需要与其他操作同步
    fn record_request(&self) {
        self.total_requests.fetch_add(1, Ordering::Relaxed);
    }

    // 连接管理 - SeqCst 确保连接计数的正确性
    fn connection_started(&self) {
        self.active_connections.fetch_add(1, Ordering::SeqCst);
    }

    fn connection_ended(&self) {
        self.active_connections.fetch_sub(1, Ordering::SeqCst);
    }

    // 批量更新 bytes - 使用 fetch_add 累加
    fn record_bytes(&self, bytes: u64) {
        self.bytes_transferred.fetch_add(bytes, Ordering::Relaxed);
    }

    // 获取快照 - Acquire 确保看到所有之前的更新
    fn snapshot(&self) -> StatsSnapshot {
        StatsSnapshot {
            total_requests: self.total_requests.load(Ordering::Acquire),
            active_connections: self.active_connections.load(Ordering::Acquire),
            bytes_transferred: self.bytes_transferred.load(Ordering::Acquire),
            error_count: self.error_count.load(Ordering::Acquire),
        }
    }

    // CAS 操作示例：条件更新
    fn try_increment_errors(&self, max_errors: u64) -> bool {
        loop {
            let current = self.error_count.load(Ordering::Relaxed);
            if current >= max_errors {
                return false;
            }
            match self.error_count.compare_exchange_weak(
                current,
                current + 1,
                Ordering::SeqCst,
                Ordering::Relaxed,
            ) {
                Ok(_) => return true,
                Err(_) => continue, // 重试
            }
        }
    }
}

#[derive(Debug)]
struct StatsSnapshot {
    total_requests: u64,
    active_connections: i64,
    bytes_transferred: u64,
    error_count: u64,
}
```

### 模式 3: 线程安全的工作队列

```rust
use std::sync::{Arc, Mutex, Condvar};
use std::collections::VecDeque;
use std::thread;

// 有界阻塞队列
struct BoundedWorkQueue<T> {
    queue: Mutex<VecDeque<T>>,
    not_full: Condvar,
    not_empty: Condvar,
    capacity: usize,
}

impl<T> BoundedWorkQueue<T> {
    fn new(capacity: usize) -> Self {
        Self {
            queue: Mutex::new(VecDeque::with_capacity(capacity)),
            not_full: Condvar::new(),
            not_empty: Condvar::new(),
            capacity,
        }
    }

    // 生产者：阻塞式入队
    fn push(&self, item: T) {
        let mut queue = self.queue.lock().unwrap();

        // 等待队列不满
        while queue.len() >= self.capacity {
            queue = self.not_full.wait(queue).unwrap();
        }

        queue.push_back(item);
        self.not_empty.notify_one();
    }

    // 消费者：阻塞式出队
    fn pop(&self) -> T {
        let mut queue = self.queue.lock().unwrap();

        // 等待队列不空
        while queue.is_empty() {
            queue = self.not_empty.wait(queue).unwrap();
        }

        let item = queue.pop_front().unwrap();
        self.not_full.notify_one();
        item
    }

    // 非阻塞尝试
    fn try_push(&self, item: T) -> Result<(), T> {
        let mut queue = self.queue.lock().unwrap();

        if queue.len() >= self.capacity {
            return Err(item);
        }

        queue.push_back(item);
        self.not_empty.notify_one();
        Ok(())
    }

    fn try_pop(&self) -> Option<T> {
        let mut queue = self.queue.lock().unwrap();

        let item = queue.pop_front()?;
        self.not_full.notify_one();
        Some(item)
    }
}

// 使用示例：线程池
type Job = Box<dyn FnOnce() + Send + 'static>;

struct ThreadPool {
    workers: Vec<thread::JoinHandle<()>>,
    queue: Arc<BoundedWorkQueue<Job>>,
}

impl ThreadPool {
    fn new(size: usize, queue_capacity: usize) -> Self {
        let queue = Arc::new(BoundedWorkQueue::new(queue_capacity));
        let mut workers = Vec::with_capacity(size);

        for _ in 0..size {
            let queue = Arc::clone(&queue);
            workers.push(thread::spawn(move || {
                loop {
                    let job = queue.pop();
                    job();
                }
            }));
        }

        Self { workers, queue }
    }

    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        self.queue.push(Box::new(f));
    }
}
```

### 模式 4: 多阶段流水线并行

```rust
use std::sync::mpsc::{channel, Sender, Receiver};
use std::thread;

// 三阶段流水线：提取 -> 处理 -> 存储
struct Pipeline<T, U, V> {
    stage1_sender: Option<Sender<T>>,
    stage2_sender: Option<Sender<U>>,
    result_receiver: Receiver<V>,
    handles: Vec<thread::JoinHandle<()>>,
}

impl<T, U, V> Pipeline<T, U, V>
where
    T: Send + 'static,
    U: Send + 'static,
    V: Send + 'static,
{
    fn new<Extract, Process, Store>(
        extract_fn: Extract,
        process_fn: Process,
        store_fn: Store,
    ) -> Self
    where
        Extract: FnOnce(Receiver<T>) -> Vec<U> + Send + 'static,
        Process: FnOnce(Receiver<U>) -> Vec<V> + Send + 'static,
        Store: FnOnce(Receiver<V>) + Send + 'static,
    {
        // Stage 1 -> Stage 2
        let (s1_tx, s1_rx) = channel::<T>();
        let (s2_tx, s2_rx) = channel::<U>();
        let (result_tx, result_rx) = channel::<V>();

        // Stage 1: 提取
        let handle1 = thread::spawn(move || {
            let results = extract_fn(s1_rx);
            for item in results {
                if s2_tx.send(item).is_err() {
                    break;
                }
            }
        });

        // Stage 2: 处理
        let handle2 = thread::spawn(move || {
            let results = process_fn(s2_rx);
            for item in results {
                if result_tx.send(item).is_err() {
                    break;
                }
            }
        });

        // Stage 3: 存储
        let handle3 = thread::spawn(move || {
            store_fn(result_rx);
        });

        Self {
            stage1_sender: Some(s1_tx),
            stage2_sender: Some(s2_tx),
            result_receiver: result_rx,
            handles: vec![handle1, handle2, handle3],
        }
    }

    fn input(&self) -> &Sender<T> {
        self.stage1_sender.as_ref().unwrap()
    }

    fn wait(self) -> Vec<V> {
        drop(self.stage1_sender);
        drop(self.stage2_sender);

        for handle in self.handles {
            handle.join().unwrap();
        }

        self.result_receiver.iter().collect()
    }
}
```

### 模式 5: 并发安全缓存

```rust
use std::sync::{Arc, RwLock};
use std::collections::HashMap;
use std::hash::Hash;
use std::time::{Duration, Instant};

// 带 TTL 的线程安全缓存
struct ConcurrentCache<K, V> {
    inner: Arc<RwLock<HashMap<K, CacheEntry<V>>>>,
    default_ttl: Duration,
}

struct CacheEntry<V> {
    value: V,
    expires_at: Instant,
}

impl<V> CacheEntry<V> {
    fn is_expired(&self) -> bool {
        Instant::now() > self.expires_at
    }
}

impl<K, V> ConcurrentCache<K, V>
where
    K: Eq + Hash + Clone + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    fn new(default_ttl: Duration) -> Self {
        let cache = Self {
            inner: Arc::new(RwLock::new(HashMap::new())),
            default_ttl,
        };

        // 启动清理线程
        cache.start_cleanup_thread();
        cache
    }

    fn get(&self, key: &K) -> Option<V> {
        let map = self.inner.read().unwrap();
        map.get(key).and_then(|entry| {
            if entry.is_expired() {
                None
            } else {
                Some(entry.value.clone())
            }
        })
    }

    fn set(&self, key: K, value: V) {
        self.set_with_ttl(key, value, self.default_ttl);
    }

    fn set_with_ttl(&self, key: K, value: V, ttl: Duration) {
        let mut map = self.inner.write().unwrap();
        map.insert(key, CacheEntry {
            value,
            expires_at: Instant::now() + ttl,
        });
    }

    // 获取或插入（缓存填充模式）
    fn get_or_insert<F>(&self, key: K, factory: F) -> V
    where
        F: FnOnce() -> V,
    {
        // 先尝试读取
        if let Some(value) = self.get(&key) {
            return value;
        }

        // 需要写入
        let mut map = self.inner.write().unwrap();

        // 双重检查（可能其他线程已插入）
        if let Some(entry) = map.get(&key) {
            if !entry.is_expired() {
                return entry.value.clone();
            }
        }

        let value = factory();
        map.insert(key.clone(), CacheEntry {
            value: value.clone(),
            expires_at: Instant::now() + self.default_ttl,
        });
        value
    }

    fn start_cleanup_thread(&self) {
        let inner = Arc::clone(&self.inner);
        let cleanup_interval = self.default_ttl;

        std::thread::spawn(move || {
            loop {
                std::thread::sleep(cleanup_interval);

                let mut map = inner.write().unwrap();
                let expired_keys: Vec<K> = map
                    .iter()
                    .filter(|(_, entry)| entry.is_expired())
                    .map(|(k, _)| k.clone())
                    .collect();

                for key in expired_keys {
                    map.remove(&key);
                }
            }
        });
    }
}
```

---

## ⚠️ 数据竞争案例与解决方案 {#️-数据竞争案例与解决方案}

### 案例 1: 未同步的共享可变状态

```rust
// ❌ 数据竞争！多个线程同时读写，无同步保护
use std::thread;

fn data_race_example() {
    let mut counter = 0;

    let mut handles = vec![];
    for _ in 0..10 {
        // 错误：尝试共享可变引用
        // handle = thread::spawn(|| {
        //     counter += 1; // 编译错误！
        // });
    }
}

// ✅ 解决方案 1: 使用 Mutex
fn fixed_with_mutex() {
    let counter = std::sync::Arc::new(std::sync::Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = std::sync::Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("结果: {}", *counter.lock().unwrap());
}

// ✅ 解决方案 2: 使用 Atomic
fn fixed_with_atomic() {
    use std::sync::atomic::{AtomicI32, Ordering};

    let counter = std::sync::Arc::new(AtomicI32::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = std::sync::Arc::clone(&counter);
        let handle = thread::spawn(move || {
            counter.fetch_add(1, Ordering::SeqCst);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("结果: {}", counter.load(Ordering::SeqCst));
}
```

### 案例 2: Send/Sync 违规

```rust
use std::rc::Rc;
use std::cell::RefCell;
use std::thread;

// ❌ Rc 不是 Send，不能跨线程传递
fn send_violation() {
    let data = Rc::new(42);

    // 编译错误！
    // thread::spawn(move || {
    //     println!("{}", data);
    // });
}

// ❌ RefCell 不是 Sync，不能在多线程间共享引用
fn sync_violation() {
    let data = std::sync::Arc::new(RefCell::new(42));

    // 编译错误！
    // let data2 = std::sync::Arc::clone(&data);
    // thread::spawn(move || {
    //     *data2.borrow_mut() = 100;
    // });
}

// ✅ 解决方案：使用线程安全类型
fn thread_safe_types() {
    use std::sync::{Arc, Mutex};

    // Arc + Mutex 是 Send + Sync
    let data = Arc::new(Mutex::new(42));

    let data2 = Arc::clone(&data);
    let handle = thread::spawn(move || {
        let mut num = data2.lock().unwrap();
        *num = 100;
    });

    handle.join().unwrap();
    println!("{}", *data.lock().unwrap());
}
```

### 案例 3: 死锁

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// ❌ 死锁：锁获取顺序不一致
fn deadlock_example() {
    let mutex1 = Arc::new(Mutex::new(0));
    let mutex2 = Arc::new(Mutex::new(0));

    let m1 = Arc::clone(&mutex1);
    let m2 = Arc::clone(&mutex2);
    let handle1 = thread::spawn(move || {
        let _g1 = m1.lock().unwrap();
        thread::sleep(std::time::Duration::from_millis(10));
        let _g2 = m2.lock().unwrap(); // 可能死锁！
        println!("线程 1 获取了两个锁");
    });

    let m1 = Arc::clone(&mutex1);
    let m2 = Arc::clone(&mutex2);
    let handle2 = thread::spawn(move || {
        let _g2 = m2.lock().unwrap();
        thread::sleep(std::time::Duration::from_millis(10));
        let _g1 = m1.lock().unwrap(); // 可能死锁！
        println!("线程 2 获取了两个锁");
    });

    handle1.join().unwrap();
    handle2.join().unwrap();
}

// ✅ 解决方案 1: 统一锁获取顺序
fn fixed_deadlock_ordering() {
    let mutex1 = Arc::new(Mutex::new(0));
    let mutex2 = Arc::new(Mutex::new(0));

    let m1 = Arc::clone(&mutex1);
    let m2 = Arc::clone(&mutex2);
    let handle1 = thread::spawn(move || {
        let _g1 = m1.lock().unwrap();
        let _g2 = m2.lock().unwrap();
        println!("线程 1 获取了两个锁");
    });

    let m1 = Arc::clone(&mutex1);
    let m2 = Arc::clone(&mutex2);
    let handle2 = thread::spawn(move || {
        // 统一顺序：先 1 后 2
        let _g1 = m1.lock().unwrap();
        let _g2 = m2.lock().unwrap();
        println!("线程 2 获取了两个锁");
    });

    handle1.join().unwrap();
    handle2.join().unwrap();
}

// ✅ 解决方案 2: 使用 try_lock
fn fixed_deadlock_try_lock() {
    let mutex1 = Arc::new(Mutex::new(0));
    let mutex2 = Arc::new(Mutex::new(0));

    let m1 = Arc::clone(&mutex1);
    let m2 = Arc::clone(&mutex2);
    let handle1 = thread::spawn(move || {
        loop {
            if let Ok(g1) = m1.try_lock() {
                if let Ok(g2) = m2.try_lock() {
                    println!("线程 1 获取了两个锁");
                    break;
                }
            }
            // 重试前短暂休眠
            thread::sleep(std::time::Duration::from_millis(1));
        }
    });

    let m1 = Arc::clone(&mutex1);
    let m2 = Arc::clone(&mutex2);
    let handle2 = thread::spawn(move || {
        loop {
            if let Ok(g2) = m2.try_lock() {
                if let Ok(g1) = m1.try_lock() {
                    println!("线程 2 获取了两个锁");
                    break;
                }
            }
            thread::sleep(std::time::Duration::from_millis(1));
        }
    });

    handle1.join().unwrap();
    handle2.join().unwrap();
}

// ✅ 解决方案 3: 层级锁
struct HierarchicalMutex {
    mutex: Mutex<i32>,
    level: usize,
}

thread_local! {
    static CURRENT_LEVEL: std::cell::Cell<usize> = std::cell::Cell::new(0);
}

impl HierarchicalMutex {
    fn lock(&self) -> std::sync::MutexGuard<i32> {
        let current = CURRENT_LEVEL.with(|l| l.get());
        assert!(
            self.level > current,
            "锁顺序违规：尝试获取层级 {} 的锁，当前层级 {}",
            self.level,
            current
        );

        let guard = self.mutex.lock().unwrap();
        CURRENT_LEVEL.with(|l| l.set(self.level));
        guard
    }
}
```

### 案例 4: 优先级反转

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// 优先级反转问题：低优先级线程持有锁，高优先级线程等待
fn priority_inversion_example() {
    let resource = Arc::new(Mutex::new(vec![1, 2, 3]));

    // 低优先级线程
    let r = Arc::clone(&resource);
    let low_priority = thread::spawn(move || {
        let data = r.lock().unwrap();
        println!("低优先级线程获取锁");
        thread::sleep(std::time::Duration::from_secs(5));
        // 长时间持有锁
        println!("低优先级线程释放锁");
    });

    thread::sleep(std::time::Duration::from_millis(100));

    // 中优先级线程（占用 CPU）
    let medium_priority = thread::spawn(move || {
        println!("中优先级线程开始 CPU 密集型工作");
        let mut sum = 0;
        for i in 0..1_000_000_000 {
            sum += i;
        }
        println!("中优先级线程完成: {}", sum);
    });

    thread::sleep(std::time::Duration::from_millis(100));

    // 高优先级线程
    let r = Arc::clone(&resource);
    let high_priority = thread::spawn(move || {
        println!("高优先级线程等待锁...");
        let _data = r.lock().unwrap();
        println!("高优先级线程获取锁");
    });

    // 问题：高优先级线程被中优先级线程阻塞，
    // 而中优先级线程又在等低优先级线程释放锁

    low_priority.join().unwrap();
    medium_priority.join().unwrap();
    high_priority.join().unwrap();
}
```

### 案例 5: 条件变量误用

```rust
use std::sync::{Mutex, Condvar};
use std::thread;

// ❌ 错误：条件检查不使用 while 循环
fn bad_condition_variable() {
    let pair = std::sync::Arc::new((Mutex::new(false), Condvar::new()));

    let pair2 = std::sync::Arc::clone(&pair);
    thread::spawn(move || {
        let (lock, cvar) = &*pair2;
        let mut started = lock.lock().unwrap();
        *started = true;
        cvar.notify_one();
    });

    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();

    // ❌ 错误：使用 if 而不是 while
    // 可能发生虚假唤醒（spurious wakeup）
    if !*started {
        started = cvar.wait(started).unwrap();
    }
}

// ✅ 正确：使用 while 循环
fn good_condition_variable() {
    let pair = std::sync::Arc::new((Mutex::new(false), Condvar::new()));

    let pair2 = std::sync::Arc::clone(&pair);
    thread::spawn(move || {
        let (lock, cvar) = &*pair2;
        let mut started = lock.lock().unwrap();
        *started = true;
        cvar.notify_one();
        println!("子线程通知主线程");
    });

    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();

    // ✅ 正确：使用 while 处理虚假唤醒
    while !*started {
        started = cvar.wait(started).unwrap();
    }

    println!("主线程收到通知");
}
```

---

## 🐛 常见问题 {#-常见问题}

### 死锁

```rust
// ❌ 可能导致死锁
let mutex1 = Arc::new(Mutex::new(0));
let mutex2 = Arc::new(Mutex::new(0));

let m1 = Arc::clone(&mutex1);
let m2 = Arc::clone(&mutex2);
thread::spawn(move || {
    let _g1 = m1.lock().unwrap();
    let _g2 = m2.lock().unwrap();
});

let m1 = Arc::clone(&mutex1);
let m2 = Arc::clone(&mutex2);
thread::spawn(move || {
    let _g2 = m2.lock().unwrap(); // 不同的顺序
    let _g1 = m1.lock().unwrap();
});

// ✅ 解决方案：统一锁的顺序
```

### 数据竞争

```rust
// ❌ 数据竞争
let counter = Arc::new(0); // 不能直接共享

// ✅ 使用同步原语
let counter = Arc::new(Mutex::new(0));
```

---

## 📚 相关文档 {#-相关文档}

- [完整文档](../../crates/c05_threads/README.md)
- [线程管理指南](../../crates/c05_threads/docs/tier_02_guides/01_线程基础与生命周期.md)
- [并发控制指南](../../crates/c05_threads/docs/tier_02_guides/02_同步原语实践.md)
- [无锁数据结构](../../crates/c05_threads/docs/tier_03_references/02_无锁编程参考.md)
- [Send/Sync 形式化](../research_notes/formal_methods/send_sync_formalization.md) - Send/Sync Trait 形式化定义与安全保证

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 完整实现
**最后更新**: 2026-02-20
