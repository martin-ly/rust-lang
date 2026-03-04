# Rust并发架构设计模式

> **Rust版本**: 1.93.1
> **覆盖范围**: 并行、同步、异步架构模式
> **权威参考**: Rust Async Book, Tokio文档, Rayon文档

---

## 目录

- [Rust并发架构设计模式](#rust并发架构设计模式)
  - [目录](#目录)
  - [1. 并发模型概述](#1-并发模型概述)
    - [Rust并发哲学](#rust并发哲学)
    - [并发模型对比](#并发模型对比)
  - [2. 线程基础模式](#2-线程基础模式)
    - [线程池模式](#线程池模式)
    - [Scoped线程 (Rust 1.63+)](#scoped线程-rust-163)
  - [3. 同步模式](#3-同步模式)
    - [读写锁模式](#读写锁模式)
    - [屏障模式 (Barrier)](#屏障模式-barrier)
    - [信号量模式](#信号量模式)
  - [4. 异步模式](#4-异步模式)
    - [Actor模式 (Tokio)](#actor模式-tokio)
    - [管道模式 (Pipeline)](#管道模式-pipeline)
    - [Future组合模式](#future组合模式)
  - [5. 并行计算模式](#5-并行计算模式)
    - [数据并行 (Rayon)](#数据并行-rayon)
    - [分治模式](#分治模式)
  - [6. Actor模式](#6-actor模式)
    - [Actix框架示例](#actix框架示例)
  - [7. 无锁编程模式](#7-无锁编程模式)
    - [原子操作模式](#原子操作模式)
    - [CAS循环模式](#cas循环模式)
  - [8. 架构最佳实践](#8-架构最佳实践)
    - [选择合适的并发模型](#选择合适的并发模型)
    - [避免常见陷阱](#避免常见陷阱)
  - [参考文献](#参考文献)

---

## 1. 并发模型概述

### Rust并发哲学

```text
零成本抽象 +  fearless concurrency

1. 编译时保证线程安全 (Send/Sync)
2. 数据竞争在编译时防止
3. 运行时开销最小化
```

### 并发模型对比

| 模型 | 代表库 | 适用场景 | 特点 |
|------|--------|---------|------|
| 线程 | std::thread | CPU密集型 | 系统线程 |
| 异步 | Tokio/async-std | IO密集型 | 协程/事件循环 |
| 并行 | Rayon | 数据并行 | work-stealing |
| Actor | Actix | 消息传递 | 隔离状态 |

---

## 2. 线程基础模式

### 线程池模式

```rust
use std::sync::{mpsc, Arc, Mutex};
use std::thread;

pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: mpsc::Sender<Message>,
}

type Job = Box<dyn FnOnce() + Send + 'static>;

enum Message {
    NewJob(Job),
    Terminate,
}

impl ThreadPool {
    pub fn new(size: usize) -> ThreadPool {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);
        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        ThreadPool { workers, sender }
    }

    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.send(Message::NewJob(job)).unwrap();
    }
}

struct Worker {
    id: usize,
    thread: thread::JoinHandle<()>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Message>>>) -> Worker {
        let thread = thread::spawn(move || loop {
            let message = receiver.lock().unwrap().recv().unwrap();

            match message {
                Message::NewJob(job) => {
                    println!("Worker {} got a job; executing.", id);
                    job();
                }
                Message::Terminate => {
                    println!("Worker {} was told to terminate.", id);
                    break;
                }
            }
        });

        Worker { id, thread }
    }
}
```

### Scoped线程 (Rust 1.63+)

```rust
use std::thread;

fn scoped_threads() {
    let mut data = vec![1, 2, 3];

    thread::scope(|s| {
        s.spawn(|| {
            println!("Thread 1: {:?}", data);
        });

        s.spawn(|| {
            // 可以安全地共享data
            println!("Thread 2: {:?}", data);
        });
    });

    // data在这里仍然有效
    data.push(4);
}
```

---

## 3. 同步模式

### 读写锁模式

```rust
use std::sync::RwLock;

pub struct Cache<K, V> {
    data: RwLock<std::collections::HashMap<K, V>>,
}

impl<K: Eq + std::hash::Hash, V: Clone> Cache<K, V> {
    pub fn get(&self, key: &K) -> Option<V> {
        let read_guard = self.data.read().unwrap();
        read_guard.get(key).cloned()
    }

    pub fn insert(&self, key: K, value: V) {
        let mut write_guard = self.data.write().unwrap();
        write_guard.insert(key, value);
    }
}
```

### 屏障模式 (Barrier)

```rust
use std::sync::Barrier;

fn barrier_example() {
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];

    for i in 0..3 {
        let b = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            println!("Thread {} before barrier", i);
            b.wait();
            println!("Thread {} after barrier", i);
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
}
```

### 信号量模式

```rust
use std::sync::Arc;
use tokio::sync::Semaphore;

async fn semaphore_example() {
    let semaphore = Arc::new(Semaphore::new(3)); // 最多3个并发

    let mut handles = vec![];

    for i in 0..10 {
        let permit = semaphore.clone().acquire_owned().await.unwrap();
        handles.push(tokio::spawn(async move {
            println!("Task {} started", i);
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
            println!("Task {} finished", i);
            drop(permit);
        }));
    }

    for h in handles {
        h.await.unwrap();
    }
}
```

---

## 4. 异步模式

### Actor模式 (Tokio)

```rust
use tokio::sync::{mpsc, oneshot};

// Actor消息
type Response<T> = oneshot::Sender<T>;

pub enum ActorMessage {
    Get { key: String, respond_to: Response<Option<String>> },
    Set { key: String, value: String, respond_to: Response<()> },
}

// Actor
pub struct CacheActor {
    receiver: mpsc::Receiver<ActorMessage>,
    data: std::collections::HashMap<String, String>,
}

impl CacheActor {
    fn new(receiver: mpsc::Receiver<ActorMessage>) -> Self {
        Self {
            receiver,
            data: std::collections::HashMap::new(),
        }
    }

    async fn run(&mut self) {
        while let Some(msg) = self.receiver.recv().await {
            self.handle_message(msg);
        }
    }

    fn handle_message(&mut self, msg: ActorMessage) {
        match msg {
            ActorMessage::Get { key, respond_to } => {
                let _ = respond_to.send(self.data.get(&key).cloned());
            }
            ActorMessage::Set { key, value, respond_to } => {
                self.data.insert(key, value);
                let _ = respond_to.send(());
            }
        }
    }
}

// Actor Handle
#[derive(Clone)]
pub struct CacheActorHandle {
    sender: mpsc::Sender<ActorMessage>,
}

impl CacheActorHandle {
    pub async fn get(&self, key: &str) -> Option<String> {
        let (tx, rx) = oneshot::channel();
        let msg = ActorMessage::Get {
            key: key.to_string(),
            respond_to: tx,
        };
        let _ = self.sender.send(msg).await;
        rx.await.unwrap()
    }

    pub async fn set(&self, key: &str, value: &str) {
        let (tx, rx) = oneshot::channel();
        let msg = ActorMessage::Set {
            key: key.to_string(),
            value: value.to_string(),
            respond_to: tx,
        };
        let _ = self.sender.send(msg).await;
        rx.await.unwrap()
    }
}

pub fn start_actor() -> CacheActorHandle {
    let (tx, rx) = mpsc::channel(100);
    let mut actor = CacheActor::new(rx);

    tokio::spawn(async move {
        actor.run().await;
    });

    CacheActorHandle { sender: tx }
}
```

### 管道模式 (Pipeline)

```rust
use tokio::sync::mpsc;

async fn pipeline_example() {
    let (tx1, mut rx1) = mpsc::channel::<i32>(100);
    let (tx2, mut rx2) = mpsc::channel::<i32>(100);
    let (tx3, mut rx3) = mpsc::channel::<String>(100);

    // Stage 1: 生成数据
    tokio::spawn(async move {
        for i in 0..10 {
            tx1.send(i).await.unwrap();
        }
    });

    // Stage 2: 处理数据
    tokio::spawn(async move {
        while let Some(data) = rx1.recv().await {
            tx2.send(data * 2).await.unwrap();
        }
    });

    // Stage 3: 格式化输出
    tokio::spawn(async move {
        while let Some(data) = rx2.recv().await {
            tx3.send(format!("Result: {}", data)).await.unwrap();
        }
    });

    // 消费结果
    while let Some(result) = rx3.recv().await {
        println!("{}", result);
    }
}
```

### Future组合模式

```rust
use futures::future::{join, select, try_join};

async fn future_composition() {
    let f1 = async { "result1" };
    let f2 = async { "result2" };

    // 等待所有完成
    let (r1, r2) = join(f1, f2).await;

    // 等待第一个完成
    let result = select(f1, f2).await;

    // 超时模式
    let result = tokio::time::timeout(
        tokio::time::Duration::from_secs(5),
        some_async_operation()
    ).await;
}
```

---

## 5. 并行计算模式

### 数据并行 (Rayon)

```rust
use rayon::prelude::*;

fn data_parallel() {
    let data: Vec<i32> = (0..1000000).collect();

    // 并行map
    let squared: Vec<i32> = data.par_iter()
        .map(|x| x * x)
        .collect();

    // 并行reduce
    let sum: i32 = data.par_iter()
        .sum();

    // 并行filter
    let evens: Vec<i32> = data.par_iter()
        .filter(|&&x| x % 2 == 0)
        .cloned()
        .collect();
}
```

### 分治模式

```rust
use rayon::join;

fn parallel_merge_sort<T: Ord + Send>(data: &mut [T]) {
    if data.len() <= 1 {
        return;
    }

    let mid = data.len() / 2;
    let (left, right) = data.split_at_mut(mid);

    // 并行递归
    join(
        || parallel_merge_sort(left),
        || parallel_merge_sort(right),
    );

    // 合并结果
    // ...
}
```

---

## 6. Actor模式

### Actix框架示例

```rust
use actix::prelude::*;

// 定义Actor
struct MyActor {
    count: usize,
}

impl Actor for MyActor {
    type Context = Context<Self>;
}

// 定义消息
struct MyMessage {
    value: usize,
}

impl Message for MyMessage {
    type Result = usize;
}

// 处理消息
impl Handler<MyMessage> for MyActor {
    type Result = usize;

    fn handle(&mut self, msg: MyMessage, _ctx: &mut Context<Self>) -> Self::Result {
        self.count += msg.value;
        self.count
    }
}

// 使用
async fn actor_usage() {
    let addr = MyActor { count: 0 }.start();

    let result = addr.send(MyMessage { value: 10 }).await.unwrap();
    println!("Result: {}", result);
}
```

---

## 7. 无锁编程模式

### 原子操作模式

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct LockFreeCounter {
    count: AtomicUsize,
}

impl LockFreeCounter {
    pub fn new() -> Self {
        Self {
            count: AtomicUsize::new(0),
        }
    }

    pub fn increment(&self) -> usize {
        self.count.fetch_add(1, Ordering::Relaxed)
    }

    pub fn get(&self) -> usize {
        self.count.load(Ordering::Relaxed)
    }
}
```

### CAS循环模式

```rust
use std::sync::atomic::{AtomicPtr, Ordering};
use std::ptr;

pub struct LockFreeStack<T> {
    head: AtomicPtr<Node<T>>,
}

struct Node<T> {
    data: T,
    next: *mut Node<T>,
}

impl<T> LockFreeStack<T> {
    pub fn push(&self, data: T) {
        let new_node = Box::into_raw(Box::new(Node {
            data,
            next: ptr::null_mut(),
        }));

        loop {
            let head = self.head.load(Ordering::Relaxed);
            unsafe { (*new_node).next = head; }

            if self.head.compare_exchange(
                head,
                new_node,
                Ordering::Release,
                Ordering::Relaxed,
            ).is_ok() {
                break;
            }
        }
    }
}
```

---

## 8. 架构最佳实践

### 选择合适的并发模型

| 场景 | 推荐模型 | 原因 |
|------|---------|------|
| CPU密集型计算 | Rayon | 自动负载均衡 |
| IO密集型服务 | Tokio | 高效事件循环 |
| 状态机 | Actor | 隔离和消息传递 |
| 共享状态 | RwLock/Mutex | 简单直接 |
| 高吞吐队列 | 无锁队列 | 最小化开销 |

### 避免常见陷阱

```rust
// ❌ 错误：在异步代码中阻塞
async fn bad_practice() {
    std::thread::sleep(std::time::Duration::from_secs(1)); // 阻塞整个线程！
}

// ✅ 正确：使用异步sleep
async fn good_practice() {
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
}
```

```rust
// ❌ 错误：在锁中持有await
async fn bad_mutex() {
    let data = Arc::new(Mutex::new(vec![]));
    let guard = data.lock().unwrap();
    some_async_operation().await; // 可能死锁！
}

// ✅ 正确：缩小锁的作用域
async fn good_mutex() {
    let data = Arc::new(Mutex::new(vec![]));
    {
        let guard = data.lock().unwrap();
        // 同步操作
    }
    some_async_operation().await;
}
```

---

## 参考文献

1. The Rust Async Book: <https://rust-lang.github.io/async-book/>
2. Tokio Documentation: <https://tokio.rs/>
3. Rayon Documentation: <https://docs.rs/rayon/>
4. Actix Documentation: <https://actix.rs/>
5. Rust Atomics and Locks: <https://marabos.nl/atomics/>
