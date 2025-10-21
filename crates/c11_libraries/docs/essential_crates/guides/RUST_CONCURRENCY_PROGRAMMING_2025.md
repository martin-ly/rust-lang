# Rust 并发编程实战指南 (2025)

> **全面掌握 Rust 并发编程，从多线程到无锁数据结构**
>
> **版本**: Rust 1.90+ | **更新日期**: 2025-10-20 | **难度**: ⭐⭐⭐⭐

## 📋 目录1

- [Rust 并发编程实战指南 (2025)](#rust-并发编程实战指南-2025)
  - [📋 目录1](#-目录1)
  - [1. 并发编程基础1](#1-并发编程基础1)
    - [1.1 并发 vs 并行1](#11-并发-vs-并行1)
    - [1.2 Rust 并发模型1](#12-rust-并发模型1)
    - [1.3 线程安全保证1](#13-线程安全保证1)
  - [2. 多线程编程1](#2-多线程编程1)
    - [2.1 标准库线程1](#21-标准库线程1)
    - [2.2 线程池1](#22-线程池1)
    - [2.3 Rayon 并行迭代器1](#23-rayon-并行迭代器1)
  - [3. 共享状态并发1](#3-共享状态并发1)
    - [3.1 Mutex 互斥锁1](#31-mutex-互斥锁1)
    - [3.2 RwLock 读写锁1](#32-rwlock-读写锁1)
    - [3.3 Atomic 原子操作1](#33-atomic-原子操作1)
  - [4. 消息传递并发1](#4-消息传递并发1)
    - [4.1 标准库 channel1](#41-标准库-channel1)
    - [4.2 Crossbeam channel1](#42-crossbeam-channel1)
    - [4.3 Flume channel1](#43-flume-channel1)
  - [5. 无锁数据结构1](#5-无锁数据结构1)
    - [5.1 无锁队列1](#51-无锁队列1)
    - [5.2 无锁栈1](#52-无锁栈1)
    - [5.3 Crossbeam 并发集合1](#53-crossbeam-并发集合1)
  - [6. 高级并发模式1](#6-高级并发模式1)
    - [6.1 Work-Stealing1](#61-work-stealing1)
    - [6.2 Actor 模型1](#62-actor-模型1)
    - [6.3 CSP 模型1](#63-csp-模型1)
  - [7. 实战案例1](#7-实战案例1)
    - [7.1 并发 Web 爬虫1](#71-并发-web-爬虫1)
    - [7.2 并发数据处理管道1](#72-并发数据处理管道1)
    - [7.3 并发任务调度器1](#73-并发任务调度器1)
  - [8. 性能优化1](#8-性能优化1)
    - [8.1 减少锁竞争1](#81-减少锁竞争1)
    - [8.2 缓存友好设计1](#82-缓存友好设计1)
    - [8.3 性能分析工具1](#83-性能分析工具1)
  - [9. 常见陷阱1](#9-常见陷阱1)
  - [10. 最佳实践1](#10-最佳实践1)
  - [11. 参考资源1](#11-参考资源1)
    - [官方文档](#官方文档)
    - [推荐库](#推荐库)
    - [学习资源](#学习资源)
  - [总结](#总结)

---

## 1. 并发编程基础1

### 1.1 并发 vs 并行1

```text
┌────────────────────────────────────────────────────────────┐
│                 并发 (Concurrency)                         │
│  处理多个任务，但不一定同时执行                            │
│                                                            │
│  Thread 1: ████──────████──────████                        │
│  Thread 2: ──────████──────████──────                      │
│            ▲                                               │
│            └─ 时间片切换                                   │
└────────────────────────────────────────────────────────────┘

┌────────────────────────────────────────────────────────────┐
│                 并行 (Parallelism)                         │
│  多个任务真正同时执行                                      │
│                                                            │
│  Core 1:   ████████████████████                            │
│  Core 2:   ████████████████████                            │
│            ▲                                               │
│            └─ 同时执行                                     │
└────────────────────────────────────────────────────────────┘
```

### 1.2 Rust 并发模型1

**核心特性**:

1. **所有权系统**
   - 编译时检查数据竞争
   - 防止悬垂指针
   - 保证内存安全

2. **Send 和 Sync trait**
   - `Send`: 可以在线程间传递所有权
   - `Sync`: 可以在线程间共享引用
   - 编译器自动实现

```rust
// Send: 可以跨线程传递所有权
fn is_send<T: Send>() {}
is_send::<String>();  // ✅ String 实现了 Send

// Sync: 可以跨线程共享引用
fn is_sync<T: Sync>() {}
is_sync::<String>();  // ✅ String 实现了 Sync

// Rc 不是 Send/Sync
use std::rc::Rc;
// is_send::<Rc<i32>>();  // ❌ 编译错误
```

### 1.3 线程安全保证1

```rust
use std::sync::Arc;
use std::thread;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Arc: 原子引用计数，线程安全
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let data = Arc::new(vec![1, 2, 3, 4, 5]);
let mut handles = vec![];

for i in 0..3 {
    let data = Arc::clone(&data);
    let handle = thread::spawn(move || {
        println!("Thread {}: {:?}", i, data);
    });
    handles.push(handle);
}

for handle in handles {
    handle.join().unwrap();
}
```

---

## 2. 多线程编程1

### 2.1 标准库线程1

**基本使用**:

```rust
use std::thread;
use std::time::Duration;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 创建线程
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let handle = thread::spawn(|| {
    for i in 1..10 {
        println!("子线程: {}", i);
        thread::sleep(Duration::from_millis(1));
    }
});

// 主线程继续执行
for i in 1..5 {
    println!("主线程: {}", i);
    thread::sleep(Duration::from_millis(1));
}

// 等待子线程完成
handle.join().unwrap();

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 线程返回值
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let handle = thread::spawn(|| {
    thread::sleep(Duration::from_millis(100));
    42
});

let result = handle.join().unwrap();
println!("线程返回值: {}", result);

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 线程命名
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let handle = thread::Builder::new()
    .name("worker-1".to_string())
    .spawn(|| {
        println!("当前线程: {:?}", thread::current().name());
    })
    .unwrap();

handle.join().unwrap();
```

### 2.2 线程池1

**手动实现简单线程池**:

```rust
use std::sync::{mpsc, Arc, Mutex};
use std::thread;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 线程池结构
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: mpsc::Sender<Job>,
}

type Job = Box<dyn FnOnce() + Send + 'static>;

impl ThreadPool {
    pub fn new(size: usize) -> ThreadPool {
        assert!(size > 0);

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
        self.sender.send(job).unwrap();
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Worker 结构
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
struct Worker {
    id: usize,
    thread: thread::JoinHandle<()>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Job>>>) -> Worker {
        let thread = thread::spawn(move || loop {
            let job = receiver.lock().unwrap().recv().unwrap();
            println!("Worker {} 开始执行任务", id);
            job();
        });

        Worker { id, thread }
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 使用示例
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() {
    let pool = ThreadPool::new(4);

    for i in 0..8 {
        pool.execute(move || {
            println!("执行任务 {}", i);
            thread::sleep(Duration::from_secs(1));
        });
    }

    thread::sleep(Duration::from_secs(10));
}
```

### 2.3 Rayon 并行迭代器1

```rust
use rayon::prelude::*;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 并行 map
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let numbers: Vec<i32> = (0..1000).collect();
let results: Vec<i32> = numbers
    .par_iter()
    .map(|&x| x * x)
    .collect();

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 并行 filter + map
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let even_squares: Vec<i32> = numbers
    .par_iter()
    .filter(|&&x| x % 2 == 0)
    .map(|&x| x * x)
    .collect();

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 并行 reduce
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let sum: i32 = numbers.par_iter().sum();
let max: Option<&i32> = numbers.par_iter().max();

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 自定义并行度
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
use rayon::ThreadPoolBuilder;

let pool = ThreadPoolBuilder::new().num_threads(8).build().unwrap();
pool.install(|| {
    let sum: i32 = (0..1000).into_par_iter().sum();
    println!("Sum: {}", sum);
});
```

---

## 3. 共享状态并发1

### 3.1 Mutex 互斥锁1

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 基本使用
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
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

println!("Result: {}", *counter.lock().unwrap());

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 避免死锁
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let data1 = Arc::new(Mutex::new(0));
let data2 = Arc::new(Mutex::new(0));

// ✅ 总是按相同顺序获取锁
{
    let lock1 = data1.lock().unwrap();
    let lock2 = data2.lock().unwrap();
    // ... 使用数据 ...
}

// ❌ 不同顺序获取锁 (可能死锁)
// Thread 1: lock(data1) -> lock(data2)
// Thread 2: lock(data2) -> lock(data1)
```

### 3.2 RwLock 读写锁1

```rust
use std::sync::{Arc, RwLock};
use std::thread;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 多读单写
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let data = Arc::new(RwLock::new(vec![1, 2, 3]));
let mut handles = vec![];

// 10 个读线程
for i in 0..10 {
    let data = Arc::clone(&data);
    let handle = thread::spawn(move || {
        let read_guard = data.read().unwrap();
        println!("Reader {}: {:?}", i, *read_guard);
    });
    handles.push(handle);
}

// 1 个写线程
let data_writer = Arc::clone(&data);
let write_handle = thread::spawn(move || {
    let mut write_guard = data_writer.write().unwrap();
    write_guard.push(4);
    println!("Writer: pushed 4");
});
handles.push(write_handle);

for handle in handles {
    handle.join().unwrap();
}
```

### 3.3 Atomic 原子操作1

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 原子计数器
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let counter = Arc::new(AtomicUsize::new(0));
let mut handles = vec![];

for _ in 0..10 {
    let counter = Arc::clone(&counter);
    let handle = thread::spawn(move || {
        for _ in 0..1000 {
            counter.fetch_add(1, Ordering::SeqCst);
        }
    });
    handles.push(handle);
}

for handle in handles {
    handle.join().unwrap();
}

println!("Result: {}", counter.load(Ordering::SeqCst));

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// CAS (Compare-And-Swap)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let value = AtomicUsize::new(0);

// 尝试将 0 修改为 1
match value.compare_exchange(
    0,                      // 期望值
    1,                      // 新值
    Ordering::SeqCst,       // 成功的内存顺序
    Ordering::SeqCst        // 失败的内存顺序
) {
    Ok(prev) => println!("成功: 旧值 = {}", prev),
    Err(current) => println!("失败: 当前值 = {}", current),
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 内存顺序
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Relaxed: 最弱保证，只保证原子性
// Acquire: 读操作，确保之后的操作不会重排到此之前
// Release: 写操作，确保之前的操作不会重排到此之后
// SeqCst: 最强保证，全局顺序一致性
```

---

## 4. 消息传递并发1

### 4.1 标准库 channel1

```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 单生产者单消费者 (SPSC)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let (tx, rx) = mpsc::channel();

thread::spawn(move || {
    for i in 0..5 {
        tx.send(i).unwrap();
        thread::sleep(Duration::from_millis(100));
    }
});

for received in rx {
    println!("收到: {}", received);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 多生产者单消费者 (MPSC)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let (tx, rx) = mpsc::channel();

for i in 0..3 {
    let tx = tx.clone();
    thread::spawn(move || {
        tx.send(format!("消息来自线程 {}", i)).unwrap();
    });
}

// 删除原始 sender
drop(tx);

for received in rx {
    println!("收到: {}", received);
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 同步 channel (有界)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let (tx, rx) = mpsc::sync_channel(3); // 缓冲区大小为 3

thread::spawn(move || {
    for i in 0..10 {
        println!("发送: {}", i);
        tx.send(i).unwrap(); // 缓冲区满时会阻塞
    }
});

thread::sleep(Duration::from_secs(2));

for received in rx {
    println!("收到: {}", received);
    thread::sleep(Duration::from_millis(500));
}
```

### 4.2 Crossbeam channel1

```rust
use crossbeam::channel;
use std::thread;
use std::time::Duration;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 无界 channel
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let (tx, rx) = channel::unbounded();

thread::spawn(move || {
    tx.send("Hello").unwrap();
});

println!("{}", rx.recv().unwrap());

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 有界 channel
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let (tx, rx) = channel::bounded(5);

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// select! 多路复用
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let (tx1, rx1) = channel::unbounded();
let (tx2, rx2) = channel::unbounded();

thread::spawn(move || {
    thread::sleep(Duration::from_millis(100));
    tx1.send("from tx1").unwrap();
});

thread::spawn(move || {
    thread::sleep(Duration::from_millis(200));
    tx2.send("from tx2").unwrap();
});

crossbeam::select! {
    recv(rx1) -> msg => println!("收到: {:?}", msg),
    recv(rx2) -> msg => println!("收到: {:?}", msg),
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 超时接收
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let (tx, rx) = channel::unbounded();

match rx.recv_timeout(Duration::from_secs(1)) {
    Ok(msg) => println!("收到: {}", msg),
    Err(_) => println!("超时"),
}
```

### 4.3 Flume channel1

```rust
use flume;
use std::thread;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Flume: 高性能 MPMC channel
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let (tx, rx) = flume::unbounded();

// 多个生产者
for i in 0..3 {
    let tx = tx.clone();
    thread::spawn(move || {
        tx.send(i).unwrap();
    });
}

drop(tx); // 删除原始 sender

// 多个消费者
let mut handles = vec![];
for _ in 0..2 {
    let rx = rx.clone();
    let handle = thread::spawn(move || {
        while let Ok(msg) = rx.recv() {
            println!("收到: {}", msg);
        }
    });
    handles.push(handle);
}

for handle in handles {
    handle.join().unwrap();
}
```

---

## 5. 无锁数据结构1

### 5.1 无锁队列1

```rust
use crossbeam::queue::SegQueue;
use std::sync::Arc;
use std::thread;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// SegQueue: 无界无锁队列
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let queue = Arc::new(SegQueue::new());
let mut handles = vec![];

// 多个生产者
for i in 0..10 {
    let queue = Arc::clone(&queue);
    let handle = thread::spawn(move || {
        queue.push(i);
    });
    handles.push(handle);
}

// 多个消费者
for _ in 0..5 {
    let queue = Arc::clone(&queue);
    let handle = thread::spawn(move || {
        while let Some(item) = queue.pop() {
            println!("消费: {}", item);
        }
    });
    handles.push(handle);
}

for handle in handles {
    handle.join().unwrap();
}
```

### 5.2 无锁栈1

```rust
use crossbeam::queue::SegStack;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// SegStack: 无界无锁栈
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let stack = SegStack::new();

stack.push(1);
stack.push(2);
stack.push(3);

assert_eq!(stack.pop(), Some(3));
assert_eq!(stack.pop(), Some(2));
assert_eq!(stack.pop(), Some(1));
```

### 5.3 Crossbeam 并发集合1

```rust
use crossbeam::queue::ArrayQueue;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// ArrayQueue: 有界无锁队列
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
let queue = ArrayQueue::new(100);

// 生产者
queue.push(1).unwrap();
queue.push(2).unwrap();

// 消费者
assert_eq!(queue.pop(), Some(1));
assert_eq!(queue.pop(), Some(2));

// 队列满时返回 Err
let full_queue = ArrayQueue::new(1);
full_queue.push(1).unwrap();
assert!(full_queue.push(2).is_err());
```

---

## 6. 高级并发模式1

### 6.1 Work-Stealing1

```rust
use rayon::prelude::*;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Rayon 使用 Work-Stealing 调度
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn fibonacci(n: u64) -> u64 {
    if n < 2 {
        return n;
    }
    
    let (a, b) = rayon::join(|| fibonacci(n - 1), || fibonacci(n - 2));
    a + b
}

fn main() {
    let result = fibonacci(20);
    println!("Fibonacci(20) = {}", result);
}
```

**Work-Stealing 原理**:

```text
┌──────────────────────────────────────────────────────────┐
│                    Worker Threads                        │
├──────────────────────────────────────────────────────────┤
│                                                          │
│  Worker 1:  [Task A] [Task B]                            │
│                ↑                                         │
│                │ steal                                   │
│  Worker 2:  [Task C] [Task D] [Task E] ──────┐          │
│                                               │          │
│  Worker 3:  [Task F] ←────────────────────────┘          │
│                                                          │
│  ✅ 负载均衡：空闲线程从忙碌线程偷取任务              │
└──────────────────────────────────────────────────────────┘
```

### 6.2 Actor 模型1

```rust
use std::sync::mpsc;
use std::thread;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Actor 定义
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
enum Message {
    Increment,
    Decrement,
    GetValue(mpsc::Sender<i32>),
}

struct Counter {
    receiver: mpsc::Receiver<Message>,
    value: i32,
}

impl Counter {
    fn new(receiver: mpsc::Receiver<Message>) -> Self {
        Counter { receiver, value: 0 }
    }

    fn run(&mut self) {
        while let Ok(msg) = self.receiver.recv() {
            match msg {
                Message::Increment => self.value += 1,
                Message::Decrement => self.value -= 1,
                Message::GetValue(sender) => {
                    sender.send(self.value).unwrap();
                }
            }
        }
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Actor 使用
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let mut counter = Counter::new(rx);
        counter.run();
    });

    tx.send(Message::Increment).unwrap();
    tx.send(Message::Increment).unwrap();
    tx.send(Message::Decrement).unwrap();

    let (response_tx, response_rx) = mpsc::channel();
    tx.send(Message::GetValue(response_tx)).unwrap();

    println!("当前值: {}", response_rx.recv().unwrap());
}
```

### 6.3 CSP 模型1

```rust
use crossbeam::channel;
use std::thread;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// CSP (Communicating Sequential Processes)
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn producer(tx: channel::Sender<i32>) {
    for i in 0..10 {
        tx.send(i).unwrap();
    }
}

fn consumer(rx: channel::Receiver<i32>) {
    while let Ok(value) = rx.recv() {
        println!("消费: {}", value);
    }
}

fn main() {
    let (tx, rx) = channel::unbounded();

    thread::spawn(move || producer(tx));
    thread::spawn(move || consumer(rx));

    thread::sleep(std::time::Duration::from_secs(2));
}
```

---

## 7. 实战案例1

### 7.1 并发 Web 爬虫1

```rust
use reqwest;
use scraper::{Html, Selector};
use std::collections::HashSet;
use std::sync::{Arc, Mutex};
use tokio;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let urls = vec![
        "https://example.com/page1",
        "https://example.com/page2",
        "https://example.com/page3",
    ];

    let visited = Arc::new(Mutex::new(HashSet::new()));
    let mut handles = vec![];

    for url in urls {
        let visited = Arc::clone(&visited);
        let handle = tokio::spawn(async move {
            crawl(url, visited).await
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await??;
    }

    Ok(())
}

async fn crawl(
    url: &str,
    visited: Arc<Mutex<HashSet<String>>>,
) -> Result<(), Box<dyn std::error::Error>> {
    // 检查是否已访问
    {
        let mut visited = visited.lock().unwrap();
        if visited.contains(url) {
            return Ok(());
        }
        visited.insert(url.to_string());
    }

    // 获取页面内容
    let response = reqwest::get(url).await?;
    let body = response.text().await?;
    let document = Html::parse_document(&body);

    // 提取链接
    let selector = Selector::parse("a").unwrap();
    for element in document.select(&selector) {
        if let Some(link) = element.value().attr("href") {
            println!("找到链接: {}", link);
        }
    }

    Ok(())
}
```

### 7.2 并发数据处理管道1

```rust
use crossbeam::channel;
use std::thread;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 数据处理管道: 读取 -> 处理 -> 写入
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() {
    let (input_tx, input_rx) = channel::unbounded();
    let (output_tx, output_rx) = channel::unbounded();

    // Stage 1: 读取数据
    thread::spawn(move || {
        for i in 0..100 {
            input_tx.send(i).unwrap();
        }
    });

    // Stage 2: 处理数据 (多个 worker)
    for _ in 0..4 {
        let input_rx = input_rx.clone();
        let output_tx = output_tx.clone();

        thread::spawn(move || {
            while let Ok(data) = input_rx.recv() {
                let processed = data * 2; // 处理逻辑
                output_tx.send(processed).unwrap();
            }
        });
    }

    drop(output_tx); // 删除原始 sender

    // Stage 3: 写入结果
    let writer = thread::spawn(move || {
        let mut results = vec![];
        while let Ok(data) = output_rx.recv() {
            results.push(data);
        }
        results
    });

    let results = writer.join().unwrap();
    println!("处理了 {} 条数据", results.len());
}
```

### 7.3 并发任务调度器1

```rust
use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::Duration;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 任务调度器
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
struct TaskScheduler {
    queue: Arc<(Mutex<VecDeque<Task>>, Condvar)>,
}

type Task = Box<dyn FnOnce() + Send + 'static>;

impl TaskScheduler {
    fn new(num_workers: usize) -> Self {
        let queue = Arc::new((Mutex::new(VecDeque::new()), Condvar::new()));

        for i in 0..num_workers {
            let queue = Arc::clone(&queue);
            thread::spawn(move || {
                Self::worker_loop(i, queue);
            });
        }

        TaskScheduler { queue }
    }

    fn submit<F>(&self, task: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let (lock, cvar) = &*self.queue;
        let mut queue = lock.lock().unwrap();
        queue.push_back(Box::new(task));
        cvar.notify_one();
    }

    fn worker_loop(id: usize, queue: Arc<(Mutex<VecDeque<Task>>, Condvar)>) {
        loop {
            let (lock, cvar) = &*queue;
            let mut queue = lock.lock().unwrap();

            while queue.is_empty() {
                queue = cvar.wait(queue).unwrap();
            }

            if let Some(task) = queue.pop_front() {
                drop(queue); // 释放锁
                println!("Worker {} 执行任务", id);
                task();
            }
        }
    }
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 使用示例
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() {
    let scheduler = TaskScheduler::new(4);

    for i in 0..10 {
        scheduler.submit(move || {
            println!("任务 {} 开始", i);
            thread::sleep(Duration::from_millis(100));
            println!("任务 {} 完成", i);
        });
    }

    thread::sleep(Duration::from_secs(3));
}
```

---

## 8. 性能优化1

### 8.1 减少锁竞争1

**❌ 错误: 频繁锁竞争**:

```rust
use std::sync::{Arc, Mutex};
use std::thread;

let counter = Arc::new(Mutex::new(0));
let mut handles = vec![];

for _ in 0..10 {
    let counter = Arc::clone(&counter);
    let handle = thread::spawn(move || {
        for _ in 0..100000 {
            let mut num = counter.lock().unwrap();
            *num += 1;
            // 每次迭代都加锁/解锁 (性能差)
        }
    });
    handles.push(handle);
}
```

**✅ 正确: 本地累加后合并**:

```rust
use std::sync::{Arc, Mutex};
use std::thread;

let counter = Arc::new(Mutex::new(0));
let mut handles = vec![];

for _ in 0..10 {
    let counter = Arc::clone(&counter);
    let handle = thread::spawn(move || {
        let mut local_sum = 0;
        for _ in 0..100000 {
            local_sum += 1; // 本地累加
        }
        
        // 只加锁一次
        let mut num = counter.lock().unwrap();
        *num += local_sum;
    });
    handles.push(handle);
}
```

### 8.2 缓存友好设计1

**❌ 错误: 伪共享 (False Sharing)**:

```rust
use std::sync::Arc;
use std::thread;

struct Counter {
    count1: u64,  // 同一缓存行
    count2: u64,  // 同一缓存行
}

let counter = Arc::new(Counter { count1: 0, count2: 0 });

// Thread 1 修改 count1，Thread 2 修改 count2
// 会导致缓存行失效，性能下降
```

**✅ 正确: 填充避免伪共享**:

```rust
use std::sync::Arc;
use std::thread;

#[repr(align(64))] // 缓存行大小
struct PaddedCounter {
    count: u64,
    _padding: [u8; 56], // 填充到 64 字节
}

let counter1 = Arc::new(PaddedCounter { count: 0, _padding: [0; 56] });
let counter2 = Arc::new(PaddedCounter { count: 0, _padding: [0; 56] });

// 现在 counter1 和 counter2 在不同缓存行
```

### 8.3 性能分析工具1

**Criterion 基准测试**:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::sync::{Arc, Mutex};
use std::thread;

fn mutex_benchmark(c: &mut Criterion) {
    c.bench_function("mutex increment", |b| {
        b.iter(|| {
            let counter = Arc::new(Mutex::new(0));
            let mut handles = vec![];

            for _ in 0..10 {
                let counter = Arc::clone(&counter);
                let handle = thread::spawn(move || {
                    for _ in 0..1000 {
                        let mut num = counter.lock().unwrap();
                        *num += 1;
                    }
                });
                handles.push(handle);
            }

            for handle in handles {
                handle.join().unwrap();
            }
        });
    });
}

criterion_group!(benches, mutex_benchmark);
criterion_main!(benches);
```

---

## 9. 常见陷阱1

1. **死锁 (Deadlock)**
   - 总是按相同顺序获取锁
   - 使用 `try_lock()` 避免阻塞
   - 考虑使用无锁数据结构

2. **伪共享 (False Sharing)**
   - 使用 `#[repr(align(64))]` 对齐
   - 避免多线程修改相邻数据

3. **过度同步 (Over-Synchronization)**
   - 尽可能使用不可变数据
   - 优先使用消息传递而非共享状态
   - 本地累加后合并结果

4. **内存顺序错误 (Memory Ordering)**
   - 默认使用 `SeqCst`
   - 只有在理解原理后才使用 `Relaxed`

5. **Panic 导致锁中毒 (Lock Poisoning)**
   - 使用 `into_inner()` 或 `get_mut()` 恢复
   - 避免在持有锁时 panic

---

## 10. 最佳实践1

1. **优先使用高级抽象**
   - Rayon 用于数据并行
   - Tokio 用于异步并发
   - Crossbeam 用于消息传递

2. **选择合适的同步原语**
   - 读多写少: `RwLock`
   - 简单计数: `Atomic`
   - 复杂状态: `Mutex`

3. **避免共享状态**
   - 优先使用消息传递
   - 使用 Actor 模型

4. **性能测试**
   - 使用 Criterion 基准测试
   - 使用 Flamegraph 分析热点

5. **文档和测试**
   - 记录线程安全保证
   - 编写并发测试

---

## 11. 参考资源1

### 官方文档

- [The Rust Programming Language - Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [std::thread](https://doc.rust-lang.org/std/thread/)
- [std::sync](https://doc.rust-lang.org/std/sync/)

### 推荐库

- [Rayon](https://docs.rs/rayon) - 数据并行
- [Crossbeam](https://docs.rs/crossbeam) - 并发工具
- [Flume](https://docs.rs/flume) - MPMC channel
- [Parking Lot](https://docs.rs/parking_lot) - 高性能锁

### 学习资源

- [Rust Atomics and Locks](https://marabos.nl/atomics/) - 深入原子操作
- [Crossbeam Epoch](https://aturon.github.io/blog/2015/08/27/epoch/) - 无锁内存回收

---

## 总结

Rust 并发编程的核心优势:

1. **编译时安全保证** - 防止数据竞争
2. **零成本抽象** - 高性能并发
3. **丰富的生态** - Rayon, Tokio, Crossbeam
4. **灵活的模型** - 共享状态、消息传递、Actor

通过本指南，你已经掌握了 Rust 并发编程的核心技术和最佳实践！
