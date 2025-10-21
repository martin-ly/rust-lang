# 并发与同步原语

> **核心库**: crossbeam, parking_lot, rayon, flume  
> **适用场景**: 多线程编程、无锁数据结构、并行计算、线程间通信

---

## 📋 目录

- [并发与同步原语](#并发与同步原语)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [并发模型](#并发模型)
    - [库选择指南](#库选择指南)
  - [⚡ crossbeam - 并发工具包](#-crossbeam---并发工具包)
    - [无锁数据结构](#无锁数据结构)
    - [作用域线程](#作用域线程)
    - [高性能通道](#高性能通道)
  - [🔒 parking\_lot - 高性能锁](#-parking_lot---高性能锁)
    - [核心特性](#核心特性)
    - [基础用法](#基础用法)
  - [📡 flume - 现代MPSC](#-flume---现代mpsc)
    - [核心特性](#核心特性-1)
    - [基础用法](#基础用法-1)
  - [💡 最佳实践](#-最佳实践)
    - [1. 选择合适的同步原语](#1-选择合适的同步原语)
    - [2. 避免死锁](#2-避免死锁)
    - [3. 性能优化](#3-性能优化)
  - [🔧 常见场景](#-常见场景)
    - [场景 1: 线程池](#场景-1-线程池)
    - [场景 2: 生产者-消费者](#场景-2-生产者-消费者)
    - [场景 3: 并行数据处理](#场景-3-并行数据处理)
  - [📚 延伸阅读](#-延伸阅读)

---

## 🎯 核心概念

### 并发模型

1. **共享内存**: Mutex, RwLock, Atomic
2. **消息传递**: Channel (MPSC, MPMC)
3. **无锁结构**: Lock-free queue, stack
4. **并行计算**: Work stealing, thread pool

### 库选择指南

| 特性 | std | crossbeam | parking_lot | 推荐 |
|------|-----|-----------|-------------|------|
| **性能** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | parking_lot |
| **功能** | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | crossbeam |
| **易用性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | std/parking_lot |
| **稳定性** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | 全部 |

---

## ⚡ crossbeam - 并发工具包

### 无锁数据结构

```rust
use crossbeam::queue::{ArrayQueue, SegQueue};
use std::thread;

fn main() {
    // 固定容量无锁队列
    let queue = ArrayQueue::new(10);
    
    // 生产者
    let producer = thread::spawn({
        let queue = queue.clone();
        move || {
            for i in 0..10 {
                queue.push(i).unwrap();
            }
        }
    });
    
    // 消费者
    let consumer = thread::spawn(move || {
        let mut sum = 0;
        for _ in 0..10 {
            if let Some(value) = queue.pop() {
                sum += value;
            }
        }
        sum
    });
    
    producer.join().unwrap();
    let result = consumer.join().unwrap();
    println!("Sum: {}", result);
    
    // 无限容量无锁队列
    let seg_queue = SegQueue::new();
    seg_queue.push(1);
    seg_queue.push(2);
    println!("{:?}", seg_queue.pop());
}
```

### 作用域线程

```rust
use crossbeam::thread;

fn main() {
    let mut data = vec![1, 2, 3, 4, 5];
    
    // 作用域线程可以借用外部数据
    thread::scope(|s| {
        // 分割数据并并行处理
        let chunks = data.chunks_mut(2);
        
        for chunk in chunks {
            s.spawn(move |_| {
                for item in chunk {
                    *item *= 2;
                }
            });
        }
    }).unwrap();
    
    println!("{:?}", data); // [2, 4, 6, 8, 10]
}
```

### 高性能通道

```rust
use crossbeam::channel::{bounded, unbounded};
use std::thread;
use std::time::Duration;

fn main() {
    // 有界通道 (带背压)
    let (tx, rx) = bounded(10);
    
    thread::spawn(move || {
        for i in 0..20 {
            tx.send(i).unwrap(); // 满时阻塞
            println!("Sent: {}", i);
        }
    });
    
    thread::sleep(Duration::from_millis(100));
    
    for value in rx {
        println!("Received: {}", value);
        thread::sleep(Duration::from_millis(10));
    }
    
    // 无界通道
    let (tx2, rx2) = unbounded();
    tx2.send(42).unwrap();
    println!("{}", rx2.recv().unwrap());
    
    // select! 多路复用
    let (tx1, rx1) = bounded(1);
    let (tx2, rx2) = bounded(1);
    
    tx1.send("A").unwrap();
    tx2.send("B").unwrap();
    
    crossbeam::select! {
        recv(rx1) -> msg => println!("rx1: {:?}", msg),
        recv(rx2) -> msg => println!("rx2: {:?}", msg),
    }
}
```

---

## 🔒 parking_lot - 高性能锁

### 核心特性

- ✅ 比标准库快 2-5倍
- ✅ 更小的内存占用
- ✅ 公平锁选项
- ✅ 死锁检测 (debug模式)

### 基础用法

```rust
use parking_lot::{Mutex, RwLock};
use std::thread;

fn main() {
    // Mutex - 比 std::sync::Mutex 更快
    let counter = Mutex::new(0);
    let mut handles = vec![];
    
    for _ in 0..10 {
        handles.push(thread::spawn({
            let counter = &counter;
            move || {
                for _ in 0..1000 {
                    *counter.lock() += 1;
                }
            }
        }));
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("Counter: {}", *counter.lock());
    
    // RwLock - 读写锁
    let data = RwLock::new(vec![1, 2, 3]);
    
    // 多个读者
    let reader1 = thread::spawn({
        let data = &data;
        move || {
            let guard = data.read();
            println!("Reader 1: {:?}", *guard);
        }
    });
    
    let reader2 = thread::spawn({
        let data = &data;
        move || {
            let guard = data.read();
            println!("Reader 2: {:?}", *guard);
        }
    });
    
    reader1.join().unwrap();
    reader2.join().unwrap();
    
    // 写者
    {
        let mut guard = data.write();
        guard.push(4);
    }
    
    println!("After write: {:?}", *data.read());
}
```

---

## 📡 flume - 现代MPSC

### 核心特性

- ✅ 比 std::mpsc 更快
- ✅ 异步支持
- ✅ 无界和有界通道
- ✅ 多生产者多消费者 (MPMC)

### 基础用法

```rust
use flume;
use std::thread;

fn main() {
    // 无界通道
    let (tx, rx) = flume::unbounded();
    
    // 多生产者
    for i in 0..5 {
        let tx = tx.clone();
        thread::spawn(move || {
            tx.send(i).unwrap();
        });
    }
    drop(tx); // 关闭通道
    
    // 消费者
    while let Ok(value) = rx.recv() {
        println!("Received: {}", value);
    }
    
    // 有界通道
    let (tx, rx) = flume::bounded(10);
    
    thread::spawn(move || {
        for i in 0..20 {
            tx.send(i).unwrap();
        }
    });
    
    for value in rx {
        println!("{}", value);
    }
}
```

---

## 💡 最佳实践

### 1. 选择合适的同步原语

```rust
use parking_lot::{Mutex, RwLock};
use std::sync::atomic::{AtomicU64, Ordering};

// ✅ 简单计数器：使用 Atomic
let counter = AtomicU64::new(0);
counter.fetch_add(1, Ordering::Relaxed);

// ✅ 读多写少：使用 RwLock
let cache = RwLock::new(std::collections::HashMap::new());
let value = cache.read().get(&key);

// ✅ 复杂状态：使用 Mutex
let state = Mutex::new(ComplexState::new());
state.lock().update();

// ✅ 线程间通信：使用 Channel
let (tx, rx) = flume::bounded(100);
```

### 2. 避免死锁

```rust
use parking_lot::Mutex;
use std::sync::Arc;

// ❌ 错误：可能死锁
fn deadlock_example() {
    let lock1 = Arc::new(Mutex::new(1));
    let lock2 = Arc::new(Mutex::new(2));
    
    // 线程1: lock1 -> lock2
    // 线程2: lock2 -> lock1
    // 可能死锁！
}

// ✅ 正确：固定锁顺序
fn correct_example() {
    let lock1 = Arc::new(Mutex::new(1));
    let lock2 = Arc::new(Mutex::new(2));
    
    // 总是按照 lock1 -> lock2 的顺序获取
    let guard1 = lock1.lock();
    let guard2 = lock2.lock();
    // ...
}

// ✅ 正确：使用 try_lock
fn try_lock_example(lock1: &Mutex<i32>, lock2: &Mutex<i32>) {
    if let Some(guard1) = lock1.try_lock() {
        if let Some(guard2) = lock2.try_lock() {
            // 成功获取两个锁
        }
    }
}
```

### 3. 性能优化

```rust
use parking_lot::{Mutex, RwLock};
use crossbeam::channel;

// ✅ 减少锁竞争
fn batch_processing(data: Vec<i32>, batch_size: usize) {
    let result = Mutex::new(Vec::new());
    
    rayon::scope(|s| {
        for chunk in data.chunks(batch_size) {
            s.spawn(|_| {
                let local_result: Vec<_> = chunk.iter()
                    .map(|&x| expensive_operation(x))
                    .collect();
                
                // 批量更新，减少锁竞争
                result.lock().extend(local_result);
            });
        }
    });
}

fn expensive_operation(x: i32) -> i32 {
    x * 2
}

// ✅ 使用读写锁
fn cache_example() {
    let cache = RwLock::new(std::collections::HashMap::new());
    
    // 多个读者不互斥
    let value = cache.read().get(&key);
    
    // 写入时独占
    if value.is_none() {
        cache.write().insert(key, compute_value());
    }
}
```

---

## 🔧 常见场景

### 场景 1: 线程池

```rust
use crossbeam::channel;
use std::thread;

struct ThreadPool {
    workers: Vec<thread::JoinHandle<()>>,
    sender: channel::Sender<Box<dyn FnOnce() + Send>>,
}

impl ThreadPool {
    fn new(size: usize) -> Self {
        let (sender, receiver) = channel::unbounded();
        let mut workers = Vec::with_capacity(size);
        
        for _ in 0..size {
            let receiver = receiver.clone();
            workers.push(thread::spawn(move || {
                while let Ok(job) = receiver.recv() {
                    job();
                }
            }));
        }
        
        Self { workers, sender }
    }
    
    fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        self.sender.send(Box::new(f)).unwrap();
    }
}
```

### 场景 2: 生产者-消费者

```rust
use flume;
use std::thread;
use std::time::Duration;

fn producer_consumer() {
    let (tx, rx) = flume::bounded(10);
    
    // 多个生产者
    for i in 0..3 {
        let tx = tx.clone();
        thread::spawn(move || {
            for j in 0..10 {
                tx.send((i, j)).unwrap();
                thread::sleep(Duration::from_millis(10));
            }
        });
    }
    drop(tx);
    
    // 多个消费者
    let mut handles = vec![];
    for _ in 0..2 {
        let rx = rx.clone();
        handles.push(thread::spawn(move || {
            while let Ok((producer, value)) = rx.recv() {
                println!("Producer {} -> {}", producer, value);
            }
        }));
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}
```

### 场景 3: 并行数据处理

```rust
use rayon::prelude::*;
use parking_lot::Mutex;

fn parallel_aggregate(data: Vec<i32>) -> (i32, i32, f64) {
    let sum = Mutex::new(0);
    let max = Mutex::new(i32::MIN);
    
    data.par_iter().for_each(|&x| {
        *sum.lock() += x;
        let mut max_guard = max.lock();
        if x > *max_guard {
            *max_guard = x;
        }
    });
    
    let sum_val = *sum.lock();
    let max_val = *max.lock();
    let avg = sum_val as f64 / data.len() as f64;
    
    (sum_val, max_val, avg)
}
```

---

## 📚 延伸阅读

- [crossbeam 官方文档](https://docs.rs/crossbeam/)
- [parking_lot 官方文档](https://docs.rs/parking_lot/)
- [Rust Concurrency Book](https://doc.rust-lang.org/book/ch16-00-concurrency.html)

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20

