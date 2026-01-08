# 线程与并发使用指南

**模块**: C05 Threads
**创建日期**: 2025-12-11
**最后更新**: 2025-12-11
**Rust 版本**: 1.92.0
**Edition**: 2024

---

## 📋 目录

- [线程与并发使用指南](#线程与并发使用指南)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🚀 快速开始](#-快速开始)
    - [基本线程创建](#基本线程创建)
    - [作用域线程（Rust 1.89+）](#作用域线程rust-189)
  - [📊 核心功能](#-核心功能)
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
  - [⚡ 性能优化](#-性能优化)
    - [1. 减少锁竞争](#1-减少锁竞争)
    - [2. 使用无锁数据结构](#2-使用无锁数据结构)
    - [3. 工作窃取](#3-工作窃取)
  - [🐛 常见问题](#-常见问题)
    - [死锁](#死锁)
    - [数据竞争](#数据竞争)
  - [📚 相关文档](#-相关文档)

---

## 📋 概述

本指南介绍如何使用 C05 线程与并发模块的功能，包括线程管理、并发控制、同步原语、无锁数据结构等。

---

## 🚀 快速开始

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

## 📊 核心功能

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

## ⚡ 性能优化

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

## 🐛 常见问题

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

## 📚 相关文档

- [完整文档](../crates/c05_threads/README.md)
- [线程管理指南](../crates/c05_threads/docs/tier_02_guides/01_线程管理指南.md)
- [并发控制指南](../crates/c05_threads/docs/tier_02_guides/02_并发控制指南.md)
- [无锁数据结构](../crates/c05_threads/docs/tier_03_references/03_无锁数据结构参考.md)

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 完整实现
**最后更新**: 2025-12-11
