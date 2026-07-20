# 并发模式基础（Concurrent Patterns Basics）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [并发模式基础（Concurrent Patterns Basics）](#并发模式基础concurrent-patterns-basics)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [生产者-消费者模式](#生产者-消费者模式)
    - [基本实现](#基本实现)
    - [多生产者多消费者](#多生产者多消费者)
  - [工作池模式](#工作池模式)
    - [线程池实现](#线程池实现)
  - [读写锁模式](#读写锁模式)
    - [读写锁使用](#读写锁使用)
  - [屏障模式](#屏障模式)
    - [同步屏障](#同步屏障)
  - [实践示例](#实践示例)
    - [示例 1：任务调度器](#示例-1任务调度器)
    - [示例 2：并发计数器](#示例-2并发计数器)
  - [最佳实践](#最佳实践)
    - [1. 避免死锁](#1-避免死锁)
    - [2. 使用通道而非共享状态](#2-使用通道而非共享状态)
  - [参考资料](#参考资料)

---

## 概述

并发模式是处理并发编程中常见问题的解决方案。Rust 的类型系统提供了强大的并发安全保障，使得实现这些模式更加安全和高效。

## 生产者-消费者模式

### 基本实现

```rust
use tokio::sync::mpsc;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() {
    let (tx, mut rx) = mpsc::channel(10);

    // 生产者
    let producer = tokio::spawn(async move {
        for i in 1..=10 {
            tx.send(i).await.unwrap();
            println!("生产: {}", i);
            sleep(Duration::from_millis(100)).await;
        }
    });

    // 消费者
    let consumer = tokio::spawn(async move {
        while let Some(item) = rx.recv().await {
            println!("消费: {}", item);
            sleep(Duration::from_millis(150)).await;
        }
    });

    producer.await.unwrap();
    consumer.await.unwrap();
}
```

### 多生产者多消费者

```rust
use tokio::sync::mpsc;

#[tokio::main]
async fn main() {
    let (tx, mut rx) = mpsc::channel(100);

    // 多个生产者
    for i in 0..3 {
        let tx = tx.clone();
        tokio::spawn(async move {
            for j in 1..=5 {
                tx.send(format!("生产者 {}: 项目 {}", i, j)).await.unwrap();
            }
        });
    }
    drop(tx);  // 关闭发送端

    // 多个消费者
    let mut handles = vec![];
    for i in 0..2 {
        let mut rx = rx.resubscribe();
        handles.push(tokio::spawn(async move {
            while let Some(item) = rx.recv().await {
                println!("消费者 {}: {}", i, item);
            }
        }));
    }

    for handle in handles {
        handle.await.unwrap();
    }
}
```

## 工作池模式

### 线程池实现

```rust
use std::sync::Arc;
use tokio::sync::{mpsc, Semaphore};

pub struct ThreadPool {
    workers: Vec<tokio::task::JoinHandle<()>>,
    sender: Option<mpsc::Sender<Task>>,
}

type Task = Box<dyn FnOnce() + Send + 'static>;

impl ThreadPool {
    pub fn new(size: usize) -> Self {
        let (sender, mut receiver) = mpsc::channel::<Task>(100);
        let semaphore = Arc::new(Semaphore::new(size));

        let mut workers = Vec::with_capacity(size);
        for _ in 0..size {
            let mut receiver = receiver.resubscribe();
            let semaphore = Arc::clone(&semaphore);

            let worker = tokio::spawn(async move {
                while let Some(task) = receiver.recv().await {
                    let _permit = semaphore.acquire().await.unwrap();
                    task();
                }
            });
            workers.push(worker);
        }

        ThreadPool {
            workers,
            sender: Some(sender),
        }
    }

    pub async fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        if let Some(sender) = &self.sender {
            sender.send(Box::new(f)).await.unwrap();
        }
    }
}
```

## 读写锁模式

### 读写锁使用

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

#[tokio::main]
async fn main() {
    let data = Arc::new(RwLock::new(0));
    let mut handles = vec![];

    // 多个读操作
    for i in 0..5 {
        let data = Arc::clone(&data);
        let handle = tokio::spawn(async move {
            let value = data.read().await;
            println!("读操作 {}: {}", i, *value);
        });
        handles.push(handle);
    }

    // 写操作
    let data = Arc::clone(&data);
    let write_handle = tokio::spawn(async move {
        let mut value = data.write().await;
        *value += 1;
        println!("写操作: 更新为 {}", *value);
    });
    handles.push(write_handle);

    for handle in handles {
        handle.await.unwrap();
    }
}
```

## 屏障模式

### 同步屏障

```rust
use tokio::sync::Barrier;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];

    for i in 0..3 {
        let barrier = Arc::clone(&barrier);
        let handle = tokio::spawn(async move {
            println!("任务 {} 到达屏障", i);
            barrier.wait().await;
            println!("任务 {} 通过屏障", i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await.unwrap();
    }
}
```

## 实践示例

### 示例 1：任务调度器

```rust
use tokio::sync::mpsc;
use std::time::Duration;

#[derive(Debug, Clone)]
pub struct Task {
    pub id: u32,
    pub priority: u8,
    pub data: String,
}

pub struct TaskScheduler {
    sender: mpsc::Sender<Task>,
}

impl TaskScheduler {
    pub fn new() -> (Self, mpsc::Receiver<Task>) {
        let (tx, rx) = mpsc::channel(1000);
        (TaskScheduler { sender: tx }, rx)
    }

    pub async fn schedule(&self, task: Task) -> Result<(), mpsc::error::SendError<Task>> {
        self.sender.send(task).await
    }
}

#[tokio::main]
async fn main() {
    let (scheduler, mut receiver) = TaskScheduler::new();

    // 任务处理器
    tokio::spawn(async move {
        while let Some(task) = receiver.recv().await {
            println!("处理任务: {:?}", task);
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    });

    // 调度任务
    for i in 1..=5 {
        scheduler.schedule(Task {
            id: i,
            priority: (i % 3) as u8,
            data: format!("任务数据 {}", i),
        }).await.unwrap();
    }

    tokio::time::sleep(Duration::from_secs(1)).await;
}
```

### 示例 2：并发计数器

```rust
use std::sync::Arc;
use tokio::sync::Mutex;

pub struct ConcurrentCounter {
    value: Arc<Mutex<u32>>,
}

impl ConcurrentCounter {
    pub fn new() -> Self {
        ConcurrentCounter {
            value: Arc::new(Mutex::new(0)),
        }
    }

    pub async fn increment(&self) {
        let mut value = self.value.lock().await;
        *value += 1;
    }

    pub async fn get(&self) -> u32 {
        *self.value.lock().await
    }
}

#[tokio::main]
async fn main() {
    let counter = Arc::new(ConcurrentCounter::new());
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = tokio::spawn(async move {
            for _ in 0..100 {
                counter.increment().await;
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await.unwrap();
    }

    println!("最终计数: {}", counter.get().await);
}
```

## 最佳实践

### 1. 避免死锁

```rust
// ❌ 错误：可能导致死锁
async fn bad_lock_order(a: &Mutex<i32>, b: &Mutex<i32>) {
    let _lock1 = a.lock().await;
    let _lock2 = b.lock().await;
}

// ✅ 正确：一致的锁顺序
async fn good_lock_order(a: &Mutex<i32>, b: &Mutex<i32>) {
    // 总是按相同顺序获取锁
    let _lock1 = a.lock().await;
    let _lock2 = b.lock().await;
}
```

### 2. 使用通道而非共享状态

```rust
// ✅ 推荐：使用通道
use tokio::sync::mpsc;

async fn channel_based() {
    let (tx, mut rx) = mpsc::channel(100);
    // 通过通道通信
}

// ❌ 不推荐：过度使用共享状态
use tokio::sync::Mutex;

async fn shared_state_based() {
    let data = Arc::new(Mutex::new(0));
    // 需要锁保护
}
```

## 参考资料

- [并发模式索引](./00_index.md)
- [设计模式索引](../00_index.md)
- [并发编程范式](../../02_programming_paradigms/05_concurrent/00_index.md)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回设计模式: [`../00_index.md`](../00_index.md)
