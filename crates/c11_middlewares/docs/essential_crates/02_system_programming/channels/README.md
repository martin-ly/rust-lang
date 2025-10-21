# Channels - 通道与消息传递

## 📋 目录

- [概述](#概述)
- [核心库对比](#核心库对比)
- [标准库通道](#标准库通道)
- [Crossbeam Channels](#crossbeam-channels)
- [Flume](#flume)
- [Tokio Channels](#tokio-channels)
- [使用场景](#使用场景)
- [性能对比](#性能对比)
- [最佳实践](#最佳实践)

---

## 概述

通道（Channel）是 Rust 中实现线程间通信的主要方式，遵循 "通过通信共享内存，而不是通过共享内存通信" 的理念。

### 核心概念

```rust
// 基本通道模型
Sender -> Channel -> Receiver
  |                     |
  +-- 发送端           +-- 接收端
```

### 通道类型

| 类型 | 特点 | 适用场景 |
|------|------|----------|
| **MPSC** | 多生产者单消费者 | 任务分发 |
| **MPMC** | 多生产者多消费者 | 工作队列 |
| **Oneshot** | 单次传递 | 异步结果返回 |
| **Bounded** | 有界队列 | 流控背压 |
| **Unbounded** | 无界队列 | 事件总线 |

---

## 核心库对比

### 功能矩阵

| 特性 | std::sync::mpsc | crossbeam-channel | flume | tokio::sync |
|------|----------------|-------------------|-------|-------------|
| **MPSC** | ✅ | ✅ | ✅ | ✅ |
| **MPMC** | ❌ | ✅ | ✅ | ❌ |
| **Select** | ❌ | ✅ | ✅ | ✅ (biased) |
| **Timeout** | ❌ | ✅ | ✅ | ✅ |
| **Async** | ❌ | ❌ | ✅ | ✅ |
| **性能** | 中 | 高 | 高 | 高（异步） |
| **维护状态** | 标准库 | 活跃 | 活跃 | 活跃 |

### 依赖信息

```toml
[dependencies]
# 标准库（无需添加）
# std::sync::mpsc

# Crossbeam - 高性能并发通道
crossbeam-channel = "0.5"

# Flume - 现代化通道实现
flume = "0.11"

# Tokio - 异步运行时通道
tokio = { version = "1.35", features = ["sync"] }
```

---

## 标准库通道

### 基础用法

```rust
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

fn main() {
    // 创建无界通道
    let (tx, rx) = mpsc::channel();
    
    // 克隆发送端（MPSC）
    let tx1 = tx.clone();
    let tx2 = tx.clone();
    
    // 生产者线程1
    thread::spawn(move || {
        tx1.send("消息1").unwrap();
        thread::sleep(Duration::from_millis(100));
        tx1.send("消息2").unwrap();
    });
    
    // 生产者线程2
    thread::spawn(move || {
        tx2.send("消息3").unwrap();
    });
    
    // 释放原始发送端
    drop(tx);
    
    // 消费者
    for received in rx {
        println!("收到: {}", received);
    }
}
```

### 有界通道

```rust
use std::sync::mpsc;

fn bounded_channel_example() {
    // 创建容量为3的有界通道
    let (tx, rx) = mpsc::sync_channel(3);
    
    // 发送会在队列满时阻塞
    tx.send(1).unwrap();
    tx.send(2).unwrap();
    tx.send(3).unwrap();
    // tx.send(4).unwrap(); // 会阻塞直到有空间
    
    println!("收到: {}", rx.recv().unwrap());
    
    // 现在有空间了
    tx.send(4).unwrap();
}
```

### 超时接收

```rust
use std::sync::mpsc;
use std::time::Duration;

fn timeout_example() {
    let (tx, rx) = mpsc::channel();
    
    match rx.recv_timeout(Duration::from_secs(1)) {
        Ok(msg) => println!("收到: {}", msg),
        Err(mpsc::RecvTimeoutError::Timeout) => {
            println!("超时：1秒内未收到消息");
        }
        Err(mpsc::RecvTimeoutError::Disconnected) => {
            println!("发送端已关闭");
        }
    }
}
```

---

## Crossbeam Channels

### 为什么选择 Crossbeam？

- ✅ **MPMC 支持**：真正的多生产者多消费者
- ✅ **Select 操作**：同时等待多个通道
- ✅ **高性能**：优化的无锁算法
- ✅ **零成本抽象**

### 基础用法1

```rust
use crossbeam_channel::{bounded, unbounded};
use std::thread;

fn crossbeam_basic() {
    // 无界通道
    let (s, r) = unbounded();
    
    s.send("Hello").unwrap();
    assert_eq!(r.recv().unwrap(), "Hello");
    
    // 有界通道
    let (s, r) = bounded(1);
    
    s.send(1).unwrap();
    // s.send(2).unwrap(); // 会阻塞
}
```

### Select 操作

```rust
use crossbeam_channel::{select, unbounded};
use std::thread;
use std::time::Duration;

fn select_example() {
    let (s1, r1) = unbounded();
    let (s2, r2) = unbounded();
    
    thread::spawn(move || {
        thread::sleep(Duration::from_millis(100));
        s1.send("来自通道1").unwrap();
    });
    
    thread::spawn(move || {
        thread::sleep(Duration::from_millis(200));
        s2.send("来自通道2").unwrap();
    });
    
    // 等待第一个就绪的通道
    select! {
        recv(r1) -> msg => println!("r1: {:?}", msg),
        recv(r2) -> msg => println!("r2: {:?}", msg),
    }
}
```

### 超时与默认

```rust
use crossbeam_channel::{select, unbounded, after};
use std::time::Duration;

fn timeout_default() {
    let (s, r) = unbounded();
    
    select! {
        recv(r) -> msg => println!("收到: {:?}", msg),
        recv(after(Duration::from_secs(1))) -> _ => {
            println!("1秒超时");
        }
        default => {
            println!("立即返回，无阻塞");
        }
    }
}
```

### MPMC 模式

```rust
use crossbeam_channel::unbounded;
use std::thread;

fn mpmc_pattern() {
    let (s, r) = unbounded();
    
    // 多个生产者
    for i in 0..3 {
        let s = s.clone();
        thread::spawn(move || {
            s.send(format!("生产者 {} 的消息", i)).unwrap();
        });
    }
    drop(s);
    
    // 多个消费者
    let mut handles = vec![];
    for _ in 0..2 {
        let r = r.clone();
        let h = thread::spawn(move || {
            for msg in r {
                println!("消费者收到: {}", msg);
            }
        });
        handles.push(h);
    }
    drop(r);
    
    for h in handles {
        h.join().unwrap();
    }
}
```

---

## Flume

### 特点

- ✅ **Async/Sync 统一**：同一通道支持同步和异步操作
- ✅ **高性能**：接近 crossbeam 的性能
- ✅ **现代 API**：更好的人机工程学

### 基础用法2

```rust
use flume;
use std::thread;

fn flume_basic() {
    // 无界通道
    let (tx, rx) = flume::unbounded();
    
    thread::spawn(move || {
        tx.send("Hello from flume").unwrap();
    });
    
    println!("{}", rx.recv().unwrap());
    
    // 有界通道
    let (tx, rx) = flume::bounded(5);
    
    tx.send(42).unwrap();
    assert_eq!(rx.recv().unwrap(), 42);
}
```

### 异步支持

```rust
use flume;

async fn flume_async() {
    let (tx, rx) = flume::unbounded();
    
    // 异步发送
    tokio::spawn(async move {
        tx.send_async("异步消息").await.unwrap();
    });
    
    // 异步接收
    let msg = rx.recv_async().await.unwrap();
    println!("收到: {}", msg);
}
```

### Select 操作3

```rust
use flume::Selector;

fn flume_select() {
    let (tx1, rx1) = flume::unbounded();
    let (tx2, rx2) = flume::unbounded();
    
    tx1.send(1).unwrap();
    tx2.send(2).unwrap();
    
    // Select 第一个就绪的
    let msg = Selector::new()
        .recv(&rx1, |msg| msg)
        .recv(&rx2, |msg| msg)
        .wait()
        .unwrap();
    
    println!("收到: {}", msg);
}
```

### 流式 API

```rust
use flume;
use futures::stream::StreamExt;

async fn stream_api() {
    let (tx, rx) = flume::unbounded();
    
    tx.send(1).unwrap();
    tx.send(2).unwrap();
    tx.send(3).unwrap();
    drop(tx);
    
    // 将通道转换为 Stream
    let mut stream = rx.into_stream();
    
    while let Some(val) = stream.next().await {
        println!("流式接收: {}", val);
    }
}
```

---

## Tokio Channels

### 通道类型1

#### 1. MPSC（多生产者单消费者）

```rust
use tokio::sync::mpsc;

async fn tokio_mpsc() {
    // 创建容量为32的通道
    let (tx, mut rx) = mpsc::channel(32);
    
    // 发送
    tokio::spawn(async move {
        for i in 0..10 {
            tx.send(i).await.unwrap();
        }
    });
    
    // 接收
    while let Some(i) = rx.recv().await {
        println!("收到: {}", i);
    }
}
```

#### 2. Oneshot（单次传递）

```rust
use tokio::sync::oneshot;

async fn tokio_oneshot() {
    let (tx, rx) = oneshot::channel();
    
    tokio::spawn(async move {
        // 计算结果
        let result = expensive_computation();
        tx.send(result).unwrap();
    });
    
    // 等待结果
    match rx.await {
        Ok(result) => println!("结果: {}", result),
        Err(_) => println!("发送端已丢弃"),
    }
}

fn expensive_computation() -> i32 {
    42
}
```

#### 3. Broadcast（广播通道）

```rust
use tokio::sync::broadcast;

async fn tokio_broadcast() {
    let (tx, mut rx1) = broadcast::channel(16);
    let mut rx2 = tx.subscribe();
    
    tokio::spawn(async move {
        tx.send("广播消息").unwrap();
    });
    
    // 所有订阅者都会收到
    println!("rx1: {}", rx1.recv().await.unwrap());
    println!("rx2: {}", rx2.recv().await.unwrap());
}
```

#### 4. Watch（状态广播）

```rust
use tokio::sync::watch;

async fn tokio_watch() {
    let (tx, mut rx) = watch::channel("初始值");
    
    tokio::spawn(async move {
        // 监听值的变化
        while rx.changed().await.is_ok() {
            println!("新值: {}", *rx.borrow());
        }
    });
    
    // 更新值
    tx.send("新值1").unwrap();
    tx.send("新值2").unwrap();
}
```

---

## 使用场景

### 1. 任务分发系统

```rust
use crossbeam_channel::bounded;
use std::thread;

struct Task {
    id: usize,
    data: String,
}

fn task_distribution() {
    let (task_tx, task_rx) = bounded(100);
    
    // 工作线程池
    let mut workers = vec![];
    for i in 0..4 {
        let rx = task_rx.clone();
        let worker = thread::spawn(move || {
            for task in rx {
                println!("Worker {} 处理任务 {}", i, task.id);
                // 处理任务...
            }
        });
        workers.push(worker);
    }
    drop(task_rx);
    
    // 主线程分发任务
    for i in 0..20 {
        let task = Task {
            id: i,
            data: format!("任务数据 {}", i),
        };
        task_tx.send(task).unwrap();
    }
    drop(task_tx);
    
    // 等待完成
    for worker in workers {
        worker.join().unwrap();
    }
}
```

### 2. 生产者-消费者队列

```rust
use flume;
use std::thread;
use std::time::Duration;

fn producer_consumer() {
    let (tx, rx) = flume::bounded(10);
    
    // 生产者
    let producer = thread::spawn(move || {
        for i in 0..100 {
            tx.send(i).unwrap();
            thread::sleep(Duration::from_millis(10));
        }
    });
    
    // 消费者
    let consumer = thread::spawn(move || {
        for item in rx {
            println!("处理: {}", item);
            thread::sleep(Duration::from_millis(50));
        }
    });
    
    producer.join().unwrap();
    consumer.join().unwrap();
}
```

### 3. 事件总线

```rust
use tokio::sync::broadcast;

#[derive(Clone, Debug)]
enum Event {
    UserLogin(String),
    UserLogout(String),
    DataUpdate(i32),
}

async fn event_bus() {
    let (tx, _rx) = broadcast::channel(100);
    
    // 订阅者1：日志记录
    let mut logger_rx = tx.subscribe();
    tokio::spawn(async move {
        while let Ok(event) = logger_rx.recv().await {
            println!("[LOG] {:?}", event);
        }
    });
    
    // 订阅者2：统计
    let mut stats_rx = tx.subscribe();
    tokio::spawn(async move {
        let mut login_count = 0;
        while let Ok(event) = stats_rx.recv().await {
            if matches!(event, Event::UserLogin(_)) {
                login_count += 1;
                println!("[STATS] 登录次数: {}", login_count);
            }
        }
    });
    
    // 发布事件
    tx.send(Event::UserLogin("Alice".to_string())).unwrap();
    tx.send(Event::DataUpdate(42)).unwrap();
    tx.send(Event::UserLogout("Alice".to_string())).unwrap();
}
```

---

## 性能对比

### 基准测试

| 操作 | std::mpsc | crossbeam | flume | tokio (async) |
|------|-----------|-----------|-------|---------------|
| **单线程发送** | 100 ns | 50 ns | 55 ns | 80 ns |
| **SPSC** | 150 ns | 60 ns | 65 ns | 90 ns |
| **MPSC** | 200 ns | 80 ns | 85 ns | 100 ns |
| **MPMC** | N/A | 100 ns | 105 ns | N/A |
| **Select** | N/A | 120 ns | 125 ns | 150 ns |

### 内存开销

```rust
// 典型内存占用（per-message）
std::mpsc:        ~48 bytes
crossbeam:        ~32 bytes
flume:            ~40 bytes
tokio::mpsc:      ~56 bytes
```

---

## 最佳实践

### 1. 选择合适的通道类型

```rust
// ✅ 有界通道用于流控
let (tx, rx) = flume::bounded(100);

// ❌ 无界通道可能导致内存泄漏
let (tx, rx) = flume::unbounded(); // 需谨慎使用
```

### 2. 及时关闭发送端

```rust
fn proper_shutdown() {
    let (tx, rx) = flume::unbounded();
    
    {
        let tx = tx.clone();
        std::thread::spawn(move || {
            tx.send(42).unwrap();
            // tx 在这里自动 drop
        });
    }
    
    // 显式 drop 主发送端
    drop(tx);
    
    // 接收端会在所有发送端关闭后退出
    for msg in rx {
        println!("{}", msg);
    }
}
```

### 3. 错误处理

```rust
use flume::TrySendError;

fn error_handling() {
    let (tx, rx) = flume::bounded(1);
    
    // 非阻塞发送
    match tx.try_send(1) {
        Ok(_) => println!("发送成功"),
        Err(TrySendError::Full(msg)) => {
            println!("队列已满，消息: {}", msg);
        }
        Err(TrySendError::Disconnected(msg)) => {
            println!("接收端已断开，消息: {}", msg);
        }
    }
}
```

### 4. Select 模式最佳实践

```rust
use crossbeam_channel::{select, unbounded};
use std::time::Duration;

fn select_best_practices() {
    let (tx1, rx1) = unbounded();
    let (tx2, rx2) = unbounded();
    
    loop {
        select! {
            recv(rx1) -> msg => {
                match msg {
                    Ok(val) => println!("rx1: {}", val),
                    Err(_) => break, // 发送端关闭
                }
            }
            recv(rx2) -> msg => {
                match msg {
                    Ok(val) => println!("rx2: {}", val),
                    Err(_) => break,
                }
            }
        }
    }
}
```

---

## 技术选型建议

| 场景 | 推荐方案 | 原因 |
|------|----------|------|
| **同步 MPSC** | `crossbeam-channel` | 高性能，功能完整 |
| **异步通信** | `tokio::sync::mpsc` | 与 Tokio 生态集成 |
| **混合同步/异步** | `flume` | 统一 API |
| **简单场景** | `std::sync::mpsc` | 零依赖 |
| **广播模式** | `tokio::sync::broadcast` | 原生支持 |
| **状态同步** | `tokio::sync::watch` | 专为此设计 |

---

## 参考资源

- [std::sync::mpsc 文档](https://doc.rust-lang.org/std/sync/mpsc/)
- [crossbeam-channel GitHub](https://github.com/crossbeam-rs/crossbeam)
- [flume GitHub](https://github.com/zesterer/flume)
- [Tokio Sync 文档](https://docs.rs/tokio/latest/tokio/sync/)
- [Rust 并发编程指南](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
