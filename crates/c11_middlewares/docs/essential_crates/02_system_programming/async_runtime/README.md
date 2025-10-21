# 异步运行时

> **核心库**: tokio, async-std, smol, futures  
> **适用场景**: 异步编程、并发I/O、网络服务、高性能应用

---

## 📋 目录

- [异步运行时](#异步运行时)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [异步编程基础](#异步编程基础)
    - [运行时对比](#运行时对比)
  - [🚀 Tokio - 工业标准](#-tokio---工业标准)
    - [核心特性](#核心特性)
    - [基础用法](#基础用法)
      - [异步任务](#异步任务)
      - [并发执行](#并发执行)
      - [超时与取消](#超时与取消)
      - [通道通信](#通道通信)
    - [高级特性](#高级特性)
      - [任务调度](#任务调度)
      - [异步互斥](#异步互斥)
      - [任务本地存储](#任务本地存储)
  - [🌊 async-std - 简洁优雅](#-async-std---简洁优雅)
    - [核心特性1](#核心特性1)
    - [基础用法1](#基础用法1)
  - [🪶 smol - 轻量高效](#-smol---轻量高效)
    - [核心特性2](#核心特性2)
    - [基础用法2](#基础用法2)
  - [🔧 futures - 异步工具](#-futures---异步工具)
    - [核心工具](#核心工具)
  - [💡 最佳实践](#-最佳实践)
    - [1. 选择运行时](#1-选择运行时)
    - [2. 错误处理](#2-错误处理)
    - [3. 性能优化](#3-性能优化)
    - [4. 避免阻塞](#4-避免阻塞)
  - [🔧 常见场景](#-常见场景)
    - [场景 1: HTTP 服务器](#场景-1-http-服务器)
    - [场景 2: 并发请求](#场景-2-并发请求)
    - [场景 3: 流式处理](#场景-3-流式处理)
  - [📚 延伸阅读](#-延伸阅读)

---

## 🎯 核心概念

### 异步编程基础

```rust
// 异步函数定义
async fn fetch_data(id: u32) -> Result<String, Error> {
    // 异步操作
    Ok(format!("Data {}", id))
}

// 调用异步函数
#[tokio::main]
async fn main() {
    let result = fetch_data(1).await;
    println!("{:?}", result);
}
```

### 运行时对比

| 特性 | Tokio | async-std | smol | 推荐场景 |
|------|-------|-----------|------|----------|
| **性能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Tokio |
| **生态** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | Tokio |
| **易用性** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | async-std |
| **体积** | ⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | smol |
| **功能** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | Tokio |

---

## 🚀 Tokio - 工业标准

### 核心特性

- ✅ **高性能**: 工作窃取调度器
- ✅ **功能全面**: 计时器、I/O、同步原语
- ✅ **成熟生态**: axum, tonic, hyper
- ✅ **生产就绪**: 大规模应用验证

### 基础用法

#### 异步任务

```rust
use tokio;

#[tokio::main]
async fn main() {
    println!("Hello");
    
    // 异步睡眠
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    
    println!("World");
}
```

#### 并发执行

```rust
use tokio;

async fn task1() -> String {
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    "Task 1".to_string()
}

async fn task2() -> String {
    tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
    "Task 2".to_string()
}

#[tokio::main]
async fn main() {
    // 并发执行两个任务
    let (result1, result2) = tokio::join!(task1(), task2());
    println!("{}, {}", result1, result2);
    
    // select! 宏 - 等待第一个完成
    tokio::select! {
        r1 = task1() => println!("Task 1 finished first: {}", r1),
        r2 = task2() => println!("Task 2 finished first: {}", r2),
    }
}
```

#### 超时与取消

```rust
use tokio::time::{timeout, Duration};

async fn long_operation() -> Result<String, &'static str> {
    tokio::time::sleep(Duration::from_secs(5)).await;
    Ok("Done".to_string())
}

#[tokio::main]
async fn main() {
    // 设置超时
    match timeout(Duration::from_secs(2), long_operation()).await {
        Ok(Ok(result)) => println!("Success: {}", result),
        Ok(Err(e)) => println!("Error: {}", e),
        Err(_) => println!("Timeout!"),
    }
}
```

#### 通道通信

```rust
use tokio::sync::mpsc;

#[tokio::main]
async fn main() {
    let (tx, mut rx) = mpsc::channel(32);
    
    // 生产者任务
    tokio::spawn(async move {
        for i in 0..10 {
            tx.send(i).await.unwrap();
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        }
    });
    
    // 消费者
    while let Some(value) = rx.recv().await {
        println!("Received: {}", value);
    }
}
```

### 高级特性

#### 任务调度

```rust
use tokio::task;

#[tokio::main]
async fn main() {
    // spawn: 在后台运行任务
    let handle = task::spawn(async {
        // 长时间运行的任务
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        "Result"
    });
    
    // 等待任务完成
    let result = handle.await.unwrap();
    println!("{}", result);
    
    // spawn_blocking: CPU密集型任务
    let blocking_result = task::spawn_blocking(|| {
        // 阻塞操作
        std::thread::sleep(std::time::Duration::from_secs(1));
        42
    }).await.unwrap();
    
    println!("Blocking result: {}", blocking_result);
}
```

#### 异步互斥

```rust
use tokio::sync::Mutex;
use std::sync::Arc;

#[tokio::main]
async fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = tokio::spawn(async move {
            let mut num = counter.lock().await;
            *num += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.await.unwrap();
    }
    
    println!("Counter: {}", *counter.lock().await);
}
```

#### 任务本地存储

```rust
use tokio::task_local;

task_local! {
    static REQUEST_ID: u64;
}

async fn process_request() {
    REQUEST_ID.with(|id| {
        println!("Processing request: {}", id);
    });
}

#[tokio::main]
async fn main() {
    REQUEST_ID.scope(123, process_request()).await;
}
```

---

## 🌊 async-std - 简洁优雅

### 核心特性1

- ✅ **API 设计**: 类似标准库
- ✅ **易于学习**: 平缓学习曲线
- ✅ **跨平台**: WASM 支持良好

### 基础用法1

```rust
use async_std::task;
use async_std::prelude::*;

#[async_std::main]
async fn main() {
    // 并发任务
    let task1 = task::spawn(async {
        task::sleep(std::time::Duration::from_secs(1)).await;
        "Task 1"
    });
    
    let task2 = task::spawn(async {
        task::sleep(std::time::Duration::from_secs(1)).await;
        "Task 2"
    });
    
    let (r1, r2) = futures::join!(task1, task2);
    println!("{}, {}", r1, r2);
}
```

---

## 🪶 smol - 轻量高效

### 核心特性2

- ✅ **极小体积**: 最小依赖
- ✅ **高性能**: 优化的调度器
- ✅ **灵活**: 可定制性强

### 基础用法2

```rust
use smol;

fn main() {
    smol::block_on(async {
        println!("Hello from smol!");
        
        // 并发执行
        let task1 = smol::spawn(async {
            smol::Timer::after(std::time::Duration::from_secs(1)).await;
            "Task 1"
        });
        
        let result = task1.await;
        println!("{}", result);
    });
}
```

---

## 🔧 futures - 异步工具

### 核心工具

```rust
use futures::{
    future::{join_all, select_all},
    stream::{self, StreamExt},
};

#[tokio::main]
async fn main() {
    // join_all: 等待所有任务完成
    let tasks = (0..5).map(|i| async move {
        tokio::time::sleep(tokio::time::Duration::from_millis(i * 100)).await;
        i
    });
    let results = join_all(tasks).await;
    println!("{:?}", results);
    
    // Stream 处理
    let mut stream = stream::iter(vec![1, 2, 3, 4, 5]);
    while let Some(value) = stream.next().await {
        println!("Stream value: {}", value);
    }
}
```

---

## 💡 最佳实践

### 1. 选择运行时

```rust
// ✅ 推荐 Tokio (生产环境)
use tokio;

#[tokio::main]
async fn main() {
    // 高性能、完整功能、成熟生态
}

// ✅ async-std (快速原型)
use async_std;

#[async_std::main]
async fn main() {
    // 简单易用、快速开发
}

// ✅ smol (嵌入式/最小化)
use smol;

fn main() {
    smol::block_on(async {
        // 最小体积、高性能
    });
}
```

### 2. 错误处理

```rust
use tokio;
use thiserror::Error;

#[derive(Error, Debug)]
enum AppError {
    #[error("Network error: {0}")]
    Network(String),
    
    #[error("Timeout")]
    Timeout,
}

async fn fetch_with_retry(url: &str) -> Result<String, AppError> {
    for attempt in 1..=3 {
        match tokio::time::timeout(
            tokio::time::Duration::from_secs(5),
            fetch_data(url)
        ).await {
            Ok(Ok(data)) => return Ok(data),
            Ok(Err(e)) => {
                if attempt == 3 {
                    return Err(AppError::Network(e.to_string()));
                }
            }
            Err(_) => return Err(AppError::Timeout),
        }
        
        tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    }
    
    unreachable!()
}

async fn fetch_data(url: &str) -> Result<String, Box<dyn std::error::Error>> {
    Ok(format!("Data from {}", url))
}
```

### 3. 性能优化

```rust
use tokio::task;

// ✅ 使用 spawn_blocking 处理 CPU 密集型任务
async fn process_image(data: Vec<u8>) -> Vec<u8> {
    task::spawn_blocking(move || {
        // CPU 密集型图像处理
        data
    }).await.unwrap()
}

// ✅ 批量处理
use futures::stream::{self, StreamExt};

async fn batch_process(items: Vec<u32>) {
    stream::iter(items)
        .map(|item| async move {
            // 处理单个项
            item * 2
        })
        .buffer_unordered(10) // 并发度 10
        .collect::<Vec<_>>()
        .await;
}
```

### 4. 避免阻塞

```rust
use tokio::task;

// ❌ 错误：在异步上下文中阻塞
async fn bad_example() {
    std::thread::sleep(std::time::Duration::from_secs(1)); // 阻塞整个线程！
}

// ✅ 正确：使用异步睡眠
async fn good_example() {
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
}

// ✅ 正确：阻塞操作使用 spawn_blocking
async fn handle_blocking() {
    task::spawn_blocking(|| {
        std::thread::sleep(std::time::Duration::from_secs(1));
    }).await.unwrap();
}
```

---

## 🔧 常见场景

### 场景 1: HTTP 服务器

```rust
use tokio;
use std::sync::Arc;
use tokio::sync::Mutex;

struct AppState {
    counter: Mutex<u64>,
}

async fn handle_request(state: Arc<AppState>) -> String {
    let mut counter = state.counter.lock().await;
    *counter += 1;
    format!("Request #{}", counter)
}

#[tokio::main]
async fn main() {
    let state = Arc::new(AppState {
        counter: Mutex::new(0),
    });
    
    // 模拟处理多个请求
    let mut handles = vec![];
    for _ in 0..10 {
        let state = Arc::clone(&state);
        handles.push(tokio::spawn(async move {
            handle_request(state).await
        }));
    }
    
    for handle in handles {
        println!("{}", handle.await.unwrap());
    }
}
```

### 场景 2: 并发请求

```rust
use tokio;

async fn fetch_url(url: &str) -> Result<String, Box<dyn std::error::Error>> {
    // 模拟 HTTP 请求
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    Ok(format!("Data from {}", url))
}

#[tokio::main]
async fn main() {
    let urls = vec![
        "https://api1.example.com",
        "https://api2.example.com",
        "https://api3.example.com",
    ];
    
    let tasks: Vec<_> = urls.iter()
        .map(|url| fetch_url(url))
        .collect();
    
    let results = futures::future::join_all(tasks).await;
    
    for result in results {
        match result {
            Ok(data) => println!("{}", data),
            Err(e) => eprintln!("Error: {}", e),
        }
    }
}
```

### 场景 3: 流式处理

```rust
use tokio::sync::mpsc;
use futures::StreamExt;

async fn process_stream() {
    let (tx, mut rx) = mpsc::channel(100);
    
    // 生产者
    tokio::spawn(async move {
        for i in 0..100 {
            tx.send(i).await.unwrap();
        }
    });
    
    // 消费者 - 流式处理
    let mut stream = tokio_stream::wrappers::ReceiverStream::new(rx);
    while let Some(value) = stream.next().await {
        println!("Processing: {}", value);
        tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    }
}
```

---

## 📚 延伸阅读

- [Tokio 官方文档](https://tokio.rs/)
- [async-std 官方文档](https://async.rs/)
- [Async Book](https://rust-lang.github.io/async-book/)
- [Tokio Tutorial](https://tokio.rs/tokio/tutorial)

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
