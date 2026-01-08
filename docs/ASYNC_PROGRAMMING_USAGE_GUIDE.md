# 异步编程使用指南

**模块**: C06 Async
**创建日期**: 2025-12-11
**最后更新**: 2025-12-11
**Rust 版本**: 1.92.0
**Edition**: 2024

---

## 📋 目录

- [异步编程使用指南](#异步编程使用指南)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🚀 快速开始](#-快速开始)
    - [基本异步函数](#基本异步函数)
    - [并发执行](#并发执行)
  - [📊 核心功能](#-核心功能)
    - [1. Future Trait](#1-future-trait)
    - [2. 异步运行时](#2-异步运行时)
      - [Tokio 运行时](#tokio-运行时)
      - [自定义运行时配置](#自定义运行时配置)
    - [3. 异步 I/O](#3-异步-io)
      - [文件 I/O](#文件-io)
      - [网络 I/O](#网络-io)
    - [4. Reactor 模式](#4-reactor-模式)
    - [5. Actor 模式](#5-actor-模式)
  - [⚡ 性能优化](#-性能优化)
    - [1. 使用 select! 宏](#1-使用-select-宏)
    - [2. 使用 Stream](#2-使用-stream)
    - [3. 背压处理](#3-背压处理)
  - [🔧 错误处理](#-错误处理)
    - [异步错误传播](#异步错误传播)
    - [错误恢复](#错误恢复)
  - [🐛 常见问题](#-常见问题)
    - [阻塞运行时](#阻塞运行时)
    - [Future 必须 Send](#future-必须-send)
  - [📚 相关文档](#-相关文档)

---

## 📋 概述

本指南介绍如何使用 C06 异步编程模块的功能，包括 async/await、Future、异步运行时、Reactor 模式、Actor 模式等。

---

## 🚀 快速开始

### 基本异步函数

```rust
use tokio::time::{sleep, Duration};

async fn fetch_data() -> String {
    sleep(Duration::from_secs(1)).await;
    "数据".to_string()
}

#[tokio::main]
async fn main() {
    let result = fetch_data().await;
    println!("结果: {}", result);
}
```

### 并发执行

```rust
use tokio::time::{sleep, Duration, Instant};

async fn task1() -> &'static str {
    sleep(Duration::from_secs(1)).await;
    "任务1完成"
}

async fn task2() -> &'static str {
    sleep(Duration::from_secs(1)).await;
    "任务2完成"
}

#[tokio::main]
async fn main() {
    let start = Instant::now();

    // 并发执行
    let (result1, result2) = tokio::join!(task1(), task2());

    println!("{}: {:?}", result1, start.elapsed());
    println!("{}: {:?}", result2, start.elapsed());
    // 总耗时约 1 秒（并发执行）
}
```

---

## 📊 核心功能

### 1. Future Trait

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

struct MyFuture {
    value: i32,
}

impl Future for MyFuture {
    type Output = i32;

    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(self.value)
    }
}

#[tokio::main]
async fn main() {
    let future = MyFuture { value: 42 };
    let result = future.await;
    println!("结果: {}", result);
}
```

### 2. 异步运行时

#### Tokio 运行时

```rust
use tokio::runtime::Runtime;

let rt = Runtime::new().unwrap();

rt.block_on(async {
    println!("在 Tokio 运行时中执行");
});
```

#### 自定义运行时配置

```rust
use tokio::runtime::Builder;

let rt = Builder::new_multi_thread()
    .worker_threads(4)
    .max_blocking_threads(512)
    .enable_all()
    .build()
    .unwrap();
```

### 3. 异步 I/O

#### 文件 I/O

```rust
use tokio::fs;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 异步读取文件
    let contents = fs::read_to_string("file.txt").await?;
    println!("文件内容: {}", contents);

    // 异步写入文件
    fs::write("output.txt", "Hello, World!").await?;

    Ok(())
}
```

#### 网络 I/O

```rust
use tokio::net::TcpListener;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;

    loop {
        let (mut socket, _) = listener.accept().await?;

        tokio::spawn(async move {
            let mut buf = [0; 1024];
            match socket.read(&mut buf).await {
                Ok(n) => {
                    if n == 0 {
                        return;
                    }
                    socket.write_all(&buf[0..n]).await.unwrap();
                }
                Err(e) => eprintln!("错误: {}", e),
            }
        });
    }
}
```

### 4. Reactor 模式

```rust
use c06_async::reactor::Reactor;

let mut reactor = Reactor::new();

// 注册事件处理器
reactor.register_handler(EventType::Read, |event| {
    println!("处理读事件: {:?}", event);
});

// 运行事件循环
reactor.run().await;
```

### 5. Actor 模式

```rust
use c06_async::actor::{Actor, ActorRef, Message};

struct MyActor {
    count: i32,
}

impl Actor for MyActor {
    type Message = i32;

    async fn handle(&mut self, msg: Self::Message) {
        self.count += msg;
        println!("计数: {}", self.count);
    }
}

#[tokio::main]
async fn main() {
    let actor_ref = ActorRef::spawn(MyActor { count: 0 }).await;

    actor_ref.send(1).await;
    actor_ref.send(2).await;
    actor_ref.send(3).await;
}
```

---

## ⚡ 性能优化

### 1. 使用 select! 宏

```rust
use tokio::time::{sleep, Duration, timeout};

#[tokio::main]
async fn main() {
    tokio::select! {
        result = async_task1() => {
            println!("任务1完成: {:?}", result);
        }
        result = async_task2() => {
            println!("任务2完成: {:?}", result);
        }
        _ = sleep(Duration::from_secs(5)) => {
            println!("超时");
        }
    }
}
```

### 2. 使用 Stream

```rust
use tokio_stream::{self as stream, StreamExt};

#[tokio::main]
async fn main() {
    let mut stream = stream::iter(1..=10);

    while let Some(value) = stream.next().await {
        println!("值: {}", value);
    }
}
```

### 3. 背压处理

```rust
use tokio::sync::mpsc;

let (tx, mut rx) = mpsc::channel(100); // 有界通道

tokio::spawn(async move {
    for i in 0..1000 {
        // 如果通道满了，会等待
        tx.send(i).await.unwrap();
    }
});

while let Some(value) = rx.recv().await {
    println!("接收: {}", value);
}
```

---

## 🔧 错误处理

### 异步错误传播

```rust
use std::error::Error;

async fn fetch_data() -> Result<String, Box<dyn Error>> {
    // 使用 ? 操作符传播错误
    let response = reqwest::get("https://api.example.com").await?;
    let text = response.text().await?;
    Ok(text)
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let data = fetch_data().await?;
    println!("数据: {}", data);
    Ok(())
}
```

### 错误恢复

```rust
use tokio::time::{sleep, Duration};

async fn retry_operation<F, Fut, T, E>(mut f: F, max_retries: u32) -> Result<T, E>
where
    F: FnMut() -> Fut,
    Fut: std::future::Future<Output = Result<T, E>>,
{
    for attempt in 1..=max_retries {
        match f().await {
            Ok(value) => return Ok(value),
            Err(e) => {
                if attempt < max_retries {
                    sleep(Duration::from_secs(1)).await;
                    continue;
                }
                return Err(e);
            }
        }
    }
    unreachable!()
}
```

---

## 🐛 常见问题

### 阻塞运行时

```rust
// ❌ 在异步上下文中阻塞
async fn bad_example() {
    std::thread::sleep(Duration::from_secs(1)); // 阻塞！
}

// ✅ 使用异步睡眠
async fn good_example() {
    tokio::time::sleep(Duration::from_secs(1)).await;
}
```

### Future 必须 Send

```rust
// ❌ 非 Send 类型
use std::rc::Rc;

async fn bad_example() {
    let rc = Rc::new(42);
    // Rc 不是 Send，不能跨线程
}

// ✅ 使用 Arc
use std::sync::Arc;

async fn good_example() {
    let arc = Arc::new(42);
    // Arc 是 Send，可以跨线程
}
```

---

## 📚 相关文档

- [完整文档](../crates/c06_async/README.md)
- [异步编程指南](../crates/c06_async/docs/tier_02_guides/01_异步编程快速入门.md)
- [Reactor 模式](../crates/c06_async/docs/tier_03_references/02_Reactor模式参考.md)
- [Actor 模式](../crates/c06_async/docs/tier_03_references/03_Actor模式参考.md)

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 完整实现
**最后更新**: 2025-12-11
