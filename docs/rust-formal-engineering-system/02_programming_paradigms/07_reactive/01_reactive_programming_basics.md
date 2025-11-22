# 响应式编程基础（Reactive Programming Basics）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [响应式编程基础（Reactive Programming Basics）](#响应式编程基础reactive-programming-basics)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [响应式流](#响应式流)
    - [使用 tokio-stream](#使用-tokio-stream)
    - [流转换](#流转换)
  - [观察者模式](#观察者模式)
    - [事件流](#事件流)
  - [背压处理](#背压处理)
    - [缓冲流](#缓冲流)
  - [实践示例](#实践示例)
    - [示例 1：事件驱动系统](#示例-1事件驱动系统)
    - [示例 2：数据流处理](#示例-2数据流处理)
  - [最佳实践](#最佳实践)
    - [1. 错误处理](#1-错误处理)
    - [2. 超时处理](#2-超时处理)
  - [参考资料](#参考资料)

---

## 概述

响应式编程是一种面向数据流和变化传播的编程范式。在 Rust 中，可以使用 `futures`、`tokio-stream` 等库实现响应式编程。

## 响应式流

### 使用 tokio-stream

```rust
use tokio_stream::{self as stream, StreamExt};

#[tokio::main]
async fn main() {
    let mut stream = stream::iter(1..=10);

    while let Some(value) = stream.next().await {
        println!("收到值: {}", value);
    }
}
```

### 流转换

```rust
use tokio_stream::{self as stream, StreamExt};

#[tokio::main]
async fn main() {
    let numbers = stream::iter(1..=10);

    let doubled: Vec<i32> = numbers
        .map(|x| x * 2)
        .filter(|&x| x > 10)
        .collect()
        .await;

    println!("结果: {:?}", doubled);
}
```

## 观察者模式

### 事件流

```rust
use tokio::sync::broadcast;
use tokio_stream::wrappers::BroadcastStream;
use tokio_stream::StreamExt;

#[tokio::main]
async fn main() {
    let (tx, _rx) = broadcast::channel::<String>(16);

    // 发布事件
    tokio::spawn(async move {
        for i in 1..=5 {
            tx.send(format!("事件 {}", i)).unwrap();
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        }
    });

    // 订阅事件
    let mut rx = BroadcastStream::new(tx.subscribe());
    while let Some(event) = rx.next().await {
        match event {
            Ok(msg) => println!("收到: {}", msg),
            Err(e) => eprintln!("错误: {}", e),
        }
    }
}
```

## 背压处理

### 缓冲流

```rust
use tokio_stream::{self as stream, StreamExt};

async fn process_with_backpressure() {
    let mut stream = stream::iter(1..=1000);

    // 使用 buffer_unordered 控制并发
    stream
        .map(|x| async move {
            // 处理每个元素
            process_item(x).await
        })
        .buffer_unordered(10)  // 最多 10 个并发
        .for_each(|result| async move {
            println!("处理结果: {:?}", result);
        })
        .await;
}

async fn process_item(item: i32) -> i32 {
    tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
    item * 2
}
```

## 实践示例

### 示例 1：事件驱动系统

```rust
use tokio::sync::mpsc;
use tokio_stream::wrappers::ReceiverStream;
use tokio_stream::StreamExt;

#[derive(Debug, Clone)]
enum Event {
    UserLogin { user_id: u32 },
    UserLogout { user_id: u32 },
    Message { from: u32, to: u32, content: String },
}

pub struct EventBus {
    sender: mpsc::Sender<Event>,
}

impl EventBus {
    pub fn new() -> (Self, ReceiverStream<Event>) {
        let (tx, rx) = mpsc::channel(100);
        let bus = EventBus { sender: tx };
        let stream = ReceiverStream::new(rx);
        (bus, stream)
    }

    pub async fn publish(&self, event: Event) -> Result<(), mpsc::error::SendError<Event>> {
        self.sender.send(event).await
    }
}

#[tokio::main]
async fn main() {
    let (bus, mut stream) = EventBus::new();

    // 订阅者
    tokio::spawn(async move {
        while let Some(event) = stream.next().await {
            match event {
                Event::UserLogin { user_id } => {
                    println!("用户 {} 登录", user_id);
                }
                Event::UserLogout { user_id } => {
                    println!("用户 {} 登出", user_id);
                }
                Event::Message { from, to, content } => {
                    println!("消息: {} -> {}: {}", from, to, content);
                }
            }
        }
    });

    // 发布事件
    bus.publish(Event::UserLogin { user_id: 1 }).await.unwrap();
    bus.publish(Event::Message {
        from: 1,
        to: 2,
        content: "Hello".to_string(),
    }).await.unwrap();

    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
}
```

### 示例 2：数据流处理

```rust
use tokio_stream::{self as stream, StreamExt};

async fn data_processing_pipeline() {
    let data = stream::iter(1..=100);

    let result: Vec<i32> = data
        .map(|x| async move {
            // 步骤 1: 转换
            x * 2
        })
        .buffered(10)  // 缓冲 10 个
        .filter(|&x| async move {
            // 步骤 2: 过滤
            x > 50
        })
        .map(|x| async move {
            // 步骤 3: 进一步处理
            x + 10
        })
        .buffered(10)
        .collect()
        .await;

    println!("处理结果: {:?}", result);
}
```

## 最佳实践

### 1. 错误处理

```rust
use tokio_stream::{self as stream, StreamExt};

async fn handle_errors() {
    let stream = stream::iter(vec![Ok(1), Err("error"), Ok(2)]);

    stream
        .filter_map(|result| async move {
            match result {
                Ok(value) => Some(value),
                Err(e) => {
                    eprintln!("错误: {}", e);
                    None
                }
            }
        })
        .for_each(|value| async move {
            println!("值: {}", value);
        })
        .await;
}
```

### 2. 超时处理

```rust
use tokio_stream::{self as stream, StreamExt};
use tokio::time::{timeout, Duration};

async fn with_timeout() {
    let mut stream = stream::iter(1..=10);

    while let Some(value) = stream.next().await {
        match timeout(Duration::from_secs(1), process_item(value)).await {
            Ok(result) => println!("结果: {:?}", result),
            Err(_) => eprintln!("超时"),
        }
    }
}
```

## 参考资料

- [响应式编程索引](./00_index.md)
- [编程范式索引](../00_index.md)
- [Tokio Stream 文档](https://docs.rs/tokio-stream/)
- [Futures 文档](https://docs.rs/futures/)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回编程范式: [`../00_index.md`](../00_index.md)
