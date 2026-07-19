# 异步编程高级示例（Advanced Async Programming）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [异步编程高级示例（Advanced Async Programming）](#异步编程高级示例advanced-async-programming)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [Future 和 async/await](#future-和-asyncawait)
    - [基本用法](#基本用法)
    - [组合异步操作](#组合异步操作)
  - [并发执行](#并发执行)
    - [使用 tokio::spawn](#使用-tokiospawn)
    - [使用 select](#使用-select)
  - [错误处理](#错误处理)
    - [Result 和 async](#result-和-async)
    - [错误传播](#错误传播)
  - [实践示例](#实践示例)
    - [示例 1：HTTP 客户端](#示例-1http-客户端)
    - [示例 2：异步流处理](#示例-2异步流处理)
    - [示例 3：异步互斥锁](#示例-3异步互斥锁)
    - [示例 4：异步通道](#示例-4异步通道)
  - [性能优化](#性能优化)
    - [1. 批量处理](#1-批量处理)
    - [2. 限制并发数](#2-限制并发数)
  - [参考资料](#参考资料)

---

## 概述

异步编程允许程序在等待 I/O 操作时执行其他任务，提高程序的并发性能。Rust 的异步编程基于 Future trait 和 async/await 语法。

## Future 和 async/await

### 基本用法

```rust
use std::time::Duration;
use tokio::time::sleep;

// 示例：基本的 async 函数
async fn fetch_data() -> String {
    sleep(Duration::from_secs(1)).await;
    String::from("数据")
}

// 示例：使用 async/await
#[tokio::main]
async fn main() {
    let data = fetch_data().await;
    println!("{}", data);
}
```

### 组合异步操作

```rust
use tokio::time::{sleep, Duration};

// 示例：顺序执行
async fn sequential() {
    let result1 = fetch_data().await;
    println!("结果 1: {}", result1);

    let result2 = fetch_data().await;
    println!("结果 2: {}", result2);
}

// 示例：并发执行
async fn concurrent() {
    let (result1, result2) = tokio::join!(
        fetch_data(),
        fetch_data()
    );
    println!("结果 1: {}", result1);
    println!("结果 2: {}", result2);
}
```

## 并发执行

### 使用 tokio::spawn

```rust
use tokio::time::{sleep, Duration};

async fn task(id: u32) {
    println!("任务 {} 开始", id);
    sleep(Duration::from_secs(1)).await;
    println!("任务 {} 完成", id);
}

#[tokio::main]
async fn main() {
    let mut handles = vec![];

    for i in 1..=5 {
        let handle = tokio::spawn(task(i));
        handles.push(handle);
    }

    for handle in handles {
        handle.await.unwrap();
    }
}
```

### 使用 select

```rust
use tokio::time::{sleep, Duration, timeout};
use tokio::sync::oneshot;

async fn race_conditions() {
    let (tx1, rx1) = oneshot::channel();
    let (tx2, rx2) = oneshot::channel();

    tokio::spawn(async move {
        sleep(Duration::from_millis(100)).await;
        let _ = tx1.send("任务 1 完成");
    });

    tokio::spawn(async move {
        sleep(Duration::from_millis(200)).await;
        let _ = tx2.send("任务 2 完成");
    });

    tokio::select! {
        result = rx1 => {
            println!("{}", result.unwrap());
        }
        result = rx2 => {
            println!("{}", result.unwrap());
        }
    }
}
```

## 错误处理

### Result 和 async

```rust
use std::io;

async fn fetch_with_error() -> Result<String, io::Error> {
    // 模拟可能失败的操作
    tokio::time::sleep(Duration::from_secs(1)).await;
    Ok(String::from("成功"))
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    match fetch_with_error().await {
        Ok(data) => println!("{}", data),
        Err(e) => eprintln!("错误: {}", e),
    }
    Ok(())
}
```

### 错误传播

```rust
async fn process_data() -> Result<String, String> {
    let data = fetch_with_error()
        .await
        .map_err(|e| format!("获取数据失败: {}", e))?;

    Ok(format!("处理后的数据: {}", data))
}
```

## 实践示例

### 示例 1：HTTP 客户端

```rust
use tokio::time::{sleep, Duration};

struct HttpClient;

impl HttpClient {
    async fn get(&self, url: &str) -> Result<String, String> {
        // 模拟 HTTP 请求
        sleep(Duration::from_millis(100)).await;
        Ok(format!("响应来自: {}", url))
    }

    async fn get_multiple(&self, urls: Vec<&str>) -> Vec<Result<String, String>> {
        let mut tasks = vec![];

        for url in urls {
            let client = self;
            tasks.push(tokio::spawn(async move {
                client.get(url).await
            }));
        }

        let mut results = vec![];
        for task in tasks {
            results.push(task.await.unwrap());
        }

        results
    }
}

#[tokio::main]
async fn main() {
    let client = HttpClient;
    let urls = vec!["https://example.com", "https://rust-lang.org"];
    let results = client.get_multiple(urls).await;

    for result in results {
        match result {
            Ok(response) => println!("{}", response),
            Err(e) => eprintln!("错误: {}", e),
        }
    }
}
```

### 示例 2：异步流处理

```rust
use tokio_stream::{self as stream, StreamExt};
use tokio::time::{sleep, Duration};

async fn process_stream() {
    let mut stream = stream::iter(1..=10);

    while let Some(value) = stream.next().await {
        println!("处理值: {}", value);
        sleep(Duration::from_millis(100)).await;
    }
}

// 示例：转换流
async fn transform_stream() {
    let stream = stream::iter(1..=5);

    let doubled: Vec<i32> = stream
        .map(|x| x * 2)
        .collect()
        .await;

    println!("{:?}", doubled);
}
```

### 示例 3：异步互斥锁

```rust
use tokio::sync::Mutex;
use std::sync::Arc;
use tokio::time::{sleep, Duration};

async fn shared_state_example() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = tokio::spawn(async move {
            let mut num = counter.lock().await;
            *num += 1;
            sleep(Duration::from_millis(10)).await;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await.unwrap();
    }

    println!("最终计数: {}", *counter.lock().await);
}
```

### 示例 4：异步通道

```rust
use tokio::sync::mpsc;
use tokio::time::{sleep, Duration};

async fn channel_example() {
    let (tx, mut rx) = mpsc::channel(32);

    // 生产者
    tokio::spawn(async move {
        for i in 0..10 {
            tx.send(i).await.unwrap();
            sleep(Duration::from_millis(100)).await;
        }
    });

    // 消费者
    while let Some(value) = rx.recv().await {
        println!("收到: {}", value);
    }
}
```

## 性能优化

### 1. 批量处理

```rust
async fn batch_process(items: Vec<i32>) -> Vec<i32> {
    const BATCH_SIZE: usize = 10;
    let mut results = vec![];

    for chunk in items.chunks(BATCH_SIZE) {
        let batch_results: Vec<i32> = futures::future::join_all(
            chunk.iter().map(|&item| async move {
                process_item(item).await
            })
        ).await;

        results.extend(batch_results);
    }

    results
}

async fn process_item(item: i32) -> i32 {
    sleep(Duration::from_millis(10)).await;
    item * 2
}
```

### 2. 限制并发数

```rust
use futures::stream::{self, StreamExt};

async fn limited_concurrency(items: Vec<i32>) -> Vec<i32> {
    stream::iter(items)
        .map(|item| async move {
            process_item(item).await
        })
        .buffer_unordered(5)  // 最多 5 个并发
        .collect()
        .await
}
```

## 参考资料

- [异步编程理论](../../02_programming_paradigms/02_async/00_index.md)
- [C06 异步模块](../../../../crates/c06_async/)
- [Tokio 文档](https://tokio.rs/)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回实践示例: [`../00_index.md`](../00_index.md)
