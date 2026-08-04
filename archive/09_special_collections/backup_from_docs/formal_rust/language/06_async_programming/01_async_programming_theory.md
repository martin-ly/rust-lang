# 01 异步编程基础理论

## 章节简介

本章深入探讨Rust异步编程的理论基础，包括异步编程模型、Future trait、async/await语法、异步运行时等核心概念。
特别关注2025年Rust异步编程的最新发展，为构建高性能、高可靠的异步系统提供理论基础。

## 目录

- [01 异步编程基础理论](#01-异步编程基础理论)
  - [章节简介](#章节简介)
  - [目录](#目录)
  - [1. 异步编程模型](#1-异步编程模型)
    - [1.1 同步 vs 异步](#11-同步-vs-异步)
    - [1.2 事件驱动模型](#12-事件驱动模型)
    - [1.3 协程模型](#13-协程模型)
  - [2. Future Trait 核心抽象](#2-future-trait-核心抽象)
    - [2.1 Future Trait 定义](#21-future-trait-定义)
    - [2.2 自定义 Future 实现](#22-自定义-future-实现)
    - [2.3 Future 组合](#23-future-组合)
  - [3. async/await 语法](#3-asyncawait-语法)
    - [3.1 基本语法](#31-基本语法)
    - [3.2 异步迭代器](#32-异步迭代器)
    - [3.3 异步流](#33-异步流)
  - [4. 异步运行时](#4-异步运行时)
    - [4.1 Tokio 运行时](#41-tokio-运行时)
    - [4.2 async-std 运行时](#42-async-std-运行时)
    - [4.3 smol 运行时](#43-smol-运行时)
  - [5. 异步调度策略](#5-异步调度策略)
    - [5.1 工作窃取调度](#51-工作窃取调度)
    - [5.2 优先级调度](#52-优先级调度)
    - [5.3 公平调度](#53-公平调度)
  - [6. 异步编程模式](#6-异步编程模式)
    - [6.1 生产者-消费者模式](#61-生产者-消费者模式)
    - [6.2 发布-订阅模式](#62-发布-订阅模式)
    - [6.3 扇出-扇入模式](#63-扇出-扇入模式)
  - [7. 2025年新特性](#7-2025年新特性)
    - [7.1 异步特征完整稳定化](#71-异步特征完整稳定化)
    - [7.2 异步生命周期管理](#72-异步生命周期管理)
    - [7.3 异步分离逻辑](#73-异步分离逻辑)
  - [8. 工程实践](#8-工程实践)
    - [8.1 错误处理](#81-错误处理)
    - [8.2 性能优化](#82-性能优化)
    - [8.3 测试策略](#83-测试策略)

## 1. 异步编程模型

### 1.1 同步 vs 异步

**同步编程模型**：

```rust
fn sync_function() -> Result<Data, Error> {
    // 阻塞式操作
    let data = blocking_operation()?;
    process_data(data)
}
```

**异步编程模型**：

```rust
async fn async_function() -> Result<Data, Error> {
    // 非阻塞式操作
    let data = non_blocking_operation().await?;
    process_data(data)
}
```

### 1.2 事件驱动模型

```rust
use tokio::sync::mpsc;

#[tokio::main]
async fn main() {
    let (tx, mut rx) = mpsc::channel(100);
    
    // 生产者任务
    let producer = tokio::spawn(async move {
        for i in 0..10 {
            tx.send(i).await.unwrap();
        }
    });
    
    // 消费者任务
    let consumer = tokio::spawn(async move {
        while let Some(value) = rx.recv().await {
            println!("Received: {}", value);
        }
    });
    
    producer.await.unwrap();
    consumer.await.unwrap();
}
```

### 1.3 协程模型

```rust
use std::pin::Pin;
use std::future::Future;

// 协程抽象
struct Coroutine<T> {
    future: Pin<Box<dyn Future<Output = T> + Send>>,
}

impl<T> Coroutine<T> {
    fn new<F>(future: F) -> Self 
    where 
        F: Future<Output = T> + Send + 'static,
    {
        Self {
            future: Box::pin(future),
        }
    }
}
```

## 2. Future Trait 核心抽象

### 2.1 Future Trait 定义

```rust
use std::pin::Pin;
use std::task::{Context, Poll};

pub trait Future {
    type Output;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}

pub enum Poll<T> {
    Ready(T),
    Pending,
}
```

### 2.2 自定义 Future 实现

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::{Duration, Instant};

struct Delay {
    when: Instant,
}

impl Delay {
    fn new(duration: Duration) -> Self {
        Self {
            when: Instant::now() + duration,
        }
    }
}

impl Future for Delay {
    type Output = ();
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if Instant::now() >= self.when {
            Poll::Ready(())
        } else {
            // 注册唤醒器
            cx.waker().wake_by_ref();
            Poll::Pending
        }
    }
}

// 使用示例
async fn example() {
    Delay::new(Duration::from_secs(1)).await;
    println!("1 second has elapsed");
}
```

### 2.3 Future 组合

```rust
use futures::future::{join, select, join_all};

async fn combined_futures() {
    // 并行执行多个 Future
    let (result1, result2) = join(
        async_function_1(),
        async_function_2()
    ).await;
    
    // 选择第一个完成的 Future
    let result = select(
        Box::pin(async_function_1()),
        Box::pin(async_function_2())
    ).await;
    
    // 等待所有 Future 完成
    let results = join_all(vec![
        async_function_1(),
        async_function_2(),
        async_function_3(),
    ]).await;
}
```

## 3. async/await 语法

### 3.1 基本语法

```rust
// 异步函数
async fn fetch_data(url: &str) -> Result<String, Error> {
    let response = reqwest::get(url).await?;
    let body = response.text().await?;
    Ok(body)
}

// 异步闭包
let async_closure = async |x: i32| -> i32 {
    x * 2
};

// 异步块
let result = async {
    let data1 = fetch_data("http://api1.com").await?;
    let data2 = fetch_data("http://api2.com").await?;
    Ok::<String, Error>(format!("{} {}", data1?, data2?))
}.await;
```

### 3.2 异步迭代器

```rust
use async_trait::async_trait;

#[async_trait]
trait AsyncIterator {
    type Item;
    
    async fn next(&mut self) -> Option<Self::Item>;
}

struct AsyncRange {
    start: i32,
    end: i32,
    current: i32,
}

#[async_trait]
impl AsyncIterator for AsyncRange {
    type Item = i32;
    
    async fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.end {
            let result = self.current;
            self.current += 1;
            Some(result)
        } else {
            None
        }
    }
}

// 使用异步迭代器
async fn process_range() {
    let mut range = AsyncRange { start: 0, end: 10, current: 0 };
    
    while let Some(value) = range.next().await {
        println!("Processing: {}", value);
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
}
```

### 3.3 异步流

```rust
use tokio_stream::{Stream, StreamExt};

struct AsyncStream {
    data: Vec<i32>,
    index: usize,
}

impl Stream for AsyncStream {
    type Item = i32;
    
    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        
        if this.index < this.data.len() {
            let item = this.data[this.index];
            this.index += 1;
            Poll::Ready(Some(item))
        } else {
            Poll::Ready(None)
        }
    }
}

// 使用异步流
async fn process_stream() {
    let stream = AsyncStream {
        data: vec![1, 2, 3, 4, 5],
        index: 0,
    };
    
    stream.for_each(|item| async move {
        println!("Processing: {}", item);
    }).await;
}
```

## 4. 异步运行时

### 4.1 Tokio 运行时

```rust
use tokio::runtime::{Runtime, Builder};

// 创建多线程运行时
let runtime = Builder::new_multi_thread()
    .worker_threads(4)
    .enable_all()
    .build()
    .unwrap();

// 在运行时中执行异步代码
runtime.block_on(async {
    let result = async_function().await;
    println!("Result: {:?}", result);
});

// 或者使用宏
#[tokio::main]
async fn main() {
    let result = async_function().await;
    println!("Result: {:?}", result);
}
```

### 4.2 async-std 运行时

```rust
use async_std::task;

#[async_std::main]
async fn main() {
    let handle = task::spawn(async {
        // 异步任务
        println!("Hello from async task");
    });
    
    handle.await;
}
```

### 4.3 smol 运行时

```rust
use smol::Executor;

fn main() {
    let ex = Executor::new();
    
    ex.run(async {
        let task = ex.spawn(async {
            println!("Hello from smol task");
        });
        
        task.await;
    });
}
```

## 5. 异步调度策略

### 5.1 工作窃取调度

```rust
use tokio::runtime::Builder;

let runtime = Builder::new_multi_thread()
    .worker_threads(4)
    .enable_all()
    .build()
    .unwrap();

// 工作窃取调度器会自动在多个线程间分配任务
runtime.block_on(async {
    let handles: Vec<_> = (0..100)
        .map(|i| tokio::spawn(async move {
            println!("Task {} on thread {:?}", i, std::thread::current().id());
        }))
        .collect();
    
    for handle in handles {
        handle.await.unwrap();
    }
});
```

### 5.2 优先级调度

```rust
use tokio::task::JoinSet;

async fn priority_scheduling() {
    let mut set = JoinSet::new();
    
    // 高优先级任务
    set.spawn_blocking(|| {
        println!("High priority task");
    });
    
    // 低优先级任务
    set.spawn_blocking(|| {
        println!("Low priority task");
    });
    
    while let Some(result) = set.join_next().await {
        result.unwrap();
    }
}
```

### 5.3 公平调度

```rust
use tokio::sync::Semaphore;

async fn fair_scheduling() {
    let semaphore = Semaphore::new(5); // 限制并发数
    
    let handles: Vec<_> = (0..20)
        .map(|i| {
            let permit = semaphore.clone().acquire_owned();
            tokio::spawn(async move {
                let _permit = permit.await.unwrap();
                println!("Task {} executing", i);
                tokio::time::sleep(Duration::from_millis(100)).await;
            })
        })
        .collect();
    
    for handle in handles {
        handle.await.unwrap();
    }
}
```

## 6. 异步编程模式

### 6.1 生产者-消费者模式

```rust
use tokio::sync::mpsc;

async fn producer_consumer() {
    let (tx, mut rx) = mpsc::channel(100);
    
    // 生产者
    let producer = tokio::spawn(async move {
        for i in 0..10 {
            tx.send(i).await.unwrap();
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    });
    
    // 消费者
    let consumer = tokio::spawn(async move {
        while let Some(value) = rx.recv().await {
            println!("Consumed: {}", value);
        }
    });
    
    producer.await.unwrap();
    consumer.await.unwrap();
}
```

### 6.2 发布-订阅模式

```rust
use tokio::sync::broadcast;

async fn pub_sub() {
    let (tx, mut rx1) = broadcast::channel(16);
    let mut rx2 = tx.subscribe();
    
    // 发布者
    let publisher = tokio::spawn(async move {
        for i in 0..10 {
            tx.send(i).unwrap();
            tokio::time::sleep(Duration::from_millis(100)).await;
        }
    });
    
    // 订阅者1
    let subscriber1 = tokio::spawn(async move {
        while let Ok(value) = rx1.recv().await {
            println!("Subscriber 1: {}", value);
        }
    });
    
    // 订阅者2
    let subscriber2 = tokio::spawn(async move {
        while let Ok(value) = rx2.recv().await {
            println!("Subscriber 2: {}", value);
        }
    });
    
    publisher.await.unwrap();
    subscriber1.await.unwrap();
    subscriber2.await.unwrap();
}
```

### 6.3 扇出-扇入模式

```rust
use tokio::sync::mpsc;
use futures::stream::{self, StreamExt};

async fn fan_out_fan_in() {
    let (tx, mut rx) = mpsc::channel(100);
    
    // 扇出：多个生产者
    let producers: Vec<_> = (0..3)
        .map(|id| {
            let tx = tx.clone();
            tokio::spawn(async move {
                for i in 0..5 {
                    tx.send((id, i)).await.unwrap();
                    tokio::time::sleep(Duration::from_millis(100)).await;
                }
            })
        })
        .collect();
    
    // 扇入：单个消费者
    let consumer = tokio::spawn(async move {
        while let Some((producer_id, value)) = rx.recv().await {
            println!("Producer {} sent: {}", producer_id, value);
        }
    });
    
    for producer in producers {
        producer.await.unwrap();
    }
    
    consumer.await.unwrap();
}
```

## 7. 2025年新特性

### 7.1 异步特征完整稳定化

```rust
// 2025年：异步特征完整支持
trait AsyncProcessor: Send + Sync {
    async fn process(&self, data: &[u8]) -> Result<Vec<u8>, Error>;
    async fn validate(&self, input: &str) -> bool;
    async fn transform(&self, input: &str) -> Result<String, Error>;
}

// 动态分发支持
async fn use_async_trait(processor: Box<dyn AsyncProcessor>) {
    let data = b"hello world";
    let result = processor.process(data).await.unwrap();
    println!("Processed: {:?}", result);
}

// 向上转型支持
async fn upcast_example() {
    let processor: Box<dyn AsyncProcessor> = Box::new(MyProcessor);
    
    // 向上转型到更通用的特征
    let processor: Box<dyn std::any::Any> = processor;
}
```

### 7.2 异步生命周期管理

```rust
// 2025年：复杂的异步生命周期
async fn complex_lifetime<'a, T>(
    data: &'a T,
    processor: &'a dyn AsyncProcessor,
) -> Result<Vec<u8>, Error>
where
    T: AsRef<[u8]> + Send + Sync,
{
    let bytes = data.as_ref();
    processor.process(bytes).await
}

// 异步生命周期约束
trait AsyncContainer {
    type Item<'a> where Self: 'a;
    
    async fn get<'a>(&'a self, index: usize) -> Option<Self::Item<'a>>;
    async fn set<'a>(&'a mut self, index: usize, value: Self::Item<'a>) -> Result<(), Error>;
}
```

### 7.3 异步分离逻辑

```rust
// 2025年：异步分离逻辑
use std::pin::Pin;

trait AsyncSafe: Send + Sync {
    async fn safe_operation(self: Pin<&mut Self>) -> Result<(), Error>;
    async fn concurrent_access(&self) -> Result<Data, Error>;
}

struct AsyncData {
    data: Vec<u8>,
    counter: AtomicUsize,
}

impl AsyncSafe for AsyncData {
    async fn safe_operation(self: Pin<&mut Self>) -> Result<(), Error> {
        // 安全的异步操作
        let this = self.get_mut();
        this.counter.fetch_add(1, Ordering::Relaxed);
        Ok(())
    }
    
    async fn concurrent_access(&self) -> Result<Data, Error> {
        // 并发安全的访问
        let count = self.counter.load(Ordering::Relaxed);
        Ok(Data { count })
    }
}
```

## 8. 工程实践

### 8.1 错误处理

```rust
use thiserror::Error;

#[derive(Error, Debug)]
enum AsyncError {
    #[error("Network error: {0}")]
    Network(#[from] reqwest::Error),
    #[error("Timeout error")]
    Timeout,
    #[error("Validation error: {0}")]
    Validation(String),
}

async fn robust_async_function() -> Result<String, AsyncError> {
    let result = tokio::time::timeout(
        Duration::from_secs(5),
        fetch_data("http://api.example.com")
    ).await
    .map_err(|_| AsyncError::Timeout)??;
    
    if result.is_empty() {
        return Err(AsyncError::Validation("Empty response".to_string()));
    }
    
    Ok(result)
}
```

### 8.2 性能优化

```rust
use tokio::sync::Semaphore;

async fn optimized_async_processing() {
    let semaphore = Semaphore::new(10); // 限制并发数
    
    let handles: Vec<_> = (0..100)
        .map(|i| {
            let permit = semaphore.clone().acquire_owned();
            tokio::spawn(async move {
                let _permit = permit.await.unwrap();
                
                // 使用连接池
                let client = reqwest::Client::new();
                let response = client
                    .get(&format!("http://api.example.com/{}", i))
                    .send()
                    .await
                    .unwrap();
                
                response.text().await.unwrap()
            })
        })
        .collect();
    
    let results = futures::future::join_all(handles).await;
    println!("Processed {} requests", results.len());
}
```

### 8.3 测试策略

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use tokio::test;
    
    #[test]
    async fn test_async_function() {
        let result = async_function().await;
        assert!(result.is_ok());
    }
    
    #[tokio::test]
    async fn test_with_tokio() {
        let result = fetch_data("http://httpbin.org/get").await;
        assert!(result.is_ok());
    }
    
    #[test]
    async fn test_mock_async() {
        let mock_processor = MockProcessor;
        let result = mock_processor.process(b"test").await;
        assert_eq!(result.unwrap(), b"processed test");
    }
}

struct MockProcessor;

#[async_trait::async_trait]
impl AsyncProcessor for MockProcessor {
    async fn process(&self, data: &[u8]) -> Result<Vec<u8>, Error> {
        Ok(format!("processed {}", String::from_utf8_lossy(data)).into_bytes())
    }
    
    async fn validate(&self, _input: &str) -> bool {
        true
    }
    
    async fn transform(&self, input: &str) -> Result<String, Error> {
        Ok(input.to_uppercase())
    }
}
```

---

**完成度**: 100%

本章全面介绍了Rust异步编程的基础理论，包括异步编程模型、Future trait、async/await语法、异步运行时等核心概念。特别关注2025年Rust异步编程的最新发展，为构建高性能、高可靠的异步系统提供了坚实的理论基础。
