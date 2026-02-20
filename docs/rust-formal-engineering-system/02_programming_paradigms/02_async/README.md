# 异步编程范式

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [c06_async/](../../../../crates/c06_async/)

[返回主索引](../../00_master_index.md)

---

## 异步编程核心概念

### Future 与异步执行

Rust 的异步编程基于 Future trait：

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// Future 是惰性的：创建时不执行，直到被 poll
async fn async_hello() -> String {
    String::from("Hello, async!")
}

// async fn 返回 impl Future<Output = T>
fn explicit_future() -> impl Future<Output = i32> {
    async {
        42
    }
}

// 手动实现的 Future
struct TimerFuture {
    duration: std::time::Duration,
}

impl Future for TimerFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // 实现 poll 逻辑
        Poll::Ready(())
    }
}
```

### async/await 语法

```rust
use tokio::time::{sleep, Duration};

// async fn 定义异步函数
async fn fetch_data(url: &str) -> Result<String, reqwest::Error> {
    // await 挂起当前任务，等待 Future 完成
    let response = reqwest::get(url).await?;
    let body = response.text().await?;
    Ok(body)
}

// 并发执行多个异步任务
async fn concurrent_fetch() {
    let urls = vec![
        "https://example.com/1",
        "https://example.com/2",
        "https://example.com/3",
    ];

    // 创建多个 Future
    let futures: Vec<_> = urls
        .iter()
        .map(|url| fetch_data(url))
        .collect();

    // join_all 并发执行所有 Future
    let results = futures::future::join_all(futures).await;

    for result in results {
        match result {
            Ok(body) => println!("Fetched {} bytes", body.len()),
            Err(e) => eprintln!("Error: {}", e),
        }
    }
}

// select! 等待多个 Future 中的第一个完成
use tokio::select;

async fn race_example() {
    let slow = sleep(Duration::from_secs(2));
    let fast = sleep(Duration::from_secs(1));

    select! {
        _ = slow => println!("Slow completed first"),
        _ = fast => println!("Fast completed first"),
    }
}
```

### 异步状态机

```rust
// async fn 被编译为状态机
// 每个 await 点对应一个状态

async fn state_machine_demo() {
    // 状态 0：开始
    println!("Step 1");

    let x = some_async_op().await;  // 状态 1：等待

    println!("Step 2: {}", x);

    let y = another_async_op().await;  // 状态 2：等待

    println!("Step 3: {}", y);  // 状态 3：完成
}

async fn some_async_op() -> i32 {
    42
}

async fn another_async_op() -> i32 {
    100
}

// 状态机的简化表示
enum MyAsyncFn {
    Start,
    WaitingForX,
    WaitingForY,
    Done,
}

// Pin 与自引用
use std::pin::Pin;

// 异步块可能包含自引用（如引用局部变量）
// Pin 确保这些自引用在 poll 之间有效
fn pin_demo() {
    let future = async {
        let local = 5;
        // 如果 Future 被移动，引用 &local 会失效
        // Pin 防止这种移动
        some_async_op().await;
    };

    // Pin<Box<dyn Future>> 是常见的运行时类型
}
```

### 流（Streams）

```rust
use futures::stream::{self, Stream, StreamExt};

// Stream 是异步的迭代器n stream_example() -> impl Stream<Item = i32> {
    stream::iter(vec![1, 2, 3, 4, 5])
}

// 处理流
async fn process_stream() {
    let mut stream = stream::iter(vec![1, 2, 3, 4, 5]);

    while let Some(value) = stream.next().await {
        println!("Got: {}", value);
    }
}

// 流组合器
async fn stream_combinators() {
    let stream = stream::iter(vec![1, 2, 3, 4, 5]);

    let result: Vec<i32> = stream
        .filter(|x| async move { *x > 2 })  // 过滤
        .map(|x| x * 2)                      // 映射
        .take(3)                             // 取前 3 个
        .collect()                           // 收集到 Vec
        .await;

    println!("{:?}", result);  // [6, 8, 10]
}
```

### 异步运行时

```rust
// Tokio：最常用的异步运行时
#[tokio::main]
async fn main() {
    // 创建一个任务
    let handle = tokio::spawn(async {
        println!("Running in background task");
        42
    });

    // 等待任务完成
    let result = handle.await.unwrap();
    println!("Result: {}", result);
}

// 多线程运行时
#[tokio::main(flavor = "multi_thread", worker_threads = 4)]
async fn multi_thread_main() {
    // 使用 4 个工作线程的运行时
}

// 任务间通信
use tokio::sync::{mpsc, oneshot};

async fn async_channels() {
    // mpsc：多生产者单消费者
    let (tx, mut rx) = mpsc::channel(100);

    tokio::spawn(async move {
        for i in 0..10 {
            tx.send(i).await.unwrap();
        }
    });

    while let Some(msg) = rx.recv().await {
        println!("Received: {}", msg);
    }

    // oneshot：单次通信
    let (tx, rx) = oneshot::channel();

    tokio::spawn(async move {
        tx.send("Hello!").unwrap();
    });

    let msg = rx.await.unwrap();
    println!("{}", msg);
}
```
