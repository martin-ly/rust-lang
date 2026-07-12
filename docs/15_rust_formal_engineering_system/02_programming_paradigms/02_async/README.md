# 异步编程范式 {#异步编程范式}
>
> **EN**: Async Index
> **Summary**: 异步编程范式 Async Index. (stub/archive redirect)
> **分级**: [B]
> **Bloom 层级**: L5-L6
> **创建日期**: 2026-02-20
> **最后更新**: 2026-06-25（已按 Rust 1.97.0 复审）
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> 内容已整合至： [c06_async/](../../../../crates/c06_async/README.md)

> **权威来源**: 本文件为 Rust 形式化工程体系专题入口；通用 Rust 概念解释请见对应 `concept/` 权威页：
>
> - [`concept/03_advanced/01_async/01_async.md`](../../../../concept/03_advanced/01_async/01_async.md)
> - [`concept/03_advanced/01_async/04_future_and_executor_mechanisms.md`](../../../../concept/03_advanced/01_async/04_future_and_executor_mechanisms.md)
>
> 根据 AGENTS.md §3.4，`docs/` 仅保留专题工程视角内容；通用概念解释统一维护在 `concept/` 中。

[返回主索引](../../00_master_index.md)

---

## 异步编程核心概念 {#异步编程核心概念}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### Future 与异步执行 {#future-与异步执行}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

Rust 的异步（Async）编程基于 Future trait：

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

### async/await 语法 {#asyncawait-语法}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
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

### 异步状态机 {#异步状态机}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

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

### 流（Streams） {#流streams}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
use futures::stream::{self, Stream, StreamExt};

// Stream 是异步的迭代器
fn stream_example() -> impl Stream<Item = i32> {
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

### 异步运行时 {#异步运行时}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
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

### 取消与超时 {#取消与超时}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
use tokio::time::{timeout, Duration};
use tokio::select;

// 超时处理
async fn with_timeout() -> Result<String, &'static str> {
    let result = timeout(
        Duration::from_secs(5),
        fetch_data("https://slow.example.com")
    ).await;

    match result {
        Ok(Ok(data)) => Ok(data),
        Ok(Err(_)) => Err("Request failed"),
        Err(_) => Err("Timeout"),
    }
}

// 取消令牌
use tokio_util::sync::CancellationToken;

async fn cancellable_task(token: CancellationToken) {
    loop {
        select! {
            _ = token.cancelled() => {
                println!("Task cancelled, cleaning up...");
                break;
            }
            _ = tokio::time::sleep(Duration::from_secs(1)) => {
                println!("Working...");
            }
        }
    }
}

fn cancellation_demo() {
    let token = CancellationToken::new();
    let child_token = token.child_token();

    tokio::spawn(cancellable_task(child_token));

    // 稍后取消
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_secs(3)).await;
        token.cancel();
    });
}
```

### 并发控制 {#并发控制}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
use tokio::sync::Semaphore;

// 限制并发数
async fn limited_concurrency(urls: Vec<String>, max_concurrent: usize) {
    let semaphore = Arc::new(Semaphore::new(max_concurrent));

    let futures: Vec<_> = urls.into_iter().map(|url| {
        let sem = semaphore.clone();
        tokio::spawn(async move {
            let _permit = sem.acquire().await.unwrap();
            fetch_data(&url).await
        })
    }).collect();

    let results = futures::future::join_all(futures).await;
    for result in results {
        match result {
            Ok(Ok(data)) => println!("Fetched: {} bytes", data.len()),
            Ok(Err(e)) => eprintln!("Error: {}", e),
            Err(e) => eprintln!("Task panicked: {}", e),
        }
    }
}

// 批量处理
async fn batch_process<T, F, Fut>(
    items: Vec<T>,
    batch_size: usize,
    f: F,
) -> Vec<Fut::Output>
where
    F: Fn(T) -> Fut + Send + Sync + 'static,
    Fut: Future + Send + 'static,
    Fut::Output: Send,
    T: Send + 'static,
{
    let mut results = Vec::with_capacity(items.len());

    for chunk in items.chunks(batch_size) {
        let batch_futures: Vec<_> = chunk
            .iter()
            .cloned()
            .map(|item| tokio::spawn(f(item)))
            .collect();

        for handle in batch_futures {
            results.push(handle.await.unwrap());
        }
    }

    results
}
```

---

## 使用场景 {#使用场景}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 场景 | 异步模式 | 关键技术 |
| :--- | :--- | :--- |
| 高并发网络服务 | 多线程运行时（Runtime） | `tokio::main(multi_thread)` |
| 大量并发连接 | 限制并发数 | `Semaphore` |
| 长连接处理 | 取消与清理 | `CancellationToken` |
| 实时数据流 | 流处理 | `Stream`, `StreamExt` |
| 批量任务处理 | 批量并发 | `chunks` + `join_all` |
| 外部 API 调用 | 超时处理 | `timeout` |
| 背压控制 | 有界通道 | `mpsc::channel(n)` |
| 单次请求响应 | 一次性通信 | `oneshot` |

---

## 相关研究笔记 {#相关研究笔记}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 软件设计理论 {#软件设计理论}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 异步执行模型 | 异步模型理论 | [../../../12_research_notes/08_software_design_theory/04_execution_models/02_async.md](../../../12_research_notes/08_software_design_theory/04_execution_models/02_async.md) |
| 并发执行模型 | 并发模型理论 | [../../../12_research_notes/08_software_design_theory/04_execution_models/03_concurrent.md](../../../12_research_notes/08_software_design_theory/04_execution_models/03_concurrent.md) |

### 形式化方法 {#形式化方法}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 异步状态机 | 异步状态机形式化 | [../../../12_research_notes/02_formal_methods/02_async_state_machine.md](../../../12_research_notes/02_formal_methods/02_async_state_machine.md) |
| Pin 与自引用（Reference） | 自引用类型形式化 | [../../../12_research_notes/02_formal_methods/10_pin_self_referential.md](../../../12_research_notes/02_formal_methods/10_pin_self_referential.md) |
| Send/Sync 形式化 | 线程安全 trait 形式化 | [../../../12_research_notes/02_formal_methods/12_send_sync_formalization.md](../../../12_research_notes/02_formal_methods/12_send_sync_formalization.md) |

### 实验分析 {#实验分析}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 并发性能 | 并发性能测试 | [../../../12_research_notes/09_experiments/02_concurrency_performance.md](../../../12_research_notes/09_experiments/02_concurrency_performance.md) |

---

## 相关 crates {#相关-crates}

| crate | 描述 | 路径 |
| :--- | :--- | :--- |
| c06_async | 异步并发实现 | [../../../../crates/c06_async/](../../../../crates/c06_async/README.md) |
| c09_design_pattern | 异步设计模式 | [../../../../crates/c09_design_pattern/](../../../../crates/c09_design_pattern/README.md) |

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../../../../concept/00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-06-25（已按 Rust 1.97.0 复审）
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**
> **来源: [TRPL Ch. 17 - Async](https://doc.rust-lang.org/book/ch17-00-async-await.html)**
> **来源: [Tokio Documentation](https://tokio.rs/)**
> **来源: [RFC 2394 - Async/Await](https://rust-lang.github.io/rfcs/2394-async_await.html)**
> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_system)**
> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**
> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**
