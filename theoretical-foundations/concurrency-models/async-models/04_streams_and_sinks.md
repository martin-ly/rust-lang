# C06-04. 异步流 (Streams) 与接收器 (Sinks)

`Future` 代表一个随时间推移最终会产生的单个值。但很多时候，我们需要处理的是一系列随时间推移而产生的值，例如网络套接字的数据块、GUI 事件流或定时器滴答。

为了处理这种异步序列，Rust 生态系统引入了 `Stream` Trait，可以将其视为异步版本的 `Iterator`。本章将探讨 `Stream` 的核心概念、用法以及如何通过 `Sink` 向异步数据源发送数据。

## 1. `Stream` Trait

`Stream` Trait 由 `futures` crate 定义，是异步生态系统的基石之一。它的定义与 `Iterator` 非常相似：

```rust
use std::pin::Pin;
use std::task::{Context, Poll};

pub trait Stream {
    // Stream 产生的项目类型
    type Item;

    // 尝试从流中拉取下一个项目
    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>>;
}
```

- **`poll_next`**: 这是 `Stream` 的核心方法。当被轮询时，它会尝试产生一个值。
  - **`Poll::Ready(Some(item))`**: 表示流成功产生了一个新项目 `item`。
  - **`Poll::Ready(None)`**: 表示流已经结束，未来不会再产生任何项目。
  - **`Poll::Pending`**: 表示流目前没有新项目，但未来可能会有。它会注册 `Waker` 以便在准备好时通知执行器再次轮询。

这个模型与 `Future` 的 `poll` 方法如出一辙，使得 `Stream` 可以无缝地集成到 `async/await` 语法和执行器中。

## 2. 使用 `Stream`

虽然可以直接实现 `Stream` Trait，但在实践中，我们通常使用 `async-stream` 或 `tokio-stream` 等库提供的宏来更方便地创建流。

一个常见的任务是处理 `Stream`。`futures` crate 提供了 `StreamExt` Trait，为所有 `Stream` 类型添加了大量强大的组合子方法，类似于 `Iterator` 的适配器。

要使用这些方法，需要 `use futures::StreamExt;`。

```rust
use futures::{stream, StreamExt};

# [tokio::main]
async fn main() {
    let mut stream = stream::iter(1..=5); // 创建一个简单的流

    // 使用 `while let` 循环处理流
    while let Some(value) = stream.next().await {
        println!("Got value: {}", value);
    }

    // 使用 for_each 并发处理
    stream::iter(1..=3)
        .for_each(|x| async move {
            println!("Processing {} concurrently", x);
        })
        .await;
    
    // 使用 map 和 collect 转换流
    let doubled: Vec<_> = stream::iter(1..=3)
        .map(|x| x * 2)
        .collect()
        .await;
    
    println!("Doubled values: {:?}", doubled); // [2, 4, 6]
}
```

- **`next().await`**: 这是从 `Stream` 中获取下一个值的最基本方式。它返回一个 `Future`，当流产生一个值或结束时完成。
- **组合子**: `map`, `filter`, `fold`, `for_each` 等方法允许以声明式的方式对流进行转换和处理。

## 3. `Sink` Trait

`Sink` 是 `Stream` 的对偶概念，代表一个可以异步**接收**值的地方。它由 `futures` crate 定义，用于抽象化异步数据写入。

```rust
use std::pin::Pin;
use std::task::{Context, Poll};

pub trait Sink<Item> {
    type Error;

    // 准备好接收一个项目
    fn poll_ready(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>>;

    // 发送一个项目
    fn start_send(self: Pin<&mut Self>, item: Item) -> Result<(), Self::Error>;

    // 关闭 Sink
    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>>;
    fn poll_close(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Result<(), Self.Error>>;
}
```

- **`poll_ready`**: 检查 `Sink` 是否准备好接收新数据。如果返回 `Poll::Pending`，则表示 `Sink` 的缓冲区已满。
- **`start_send`**: 在 `poll_ready` 返回 `Poll::Ready(Ok(()))` 后，此方法将一个项目放入 `Sink` 的缓冲区。这是一个同步操作。
- **`poll_flush`**: 尝试将缓冲区中的所有数据刷新到底层 I/O。
- **`poll_close`**: 关闭 `Sink`，确保所有数据都已刷新。

`SinkExt` Trait 为 `Sink` 提供了更易于使用的方法，如 `send`。

```rust
use futures::{SinkExt, stream::iter};
use tokio::sync::mpsc;

# [tokio::main]
async fn main() {
    let (tx, mut rx) = mpsc::channel(10); // 创建一个 MPSC 通道

    // tx (sender) 是一个 Sink
    tokio::spawn(async move {
        let mut source_stream = iter(vec![1, 2, 3]);
        // 将一个流的所有项目转发到一个 Sink
        if let Err(e) = tx.send_all(&mut source_stream).await {
            println!("Failed to send: {}", e);
        }
    });

    while let Some(val) = rx.recv().await {
        println!("Received: {}", val);
    }
}
```

`send` 方法会处理 `poll_ready` 和 `start_send` 的整个流程。

## 总结

- **`Stream`**: 异步的 `Iterator`，用于处理一系列随时间推移而产生的值。`StreamExt` 提供了丰富的组合子。
- **`Sink`**: 异步的接收器，用于向异步目标发送数据。`SinkExt` 提供了便捷的发送方法。
- **生态系统**: `Stream` 和 `Sink` 是 `tokio`、`async-std` 等运行时中网络、进程间通信和定时器等功能的核心抽象。

掌握 `Stream` 和 `Sink` 是构建复杂、高效的 Rust 异步应用程序的关键一步，它使得处理连续的异步事件流变得与处理同步集合一样直观和强大。
