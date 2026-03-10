# Rust 1.94: 生成器与异步编程深度整合

> **Rust 版本**: 1.94.0
> **Edition**: 2024
> **最后更新**: 2026-03-10

---

## 目录

- [Rust 1.94: 生成器与异步编程深度整合](#rust-194-生成器与异步编程深度整合)
  - [目录](#目录)
  - [生成器基础](#生成器基础)
    - [1.1 gen 关键字](#11-gen-关键字)
    - [1.2 生成器与所有权](#12-生成器与所有权)
  - [异步生成器](#异步生成器)
    - [2.1 基础异步生成器](#21-基础异步生成器)
    - [2.2 异步生成器与 Pin](#22-异步生成器与-pin)
  - [与 Stream 的整合](#与-stream-的整合)
    - [3.1 生成器到 Stream 的转换](#31-生成器到-stream-的转换)
    - [3.2 Stream 适配器](#32-stream-适配器)
  - [实战模式](#实战模式)
    - [4.1 异步分页加载](#41-异步分页加载)
    - [4.2 实时数据处理管道](#42-实时数据处理管道)
    - [4.3 WebSocket 消息流](#43-websocket-消息流)
  - [性能优化](#性能优化)
    - [5.1 生成器与迭代器对比](#51-生成器与迭代器对比)
  - [相关文档](#相关文档)

---

## 生成器基础

### 1.1 gen 关键字

Rust 1.94 引入了 `gen` 关键字，允许创建惰性求值的序列：

```rust
#![feature(gen_blocks)]

/// 基础生成器
fn simple_generator() -> impl Iterator<Item = i32> {
    gen {
        yield 1;
        yield 2;
        yield 3;
    }
}

/// 无限序列生成器
fn fibonacci() -> impl Iterator<Item = u64> {
    gen {
        let (mut a, mut b) = (0, 1);
        loop {
            yield a;
            (a, b) = (b, a + b);
        }
    }
}

/// 带状态的生成器
fn stateful_generator(seed: i32) -> impl Iterator<Item = i32> {
    gen {
        let mut current = seed;
        loop {
            current = current.wrapping_mul(1103515245).wrapping_add(12345);
            yield current;
        }
    }
}
```

### 1.2 生成器与所有权

```rust
#![feature(gen_blocks)]

/// 转移所有权的生成器
fn into_lines(text: String) -> impl Iterator<Item = String> {
    gen {
        for line in text.lines() {
            yield line.to_string();
        }
        // text 在这里被释放
    }
}

/// 借用生成器
fn borrowed_tokens(text: &str) -> impl Iterator<Item = &str> + use<'_> {
    gen {
        for token in text.split_whitespace() {
            yield token;
        }
    }
}

/// 复杂的所有权模式
fn chunk_generator(
    data: Vec<u8>,
    chunk_size: usize
) -> impl Iterator<Item = Vec<u8>> + use<> {
    gen {
        let mut start = 0;
        while start < data.len() {
            let end = (start + chunk_size).min(data.len());
            yield data[start..end].to_vec();
            start = end;
        }
    }
}
```

---

## 异步生成器

### 2.1 基础异步生成器

```rust
#![feature(async_gen_blocks)]

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

/// 异步数据流生成器
async fn async_stream_data() -> impl Iterator<Item = Result<String, std::io::Error>> {
    gen {
        for i in 0..10 {
            // 模拟异步 I/O
            tokio::time::sleep(std::time::Duration::from_millis(10)).await;

            if i == 5 {
                yield Err(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    "Simulated error"
                ));
            } else {
                yield Ok(format!("Data chunk {}", i));
            }
        }
    }
}

/// 带背压的异步生成器
async fn backpressure_stream(
    receiver: tokio::sync::mpsc::Receiver<i32>
) -> impl Iterator<Item = i32> {
    gen {
        let mut receiver = receiver;
        while let Some(value) = receiver.recv().await {
            yield value;
            // 自动处理背压：如果消费慢，recv().await 会等待
        }
    }
}
```

### 2.2 异步生成器与 Pin

```rust
#![feature(async_gen_blocks)]

use std::pin::Pin;
use std::marker::PhantomPinned;

/// 自引用异步生成器
pub struct SelfReferencingStream {
    data: Vec<u8>,
    position: usize,
    _pin: PhantomPinned,
}

impl SelfReferencingStream {
    pub fn new(data: Vec<u8>) -> Pin<Box<Self>> {
        Box::pin(Self {
            data,
            position: 0,
            _pin: PhantomPinned,
        })
    }

    /// 生成下一个块
    pub async fn next_chunk(self: Pin<&mut Self>) -> Option<&[u8]> {
        let this = unsafe { self.get_unchecked_mut() };

        if this.position >= this.data.len() {
            return None;
        }

        let start = this.position;
        let end = (start + 1024).min(this.data.len());
        this.position = end;

        // 模拟异步处理
        tokio::task::yield_now().await;

        Some(&this.data[start..end])
    }
}

/// 将自引用结构包装为生成器
fn pinned_stream(
    data: Vec<u8>
) -> impl Future<Output = impl Iterator<Item = Vec<u8>>> {
    async move {
        let mut stream = SelfReferencingStream::new(data);

        gen {
            while let Some(chunk) = stream.as_mut().next_chunk().await {
                yield chunk.to_vec();
            }
        }
    }
}
```

---

## 与 Stream 的整合

### 3.1 生成器到 Stream 的转换

```rust
#![feature(gen_blocks)]
#![feature(async_gen_blocks)]

use futures::stream::{Stream, StreamExt};
use std::pin::Pin;
use std::task::{Context, Poll};

/// 将生成器转换为 Stream
pub struct GeneratorStream<T> {
    iterator: std::cell::RefCell<dyn Iterator<Item = T>>,
}

impl<T> Stream for GeneratorStream<T> {
    type Item = T;

    fn poll_next(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Option<T>> {
        match self.iterator.borrow_mut().next() {
            Some(item) => Poll::Ready(Some(item)),
            None => Poll::Ready(None),
        }
    }
}

/// 使用 gen 创建 Stream
fn generator_as_stream() -> impl Stream<Item = i32> {
    async_gen {
        for i in 0..100 {
            tokio::time::sleep(std::time::Duration::from_millis(1)).await;
            yield i;
        }
    }
}

/// 组合多个生成器
fn combined_stream() -> impl Stream<Item = String> {
    async_gen {
        let numbers = gen {
            for i in 0..10 {
                yield format!("Number: {}", i);
            }
        };

        let letters = gen {
            for c in 'a'..='z' {
                yield format!("Letter: {}", c);
            }
        };

        // 交错生成
        let mut numbers = numbers;
        let mut letters = letters;

        loop {
            match (numbers.next(), letters.next()) {
                (Some(n), Some(l)) => {
                    yield n;
                    yield l;
                }
                (Some(n), None) => yield n,
                (None, Some(l)) => yield l,
                (None, None) => break,
            }
        }
    }
}
```

### 3.2 Stream 适配器

```rust
#![feature(async_gen_blocks)]

use futures::stream::Stream;

/// 批量处理 Stream 中的元素
fn batch_stream<S, T>(
    stream: S,
    batch_size: usize
) -> impl Stream<Item = Vec<T>>
where
    S: Stream<Item = T>,
{
    async_gen {
        use futures::stream::StreamExt;
        let mut stream = stream;
        let mut batch = Vec::with_capacity(batch_size);

        while let Some(item) = stream.next().await {
            batch.push(item);

            if batch.len() >= batch_size {
                yield batch;
                batch = Vec::with_capacity(batch_size);
            }
        }

        if !batch.is_empty() {
            yield batch;
        }
    }
}

/// 带超时的 Stream
fn timeout_stream<S, T>(
    stream: S,
    duration: std::time::Duration
) -> impl Stream<Item = Result<T, tokio::time::error::Elapsed>>
where
    S: Stream<Item = T>,
{
    async_gen {
        use futures::stream::StreamExt;
        let mut stream = stream;

        while let Some(item) = stream.next().await {
            match tokio::time::timeout(duration, async { item }).await {
                Ok(value) => yield Ok(value),
                Err(e) => yield Err(e),
            }
        }
    }
}
```

---

## 实战模式

### 4.1 异步分页加载

```rust
#![feature(async_gen_blocks)]

use std::future::Future;

/// 异步分页数据加载器
pub struct AsyncPaginator<T, F> {
    fetch_page: F,
    _phantom: std::marker::PhantomData<T>,
}

impl<T, F, Fut> AsyncPaginator<T, F>
where
    F: Fn(usize) -> Fut,
    Fut: Future<Output = Vec<T>>,
{
    pub fn new(fetch_page: F) -> Self {
        Self {
            fetch_page,
            _phantom: std::marker::PhantomData,
        }
    }

    /// 加载所有页面
    pub fn load_all(&self) -> impl Future<Output = impl Iterator<Item = T>> + use<T, F> {
        let fetch = &self.fetch_page;

        async move {
            gen {
                let mut page = 0;
                loop {
                    let items = fetch(page).await;
                    if items.is_empty() {
                        break;
                    }
                    for item in items {
                        yield item;
                    }
                    page += 1;
                }
            }
        }
    }

    /// 加载直到满足条件
    pub fn load_until<P>(
        &self,
        predicate: P
    ) -> impl Future<Output = impl Iterator<Item = T>> + use<T, F, P>
    where
        P: Fn(&T) -> bool,
    {
        let fetch = &self.fetch_page;

        async move {
            gen {
                let mut page = 0;
                'outer: loop {
                    let items = fetch(page).await;
                    if items.is_empty() {
                        break;
                    }
                    for item in items {
                        if predicate(&item) {
                            break 'outer;
                        }
                        yield item;
                    }
                    page += 1;
                }
            }
        }
    }
}

// 使用示例
async fn example_usage() {
    let paginator = AsyncPaginator::new(|page| async move {
        // 模拟 API 调用
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;

        if page >= 5 {
            vec![]
        } else {
            (0..10).map(|i| format!("Page {}, Item {}", page, i)).collect()
        }
    });

    // 加载所有数据
    let all_items: Vec<String> = paginator.load_all().await.take(25).collect();
    println!("Loaded {} items", all_items.len());
}
```

### 4.2 实时数据处理管道

```rust
#![feature(async_gen_blocks)]

use tokio::sync::mpsc;

/// 实时数据处理管道
pub struct DataPipeline<T> {
    input: mpsc::Receiver<T>,
}

impl<T: Send + 'static> DataPipeline<T> {
    pub fn new(input: mpsc::Receiver<T>) -> Self {
        Self { input }
    }

    /// 处理管道：过滤 -> 转换 -> 批处理
    pub fn process<F, U>(
        mut self,
        filter: impl Fn(&T) -> bool + Send + 'static,
        transform: impl Fn(T) -> U + Send + 'static,
        batch_size: usize,
    ) -> impl Stream<Item = Vec<U>>
    where
        F: Future<Output = ()>,
        U: Send + 'static,
    {
        async_gen {
            let mut batch = Vec::with_capacity(batch_size);

            while let Some(item) = self.input.recv().await {
                // 过滤
                if !filter(&item) {
                    continue;
                }

                // 转换
                let transformed = transform(item);
                batch.push(transformed);

                // 批处理
                if batch.len() >= batch_size {
                    yield batch;
                    batch = Vec::with_capacity(batch_size);
                }
            }

            // 剩余数据
            if !batch.is_empty() {
                yield batch;
            }
        }
    }
}

/// 使用示例
async fn pipeline_example() {
    let (tx, rx) = mpsc::channel(100);

    // 启动生产者
    tokio::spawn(async move {
        for i in 0..1000 {
            tx.send(i).await.unwrap();
        }
    });

    // 创建管道
    let pipeline = DataPipeline::new(rx);

    // 处理：过滤偶数，乘以2，每批10个
    let mut processed = pipeline.process(
        |n| n % 2 == 0,
        |n| n * 2,
        10
    );

    while let Some(batch) = processed.next().await {
        println!("Processed batch: {:?}", batch);
    }
}
```

### 4.3 WebSocket 消息流

```rust
#![feature(async_gen_blocks)]

use futures::{SinkExt, StreamExt};
use tokio_tungstenite::{connect_async, tungstenite::protocol::Message};

/// WebSocket 消息流
async fn websocket_stream(
    url: &str
) -> Result<impl Iterator<Item = Message>, Box<dyn std::error::Error>> {
    let (ws_stream, _) = connect_async(url).await?;
    let (mut write, mut read) = ws_stream.split();

    // 发送订阅消息
    write.send(Message::Text(r#"{"subscribe": "all"}"#.to_string())).await?;

    Ok(gen {
        while let Some(msg) = read.next().await {
            match msg {
                Ok(message) => {
                    if message.is_close() {
                        break;
                    }
                    yield message;
                }
                Err(e) => {
                    eprintln!("WebSocket error: {}", e);
                    break;
                }
            }
        }
    })
}

/// 带重连的 WebSocket 流
async fn resilient_websocket_stream(
    url: String,
    retry_delay: std::time::Duration
) -> impl Stream<Item = Message> {
    async_gen {
        loop {
            match websocket_stream(&url).await {
                Ok(stream) => {
                    for msg in stream {
                        yield msg;
                    }
                }
                Err(e) => {
                    eprintln!("Connection failed: {}, retrying...", e);
                }
            }

            tokio::time::sleep(retry_delay).await;
        }
    }
}
```

---

## 性能优化

### 5.1 生成器与迭代器对比

```rust
#![feature(gen_blocks)]

/// 基准测试：生成器 vs 迭代器
mod benchmarks {
    /// 传统迭代器实现
    fn iterator_approach(n: usize) -> impl Iterator<Item = usize> {
        (0..n).map(|i| i * i)
    }

    /// 生成器实现
    fn generator_approach(n: usize) -> impl Iterator<Item = usize> {
        gen {
            for i in 0..n {
                yield i * i;
            }
        }
    }

    /// 性能对比：
    /// - 优化后的生成器与迭代器性能相当
    /// - 生成器代码更清晰，适合复杂逻辑
    /// - 迭代器链更适合简单转换
}
```

---

## 相关文档

- [Rust 1.94 发布说明](../../../docs/06_toolchain/16_rust_1.94_release_notes.md)
- [C06 异步主索引](../00_MASTER_INDEX.md)
- [生成器 RFC](https://rust-lang.github.io/rfcs/2996-generator-capture-mutable.html)
- [async/await 指南](../tier_02_guides/01_async_await_guide.md)
