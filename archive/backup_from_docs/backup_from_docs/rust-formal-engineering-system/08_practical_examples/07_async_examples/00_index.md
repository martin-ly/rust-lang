# 异步示例（Async Examples）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [异步示例（Async Examples）索引](#异步示例async-examples索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心示例](#-核心示例)
    - [1. 异步基础（Async Basics）](#1-异步基础async-basics)
    - [2. 异步并发（Async Concurrency）](#2-异步并发async-concurrency)
    - [3. 异步 I/O（Async I/O）](#3-异步-ioasync-io)
    - [4. 异步流处理（Async Stream Processing）](#4-异步流处理async-stream-processing)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [文件级清单（精选）](#文件级清单精选)
      - [`crates/c06_async/src/`](#cratesc06_asyncsrc)
      - [`crates/c10_networks/src/`](#cratesc10_networkssrc)
    - [快速开始示例](#快速开始示例)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块提供 Rust 异步编程的实用示例，涵盖异步基础、异步并发、异步 I/O 和异步流处理等核心主题。
所有示例均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **异步高效**: 专注于异步编程实践
- **最佳实践**: 基于 Rust 社区最新异步实践
- **完整覆盖**: 涵盖多个异步场景
- **易于理解**: 提供详细的异步说明和代码示例

## 📚 核心示例

### 1. 异步基础（Async Basics）

**推荐库**: `tokio`, `async-std`, `futures`, `async-trait`

- **async/await 使用**: `async` 函数和 `await` 关键字
- **Future 实现**: 自定义 Future 类型实现
- **异步函数**: 异步函数定义和调用
- **异步闭包**: 异步闭包使用

**相关资源**:

- [Rust Book - Async](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [Tokio 教程](https://tokio.rs/tokio/tutorial)
- [async-std 文档](https://docs.rs/async-std/)

### 2. 异步并发（Async Concurrency）

**推荐库**: `tokio`, `futures`, `async-channel`

- **异步任务管理**: 任务生成、任务等待
- **异步通道通信**: 异步通道、多生产者多消费者
- **异步同步原语**: 异步互斥锁、异步读写锁
- **异步错误处理**: 异步环境下的错误处理

**相关资源**:

- [Tokio 文档](https://tokio.rs/)
- [futures 文档](https://docs.rs/futures/)
- [async-channel 文档](https://docs.rs/async-channel/)

### 3. 异步 I/O（Async I/O）

**推荐库**: `tokio`, `async-std`, `tokio-util`

- **异步文件操作**: 异步文件读写、文件系统操作
- **异步网络编程**: TCP/UDP 异步编程
- **异步数据库操作**: 异步数据库客户端
- **异步 HTTP 客户端**: HTTP 请求、响应处理

**相关资源**:

- [Tokio I/O](https://tokio.rs/tokio/tutorial/io)
- [async-std I/O](https://docs.rs/async-std/)
- [tokio-util 文档](https://docs.rs/tokio-util/)

### 4. 异步流处理（Async Stream Processing）

**推荐库**: `futures`, `tokio-stream`, `async-stream`

- **异步迭代器**: `AsyncIterator` trait 使用
- **异步流处理**: `Stream` trait 和流处理
- **背压处理**: 背压、流量控制
- **流式数据处理**: 流式数据处理、管道操作

**相关资源**:

- [futures Stream](https://docs.rs/futures/latest/futures/stream/index.html)
- [tokio-stream 文档](https://docs.rs/tokio-stream/)
- [async-stream 文档](https://docs.rs/async-stream/)

## 💻 实践与样例

### 代码示例位置

- **异步示例**: [crates/c06_async](../../../crates/c06_async/)
- **网络编程**: [crates/c10_networks](../../../crates/c10_networks/)
- **微服务**: [crates/c13_microservice](../../../crates/c13_microservice/)

### 文件级清单（精选）

#### `crates/c06_async/src/`

- `async_basics.rs` - 异步基础示例
- `async_concurrency.rs` - 异步并发示例
- `async_io_examples.rs` - 异步 I/O 示例
- `async_streams.rs` - 异步流示例

#### `crates/c10_networks/src/`

- `async_network_examples.rs` - 异步网络示例
- `async_http_client.rs` - 异步 HTTP 客户端
- `async_websocket.rs` - 异步 WebSocket

### 快速开始示例

```rust
// 异步基础示例
use tokio;

#[tokio::main]
async fn main() {
    println!("异步函数调用");
    let result = async_function().await;
    println!("结果: {}", result);
}

async fn async_function() -> i32 {
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    42
}
```

```rust
// 异步并发示例
use tokio;
use std::time::Duration;

#[tokio::main]
async fn main() {
    let mut handles = vec![];

    for i in 0..10 {
        let handle = tokio::spawn(async move {
            tokio::time::sleep(Duration::from_millis(100)).await;
            println!("任务 {} 完成", i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await.unwrap();
    }
}
```

---

## 🔗 相关索引

- **理论基础（并发模型）**: [`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- **编程范式（异步）**: [`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- **设计模式（异步模式）**: [`../../03_design_patterns/04_concurrent/00_index.md`](../../03_design_patterns/04_concurrent/00_index.md)

---

## 🧭 导航

- **返回实用示例**: [`../00_index.md`](../00_index.md)
- **并发示例**: [`../06_concurrent_examples/00_index.md`](../06_concurrent_examples/00_index.md)
- **Web 示例**: [`../08_web_examples/00_index.md`](../08_web_examples/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
