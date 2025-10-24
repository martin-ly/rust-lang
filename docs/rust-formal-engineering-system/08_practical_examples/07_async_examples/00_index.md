# 异步示例（Async Examples）索引


## 📊 目录

- [异步示例（Async Examples）索引](#异步示例async-examples索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心示例](#核心示例)
    - [异步基础](#异步基础)
    - [异步并发](#异步并发)
    - [异步 I/O](#异步-io)
    - [异步流处理](#异步流处理)
  - [实践与样例](#实践与样例)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)


## 目的

- 提供 Rust 异步编程的实用示例。
- 展示如何编写高效的异步代码。

## 核心示例

### 异步基础

- async/await 使用示例
- Future 实现示例
- 异步函数示例
- 异步闭包示例

### 异步并发

- 异步任务管理
- 异步通道通信
- 异步同步原语
- 异步错误处理

### 异步 I/O

- 异步文件操作
- 异步网络编程
- 异步数据库操作
- 异步 HTTP 客户端

### 异步流处理

- 异步迭代器
- 异步流处理
- 背压处理
- 流式数据处理

## 实践与样例

- 异步示例：参见 [crates/c06_async](../../../crates/c06_async/)
- 网络编程：[crates/c10_networks](../../../crates/c10_networks/)
- 微服务：[crates/c13_microservice](../../../crates/c13_microservice/)

### 文件级清单（精选）

- `crates/c06_async/src/`：
  - `async_basics.rs`：异步基础示例
  - `async_concurrency.rs`：异步并发示例
  - `async_io_examples.rs`：异步 I/O 示例
  - `async_streams.rs`：异步流示例
- `crates/c10_networks/src/`：
  - `async_network_examples.rs`：异步网络示例
  - `async_http_client.rs`：异步 HTTP 客户端
  - `async_websocket.rs`：异步 WebSocket

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（异步）：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- 设计模式（异步模式）：[`../../03_design_patterns/04_concurrent/00_index.md`](../../03_design_patterns/04_concurrent/00_index.md)

## 导航

- 返回实用示例：[`../00_index.md`](../00_index.md)
- 并发示例：[`../06_concurrent_examples/00_index.md`](../06_concurrent_examples/00_index.md)
- Web 示例：[`../08_web_examples/00_index.md`](../08_web_examples/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
