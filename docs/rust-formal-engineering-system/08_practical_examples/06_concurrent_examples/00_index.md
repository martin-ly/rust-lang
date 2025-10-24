# 并发示例（Concurrent Examples）索引


## 📊 目录

- [目的](#目的)
- [核心示例](#核心示例)
  - [线程同步](#线程同步)
  - [消息传递](#消息传递)
  - [异步编程](#异步编程)
  - [无锁编程](#无锁编程)
- [实践与样例](#实践与样例)
  - [文件级清单（精选）](#文件级清单精选)
- [相关索引](#相关索引)
- [导航](#导航)


## 目的

- 提供 Rust 并发编程的实用示例。
- 展示如何编写安全高效的并发代码。

## 核心示例

### 线程同步

- 互斥锁使用示例
- 读写锁使用示例
- 条件变量示例
- 屏障同步示例

### 消息传递

- 通道通信示例
- 生产者-消费者模式
- 工作窃取模式
- 背压处理示例

### 异步编程

- Future 实现示例
- 异步流处理示例
- 异步错误处理示例
- 异步并发模式

### 无锁编程

- 原子操作示例
- 无锁数据结构
- 内存序示例
- 无锁算法实现

## 实践与样例

- 并发示例：参见 [crates/c05_threads](../../../crates/c05_threads/)
- 异步编程：[crates/c06_async](../../../crates/c06_async/)
- 分布式系统：[crates/c20_distributed](../../../crates/c20_distributed/)

### 文件级清单（精选）

- `crates/c05_threads/src/`：
  - `synchronization_examples.rs`：同步原语示例
  - `message_passing_examples.rs`：消息传递示例
  - `concurrent_patterns.rs`：并发模式示例
- `crates/c06_async/src/`：
  - `async_concurrency_examples.rs`：异步并发示例
  - `future_implementations.rs`：Future 实现示例
  - `async_streams.rs`：异步流示例

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（并发）：[`../../02_programming_paradigms/05_concurrent/00_index.md`](../../02_programming_paradigms/05_concurrent/00_index.md)
- 设计模式（并发模式）：[`../../03_design_patterns/04_concurrent/00_index.md`](../../03_design_patterns/04_concurrent/00_index.md)

## 导航

- 返回实用示例：[`../00_index.md`](../00_index.md)
- 安全示例：[`../05_security_examples/00_index.md`](../05_security_examples/00_index.md)
- 异步示例：[`../07_async_examples/00_index.md`](../07_async_examples/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
