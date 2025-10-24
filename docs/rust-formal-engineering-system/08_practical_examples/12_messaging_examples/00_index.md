# 消息队列示例（Messaging Examples）索引

## 📊 目录

- [消息队列示例（Messaging Examples）索引](#消息队列示例messaging-examples索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心示例](#核心示例)
    - [消息队列系统](#消息队列系统)
    - [消息传递模式](#消息传递模式)
    - [消息处理](#消息处理)
    - [可靠性保证](#可靠性保证)
  - [实践与样例](#实践与样例)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 提供 Rust 消息队列开发的实用示例。
- 展示如何构建可靠的消息传递系统。

## 核心示例

### 消息队列系统

- RabbitMQ 集成示例
- Apache Kafka 集成示例
- Redis 消息队列示例
- 内存消息队列示例

### 消息传递模式

- 发布-订阅模式
- 点对点消息传递
- 请求-响应模式
- 消息路由示例

### 消息处理

- 消息序列化示例
- 消息反序列化示例
- 消息验证示例
- 错误处理示例

### 可靠性保证

- 消息确认机制
- 重试机制示例
- 死信队列示例
- 消息持久化示例

## 实践与样例

- 消息队列示例：参见 [crates/c80_messaging](../../../crates/c80_messaging/)
- 消息传递：[crates/c81_message_passing](../../../crates/c81_message_passing/)
- 事件驱动：[crates/c82_event_driven](../../../crates/c82_event_driven/)

### 文件级清单（精选）

- `crates/c80_messaging/src/`：
  - `message_queues.rs`：消息队列示例
  - `message_patterns.rs`：消息传递模式示例
  - `message_processing.rs`：消息处理示例
  - `reliability_guarantees.rs`：可靠性保证示例
- `crates/c81_message_passing/src/`：
  - `async_messaging.rs`：异步消息传递示例
  - `message_routing.rs`：消息路由示例
  - `message_batching.rs`：消息批处理示例

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（异步）：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- 设计模式（消息传递模式）：[`../../03_design_patterns/04_concurrent/00_index.md`](../../03_design_patterns/04_concurrent/00_index.md)

## 导航

- 返回实用示例：[`../00_index.md`](../00_index.md)
- 数据库示例：[`../11_database_examples/00_index.md`](../11_database_examples/00_index.md)
- 可观测性示例：[`../13_observability_examples/00_index.md`](../13_observability_examples/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
