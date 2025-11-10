# 消息队列示例（Messaging Examples）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [消息队列示例（Messaging Examples）索引](#消息队列示例messaging-examples索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心示例](#-核心示例)
    - [1. 消息队列系统（Message Queue Systems）](#1-消息队列系统message-queue-systems)
    - [2. 消息传递模式（Message Passing Patterns）](#2-消息传递模式message-passing-patterns)
    - [3. 消息处理（Message Processing）](#3-消息处理message-processing)
    - [4. 可靠性保证（Reliability Guarantees）](#4-可靠性保证reliability-guarantees)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [文件级清单（精选）](#文件级清单精选)
      - [`crates/c80_messaging/src/`](#cratesc80_messagingsrc)
      - [`crates/c81_message_passing/src/`](#cratesc81_message_passingsrc)
    - [快速开始示例](#快速开始示例)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块提供 Rust 消息队列开发的实用示例，涵盖消息队列系统、消息传递模式、消息处理和可靠性保证等核心主题。所有示例均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **消息队列开发**: 专注于消息队列应用开发实践
- **最佳实践**: 基于 Rust 社区最新消息队列实践
- **完整覆盖**: 涵盖多个消息队列场景
- **易于理解**: 提供详细的消息队列开发说明和代码示例

## 📚 核心示例

### 1. 消息队列系统（Message Queue Systems）

**推荐库**: `lapin`, `rdkafka`, `redis`, `flume`

- **RabbitMQ 集成**: RabbitMQ 消息队列操作
- **Apache Kafka 集成**: Kafka 消息队列操作
- **Redis 消息队列**: Redis 消息队列操作
- **内存消息队列**: 内存消息队列实现

**相关资源**:

- [lapin 文档](https://docs.rs/lapin/)
- [rdkafka 文档](https://docs.rs/rdkafka/)
- [redis 文档](https://docs.rs/redis/)
- [flume 文档](https://docs.rs/flume/)

### 2. 消息传递模式（Message Passing Patterns）

**推荐库**: `lapin`, `rdkafka`, `flume`, `crossbeam-channel`

- **发布-订阅模式**: 发布者-订阅者模式实现
- **点对点消息传递**: 点对点消息传递实现
- **请求-响应模式**: 请求-响应模式实现
- **消息路由**: 消息路由、消息过滤

**相关资源**:

- [lapin 文档](https://docs.rs/lapin/)
- [rdkafka 文档](https://docs.rs/rdkafka/)
- [flume 文档](https://docs.rs/flume/)
- [crossbeam-channel 文档](https://docs.rs/crossbeam-channel/)

### 3. 消息处理（Message Processing）

**推荐库**: `serde`, `bincode`, `rmp-serde`, `validator`

- **消息序列化**: JSON、MessagePack、Bincode 序列化
- **消息反序列化**: 消息反序列化、类型转换
- **消息验证**: 消息格式验证、数据验证
- **错误处理**: 消息处理错误、重试机制

**相关资源**:

- [serde 文档](https://serde.rs/)
- [bincode 文档](https://docs.rs/bincode/)
- [rmp-serde 文档](https://docs.rs/rmp-serde/)
- [validator 文档](https://docs.rs/validator/)

### 4. 可靠性保证（Reliability Guarantees）

**推荐库**: `lapin`, `rdkafka`, `flume`

- **消息确认机制**: 消息确认、ACK 机制
- **重试机制**: 消息重试、指数退避
- **死信队列**: 死信队列、错误处理
- **消息持久化**: 消息持久化、数据恢复

**相关资源**:

- [lapin 文档](https://docs.rs/lapin/)
- [rdkafka 文档](https://docs.rs/rdkafka/)
- [flume 文档](https://docs.rs/flume/)

## 💻 实践与样例

### 代码示例位置

- **消息队列示例**: [crates/c80_messaging](../../../crates/c80_messaging/)
- **消息传递**: [crates/c81_message_passing](../../../crates/c81_message_passing/)
- **事件驱动**: [crates/c82_event_driven](../../../crates/c82_event_driven/)

### 文件级清单（精选）

#### `crates/c80_messaging/src/`

- `message_queues.rs` - 消息队列示例
- `message_patterns.rs` - 消息传递模式示例
- `message_processing.rs` - 消息处理示例
- `reliability_guarantees.rs` - 可靠性保证示例

#### `crates/c81_message_passing/src/`

- `async_messaging.rs` - 异步消息传递示例
- `message_routing.rs` - 消息路由示例
- `message_batching.rs` - 消息批处理示例

### 快速开始示例

```rust
// RabbitMQ 消息队列示例
use lapin::{Connection, ConnectionProperties, Result};
use lapin::options::*;
use lapin::types::FieldTable;

#[tokio::main]
async fn main() -> Result<()> {
    let conn = Connection::connect(
        "amqp://guest:guest@localhost:5672/%2f",
        ConnectionProperties::default(),
    ).await?;

    let channel = conn.create_channel().await?;

    channel.queue_declare(
        "hello",
        QueueDeclareOptions::default(),
        FieldTable::default(),
    ).await?;

    channel.basic_publish(
        "",
        "hello",
        BasicPublishOptions::default(),
        b"Hello, World!",
        BasicProperties::default(),
    ).await?;

    Ok(())
}
```

```rust
// Redis 消息队列示例
use redis::Commands;

fn main() -> redis::RedisResult<()> {
    let client = redis::Client::open("redis://127.0.0.1/")?;
    let mut con = client.get_connection()?;

    con.lpush("queue", "message")?;
    let message: String = con.rpop("queue", None)?;

    println!("收到消息: {}", message);
    Ok(())
}
```

---

## 🔗 相关索引

- **理论基础（并发模型）**: [`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- **编程范式（异步）**: [`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- **设计模式（消息传递模式）**: [`../../03_design_patterns/04_concurrent/00_index.md`](../../03_design_patterns/04_concurrent/00_index.md)

---

## 🧭 导航

- **返回实用示例**: [`../00_index.md`](../00_index.md)
- **数据库示例**: [`../11_database_examples/00_index.md`](../11_database_examples/00_index.md)
- **可观测性示例**: [`../13_observability_examples/00_index.md`](../13_observability_examples/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
