# 消息队列

> **核心库**: rdkafka, lapin, async-nats, pulsar-rs  
> **适用场景**: 分布式消息、事件驱动、异步通信、流处理、微服务解耦

---

## 📋 目录

- [消息队列](#消息队列)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [消息队列概念](#消息队列概念)
    - [为什么需要消息队列](#为什么需要消息队列)
    - [消息模式对比](#消息模式对比)
  - [核心库对比](#核心库对比)
    - [功能矩阵](#功能矩阵)
    - [选择指南](#选择指南)
    - [性能对比](#性能对比)
  - [rdkafka - Kafka 客户端](#rdkafka---kafka-客户端)
    - [核心特性](#核心特性)
    - [生产者](#生产者)
      - [基础用法：异步生产者](#基础用法异步生产者)
      - [高级用法：批量发送](#高级用法批量发送)
    - [消费者](#消费者)
      - [基础用法：消费者组](#基础用法消费者组)
      - [高级用法：手动提交 offset](#高级用法手动提交-offset)
    - [流处理](#流处理)
      - [窗口聚合示例](#窗口聚合示例)
  - [lapin - RabbitMQ 客户端](#lapin---rabbitmq-客户端)
    - [核心特性1](#核心特性1)
    - [基础用法](#基础用法)
      - [生产者和消费者](#生产者和消费者)
      - [消费者（工作队列）](#消费者工作队列)
    - [工作队列模式](#工作队列模式)
    - [发布订阅模式](#发布订阅模式)
  - [async-nats - NATS 客户端](#async-nats---nats-客户端)
    - [核心特性2](#核心特性2)
    - [发布订阅](#发布订阅)
      - [基础用法1](#基础用法1)
      - [订阅消息](#订阅消息)
    - [请求响应](#请求响应)
    - [JetStream 持久化](#jetstream-持久化)
  - [实战场景](#实战场景)
    - [场景1: 订单处理系统](#场景1-订单处理系统)
    - [场景2: 实时日志聚合](#场景2-实时日志聚合)
    - [场景3: 微服务事件总线](#场景3-微服务事件总线)
  - [最佳实践](#最佳实践)
    - [1. 消息幂等性处理](#1-消息幂等性处理)
    - [2. 错误处理和重试](#2-错误处理和重试)
    - [3. 消费者组配置](#3-消费者组配置)
    - [4. 消息压缩](#4-消息压缩)
    - [5. 监控和可观测性](#5-监控和可观测性)
  - [常见陷阱](#常见陷阱)
    - [⚠️ 陷阱1: Kafka offset 提交错误](#️-陷阱1-kafka-offset-提交错误)
    - [⚠️ 陷阱2: RabbitMQ 不确认消息导致内存泄漏](#️-陷阱2-rabbitmq-不确认消息导致内存泄漏)
    - [⚠️ 陷阱3: 消息顺序性误解](#️-陷阱3-消息顺序性误解)
    - [⚠️ 陷阱4: 消息堆积未监控](#️-陷阱4-消息堆积未监控)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [教程与文章](#教程与文章)
    - [示例项目](#示例项目)
    - [相关文档](#相关文档)

---

## 概述

### 消息队列概念

消息队列（Message Queue, MQ）是分布式系统中异步通信的核心组件，用于解耦服务、缓冲流量、保证消息可靠性。

**核心概念**:

```text
┌─────────────┐    发送消息    ┌─────────────┐    消费消息    ┌─────────────┐
│  生产者     │ ──────────────> │  消息队列    │ ──────────────> │  消费者     │
│ (Producer)  │                │   (Broker)   │                │ (Consumer)  │
└─────────────┘                └─────────────┘                └─────────────┘
      │                              │                              │
      │                              │                              │
      ▼                              ▼                              ▼
  发送确认 (ACK)              持久化存储                      消息确认 (ACK)
```

**关键术语**:

- **Topic/Queue**: 消息主题或队列，消息的逻辑分类
- **Producer**: 生产者，发送消息的应用
- **Consumer**: 消费者，接收消息的应用
- **Broker**: 消息代理，存储和转发消息的服务器
- **Partition**: 分区，用于水平扩展的消息子集（Kafka）
- **Consumer Group**: 消费者组，实现负载均衡和容错

### 为什么需要消息队列

1. **异步解耦**: 生产者和消费者独立演进，不需要同步等待
2. **削峰填谷**: 缓冲突发流量，保护下游服务
3. **可靠性**: 消息持久化，确保不丢失
4. **扩展性**: 通过分区和消费者组实现水平扩展
5. **顺序保证**: 在分区内保证消息顺序（Kafka）

**使用场景**:

- 订单处理、支付通知
- 日志聚合、指标收集
- 事件溯源、CQRS
- 数据管道、ETL
- 微服务解耦、事件驱动架构

### 消息模式对比

| 模式 | 描述 | 适用场景 | 实现 |
|------|------|---------|------|
| **点对点 (P2P)** | 一条消息只被一个消费者消费 | 任务分发、工作队列 | RabbitMQ Queue, Kafka Consumer Group |
| **发布订阅 (Pub/Sub)** | 一条消息被多个订阅者消费 | 事件广播、通知系统 | RabbitMQ Exchange, Kafka Topic, NATS |
| **请求响应 (Req/Reply)** | 同步或异步的RPC模式 | API网关、微服务调用 | RabbitMQ RPC, NATS Request |
| **流处理 (Streaming)** | 连续处理消息流 | 实时分析、窗口聚合 | Kafka Streams |

---

## 核心库对比

### 功能矩阵

| 特性 | rdkafka | lapin | async-nats | pulsar-rs | 说明 |
|------|---------|-------|------------|-----------|------|
| **协议** | Kafka | AMQP 0.9.1 | NATS | Pulsar | 底层协议 |
| **异步支持** | ✅ Tokio | ✅ Tokio | ✅ Tokio | ✅ Tokio | 全异步 |
| **持久化** | ✅ 强 | ✅ | 可选 (JetStream) | ✅ | Kafka 最强 |
| **顺序保证** | ✅ 分区内 | 有限 | ❌ | ✅ | Kafka 严格顺序 |
| **分区** | ✅ | ❌ | ❌ | ✅ | 水平扩展 |
| **消费者组** | ✅ | ❌ | ✅ Queue Group | ✅ | 负载均衡 |
| **流处理** | ✅ | ❌ | ❌ | 部分 | Kafka 最佳 |
| **消息路由** | 简单 | ✅ Exchange | ✅ Subject | ✅ | RabbitMQ 最灵活 |
| **吞吐量** | 极高 | 中等 | 高 | 高 | Kafka >100MB/s |
| **延迟** | 中等 (ms) | 低 (μs) | 极低 (μs) | 中等 | NATS 最快 |
| **跨平台** | ✅ | ✅ | ✅ | ✅ | 都支持 |

### 选择指南

| 场景 | 推荐库 | 理由 |
|------|--------|------|
| **大规模日志/事件流** | rdkafka (Kafka) | 高吞吐、持久化、顺序保证 |
| **实时分析/流处理** | rdkafka (Kafka) | Kafka Streams、窗口聚合 |
| **微服务解耦** | async-nats (NATS) | 轻量、低延迟、易部署 |
| **复杂消息路由** | lapin (RabbitMQ) | Exchange、Binding、灵活路由 |
| **任务队列/工作分发** | lapin (RabbitMQ) | 工作队列、优先级、死信队列 |
| **请求响应模式** | async-nats (NATS) | 内置 Request/Reply |
| **跨数据中心同步** | pulsar-rs (Pulsar) | 地理复制、多租户 |
| **高性能 + 持久化** | rdkafka (Kafka) | 两者兼顾 |

### 性能对比

**基准测试环境**:

- CPU: 8核 Intel Xeon
- 内存: 32GB
- 网络: 1Gbps
- 消息大小: 1KB

| 操作 | rdkafka | lapin | async-nats | 说明 |
|------|---------|-------|------------|------|
| **生产吞吐** | 500K msg/s | 50K msg/s | 300K msg/s | Kafka 最高 |
| **消费吞吐** | 800K msg/s | 80K msg/s | 500K msg/s | Kafka 批量读取 |
| **端到端延迟** | 5-10ms | 1-2ms | <1ms | NATS 最低 |
| **存储效率** | 极高 (压缩) | 中等 | 内存 (可选持久) | Kafka 日志段压缩 |

---

## rdkafka - Kafka 客户端

### 核心特性

- ✅ **高吞吐**: >100MB/s 单节点，可水平扩展
- ✅ **持久化**: 日志段存储，可配置保留策略
- ✅ **顺序保证**: 分区内严格顺序
- ✅ **exactly-once**: 事务支持，幂等生产者
- ✅ **流处理**: Kafka Streams API

**安装**:

```toml
[dependencies]
rdkafka = { version = "0.36", features = ["tokio"] }
tokio = { version = "1", features = ["full"] }
```

### 生产者

#### 基础用法：异步生产者

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::config::ClientConfig;
use rdkafka::util::Timeout;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建生产者
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("message.timeout.ms", "5000")
        .set("compression.type", "lz4")  // 启用压缩
        .create()?;
    
    // 发送单条消息
    let topic = "orders";
    let key = "order-123";
    let payload = r#"{"orderId": "123", "amount": 100.0}"#;
    
    let delivery_status = producer
        .send(
            FutureRecord::to(topic)
                .payload(payload)
                .key(key),
            Timeout::After(std::time::Duration::from_secs(5)),
        )
        .await;
    
    match delivery_status {
        Ok((partition, offset)) => {
            println!("消息已发送: partition={}, offset={}", partition, offset);
        }
        Err((e, _)) => {
            eprintln!("发送失败: {:?}", e);
        }
    }
    
    Ok(())
}
```

**要点**:

1. `bootstrap.servers` 指定 Kafka 集群地址
2. `FutureRecord` 支持 key 和 payload
3. key 决定消息分区（相同 key 路由到同一分区）
4. 返回 `(partition, offset)` 确认消息位置

#### 高级用法：批量发送

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::config::ClientConfig;
use futures::stream::{self, StreamExt};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("linger.ms", "10")  // 批量延迟10ms
        .set("batch.size", "16384")  // 16KB批次
        .create()?;
    
    // 生成1000条消息
    let messages: Vec<_> = (0..1000)
        .map(|i| format!("message-{}", i))
        .collect();
    
    // 并发发送（限制并发度为100）
    let results = stream::iter(messages)
        .map(|payload| {
            let producer = producer.clone();
            async move {
                producer
                    .send(
                        FutureRecord::to("test-topic")
                            .payload(&payload)
                            .key(&format!("key-{}", payload)),
                        std::time::Duration::from_secs(0).into(),
                    )
                    .await
            }
        })
        .buffer_unordered(100)  // 并发100个请求
        .collect::<Vec<_>>()
        .await;
    
    let success_count = results.iter().filter(|r| r.is_ok()).count();
    println!("发送成功: {}/{}", success_count, results.len());
    
    Ok(())
}
```

**性能优化**:

- `linger.ms`: 批量延迟时间（吞吐 vs 延迟权衡）
- `batch.size`: 批次大小
- `compression.type`: 压缩算法（lz4, snappy, gzip）
- `buffer_unordered`: 并发发送

### 消费者

#### 基础用法：消费者组

```rust
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::config::ClientConfig;
use rdkafka::message::Message;
use futures::StreamExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建消费者
    let consumer: StreamConsumer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("group.id", "order-processor-group")
        .set("enable.auto.commit", "true")
        .set("auto.offset.reset", "earliest")  // 从最早的消息开始
        .create()?;
    
    // 订阅主题
    consumer.subscribe(&["orders"])?;
    
    println!("开始消费消息...");
    
    // 消费消息流
    let mut message_stream = consumer.stream();
    
    while let Some(message) = message_stream.next().await {
        match message {
            Ok(msg) => {
                let payload = msg.payload_view::<str>().unwrap_or(Ok(""))?;
                let key = msg.key_view::<str>().unwrap_or(Ok(""))?;
                
                println!(
                    "收到消息: topic={}, partition={}, offset={}, key={}, payload={}",
                    msg.topic(),
                    msg.partition(),
                    msg.offset(),
                    key,
                    payload
                );
                
                // 处理消息
                process_order(payload).await?;
            }
            Err(e) => {
                eprintln!("消费错误: {:?}", e);
            }
        }
    }
    
    Ok(())
}

async fn process_order(payload: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 业务逻辑
    println!("处理订单: {}", payload);
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    Ok(())
}
```

**要点**:

1. `group.id` 定义消费者组（组内负载均衡）
2. `auto.offset.reset` 控制初始消费位置（earliest/latest）
3. `enable.auto.commit` 自动提交 offset（简化但不保证 exactly-once）
4. 同组消费者共享分区（实现水平扩展）

#### 高级用法：手动提交 offset

```rust
use rdkafka::consumer::{Consumer, StreamConsumer, CommitMode};
use rdkafka::message::Message;
use futures::StreamExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let consumer: StreamConsumer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("group.id", "reliable-processor")
        .set("enable.auto.commit", "false")  // 禁用自动提交
        .create()?;
    
    consumer.subscribe(&["orders"])?;
    
    let mut message_stream = consumer.stream();
    
    while let Some(message) = message_stream.next().await {
        match message {
            Ok(msg) => {
                let payload = msg.payload_view::<str>().unwrap_or(Ok(""))?;
                
                // 处理消息
                match process_order_safely(payload).await {
                    Ok(_) => {
                        // 处理成功，手动提交 offset
                        consumer.commit_message(&msg, CommitMode::Async)?;
                        println!("offset 已提交: {}", msg.offset());
                    }
                    Err(e) => {
                        eprintln!("处理失败: {:?}, 不提交 offset", e);
                        // offset 不提交，重启后会重新消费
                    }
                }
            }
            Err(e) => {
                eprintln!("消费错误: {:?}", e);
            }
        }
    }
    
    Ok(())
}

async fn process_order_safely(payload: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 业务逻辑（可能失败）
    if payload.contains("invalid") {
        return Err("无效订单".into());
    }
    
    // 写入数据库、调用外部API等
    println!("处理订单: {}", payload);
    Ok(())
}
```

**可靠性保证**:

- 手动提交确保消息处理成功后才提交 offset
- 失败时不提交，重启后重新消费（at-least-once）
- 配合幂等处理实现 exactly-once

### 流处理

#### 窗口聚合示例

```rust
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::message::Message;
use futures::StreamExt;
use std::collections::HashMap;
use tokio::time::{interval, Duration};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let consumer: StreamConsumer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("group.id", "analytics")
        .create()?;
    
    consumer.subscribe(&["page-views"])?;
    
    // 滑动窗口：每5秒统计一次
    let mut window = HashMap::new();
    let mut tick = interval(Duration::from_secs(5));
    let mut message_stream = consumer.stream();
    
    loop {
        tokio::select! {
            Some(message) = message_stream.next() => {
                if let Ok(msg) = message {
                    let page = msg.key_view::<str>().unwrap_or(Ok("unknown"))?;
                    *window.entry(page.to_string()).or_insert(0) += 1;
                }
            }
            _ = tick.tick() => {
                println!("窗口统计:");
                for (page, count) in &window {
                    println!("  {} : {} views", page, count);
                }
                window.clear();
            }
        }
    }
}
```

---

## lapin - RabbitMQ 客户端

### 核心特性1

- ✅ **灵活路由**: Exchange + Binding 模式
- ✅ **多种 Exchange**: Direct, Fanout, Topic, Headers
- ✅ **可靠性**: 消息确认、持久化、镜像队列
- ✅ **优先级队列**: 消息优先级、死信队列

**安装**:

```toml
[dependencies]
lapin = "2.3"
tokio = { version = "1", features = ["full"] }
```

### 基础用法

#### 生产者和消费者

```rust
use lapin::{
    Connection, ConnectionProperties,
    options::*, types::FieldTable,
    BasicProperties,
};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 连接 RabbitMQ
    let conn = Connection::connect(
        "amqp://guest:guest@localhost:5672/%2f",
        ConnectionProperties::default(),
    ).await?;
    
    let channel = conn.create_channel().await?;
    
    // 声明队列
    let queue = channel
        .queue_declare(
            "tasks",
            QueueDeclareOptions {
                durable: true,  // 持久化
                ..Default::default()
            },
            FieldTable::default(),
        )
        .await?;
    
    println!("队列已声明: {:?}", queue);
    
    // 发送消息
    channel
        .basic_publish(
            "",
            "tasks",
            BasicPublishOptions::default(),
            b"Task: Process order #123",
            BasicProperties::default()
                .with_delivery_mode(2),  // 持久化消息
        )
        .await?;
    
    println!("消息已发送");
    
    Ok(())
}
```

#### 消费者（工作队列）

```rust
use lapin::{
    Connection, ConnectionProperties,
    options::*, types::FieldTable,
    message::Delivery,
};
use futures::StreamExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let conn = Connection::connect(
        "amqp://guest:guest@localhost:5672/%2f",
        ConnectionProperties::default(),
    ).await?;
    
    let channel = conn.create_channel().await?;
    
    // 声明队列（与生产者相同）
    channel
        .queue_declare(
            "tasks",
            QueueDeclareOptions {
                durable: true,
                ..Default::default()
            },
            FieldTable::default(),
        )
        .await?;
    
    // 设置 QoS（预取1条消息）
    channel
        .basic_qos(1, BasicQosOptions::default())
        .await?;
    
    // 开始消费
    let mut consumer = channel
        .basic_consume(
            "tasks",
            "worker-1",
            BasicConsumeOptions::default(),
            FieldTable::default(),
        )
        .await?;
    
    println!("等待消息...");
    
    while let Some(delivery) = consumer.next().await {
        if let Ok(delivery) = delivery {
            let payload = std::str::from_utf8(&delivery.data)?;
            println!("收到任务: {}", payload);
            
            // 处理任务
            tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
            
            // 手动确认
            delivery.ack(BasicAckOptions::default()).await?;
            println!("任务完成");
        }
    }
    
    Ok(())
}
```

### 工作队列模式

**特点**: 多个消费者竞争消费，实现负载均衡。

```rust
use lapin::{Connection, ConnectionProperties, options::*, types::FieldTable};
use futures::StreamExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let conn = Connection::connect(
        "amqp://localhost:5672",
        ConnectionProperties::default(),
    ).await?;
    
    let channel = conn.create_channel().await?;
    
    // 声明工作队列
    channel
        .queue_declare(
            "work-queue",
            QueueDeclareOptions {
                durable: true,
                ..Default::default()
            },
            FieldTable::default(),
        )
        .await?;
    
    // 模拟多个工作者
    for worker_id in 1..=3 {
        let channel = channel.clone();
        
        tokio::spawn(async move {
            worker(worker_id, channel).await.unwrap();
        });
    }
    
    // 保持运行
    tokio::signal::ctrl_c().await?;
    Ok(())
}

async fn worker(
    id: u32,
    channel: lapin::Channel,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut consumer = channel
        .basic_consume(
            "work-queue",
            &format!("worker-{}", id),
            BasicConsumeOptions::default(),
            FieldTable::default(),
        )
        .await?;
    
    println!("Worker {} 启动", id);
    
    while let Some(delivery) = consumer.next().await {
        if let Ok(delivery) = delivery {
            let payload = std::str::from_utf8(&delivery.data)?;
            println!("Worker {} 处理: {}", id, payload);
            
            // 模拟工作
            let work_time = payload.matches('.').count() as u64;
            tokio::time::sleep(tokio::time::Duration::from_secs(work_time)).await;
            
            delivery.ack(BasicAckOptions::default()).await?;
            println!("Worker {} 完成", id);
        }
    }
    
    Ok(())
}
```

### 发布订阅模式

**特点**: 一条消息广播给所有订阅者。

```rust
use lapin::{
    Connection, ConnectionProperties,
    options::*, types::FieldTable,
    ExchangeKind, BasicProperties,
};
use futures::StreamExt;

// 发布者
async fn publisher() -> Result<(), Box<dyn std::error::Error>> {
    let conn = Connection::connect(
        "amqp://localhost:5672",
        ConnectionProperties::default(),
    ).await?;
    
    let channel = conn.create_channel().await?;
    
    // 声明 fanout exchange（广播）
    channel
        .exchange_declare(
            "logs",
            ExchangeKind::Fanout,
            ExchangeDeclareOptions::default(),
            FieldTable::default(),
        )
        .await?;
    
    // 发布日志
    let log_messages = vec!["INFO: Server started", "WARN: High memory", "ERROR: Connection lost"];
    
    for msg in log_messages {
        channel
            .basic_publish(
                "logs",
                "",  // routing_key 为空（fanout 不需要）
                BasicPublishOptions::default(),
                msg.as_bytes(),
                BasicProperties::default(),
            )
            .await?;
        
        println!("发布日志: {}", msg);
    }
    
    Ok(())
}

// 订阅者
async fn subscriber(name: &str) -> Result<(), Box<dyn std::error::Error>> {
    let conn = Connection::connect(
        "amqp://localhost:5672",
        ConnectionProperties::default(),
    ).await?;
    
    let channel = conn.create_channel().await?;
    
    // 声明 exchange
    channel
        .exchange_declare(
            "logs",
            ExchangeKind::Fanout,
            ExchangeDeclareOptions::default(),
            FieldTable::default(),
        )
        .await?;
    
    // 声明临时队列（exclusive: 连接断开自动删除）
    let queue = channel
        .queue_declare(
            "",
            QueueDeclareOptions {
                exclusive: true,
                ..Default::default()
            },
            FieldTable::default(),
        )
        .await?;
    
    // 绑定到 exchange
    channel
        .queue_bind(
            queue.name().as_str(),
            "logs",
            "",
            QueueBindOptions::default(),
            FieldTable::default(),
        )
        .await?;
    
    // 消费消息
    let mut consumer = channel
        .basic_consume(
            queue.name().as_str(),
            name,
            BasicConsumeOptions::default(),
            FieldTable::default(),
        )
        .await?;
    
    println!("{} 等待日志...", name);
    
    while let Some(delivery) = consumer.next().await {
        if let Ok(delivery) = delivery {
            let log = std::str::from_utf8(&delivery.data)?;
            println!("{} 收到: {}", name, log);
            delivery.ack(BasicAckOptions::default()).await?;
        }
    }
    
    Ok(())
}
```

---

## async-nats - NATS 客户端

### 核心特性2

- ✅ **极低延迟**: <1ms 端到端
- ✅ **轻量级**: 单二进制文件，无依赖
- ✅ **请求响应**: 内置 Request/Reply 模式
- ✅ **JetStream**: 可选持久化和重放

**安装**:

```toml
[dependencies]
async-nats = "0.33"
tokio = { version = "1", features = ["full"] }
```

### 发布订阅

#### 基础用法1

```rust
use async_nats;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 连接 NATS
    let client = async_nats::connect("localhost:4222").await?;
    
    // 发布消息
    client.publish("events.user.created", "User ID: 123".into()).await?;
    client.publish("events.user.updated", "User ID: 123".into()).await?;
    
    println!("消息已发布");
    
    // 刷新确保发送
    client.flush().await?;
    
    Ok(())
}
```

#### 订阅消息

```rust
use async_nats;
use futures::StreamExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = async_nats::connect("localhost:4222").await?;
    
    // 订阅主题（支持通配符）
    let mut subscriber = client.subscribe("events.user.*").await?;
    
    println!("订阅 events.user.*");
    
    // 消费消息
    while let Some(message) = subscriber.next().await {
        let payload = String::from_utf8_lossy(&message.payload);
        println!("收到消息: subject={}, payload={}", message.subject, payload);
    }
    
    Ok(())
}
```

**通配符支持**:

- `*`: 匹配一个单词（`events.*.created`）
- `>`: 匹配多个单词（`events.>`）

### 请求响应

**特点**: 内置 RPC 模式，超低延迟。

```rust
use async_nats;
use futures::StreamExt;

// 服务端（响应者）
async fn responder() -> Result<(), Box<dyn std::error::Error>> {
    let client = async_nats::connect("localhost:4222").await?;
    
    let mut subscriber = client.subscribe("rpc.add").await?;
    
    println!("RPC 服务启动");
    
    while let Some(message) = subscriber.next().await {
        let payload = String::from_utf8_lossy(&message.payload);
        let numbers: Vec<i32> = payload
            .split(',')
            .filter_map(|s| s.trim().parse().ok())
            .collect();
        
        let sum: i32 = numbers.iter().sum();
        let response = format!("{}", sum);
        
        // 回复请求
        if let Some(reply) = message.reply {
            client.publish(reply, response.into()).await?;
        }
    }
    
    Ok(())
}

// 客户端（请求者）
async fn requester() -> Result<(), Box<dyn std::error::Error>> {
    let client = async_nats::connect("localhost:4222").await?;
    
    // 发送请求
    let response = client
        .request("rpc.add", "10, 20, 30".into())
        .await?;
    
    let result = String::from_utf8_lossy(&response.payload);
    println!("RPC 结果: {}", result);
    
    Ok(())
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 启动响应者
    tokio::spawn(async {
        responder().await.unwrap();
    });
    
    // 等待服务启动
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    
    // 发送请求
    requester().await?;
    
    Ok(())
}
```

### JetStream 持久化

**特点**: NATS 的持久化扩展，支持消息重放和至少一次语义。

```rust
use async_nats;
use async_nats::jetstream;
use futures::StreamExt;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let client = async_nats::connect("localhost:4222").await?;
    
    // 创建 JetStream 上下文
    let jetstream = jetstream::new(client);
    
    // 创建流（Stream）
    let _stream = jetstream
        .create_stream(jetstream::stream::Config {
            name: "ORDERS".to_string(),
            subjects: vec!["orders.*".to_string()],
            max_messages: 1000,
            ..Default::default()
        })
        .await?;
    
    // 发布消息到 JetStream
    let ack = jetstream
        .publish("orders.new", "Order #123".into())
        .await?;
    
    println!("消息已存储: stream={}, sequence={}", ack.stream, ack.sequence);
    
    // 创建持久消费者
    let consumer = jetstream
        .create_consumer_on_stream(
            jetstream::consumer::pull::Config {
                durable_name: Some("order-processor".to_string()),
                ..Default::default()
            },
            "ORDERS",
        )
        .await?;
    
    // 消费消息
    let mut messages = consumer.messages().await?;
    
    while let Some(message) = messages.next().await {
        let message = message?;
        let payload = String::from_utf8_lossy(&message.payload);
        
        println!("消费消息: {}", payload);
        
        // 确认消息
        message.ack().await?;
    }
    
    Ok(())
}
```

---

## 实战场景

### 场景1: 订单处理系统

**需求描述**: 电商订单需要经过多个处理阶段：创建订单 → 扣库存 → 支付 → 发货。使用 Kafka 保证顺序和可靠性。

**完整实现**:

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::config::ClientConfig;
use rdkafka::message::Message;
use futures::StreamExt;
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
struct Order {
    order_id: String,
    user_id: String,
    amount: f64,
    status: String,
}

// 订单服务：创建订单
async fn create_order_service(producer: FutureProducer) -> Result<(), Box<dyn std::error::Error>> {
    let order = Order {
        order_id: "ORD-001".to_string(),
        user_id: "USR-123".to_string(),
        amount: 299.99,
        status: "created".to_string(),
    };
    
    let payload = serde_json::to_string(&order)?;
    
    // 使用 user_id 作为 key 确保同一用户的订单顺序
    producer
        .send(
            FutureRecord::to("orders")
                .payload(&payload)
                .key(&order.user_id),
            std::time::Duration::from_secs(0).into(),
        )
        .await
        .map_err(|(e, _)| e)?;
    
    println!("订单已创建: {:?}", order);
    Ok(())
}

// 库存服务：扣库存
async fn inventory_service() -> Result<(), Box<dyn std::error::Error>> {
    let consumer: StreamConsumer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("group.id", "inventory-service")
        .create()?;
    
    consumer.subscribe(&["orders"])?;
    
    let mut message_stream = consumer.stream();
    
    while let Some(message) = message_stream.next().await {
        if let Ok(msg) = message {
            let payload = msg.payload_view::<str>().unwrap_or(Ok(""))?;
            let mut order: Order = serde_json::from_str(payload)?;
            
            if order.status == "created" {
                // 扣库存逻辑
                println!("扣库存: order_id={}", order.order_id);
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
                
                order.status = "inventory_reserved".to_string();
                
                // 发布到下一阶段
                let producer: FutureProducer = ClientConfig::new()
                    .set("bootstrap.servers", "localhost:9092")
                    .create()?;
                
                producer
                    .send(
                        FutureRecord::to("orders")
                            .payload(&serde_json::to_string(&order)?)
                            .key(&order.user_id),
                        std::time::Duration::from_secs(0).into(),
                    )
                    .await
                    .map_err(|(e, _)| e)?;
            }
        }
    }
    
    Ok(())
}
```

**要点说明**:

1. 使用 `user_id` 作为 key 确保顺序
2. 订单状态机：created → inventory_reserved → paid → shipped
3. 每个服务独立消费和生产
4. 故障时可重新消费（幂等性保证）

### 场景2: 实时日志聚合

**需求描述**: 收集多个服务的日志，使用 Kafka 聚合到 Elasticsearch。

**完整实现**:

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::config::ClientConfig;
use rdkafka::message::Message;
use futures::StreamExt;
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
struct LogEntry {
    timestamp: i64,
    service: String,
    level: String,
    message: String,
}

// 日志生产者（各服务调用）
async fn log_producer(service_name: &str) -> Result<(), Box<dyn std::error::Error>> {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .create()?;
    
    // 模拟日志生成
    for i in 0..10 {
        let log = LogEntry {
            timestamp: chrono::Utc::now().timestamp(),
            service: service_name.to_string(),
            level: if i % 5 == 0 { "ERROR" } else { "INFO" }.to_string(),
            message: format!("Log message #{} from {}", i, service_name),
        };
        
        producer
            .send(
                FutureRecord::to("logs")
                    .payload(&serde_json::to_string(&log)?)
                    .key(service_name),
                std::time::Duration::from_secs(0).into(),
            )
            .await
            .map_err(|(e, _)| e)?;
        
        tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
    }
    
    Ok(())
}

// 日志聚合器（写入 Elasticsearch）
async fn log_aggregator() -> Result<(), Box<dyn std::error::Error>> {
    let consumer: StreamConsumer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("group.id", "log-aggregator")
        .create()?;
    
    consumer.subscribe(&["logs"])?;
    
    let mut message_stream = consumer.stream();
    let mut batch = Vec::new();
    
    while let Some(message) = message_stream.next().await {
        if let Ok(msg) = message {
            let payload = msg.payload_view::<str>().unwrap_or(Ok(""))?;
            let log: LogEntry = serde_json::from_str(payload)?;
            
            batch.push(log);
            
            // 批量写入（100条或1秒）
            if batch.len() >= 100 {
                write_to_elasticsearch(&batch).await?;
                batch.clear();
            }
        }
    }
    
    Ok(())
}

async fn write_to_elasticsearch(logs: &[LogEntry]) -> Result<(), Box<dyn std::error::Error>> {
    // 模拟批量写入 ES
    println!("写入 {} 条日志到 Elasticsearch", logs.len());
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    Ok(())
}
```

### 场景3: 微服务事件总线

**需求描述**: 使用 NATS 实现微服务间的事件驱动通信。

**完整实现**:

```rust
use async_nats;
use futures::StreamExt;
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
struct UserCreatedEvent {
    user_id: String,
    email: String,
    timestamp: i64,
}

// 用户服务：发布事件
async fn user_service() -> Result<(), Box<dyn std::error::Error>> {
    let client = async_nats::connect("localhost:4222").await?;
    
    let event = UserCreatedEvent {
        user_id: "USR-123".to_string(),
        email: "user@example.com".to_string(),
        timestamp: chrono::Utc::now().timestamp(),
    };
    
    let payload = serde_json::to_string(&event)?;
    
    client.publish("events.user.created", payload.into()).await?;
    
    println!("事件已发布: UserCreated");
    
    Ok(())
}

// 邮件服务：订阅事件
async fn email_service() -> Result<(), Box<dyn std::error::Error>> {
    let client = async_nats::connect("localhost:4222").await?;
    
    let mut subscriber = client.subscribe("events.user.created").await?;
    
    println!("邮件服务启动，监听用户创建事件");
    
    while let Some(message) = subscriber.next().await {
        let payload = String::from_utf8_lossy(&message.payload);
        let event: UserCreatedEvent = serde_json::from_str(&payload)?;
        
        println!("发送欢迎邮件: email={}", event.email);
        
        // 发送邮件逻辑
        send_welcome_email(&event.email).await?;
    }
    
    Ok(())
}

// 通知服务：订阅事件
async fn notification_service() -> Result<(), Box<dyn std::error::Error>> {
    let client = async_nats::connect("localhost:4222").await?;
    
    let mut subscriber = client.subscribe("events.user.>").await?;  // 订阅所有用户事件
    
    println!("通知服务启动，监听所有用户事件");
    
    while let Some(message) = subscriber.next().await {
        println!("收到事件: subject={}", message.subject);
        
        // 推送通知逻辑
    }
    
    Ok(())
}

async fn send_welcome_email(email: &str) -> Result<(), Box<dyn std::error::Error>> {
    println!("📧 发送欢迎邮件到: {}", email);
    Ok(())
}
```

---

## 最佳实践

### 1. 消息幂等性处理

**描述**: at-least-once 语义下，消息可能重复消费，必须保证幂等。

```rust
use std::collections::HashSet;
use std::sync::Arc;
use tokio::sync::Mutex;

struct MessageDeduplicator {
    processed_ids: Arc<Mutex<HashSet<String>>>,
}

impl MessageDeduplicator {
    async fn is_processed(&self, msg_id: &str) -> bool {
        let ids = self.processed_ids.lock().await;
        ids.contains(msg_id)
    }
    
    async fn mark_processed(&self, msg_id: String) {
        let mut ids = self.processed_ids.lock().await;
        ids.insert(msg_id);
    }
}

// 使用方式
async fn process_message(dedup: &MessageDeduplicator, msg_id: &str) {
    if dedup.is_processed(msg_id).await {
        println!("消息已处理，跳过: {}", msg_id);
        return;
    }
    
    // 处理业务逻辑
    // ...
    
    dedup.mark_processed(msg_id.to_string()).await;
}
```

### 2. 错误处理和重试

**描述**: 消息处理失败时，使用指数退避重试。

```rust
use tokio::time::{sleep, Duration};

async fn process_with_retry<F, Fut>(f: F, max_retries: u32) -> Result<(), Box<dyn std::error::Error>>
where
    F: Fn() -> Fut,
    Fut: std::future::Future<Output = Result<(), Box<dyn std::error::Error>>>,
{
    let mut attempts = 0;
    
    loop {
        match f().await {
            Ok(_) => return Ok(()),
            Err(e) if attempts < max_retries => {
                attempts += 1;
                let wait_time = Duration::from_millis(100 * 2u64.pow(attempts));
                println!("处理失败，{}ms 后重试 ({}/{}): {:?}", 
                    wait_time.as_millis(), attempts, max_retries, e);
                sleep(wait_time).await;
            }
            Err(e) => {
                eprintln!("处理失败，超过最大重试次数: {:?}", e);
                return Err(e);
            }
        }
    }
}
```

### 3. 消费者组配置

**描述**: 合理配置消费者组，避免消息堆积和不均衡。

```rust
// Kafka 消费者最佳配置
let consumer: StreamConsumer = ClientConfig::new()
    .set("bootstrap.servers", "localhost:9092")
    .set("group.id", "my-service")
    .set("enable.auto.commit", "false")  // 手动提交
    .set("auto.offset.reset", "earliest")  // 从头开始
    .set("session.timeout.ms", "10000")  // 会话超时
    .set("max.poll.interval.ms", "300000")  // 最大拉取间隔（5分钟）
    .set("fetch.min.bytes", "1024")  // 最小拉取字节数
    .set("fetch.max.wait.ms", "500")  // 最大等待时间
    .create()?;
```

### 4. 消息压缩

**描述**: 启用压缩节省带宽和存储。

```rust
// Kafka 生产者压缩
let producer: FutureProducer = ClientConfig::new()
    .set("bootstrap.servers", "localhost:9092")
    .set("compression.type", "lz4")  // 或 snappy, gzip, zstd
    .set("compression.level", "3")  // 压缩级别
    .create()?;
```

### 5. 监控和可观测性

**描述**: 记录关键指标和链路追踪。

```rust
use tracing::{info, warn, error};

async fn consume_message(msg: &str) -> Result<(), Box<dyn std::error::Error>> {
    let start = std::time::Instant::now();
    
    // 处理消息
    process(msg).await?;
    
    let duration = start.elapsed();
    info!("消息处理完成，耗时: {:?}", duration);
    
    // 记录指标
    if duration.as_millis() > 1000 {
        warn!("消息处理超时: {}ms", duration.as_millis());
    }
    
    Ok(())
}

async fn process(msg: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 业务逻辑
    Ok(())
}
```

---

## 常见陷阱

### ⚠️ 陷阱1: Kafka offset 提交错误

**问题描述**: 自动提交 offset 可能导致消息丢失或重复消费。

❌ **错误示例**:

```rust
let consumer: StreamConsumer = ClientConfig::new()
    .set("enable.auto.commit", "true")  // ❌ 自动提交
    .create()?;

while let Some(message) = stream.next().await {
    // 处理消息
    process(message).await?;  // 如果失败，offset 可能已提交
}
```

✅ **正确做法**:

```rust
let consumer: StreamConsumer = ClientConfig::new()
    .set("enable.auto.commit", "false")  // ✅ 禁用自动提交
    .create()?;

while let Some(message) = stream.next().await {
    if let Ok(msg) = message {
        match process(&msg).await {
            Ok(_) => {
                consumer.commit_message(&msg, CommitMode::Async)?;  // ✅ 处理成功后提交
            }
            Err(e) => {
                eprintln!("处理失败: {:?}", e);
                // offset 不提交，下次重新消费
            }
        }
    }
}
```

### ⚠️ 陷阱2: RabbitMQ 不确认消息导致内存泄漏

**问题描述**: 消费消息后忘记 ack/nack 会导致消息堆积。

❌ **错误示例**:

```rust
while let Some(delivery) = consumer.next().await {
    if let Ok(delivery) = delivery {
        process(&delivery.data).await;
        // ❌ 忘记确认
    }
}
```

✅ **正确做法**:

```rust
while let Some(delivery) = consumer.next().await {
    if let Ok(delivery) = delivery {
        match process(&delivery.data).await {
            Ok(_) => {
                delivery.ack(BasicAckOptions::default()).await?;  // ✅ 确认
            }
            Err(_) => {
                delivery.nack(BasicNackOptions {
                    requeue: true,  // 重新入队
                    ..Default::default()
                }).await?;
            }
        }
    }
}
```

### ⚠️ 陷阱3: 消息顺序性误解

**问题描述**: Kafka 只保证分区内顺序，全局无序。

❌ **错误示例**:

```rust
// ❌ 没有指定 key，消息轮询分区，全局无序
producer.send(
    FutureRecord::to("orders")
        .payload("order-1"),
    timeout,
).await?;
```

✅ **正确做法**:

```rust
// ✅ 使用 user_id 作为 key，同一用户的消息在同一分区
producer.send(
    FutureRecord::to("orders")
        .payload("order-1")
        .key(&user_id),  // ✅ 指定 key
    timeout,
).await?;
```

### ⚠️ 陷阱4: 消息堆积未监控

**问题描述**: 消费速度慢于生产速度导致堆积，但未及时发现。

✅ **正确做法**:

```rust
use sysinfo::{System, SystemExt};

async fn monitor_lag() {
    // 监控 Kafka lag（使用 rdkafka admin API）
    // 监控 RabbitMQ 队列深度（使用 HTTP API）
    
    loop {
        let lag = get_consumer_lag().await;
        
        if lag > 10000 {
            eprintln!("警告：消息堆积 {} 条", lag);
            // 告警通知
        }
        
        tokio::time::sleep(tokio::time::Duration::from_secs(60)).await;
    }
}

async fn get_consumer_lag() -> u64 {
    // 实现监控逻辑
    0
}
```

---

## 参考资源

### 官方文档

- 📚 [rdkafka 文档](https://docs.rs/rdkafka/latest/rdkafka/)
- 📚 [lapin 文档](https://docs.rs/lapin/latest/lapin/)
- 📚 [async-nats 文档](https://docs.rs/async-nats/latest/async_nats/)
- 📚 [Apache Kafka 官方文档](https://kafka.apache.org/documentation/)
- 📚 [RabbitMQ 官方文档](https://www.rabbitmq.com/documentation.html)
- 📚 [NATS 官方文档](https://docs.nats.io/)

### 教程与文章

- 📖 [Kafka 权威指南](https://www.confluent.io/resources/kafka-the-definitive-guide/)
- 📖 [RabbitMQ 实战](https://www.manning.com/books/rabbitmq-in-action)
- 📖 [消息队列设计模式](https://www.enterpriseintegrationpatterns.com/)

### 示例项目

- 💻 [Kafka Rust Examples](https://github.com/fede1024/rust-rdkafka/tree/master/examples)
- 💻 [RabbitMQ Tutorials (Rust)](https://github.com/rabbitmq/rabbitmq-tutorials/tree/main/rust)
- 💻 [NATS by Example](https://natsbyexample.com/)

### 相关文档

- 🔗 [异步运行时](../../02_system_programming/async_runtime/README.md)
- 🔗 [数据库连接池](../database/README.md)
- 🔗 [日志系统](../../05_toolchain/logging/README.md)

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**维护者**: Rust 学习社区
