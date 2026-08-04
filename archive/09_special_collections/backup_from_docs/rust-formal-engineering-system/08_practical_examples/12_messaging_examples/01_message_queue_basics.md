# 消息队列基础（Message Queue Basics）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [消息队列基础（Message Queue Basics）](#消息队列基础message-queue-basics)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [使用 RabbitMQ](#使用-rabbitmq)
    - [基本连接](#基本连接)
    - [发送消息](#发送消息)
    - [接收消息](#接收消息)
  - [使用 Redis 作为消息队列](#使用-redis-作为消息队列)
    - [基本发布订阅](#基本发布订阅)
    - [使用 Stream](#使用-stream)
  - [使用 Kafka](#使用-kafka)
    - [生产者](#生产者)
    - [消费者](#消费者)
  - [实践示例](#实践示例)
    - [示例 1：任务队列](#示例-1任务队列)
    - [示例 2：事件总线](#示例-2事件总线)
    - [示例 3：工作池模式](#示例-3工作池模式)
  - [最佳实践](#最佳实践)
    - [1. 消息确认](#1-消息确认)
    - [2. 错误处理](#2-错误处理)
    - [3. 消息序列化](#3-消息序列化)
  - [参考资料](#参考资料)

---

## 概述

消息队列是分布式系统中重要的组件，用于解耦服务、异步处理和负载均衡。Rust 提供了多个消息队列客户端库。

## 使用 RabbitMQ

### 基本连接

```rust
use lapin::{
    options::*,
    types::FieldTable,
    Connection, ConnectionProperties, Result,
};

#[tokio::main]
async fn main() -> Result<()> {
    let addr = "amqp://guest:guest@localhost:5672/%2f";
    let conn = Connection::connect(addr, ConnectionProperties::default()).await?;
    let channel = conn.create_channel().await?;

    // 使用 channel 进行消息操作
    Ok(())
}
```

### 发送消息

```rust
use lapin::{options::*, types::FieldTable, Channel};

async fn publish_message(
    channel: &Channel,
    queue: &str,
    message: &str,
) -> Result<()> {
    channel
        .queue_declare(
            queue,
            QueueDeclareOptions::default(),
            FieldTable::default(),
        )
        .await?;

    channel
        .basic_publish(
            "",
            queue,
            BasicPublishOptions::default(),
            message.as_bytes(),
            BasicProperties::default(),
        )
        .await?;

    Ok(())
}
```

### 接收消息

```rust
use lapin::{options::*, types::FieldTable, Channel, Consumer};

async fn consume_messages(
    channel: &Channel,
    queue: &str,
) -> Result<Consumer> {
    channel
        .queue_declare(
            queue,
            QueueDeclareOptions::default(),
            FieldTable::default(),
        )
        .await?;

    let consumer = channel
        .basic_consume(
            queue,
            "consumer_tag",
            BasicConsumeOptions::default(),
            FieldTable::default(),
        )
        .await?;

    Ok(consumer)
}

async fn process_messages(mut consumer: Consumer) -> Result<()> {
    while let Some(delivery) = consumer.next().await {
        let delivery = delivery?;
        let message = String::from_utf8_lossy(&delivery.data);
        println!("收到消息: {}", message);

        delivery
            .ack(BasicAckOptions::default())
            .await?;
    }

    Ok(())
}
```

## 使用 Redis 作为消息队列

### 基本发布订阅

```rust
use redis::{Commands, Connection};

fn publish_message(conn: &mut Connection, channel: &str, message: &str) -> redis::RedisResult<()> {
    conn.publish(channel, message)?;
    Ok(())
}

fn subscribe_to_channel(conn: &mut Connection, channel: &str) -> redis::RedisResult<()> {
    let mut pubsub = conn.as_pubsub();
    pubsub.subscribe(channel)?;

    loop {
        let msg = pubsub.get_message()?;
        let payload: String = msg.get_payload()?;
        println!("收到消息: {}", payload);
    }
}
```

### 使用 Stream

```rust
use redis::{Commands, Connection};

fn add_to_stream(conn: &mut Connection, stream: &str, data: &str) -> redis::RedisResult<String> {
    let id: String = conn.xadd(stream, "*", &[("data", data)])?;
    Ok(id)
}

fn read_from_stream(conn: &mut Connection, stream: &str) -> redis::RedisResult<Vec<String>> {
    let messages: Vec<String> = conn.xread(&[stream], &["0"], None)?;
    Ok(messages)
}
```

## 使用 Kafka

### 生产者

```rust
use rdkafka::config::ClientConfig;
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::util::Timeout;

async fn produce_message(
    producer: &FutureProducer,
    topic: &str,
    key: &str,
    payload: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    let record = FutureRecord::to(topic)
        .key(key)
        .payload(payload);

    producer
        .send(record, Timeout::After(std::time::Duration::from_secs(0)))
        .await?;

    Ok(())
}

fn create_producer() -> FutureProducer {
    ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("message.timeout.ms", "5000")
        .create()
        .expect("生产者创建失败")
}
```

### 消费者

```rust
use rdkafka::config::ClientConfig;
use rdkafka::consumer::{stream_consumer::StreamConsumer, Consumer};
use rdkafka::Message;

async fn consume_messages(
    consumer: &StreamConsumer,
    topics: &[&str],
) -> Result<(), Box<dyn std::error::Error>> {
    consumer.subscribe(topics)?;

    loop {
        match consumer.recv().await {
            Ok(message) => {
                if let Some(payload) = message.payload_view::<str>() {
                    println!("收到消息: {}", payload?);
                }
            }
            Err(e) => {
                eprintln!("消费错误: {}", e);
            }
        }
    }
}

fn create_consumer(group_id: &str) -> StreamConsumer {
    ClientConfig::new()
        .set("group.id", group_id)
        .set("bootstrap.servers", "localhost:9092")
        .set("enable.partition.eof", "false")
        .set("session.timeout.ms", "6000")
        .set("enable.auto.commit", "true")
        .create()
        .expect("消费者创建失败")
}
```

## 实践示例

### 示例 1：任务队列

```rust
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::mpsc;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Task {
    pub id: u32,
    pub task_type: String,
    pub data: String,
}

pub struct TaskQueue {
    sender: mpsc::Sender<Task>,
}

impl TaskQueue {
    pub fn new() -> (Self, mpsc::Receiver<Task>) {
        let (tx, rx) = mpsc::channel(100);
        (TaskQueue { sender: tx }, rx)
    }

    pub async fn enqueue(&self, task: Task) -> Result<(), mpsc::error::SendError<Task>> {
        self.sender.send(task).await
    }
}

pub struct TaskWorker {
    receiver: mpsc::Receiver<Task>,
}

impl TaskWorker {
    pub fn new(receiver: mpsc::Receiver<Task>) -> Self {
        TaskWorker { receiver }
    }

    pub async fn run(mut self) {
        while let Some(task) = self.receiver.recv().await {
            self.process_task(task).await;
        }
    }

    async fn process_task(&self, task: Task) {
        println!("处理任务: {:?}", task);
        // 处理任务逻辑
    }
}
```

### 示例 2：事件总线

```rust
use tokio::sync::broadcast;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Event {
    UserCreated { user_id: u32, name: String },
    OrderPlaced { order_id: u32, user_id: u32 },
    PaymentProcessed { order_id: u32, amount: f64 },
}

pub struct EventBus {
    sender: broadcast::Sender<Event>,
}

impl EventBus {
    pub fn new(capacity: usize) -> Self {
        let (tx, _) = broadcast::channel(capacity);
        EventBus { sender: tx }
    }

    pub fn publish(&self, event: Event) -> Result<usize, broadcast::error::SendError<Event>> {
        self.sender.send(event)
    }

    pub fn subscribe(&self) -> broadcast::Receiver<Event> {
        self.sender.subscribe()
    }
}

pub struct EventHandler {
    receiver: broadcast::Receiver<Event>,
    handler_name: String,
}

impl EventHandler {
    pub fn new(receiver: broadcast::Receiver<Event>, name: String) -> Self {
        EventHandler {
            receiver,
            handler_name: name,
        }
    }

    pub async fn run(mut self) {
        while let Ok(event) = self.receiver.recv().await {
            println!("[{}] 处理事件: {:?}", self.handler_name, event);
            // 处理事件逻辑
        }
    }
}
```

### 示例 3：工作池模式

```rust
use std::sync::Arc;
use tokio::sync::{mpsc, Semaphore};

pub struct WorkerPool {
    workers: Vec<tokio::task::JoinHandle<()>>,
    sender: mpsc::Sender<Task>,
}

impl WorkerPool {
    pub fn new(worker_count: usize) -> (Self, mpsc::Receiver<Task>) {
        let (tx, rx) = mpsc::channel(1000);
        let semaphore = Arc::new(Semaphore::new(worker_count));

        let mut workers = Vec::new();
        for i in 0..worker_count {
            let mut receiver = rx.resubscribe();
            let semaphore = Arc::clone(&semaphore);

            let worker = tokio::spawn(async move {
                while let Some(task) = receiver.recv().await {
                    let _permit = semaphore.acquire().await.unwrap();
                    process_task(task, i).await;
                }
            });
            workers.push(worker);
        }

        (WorkerPool { workers, sender: tx }, rx)
    }

    pub async fn submit(&self, task: Task) -> Result<(), mpsc::error::SendError<Task>> {
        self.sender.send(task).await
    }
}

async fn process_task(task: Task, worker_id: usize) {
    println!("Worker {} 处理任务: {:?}", worker_id, task);
    // 处理任务逻辑
}
```

## 最佳实践

### 1. 消息确认

```rust
// 确保消息被正确处理后才确认
async fn process_with_ack(delivery: Delivery) -> Result<()> {
    match process_message(&delivery).await {
        Ok(_) => {
            delivery.ack(BasicAckOptions::default()).await?;
            Ok(())
        }
        Err(e) => {
            // 处理失败，可以选择重试或拒绝
            delivery.nack(BasicNackOptions::default()).await?;
            Err(e)
        }
    }
}
```

### 2. 错误处理

```rust
async fn robust_consumer(mut consumer: Consumer) -> Result<()> {
    loop {
        match consumer.next().await {
            Some(Ok(delivery)) => {
                if let Err(e) = process_delivery(delivery).await {
                    eprintln!("处理消息失败: {}", e);
                }
            }
            Some(Err(e)) => {
                eprintln!("接收消息错误: {}", e);
            }
            None => break,
        }
    }
    Ok(())
}
```

### 3. 消息序列化

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct Message {
    pub id: u32,
    pub content: String,
    pub timestamp: i64,
}

fn serialize_message(msg: &Message) -> Vec<u8> {
    serde_json::to_vec(msg).unwrap()
}

fn deserialize_message(data: &[u8]) -> Result<Message, serde_json::Error> {
    serde_json::from_slice(data)
}
```

## 参考资料

- [消息队列示例索引](./00_index.md)
- [实践示例索引](../00_index.md)
- [Lapin 文档](https://docs.rs/lapin/)
- [Redis 文档](https://docs.rs/redis/)
- [rdkafka 文档](https://docs.rs/rdkafka/)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回实践示例: [`../00_index.md`](../00_index.md)
