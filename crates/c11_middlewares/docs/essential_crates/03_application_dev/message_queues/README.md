# Message Queues - 消息队列

## 📋 目录

- [概述](#概述)
- [Kafka](#kafka)
- [RabbitMQ](#rabbitmq)
- [NATS](#nats)
- [实战示例](#实战示例)

---

## 概述

消息队列是分布式系统中实现异步通信、解耦和负载均衡的核心组件。

### 核心依赖

```toml
[dependencies]
# Kafka
rdkafka = { version = "0.36", features = ["cmake-build", "ssl", "gssapi"] }

# RabbitMQ
lapin = "2.3"

# NATS
async-nats = "0.33"
```

---

## Kafka

### 生产者

```rust
use rdkafka::config::ClientConfig;
use rdkafka::producer::{FutureProducer, FutureRecord};
use std::time::Duration;

async fn kafka_producer() -> Result<(), Box<dyn std::error::Error>> {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("message.timeout.ms", "5000")
        .create()?;
    
    let delivery_status = producer
        .send(
            FutureRecord::to("my-topic")
                .payload("Hello, Kafka!")
                .key("key1"),
            Duration::from_secs(0),
        )
        .await;
    
    match delivery_status {
        Ok(delivery) => println!("发送成功: {:?}", delivery),
        Err((e, _)) => eprintln!("发送失败: {}", e),
    }
    
    Ok(())
}
```

### 消费者

```rust
use rdkafka::config::ClientConfig;
use rdkafka::consumer::{Consumer, StreamConsumer};
use rdkafka::message::Message;

async fn kafka_consumer() -> Result<(), Box<dyn std::error::Error>> {
    let consumer: StreamConsumer = ClientConfig::new()
        .set("group.id", "my-group")
        .set("bootstrap.servers", "localhost:9092")
        .set("enable.auto.commit", "true")
        .create()?;
    
    consumer.subscribe(&["my-topic"])?;
    
    loop {
        match consumer.recv().await {
            Ok(msg) => {
                let payload = match msg.payload_view::<str>() {
                    Some(Ok(s)) => s,
                    _ => "",
                };
                println!("收到消息: {}", payload);
            }
            Err(e) => eprintln!("错误: {}", e),
        }
    }
}
```

---

## RabbitMQ

### 发布者

```rust
use lapin::{
    Connection, ConnectionProperties,
    options::*,
    types::FieldTable,
    BasicProperties,
};

async fn rabbitmq_publisher() -> Result<(), Box<dyn std::error::Error>> {
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
        b"Hello, RabbitMQ!",
        BasicProperties::default(),
    ).await?;
    
    println!("消息已发送");
    Ok(())
}
```

### 消费者1

```rust
use lapin::{
    Connection, ConnectionProperties,
    options::*,
    types::FieldTable,
};
use futures_lite::StreamExt;

async fn rabbitmq_consumer() -> Result<(), Box<dyn std::error::Error>> {
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
    
    let mut consumer = channel
        .basic_consume(
            "hello",
            "my-consumer",
            BasicConsumeOptions::default(),
            FieldTable::default(),
        )
        .await?;
    
    while let Some(delivery) = consumer.next().await {
        let delivery = delivery?;
        let msg = String::from_utf8_lossy(&delivery.data);
        println!("收到: {}", msg);
        
        delivery.ack(BasicAckOptions::default()).await?;
    }
    
    Ok(())
}
```

---

## NATS

### 发布/订阅

```rust
use async_nats;

async fn nats_pubsub() -> Result<(), Box<dyn std::error::Error>> {
    // 连接 NATS
    let client = async_nats::connect("localhost:4222").await?;
    
    // 订阅
    let mut subscriber = client.subscribe("my.subject").await?;
    
    tokio::spawn(async move {
        while let Some(message) = subscriber.next().await {
            println!("收到: {:?}", message);
        }
    });
    
    // 发布
    client.publish("my.subject", "Hello NATS!".into()).await?;
    
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    Ok(())
}
```

### 请求/响应

```rust
use async_nats;

async fn nats_request_reply() -> Result<(), Box<dyn std::error::Error>> {
    let client = async_nats::connect("localhost:4222").await?;
    
    // 响应者
    let client_clone = client.clone();
    tokio::spawn(async move {
        let mut subscriber = client_clone.subscribe("request.subject").await.unwrap();
        while let Some(message) = subscriber.next().await {
            if let Some(reply) = message.reply {
                client_clone.publish(reply, "Response!".into()).await.unwrap();
            }
        }
    });
    
    // 请求者
    let response = client
        .request("request.subject", "Request!".into())
        .await?;
    
    println!("响应: {:?}", response);
    Ok(())
}
```

---

## 实战示例

### 任务队列模式

```rust
use lapin::{Connection, ConnectionProperties};

async fn task_queue() -> Result<(), Box<dyn std::error::Error>> {
    let conn = Connection::connect(
        "amqp://localhost",
        ConnectionProperties::default(),
    ).await?;
    
    let channel = conn.create_channel().await?;
    
    // 声明持久化队列
    channel.queue_declare(
        "task_queue",
        lapin::options::QueueDeclareOptions {
            durable: true,
            ..Default::default()
        },
        lapin::types::FieldTable::default(),
    ).await?;
    
    // 发送任务
    for i in 0..10 {
        let task = format!("Task {}", i);
        channel.basic_publish(
            "",
            "task_queue",
            lapin::options::BasicPublishOptions::default(),
            task.as_bytes(),
            lapin::BasicProperties::default().with_delivery_mode(2), // 持久化
        ).await?;
    }
    
    Ok(())
}
```

---

## 参考资源

- [rdkafka 文档](https://docs.rs/rdkafka/)
- [lapin GitHub](https://github.com/CleverCloud/lapin)
- [NATS 文档](https://docs.nats.io/)
