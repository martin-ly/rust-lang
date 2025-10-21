# 消息队列

> **核心库**: rdkafka, lapin, pulsar-rs  
> **适用场景**: Kafka、RabbitMQ、Pulsar、消息驱动

---

## 📋 核心库

| 库 | 协议 | 推荐度 |
|-----|------|--------|
| **rdkafka** | Kafka | ⭐⭐⭐⭐⭐ |
| **lapin** | AMQP/RabbitMQ | ⭐⭐⭐⭐⭐ |
| **pulsar-rs** | Pulsar | ⭐⭐⭐⭐ |

---

## 🔥 rdkafka - Kafka

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};
use rdkafka::config::ClientConfig;

#[tokio::main]
async fn main() {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .create()
        .expect("Producer creation error");
    
    let record = FutureRecord::to("my-topic")
        .payload("Hello Kafka")
        .key("key");
    
    producer.send(record, std::time::Duration::from_secs(0)).await;
}
```

---

## 🐰 lapin - RabbitMQ

```rust
use lapin::{Connection, ConnectionProperties, options::*, types::FieldTable};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let conn = Connection::connect(
        "amqp://localhost:5672",
        ConnectionProperties::default()
    ).await?;
    
    let channel = conn.create_channel().await?;
    
    channel.queue_declare(
        "hello",
        QueueDeclareOptions::default(),
        FieldTable::default()
    ).await?;
    
    channel.basic_publish(
        "",
        "hello",
        BasicPublishOptions::default(),
        b"Hello RabbitMQ",
        BasicProperties::default()
    ).await?;
    
    Ok(())
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
