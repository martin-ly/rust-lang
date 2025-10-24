# 消息队列与流处理完整指南：NATS/Kafka/MQTT

> **适用版本**: Rust 1.75+ (推荐 1.90+)  
> **更新日期**: 2025-10-24  
> **难度级别**: 中级到高级

本指南详细介绍三种主流消息系统在 Rust 中的完整实战：NATS（高性能低延迟）、Kafka（分布式流处理）、MQTT（物联网消息）。

---

## 📊 目录

- [消息队列与流处理完整指南：NATS/Kafka/MQTT](#消息队列与流处理完整指南natskafkamqtt)
  - [📊 目录](#-目录)
  - [消息系统对比与选型](#消息系统对比与选型)
    - [技术特性对比](#技术特性对比)
    - [选型建议](#选型建议)
  - [NATS 完整实战](#nats-完整实战)
    - [NATS 核心概念](#nats-核心概念)
    - [NATS 快速开始](#nats-快速开始)
    - [JetStream 持久化](#jetstream-持久化)
    - [NATS 高级特性](#nats-高级特性)
  - [Kafka 完整实战](#kafka-完整实战)
    - [Kafka 核心概念](#kafka-核心概念)
    - [Kafka 生产者实现](#kafka-生产者实现)
  - [MQTT 完整实战](#mqtt-完整实战)
    - [MQTT 核心概念](#mqtt-核心概念)
    - [MQTT QoS 详解](#mqtt-qos-详解)
    - [MQTT 快速开始](#mqtt-快速开始)
    - [MQTT 物联网场景](#mqtt-物联网场景)
  - [架构设计模式](#架构设计模式)
    - [模式 1: 事件驱动架构 (EDA)](#模式-1-事件驱动架构-eda)
    - [模式 2: CQRS (命令查询职责分离)](#模式-2-cqrs-命令查询职责分离)
    - [模式 3: Saga 模式 (分布式事务)](#模式-3-saga-模式-分布式事务)
  - [性能对比与测试](#性能对比与测试)
    - [延迟测试](#延迟测试)
    - [吞吐量测试](#吞吐量测试)
  - [生产环境部署](#生产环境部署)
    - [NATS 集群部署](#nats-集群部署)
    - [MQTT 生产配置](#mqtt-生产配置)
  - [监控与可观测性](#监控与可观测性)
    - [Prometheus 指标收集](#prometheus-指标收集)
  - [故障排查](#故障排查)
    - [常见问题](#常见问题)
  - [总结](#总结)
    - [NATS 核心优势](#nats-核心优势)
    - [Kafka 核心优势](#kafka-核心优势)
    - [MQTT 核心优势](#mqtt-核心优势)
    - [选型建议总结](#选型建议总结)

---

## 消息系统对比与选型

### 技术特性对比

| 特性 | NATS | Kafka | MQTT |
|------|------|-------|------|
| **延迟** | 极低 (<1ms) | 中等 (2-10ms) | 低 (5-20ms) |
| **吞吐量** | 高 (100K+ msg/s) | 极高 (1M+ msg/s) | 中等 (10K+ msg/s) |
| **持久化** | JetStream 可选 | 默认持久化 | QoS 可选 |
| **消息顺序** | 无保证 | 分区内有序 | 无保证 |
| **消息回溯** | JetStream 支持 | ✅ 完全支持 | ❌ 不支持 |
| **集群部署** | ✅ 原生支持 | ✅ 原生支持 | ⚠️ 需第三方 |
| **协议复杂度** | 简单 | 复杂 | 简单 |
| **适用场景** | 微服务通信 | 流处理/日志 | IoT/边缘 |

### 选型建议

**选择 NATS 的场景**:

- ✅ 微服务之间的请求-响应通信
- ✅ 需要极低延迟 (<1ms)
- ✅ 简单的发布-订阅模式
- ✅ 轻量级消息传递
- ❌ 不适合：需要消息回溯、复杂流处理

**选择 Kafka 的场景**:

- ✅ 日志收集和聚合
- ✅ 事件溯源 (Event Sourcing)
- ✅ 流处理和实时分析
- ✅ 需要消息回溯
- ❌ 不适合：极低延迟要求、简单消息队列

**选择 MQTT 的场景**:

- ✅ 物联网 (IoT) 设备通信
- ✅ 移动应用推送
- ✅ 网络不稳定的场景
- ✅ 设备资源受限
- ❌ 不适合：高吞吐量、复杂业务逻辑

---

## NATS 完整实战

### NATS 核心概念

**NATS 架构**:

```text
Publisher → NATS Server → Subscriber(s)
              ↓
         (可选) JetStream
         持久化 & 回溯
```

**核心概念**:

1. **Subject**: 消息主题，支持通配符
   - 精确匹配: `orders.created`
   - 单级通配符: `orders.*` (匹配 `orders.created`, `orders.updated`)
   - 多级通配符: `orders.>` (匹配 `orders.created.us`, `orders.created.eu`)

2. **消息模式**:
   - **Pub/Sub**: 一对多广播
   - **Request/Reply**: 请求-响应
   - **Queue Groups**: 负载均衡

---

### NATS 快速开始

**环境准备**:

```bash
# Docker 启动 NATS
docker run -d --name nats -p 4222:4222 -p 8222:8222 nats:latest

# 启用 JetStream
docker run -d --name nats-js -p 4222:4222 -p 8222:8222 \
  nats:latest -js
```

**依赖配置**:

```toml
[dependencies]
async-nats = "0.33"
tokio = { version = "1", features = ["full"] }
serde = { version = "1", features = ["derive"] }
serde_json = "1"
anyhow = "1"
```

**最简单的发布-订阅**:

```rust
use async_nats;
use futures::StreamExt;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 连接 NATS
    let client = async_nats::connect("nats://localhost:4222").await?;
    
    // 订阅主题
    let mut subscriber = client.subscribe("greetings").await?;
    
    // 在另一个任务中发布消息
    let publisher = client.clone();
    tokio::spawn(async move {
        for i in 0..10 {
            publisher
                .publish("greetings", format!("Hello {}", i).into())
                .await
                .unwrap();
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
        }
    });
    
    // 接收消息
    while let Some(message) = subscriber.next().await {
        let payload = String::from_utf8_lossy(&message.payload);
        println!("收到消息: {}", payload);
    }
    
    Ok(())
}
```

**请求-响应模式**:

```rust
use async_nats;
use futures::StreamExt;
use std::time::Duration;

async fn request_reply_example() -> anyhow::Result<()> {
    let client = async_nats::connect("nats://localhost:4222").await?;
    
    // 服务端：响应请求
    let responder = client.clone();
    tokio::spawn(async move {
        let mut subscriber = responder.subscribe("math.add").await.unwrap();
        while let Some(message) = subscriber.next().await {
            if let Some(reply_subject) = message.reply {
                // 解析请求
                let numbers: Vec<i32> = serde_json::from_slice(&message.payload)
                    .unwrap_or_else(|_| vec![]);
                let sum: i32 = numbers.iter().sum();
                
                // 发送响应
                responder
                    .publish(reply_subject, sum.to_string().into())
                    .await
                    .unwrap();
            }
        }
    });
    
    // 客户端：发送请求
    tokio::time::sleep(Duration::from_millis(100)).await;
    
    let request = serde_json::to_vec(&vec![1, 2, 3, 4, 5])?;
    let response = client
        .request("math.add", request.into())
        .await?;
    
    let result = String::from_utf8_lossy(&response.payload);
    println!("1+2+3+4+5 = {}", result);  // 输出: 15
    
    Ok(())
}
```

**队列组（负载均衡）**:

```rust
use async_nats;
use futures::StreamExt;

async fn queue_group_example() -> anyhow::Result<()> {
    let client = async_nats::connect("nats://localhost:4222").await?;
    
    // 创建多个消费者在同一队列组
    for worker_id in 0..3 {
        let client = client.clone();
        tokio::spawn(async move {
            // queue_subscribe: 同一队列组内的消费者负载均衡
            let mut subscriber = client
                .queue_subscribe("tasks", "workers".to_string())
                .await
                .unwrap();
            
            while let Some(message) = subscriber.next().await {
                let payload = String::from_utf8_lossy(&message.payload);
                println!("Worker {} 处理任务: {}", worker_id, payload);
                
                // 模拟处理时间
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            }
        });
    }
    
    // 发布任务
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
    for i in 0..10 {
        client
            .publish("tasks", format!("Task {}", i).into())
            .await?;
    }
    
    tokio::time::sleep(tokio::time::Duration::from_secs(2)).await;
    Ok(())
}
```

---

### JetStream 持久化

**JetStream 核心概念**:

- **Stream**: 持久化的消息存储
- **Consumer**: 消息消费者，支持多种交付模式
- **持久化**: 消息存储在磁盘，支持回溯

**创建 Stream 和 Consumer**:

```rust
use async_nats::jetstream;

async fn jetstream_example() -> anyhow::Result<()> {
    let client = async_nats::connect("nats://localhost:4222").await?;
    let jetstream = jetstream::new(client);
    
    // 创建 Stream
    let stream = jetstream
        .create_stream(jetstream::stream::Config {
            name: "ORDERS".to_string(),
            subjects: vec!["orders.*".to_string()],
            max_messages: 10000,
            max_bytes: 1024 * 1024 * 100, // 100MB
            retention: jetstream::stream::RetentionPolicy::Limits,
            storage: jetstream::stream::StorageType::File,
            ..Default::default()
        })
        .await?;
    
    println!("Stream 创建成功: {:?}", stream.info().await?);
    
    // 发布消息到 JetStream
    for i in 0..100 {
        let ack = jetstream
            .publish("orders.created", format!("Order {}", i).into())
            .await?;
        println!("消息已确认: seq={}", ack.await?.sequence);
    }
    
    // 创建 Consumer
    let consumer = stream
        .create_consumer(jetstream::consumer::pull::Config {
            durable_name: Some("order-processor".to_string()),
            ack_policy: jetstream::consumer::AckPolicy::Explicit,
            ..Default::default()
        })
        .await?;
    
    // 消费消息
    let mut messages = consumer.fetch().max_messages(10).messages().await?;
    while let Some(message) = messages.next().await {
        let message = message?;
        println!("消费消息: {}", String::from_utf8_lossy(&message.payload));
        message.ack().await?;
    }
    
    Ok(())
}
```

**消息回溯**:

```rust
use async_nats::jetstream;
use futures::StreamExt;

async fn message_replay_example() -> anyhow::Result<()> {
    let client = async_nats::connect("nats://localhost:4222").await?;
    let jetstream = jetstream::new(client);
    
    let stream = jetstream.get_stream("ORDERS").await?;
    
    // 从特定序列号开始消费
    let consumer = stream
        .create_consumer(jetstream::consumer::pull::Config {
            deliver_policy: jetstream::consumer::DeliverPolicy::ByStartSequence {
                start_sequence: 50,  // 从第50条消息开始
            },
            ack_policy: jetstream::consumer::AckPolicy::Explicit,
            ..Default::default()
        })
        .await?;
    
    // 从头开始重放所有消息
    let consumer_from_start = stream
        .create_consumer(jetstream::consumer::pull::Config {
            deliver_policy: jetstream::consumer::DeliverPolicy::All,
            replay_policy: jetstream::consumer::ReplayPolicy::Instant,
            ..Default::default()
        })
        .await?;
    
    println!("可以回溯任意历史消息！");
    
    Ok(())
}
```

---

### NATS 高级特性

**通配符订阅**:

```rust
async fn wildcard_subscriptions() -> anyhow::Result<()> {
    let client = async_nats::connect("nats://localhost:4222").await?;
    
    // 单级通配符
    let mut sub1 = client.subscribe("events.*.created").await?;
    // 匹配: events.user.created, events.order.created
    // 不匹配: events.user.updated, events.user.created.v2
    
    // 多级通配符
    let mut sub2 = client.subscribe("logs.>").await?;
    // 匹配: logs.info, logs.error.database, logs.warn.api.timeout
    
    // 发布测试
    client.publish("events.user.created", "test".into()).await?;
    client.publish("logs.error.database", "DB error".into()).await?;
    
    Ok(())
}
```

**消息头 (Headers)**:

```rust
use async_nats::HeaderMap;

async fn message_headers_example() -> anyhow::Result<()> {
    let client = async_nats::connect("nats://localhost:4222").await?;
    
    // 创建带 Header 的消息
    let mut headers = HeaderMap::new();
    headers.insert("Content-Type", "application/json");
    headers.insert("User-ID", "12345");
    headers.insert("Request-ID", "req-abc-123");
    
    client
        .publish_with_headers(
            "api.requests",
            headers,
            r#"{"action": "create_order"}"#.into(),
        )
        .await?;
    
    // 接收并读取 Headers
    let mut subscriber = client.subscribe("api.requests").await?;
    if let Some(message) = subscriber.next().await {
        if let Some(headers) = message.headers {
            println!("User-ID: {:?}", headers.get("User-ID"));
            println!("Request-ID: {:?}", headers.get("Request-ID"));
        }
    }
    
    Ok(())
}
```

**连接选项与重连**:

```rust
use async_nats::ConnectOptions;
use std::time::Duration;

async fn connection_options_example() -> anyhow::Result<()> {
    let client = ConnectOptions::new()
        .name("my-service")  // 连接名称
        .retry_on_initial_connect()  // 初始连接失败时重试
        .max_reconnects(10)  // 最大重连次数
        .reconnect_delay_callback(|attempts| {
            // 自定义重连延迟（指数退避）
            Duration::from_millis(100 * 2_u64.pow(attempts as u32))
        })
        .disconnect_callback(|| {
            println!("与 NATS 断开连接");
        })
        .reconnect_callback(|| {
            println!("重新连接到 NATS");
        })
        .connect("nats://localhost:4222")
        .await?;
    
    Ok(())
}
```

---

## Kafka 完整实战

### Kafka 核心概念

详细内容请参考 `kafka_pingora.md`，这里提供快速参考：

**核心组件**:

- **Broker**: Kafka 服务器
- **Topic**: 消息主题
- **Partition**: 分区，实现并行
- **Producer**: 生产者
- **Consumer**: 消费者
- **Consumer Group**: 消费者组

---

### Kafka 生产者实现

**快速开始**:

```rust
use rdkafka::config::ClientConfig;
use rdkafka::producer::{FutureProducer, FutureRecord};
use std::time::Duration;

async fn kafka_producer_example() -> anyhow::Result<()> {
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .set("message.timeout.ms", "5000")
        .create()?;
    
    // 发送消息
    let delivery_status = producer
        .send(
            FutureRecord::to("my-topic")
                .payload("Hello Kafka")
                .key("key-1"),
            Duration::from_secs(0),
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

完整的 Kafka 生产者、消费者、事务、性能优化等内容请参考 `kafka_pingora.md`。

---

## MQTT 完整实战

### MQTT 核心概念

**MQTT 协议特点**:

- **轻量级**: 协议开销小，适合低带宽网络
- **双向通信**: 支持设备到服务器和服务器到设备
- **QoS 保证**: 3种服务质量级别
- **遗嘱消息**: 异常断连通知
- **保留消息**: 新订阅者可获取最新状态

**MQTT 架构**:

```text
Publisher (Device)  →  MQTT Broker  →  Subscriber (App)
                         ↓
                    (可选) 持久化会话
```

---

### MQTT QoS 详解

**QoS 级别对比**:

| QoS | 保证 | 性能 | 适用场景 |
|-----|------|------|---------|
| **0** | At most once (最多一次) | 最快 | 环境监测、不重要数据 |
| **1** | At least once (至少一次) | 中等 | 日志、告警（可重复） |
| **2** | Exactly once (恰好一次) | 最慢 | 支付、控制命令 |

---

### MQTT 快速开始

**环境准备**:

```bash
# Docker 启动 Mosquitto (MQTT Broker)
docker run -d --name mosquitto -p 1883:1883 \
  -p 9001:9001 eclipse-mosquitto:latest
```

**依赖配置**:

```toml
[dependencies]
rumqttc = "0.24"
tokio = { version = "1", features = ["full"] }
serde = { version = "1", features = ["derive"] }
serde_json = "1"
```

**最简单的发布-订阅**:

```rust
use rumqttc::{MqttOptions, AsyncClient, QoS, Event, Packet};
use tokio::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 创建 MQTT 客户端选项
    let mut mqttoptions = MqttOptions::new("rust-client-1", "localhost", 1883);
    mqttoptions.set_keep_alive(Duration::from_secs(60));
    
    // 创建客户端和事件循环
    let (client, mut eventloop) = AsyncClient::new(mqttoptions, 10);
    
    // 订阅主题
    client.subscribe("sensors/temperature", QoS::AtMostOnce).await?;
    
    // 在另一个任务中发布消息
    let publisher = client.clone();
    tokio::spawn(async move {
        for i in 0..10 {
            let payload = format!(r#"{{"temp": {}}}"#, 20 + i);
            publisher
                .publish("sensors/temperature", QoS::AtMostOnce, false, payload)
                .await
                .unwrap();
            tokio::time::sleep(Duration::from_secs(1)).await;
        }
    });
    
    // 接收消息
    loop {
        match eventloop.poll().await {
            Ok(Event::Incoming(Packet::Publish(publish))) => {
                let payload = String::from_utf8_lossy(&publish.payload);
                println!("收到消息 [{}]: {}", publish.topic, payload);
            }
            Ok(_) => {}
            Err(e) => {
                eprintln!("错误: {:?}", e);
                break;
            }
        }
    }
    
    Ok(())
}
```

**QoS 级别示例**:

```rust
use rumqttc::{AsyncClient, QoS};

async fn qos_examples(client: &AsyncClient) -> anyhow::Result<()> {
    // QoS 0: 最多一次，最快，可能丢失
    client
        .publish("sensors/humidity", QoS::AtMostOnce, false, "60%")
        .await?;
    
    // QoS 1: 至少一次，可能重复
    client
        .publish("alerts/temperature", QoS::AtLeastOnce, false, "High temp!")
        .await?;
    
    // QoS 2: 恰好一次，最慢，但最可靠
    client
        .publish("commands/door/lock", QoS::ExactlyOnce, false, "LOCK")
        .await?;
    
    Ok(())
}
```

---

### MQTT 物联网场景

**场景 1: 智能家居温度监控**:

```rust
use rumqttc::{MqttOptions, AsyncClient, QoS, Event, Packet};
use serde::{Deserialize, Serialize};
use tokio::time::Duration;

#[derive(Serialize, Deserialize, Debug)]
struct TemperatureReading {
    device_id: String,
    temperature: f32,
    humidity: f32,
    timestamp: u64,
}

async fn smart_home_temperature_monitor() -> anyhow::Result<()> {
    let mut mqttoptions = MqttOptions::new("home-monitor", "localhost", 1883);
    mqttoptions.set_keep_alive(Duration::from_secs(60));
    
    let (client, mut eventloop) = AsyncClient::new(mqttoptions, 10);
    
    // 订阅所有房间的温度传感器
    client.subscribe("home/+/temperature", QoS::AtLeastOnce).await?;
    
    // 模拟传感器发送数据
    let publisher = client.clone();
    tokio::spawn(async move {
        let rooms = vec!["living_room", "bedroom", "kitchen"];
        loop {
            for room in &rooms {
                let reading = TemperatureReading {
                    device_id: format!("sensor-{}", room),
                    temperature: 20.0 + (rand::random::<f32>() * 5.0),
                    humidity: 50.0 + (rand::random::<f32>() * 20.0),
                    timestamp: std::time::SystemTime::now()
                        .duration_since(std::time::UNIX_EPOCH)
                        .unwrap()
                        .as_secs(),
                };
                
                let payload = serde_json::to_string(&reading).unwrap();
                let topic = format!("home/{}/temperature", room);
                
                publisher
                    .publish(topic, QoS::AtLeastOnce, false, payload)
                    .await
                    .unwrap();
            }
            tokio::time::sleep(Duration::from_secs(5)).await;
        }
    });
    
    // 监控和告警
    loop {
        if let Ok(Event::Incoming(Packet::Publish(publish))) = eventloop.poll().await {
            let payload = String::from_utf8_lossy(&publish.payload);
            if let Ok(reading) = serde_json::from_str::<TemperatureReading>(&payload) {
                println!("[{}] 温度: {:.1}°C, 湿度: {:.1}%", 
                        reading.device_id, reading.temperature, reading.humidity);
                
                // 温度告警
                if reading.temperature > 25.0 {
                    client
                        .publish(
                            "home/alerts/high-temperature",
                            QoS::AtLeastOnce,
                            false,
                            format!("{} 温度过高: {:.1}°C", reading.device_id, reading.temperature),
                        )
                        .await?;
                }
            }
        }
    }
}
```

**场景 2: 设备控制（遗嘱消息）**:

```rust
use rumqttc::{MqttOptions, AsyncClient, QoS, LastWill};

async fn device_control_with_lwt() -> anyhow::Result<()> {
    let mut mqttoptions = MqttOptions::new("device-controller", "localhost", 1883);
    
    // 设置遗嘱消息 (Last Will and Testament)
    let lwt = LastWill::new(
        "devices/controller/status",
        "OFFLINE",
        QoS::AtLeastOnce,
        false,
    );
    mqttoptions.set_last_will(lwt);
    mqttoptions.set_keep_alive(Duration::from_secs(10));
    
    let (client, mut eventloop) = AsyncClient::new(mqttoptions, 10);
    
    // 上线通知
    client
        .publish("devices/controller/status", QoS::AtLeastOnce, true, "ONLINE")
        .await?;
    
    // 订阅控制命令
    client.subscribe("devices/+/command", QoS::AtLeastOnce).await?;
    
    // 处理命令
    loop {
        if let Ok(Event::Incoming(Packet::Publish(publish))) = eventloop.poll().await {
            let device_id = publish.topic.split('/').nth(1).unwrap_or("unknown");
            let command = String::from_utf8_lossy(&publish.payload);
            
            println!("设备 {} 收到命令: {}", device_id, command);
            
            // 执行命令并反馈
            let result = execute_device_command(&command);
            let response_topic = format!("devices/{}/response", device_id);
            client
                .publish(response_topic, QoS::AtLeastOnce, false, result)
                .await?;
        }
    }
}

fn execute_device_command(command: &str) -> String {
    match command {
        "ON" => "Device turned ON".to_string(),
        "OFF" => "Device turned OFF".to_string(),
        _ => format!("Unknown command: {}", command),
    }
}
```

**场景 3: 保留消息（设备状态）**:

```rust
async fn retained_messages_example() -> anyhow::Result<()> {
    let mut mqttoptions = MqttOptions::new("status-publisher", "localhost", 1883);
    let (client, _) = AsyncClient::new(mqttoptions, 10);
    
    // 发布保留消息（retained = true）
    // 新订阅者会立即收到这条消息
    client
        .publish(
            "devices/thermostat/status",
            QoS::AtLeastOnce,
            true,  // retained = true
            r#"{"power": "ON", "target_temp": 22}"#,
        )
        .await?;
    
    println!("状态已发布（保留消息）");
    println!("任何新订阅者都会立即收到这个状态");
    
    Ok(())
}
```

## 架构设计模式

### 模式 1: 事件驱动架构 (EDA)

**使用 NATS 实现微服务通信**:

```rust
// 订单服务发布事件
async fn order_service_publish(client: &async_nats::Client) -> anyhow::Result<()> {
    let event = serde_json::json!({
        "event_type": "OrderCreated",
        "order_id": "ORD-12345",
        "user_id": "USER-789",
        "amount": 99.99,
        "timestamp": chrono::Utc::now().to_rfc3339()
    });
    
    client
        .publish("events.order.created", serde_json::to_vec(&event)?.into())
        .await?;
    
    Ok(())
}

// 库存服务订阅事件
async fn inventory_service_subscribe(client: &async_nats::Client) -> anyhow::Result<()> {
    let mut subscriber = client.subscribe("events.order.>").await?;
    
    while let Some(message) = subscriber.next().await {
        let event: serde_json::Value = serde_json::from_slice(&message.payload)?;
        
        match event["event_type"].as_str() {
            Some("OrderCreated") => {
                let order_id = event["order_id"].as_str().unwrap();
                println!("处理订单: {}", order_id);
                // 减少库存...
            }
            _ => {}
        }
    }
    
    Ok(())
}
```

---

### 模式 2: CQRS (命令查询职责分离)

**使用 Kafka 实现事件溯源**:

```rust
use rdkafka::producer::{FutureProducer, FutureRecord};

// 命令处理器：写入事件
async fn handle_command(producer: &FutureProducer, command: &str) -> anyhow::Result<()> {
    let event = serde_json::json!({
        "type": "AccountDebited",
        "account_id": "ACC-123",
        "amount": 50.0,
        "timestamp": chrono::Utc::now().timestamp()
    });
    
    producer
        .send(
            FutureRecord::to("account-events")
                .key("ACC-123")
                .payload(&serde_json::to_string(&event)?),
            Duration::from_secs(5),
        )
        .await
        .map_err(|(e, _)| e)?;
    
    Ok(())
}

// 查询模型：构建读取视图
async fn build_read_model(consumer: &StreamConsumer) -> anyhow::Result<()> {
    use rdkafka::consumer::{Consumer, StreamConsumer};
    use rdkafka::Message;
    
    consumer.subscribe(&["account-events"])?;
    
    let mut account_balance: std::collections::HashMap<String, f64> = HashMap::new();
    
    loop {
        if let Ok(message) = consumer.recv().await {
            let payload = message.payload_view::<str>().unwrap().unwrap();
            let event: serde_json::Value = serde_json::from_str(payload)?;
            
            let account_id = event["account_id"].as_str().unwrap().to_string();
            let amount = event["amount"].as_f64().unwrap();
            
            match event["type"].as_str() {
                Some("AccountCredited") => {
                    *account_balance.entry(account_id).or_insert(0.0) += amount;
                }
                Some("AccountDebited") => {
                    *account_balance.entry(account_id).or_insert(0.0) -= amount;
                }
                _ => {}
            }
            
            println!("账户余额: {:?}", account_balance);
        }
    }
}
```

---

### 模式 3: Saga 模式 (分布式事务)

**使用消息队列实现 Saga**:

```rust
// Saga 协调器
async fn order_saga_orchestrator(nats: &async_nats::Client) -> anyhow::Result<()> {
    // 1. 创建订单
    nats.publish("commands.order.create", "order-123".into()).await?;
    
    // 2. 预留库存
    let response = nats.request("commands.inventory.reserve", "item-456".into()).await?;
    
    if String::from_utf8_lossy(&response.payload) == "SUCCESS" {
        // 3. 处理支付
        let payment_response = nats.request("commands.payment.process", "payment-789".into()).await?;
        
        if String::from_utf8_lossy(&payment_response.payload) == "SUCCESS" {
            // 4. 完成订单
            nats.publish("commands.order.complete", "order-123".into()).await?;
            println!("订单完成");
        } else {
            // 补偿：释放库存
            nats.publish("commands.inventory.release", "item-456".into()).await?;
            nats.publish("commands.order.cancel", "order-123".into()).await?;
            println!("订单取消（支付失败）");
        }
    } else {
        // 补偿：取消订单
        nats.publish("commands.order.cancel", "order-123".into()).await?;
        println!("订单取消（库存不足）");
    }
    
    Ok(())
}
```

---

## 性能对比与测试

### 延迟测试

**测试代码**:

```rust
use tokio::time::Instant;

async fn measure_latency() -> anyhow::Result<()> {
    // NATS 延迟测试
    let nats_client = async_nats::connect("nats://localhost:4222").await?;
    let start = Instant::now();
    for _ in 0..1000 {
        nats_client.publish("test", "msg".into()).await?;
    }
    let nats_latency = start.elapsed() / 1000;
    println!("NATS 平均延迟: {:?}", nats_latency);
    
    // Kafka 延迟测试
    let kafka_producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", "localhost:9092")
        .create()?;
    let start = Instant::now();
    for _ in 0..1000 {
        kafka_producer
            .send(FutureRecord::to("test").payload("msg"), Duration::from_secs(0))
            .await
            .map_err(|(e, _)| e)?;
    }
    let kafka_latency = start.elapsed() / 1000;
    println!("Kafka 平均延迟: {:?}", kafka_latency);
    
    Ok(())
}
```

**测试结果** (参考值):

| 系统 | P50 | P95 | P99 |
|------|-----|-----|-----|
| NATS | 0.5ms | 1.2ms | 2.5ms |
| Kafka | 3ms | 8ms | 15ms |
| MQTT | 2ms | 5ms | 10ms |

---

### 吞吐量测试

```rust
async fn measure_throughput() -> anyhow::Result<()> {
    let nats_client = async_nats::connect("nats://localhost:4222").await?;
    let message_count = 100_000;
    
    let start = Instant::now();
    for i in 0..message_count {
        nats_client.publish("throughput-test", format!("msg-{}", i).into()).await?;
    }
    let elapsed = start.elapsed();
    let throughput = message_count as f64 / elapsed.as_secs_f64();
    
    println!("NATS 吞吐量: {:.0} msg/s", throughput);
    
    Ok(())
}
```

---

## 生产环境部署

### NATS 集群部署

**Docker Compose 配置**:

```yaml
version: '3.8'
services:
  nats-1:
    image: nats:latest
    ports:
      - "4222:4222"
      - "8222:8222"
    command: >
      -js
      -cluster nats://0.0.0.0:6222
      -routes nats://nats-2:6222,nats://nats-3:6222
  
  nats-2:
    image: nats:latest
    command: >
      -js
      -cluster nats://0.0.0.0:6222
      -routes nats://nats-1:6222,nats://nats-3:6222
  
  nats-3:
    image: nats:latest
    command: >
      -js
      -cluster nats://0.0.0.0:6222
      -routes nats://nats-1:6222,nats://nats-2:6222
```

---

### MQTT 生产配置

**Mosquitto 配置 (mosquitto.conf)**:

```conf
# 基础配置
listener 1883
protocol mqtt

# TLS 配置
listener 8883
cafile /etc/mosquitto/certs/ca.crt
certfile /etc/mosquitto/certs/server.crt
keyfile /etc/mosquitto/certs/server.key
require_certificate false

# 认证
password_file /etc/mosquitto/passwd
allow_anonymous false

# 持久化
persistence true
persistence_location /var/lib/mosquitto/

# 日志
log_dest file /var/log/mosquitto/mosquitto.log
log_type all
```

---

## 监控与可观测性

### Prometheus 指标收集

```rust
use prometheus::{Counter, Histogram, register_counter, register_histogram};

lazy_static::lazy_static! {
    static ref MESSAGES_PUBLISHED: Counter = register_counter!(
        "mq_messages_published_total",
        "Total number of messages published"
    ).unwrap();
    
    static ref MESSAGE_LATENCY: Histogram = register_histogram!(
        "mq_message_latency_seconds",
        "Message publishing latency"
    ).unwrap();
}

async fn publish_with_metrics(client: &async_nats::Client, subject: &str, payload: &str) -> anyhow::Result<()> {
    let timer = MESSAGE_LATENCY.start_timer();
    
    client.publish(subject, payload.into()).await?;
    
    MESSAGES_PUBLISHED.inc();
    timer.observe_duration();
    
    Ok(())
}
```

---

## 故障排查

### 常见问题

**问题 1: NATS 连接超时**:

```rust
// 解决方案: 增加超时和重试
let client = ConnectOptions::new()
    .connect_timeout(Duration::from_secs(10))
    .retry_on_initial_connect()
    .max_reconnects(10)
    .connect("nats://localhost:4222")
    .await?;
```

**问题 2: Kafka Rebalance 导致消息重复**:

```rust
// 解决方案: 幂等消费者
use std::collections::HashSet;

struct IdempotentConsumer {
    processed_ids: HashSet<String>,
}

impl IdempotentConsumer {
    fn process_message(&mut self, message_id: &str, payload: &str) {
        if self.processed_ids.contains(message_id) {
            println!("跳过重复消息: {}", message_id);
            return;
        }
        
        // 处理消息...
        println!("处理消息: {}", payload);
        
        self.processed_ids.insert(message_id.to_string());
    }
}
```

**问题 3: MQTT 连接频繁断开**:

```rust
// 解决方案: 调整 Keep-Alive 和重连策略
let mut mqttoptions = MqttOptions::new("client-1", "localhost", 1883);
mqttoptions.set_keep_alive(Duration::from_secs(30));  // 增加心跳间隔
mqttoptions.set_connection_timeout(60);  // 增加连接超时

// 自动重连已内置在 rumqttc 中
```

---

## 总结

本指南涵盖了三种主流消息系统的完整实战：

### NATS 核心优势

- ✅ 极低延迟 (<1ms)
- ✅ 请求-响应模式
- ✅ JetStream 持久化
- ✅ 简单易用

### Kafka 核心优势

- ✅ 高吞吐量 (1M+ msg/s)
- ✅ 消息回溯
- ✅ 流处理能力
- ✅ 生态成熟

### MQTT 核心优势

- ✅ 轻量级协议
- ✅ QoS 灵活
- ✅ 适合 IoT
- ✅ 网络友好

### 选型建议总结

1. **微服务通信**: NATS (低延迟、请求-响应)
2. **日志收集/流处理**: Kafka (高吞吐、回溯)
3. **物联网设备**: MQTT (轻量、QoS)
4. **混合场景**: 可以组合使用

---

**相关资源**:

- [NATS 官方文档](https://docs.nats.io/)
- [async-nats GitHub](https://github.com/nats-io/nats.rs)
- [Kafka 官方文档](https://kafka.apache.org/documentation/)
- [MQTT 官方文档](https://mqtt.org/)
- [rumqttc GitHub](https://github.com/bytebeamio/rumqtt)

---

**更新日期**: 2025-10-24  
**文档版本**: 1.0  
**反馈**: 如有问题或建议，欢迎提 Issue
