# Lapin/RDKafka 消息队列形式化分析

> **主题**: AMQP/Kafka异步客户端
>
> **形式化框架**: 消息确认 + 分区策略
>
> **参考**: lapin Documentation; rdkafka Documentation

---

## 目录

- [Lapin/RDKafka 消息队列形式化分析](#lapinrdkafka-消息队列形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. AMQP语义](#2-amqp语义)
    - [定理 2.1 (确认模式)](#定理-21-确认模式)
    - [定理 2.2 (QoS预取)](#定理-22-qos预取)
  - [3. Kafka分区](#3-kafka分区)
    - [定理 3.1 (分区分配)](#定理-31-分区分配)
    - [定理 3.2 (偏移提交)](#定理-32-偏移提交)
  - [4. 消费语义](#4-消费语义)
    - [定理 4.1 (至少一次)](#定理-41-至少一次)
  - [5. 反例](#5-反例)
    - [反例 5.1 (先确认后处理)](#反例-51-先确认后处理)
    - [反例 5.2 (自动提交)](#反例-52-自动提交)

---

## 1. 引言

消息队列客户端:

- **Lapin**: RabbitMQ/AMQP客户端
- **RDKafka**: Apache Kafka客户端

---

## 2. AMQP语义

### 定理 2.1 (确认模式)

| 模式 | 语义 | 可靠性 |
|------|------|--------|
| NO_ACK | 无确认 | 可能丢失 |
| ACK | 手动确认 | 至少一次 |
| NACK(requeue) | 拒绝重入队 | 可重试 |
| NACK(drop) | 丢弃 | 死信 |

```rust
let options = BasicConsumeOptions {
    no_ack: false,  // 手动确认
    ..Default::default()
};
```

∎

### 定理 2.2 (QoS预取)

> 控制未确认消息数量。

```rust
channel
    .basic_qos(10, BasicQosOptions::default())  // 最多10条未确认
    .await?;
```

∎

---

## 3. Kafka分区

### 定理 3.1 (分区分配)

> 消费者组内分区自动分配。

```rust
let consumer: StreamConsumer = ClientConfig::new()
    .set("group.id", "my_group")
    .set("enable.auto.commit", "false")  // 手动提交
    .create()?;
```

∎

### 定理 3.2 (偏移提交)

> 业务处理后提交偏移。

```rust
consumer.commit_message(&message, CommitMode::Async)?;
```

∎

---

## 4. 消费语义

### 定理 4.1 (至少一次)

> 手动确认保证至少一次投递。

```rust
// 处理完成后再确认
deliveries.for_each(|delivery| async move {
    let delivery = delivery.expect("error");
    process(delivery.data).await;
    channel.basic_ack(delivery.delivery_tag, BasicAckOptions::default()).await;
});
```

∎

---

## 5. 反例

### 反例 5.1 (先确认后处理)

```rust
// 危险: 消息可能丢失
channel.basic_ack(tag, opts).await?;
process(message).await;  // 失败则消息丢失

// 正确: 处理完成再确认
process(message).await;
channel.basic_ack(tag, opts).await?;
```

### 反例 5.2 (自动提交)

```rust
// 危险: 自动提交可能丢失消息
.set("enable.auto.commit", "true")

// 正确: 手动提交，业务成功后
```

---

*文档版本: 1.0.0*
*定理数量: 5个*
