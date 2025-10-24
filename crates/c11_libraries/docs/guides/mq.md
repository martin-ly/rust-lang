# 消息与流（NATS/Kafka/MQTT）

> 适用范围：Rust 1.89+；示例需按需启用特性（`mq-nats|mq-kafka|mq-mqtt`），风格遵循 `../../c10_networks/docs/STYLE.md`。


## 📊 目录

- [特性与语义](#特性与语义)
- [NATS 示例](#nats-示例)
  - [NATS JetStream（草案）](#nats-jetstream草案)
- [Kafka 示例（最小可用草案）](#kafka-示例最小可用草案)
  - [Windows/WSL 环境准备（rdkafka）](#windowswsl-环境准备rdkafka)
- [MQTT 示例](#mqtt-示例)
  - [会话持久化](#会话持久化)
- [设计建议](#设计建议)
- [FAQ](#faq)


- NATS: `mq-nats`
- Kafka: `mq-kafka`（当前为最小骨架，见 `kafka_pingora.md` 现状）
- MQTT: `mq-mqtt`

接口：`mq::{MessageProducer, MessageConsumer}`

## 特性与语义

- NATS：低延迟、at-most-once（JetStream 可达至少一次/保留）
- Kafka：分区日志、至少一次（恰好一次需端到端幂等与事务）
- MQTT：QoS0/1/2；适合 IoT 与边缘设备

## NATS 示例

```rust
use c12_middlewares::mq::{MessageProducer, MessageConsumer};

# async fn demo() -> anyhow::Result<()> {
#[cfg(feature = "mq-nats")]
{
    let prod = c12_middlewares::nats_client::NatsProducer;
    let mut cons = c12_middlewares::nats_client::NatsConsumer;
    cons.subscribe("t").await?;
    prod.send("t", b"hello").await?;
    // let msg = cons.next().await?; // 视接口而定
}
Ok(())
}
```

- 可靠性：基础 NATS 为 at-most-once；如需保留/确认流，使用 JetStream（未来示例将补充）。
- 重连：客户端通常内置重连；应用侧需做好幂等处理。

### NATS JetStream（草案）

```rust
# async fn jetstream_demo() -> anyhow::Result<()> {
#[cfg(feature = "mq-nats")]
{
    use c12_middlewares::nats_client::jetstream::{JsProducer, JsConsumer};
    let p = JsProducer::connect("nats://127.0.0.1:4222", "stream", "subject").await?;
    let mut c = JsConsumer::connect("nats://127.0.0.1:4222", "stream", "consumer").await?;
    p.send(b"hello").await?;
    let _msg = c.next().await?; // ack 语义按实现为准
}
Ok(())
}
```

## Kafka 示例（最小可用草案）

```rust
use c12_middlewares::mq::{MessageProducer, MessageConsumer};

# async fn demo_kafka() -> anyhow::Result<()> {
#[cfg(feature = "mq-kafka")]
{
    use c12_middlewares::kafka_client::{KafkaConfig, KafkaProducer, KafkaConsumer};

    let cfg = KafkaConfig::new("localhost:9092", "g1")
        .with_idempotent_producer(true)
        .with_auto_offset_reset("earliest");

    let producer = KafkaProducer::new_with_config(&cfg)?;
    let mut consumer = KafkaConsumer::new_with_config(&cfg, &["t"]) ?;

    producer.send("t", b"hello").await?; // 幂等生产建议开启
    let _msg = consumer.next().await?;      // 消费后按策略提交位点
}
Ok(())
}
```

- 可靠性：至少一次；建议开启幂等生产与按处理成功后提交位点的策略。
- 安全：SASL/TLS、ACL、分区与顺序保证、再均衡处理见 `kafka_pingora.md` 路线图。

### Windows/WSL 环境准备（rdkafka）

- Windows：
  - 安装 `librdkafka`（可用 vcpkg：`vcpkg install librdkafka:x64-windows`），将动态库路径加入 `PATH`
  - 或使用预编译包并配置 `RDKAFKA_LIB_DIR`/`RDKAFKA_INCLUDE_DIR`
- WSL：
  - `apt-get install librdkafka-dev`，并通过 WSL 构建/运行
- 连接错误排查：
  - 校验 `bootstrap.servers`、SASL/TLS 配置；检查消费组权限与主题分区

## MQTT 示例

```rust
# async fn demo_mqtt() -> anyhow::Result<()> {
#[cfg(feature = "mq-mqtt")]
{
    use c12_middlewares::mqtt_client::{MqttProducer, MqttConsumer};
    let (p, mut c) = MqttProducer::connect("127.0.0.1", 1883, "client-1").await?;
    c.subscribe("t", 1).await?; // QoS 1
    p.publish("t", b"hello", 1).await?;
    let _msg = c.next().await?;
}
Ok(())
}
```

- QoS：根据业务权衡吞吐与可靠性（QoS2 代价更高）。
- 会话：保持会话/遗嘱消息/保留消息等可结合配置。

### 会话持久化

- 选择持久化会话 `clean_session=false`（具体以实现为准），在断连后重新连接并恢复订阅与未完成 QoS 的消息
- 使用遗嘱消息（LWT）在异常断连时通知下游

## 设计建议

- 幂等性：消费者处理逻辑应具备幂等，结合去重键或状态表
- 背压：使用有界通道与批量提交位点/确认
- 可观测：启用 `obs`，记录主题/分区/位点/延迟等指标

## FAQ

- Q: 如何保证有序处理？
  - A: Kafka 按分区内有序；选择合理的分区键。NATS/MQTT 需应用侧约束并发。
- Q: 如何处理消息堆积？
  - A: 提升消费者并发、增加分区、限速生产者；必要时丢弃低优先级。
- Q: 断连后如何恢复？
  - A: 使用客户端重连策略，持久化位点/会话，处理重复投递。
