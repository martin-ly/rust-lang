# 消息与流（NATS/Kafka/MQTT）

- NATS: `mq-nats`
- Kafka: `mq-kafka`
- MQTT: `mq-mqtt`

接口：`mq::{MessageProducer, MessageConsumer}`

示例（NATS 与 Kafka）：

```rust
use c12_middlewares::mq::{MessageProducer, MessageConsumer};

# async fn demo() -> anyhow::Result<()> {
#[cfg(feature = "mq-nats")]
{
    let prod = c12_middlewares::nats_client::NatsProducer;
    let mut cons = c12_middlewares::nats_client::NatsConsumer;
    cons.subscribe("t").await?;
    prod.send("t", b"hello").await?;
}
Ok(())
}
```

```rust
use c12_middlewares::mq::{MessageProducer, MessageConsumer};

# async fn demo_kafka() -> anyhow::Result<()> {
#[cfg(feature = "mq-kafka")]
{
    let producer = c12_middlewares::kafka_client::KafkaProducer::new(&[
        ("bootstrap.servers", "localhost:9092"),
    ])?;

    let mut consumer = c12_middlewares::kafka_client::KafkaConsumer::new(&[
        ("bootstrap.servers", "localhost:9092"),
        ("group.id", "g1"),
        ("enable.partition.eof", "false"),
        ("auto.offset.reset", "earliest"),
    ], &["t"]) ?;

    producer.send("t", b"hello").await?;
    let _msg = consumer.next().await?;
}
Ok(())
}
```
