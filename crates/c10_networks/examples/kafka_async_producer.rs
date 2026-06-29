//! rdkafka 异步 Producer 示例
//!
//! 运行时需要 Kafka 服务。默认连接 `localhost:9092`；可通过 `KAFKA_BOOTSTRAP` 环境变量覆盖。
//! 目标 topic 默认为 `rust-learning-topic`；可通过 `KAFKA_TOPIC` 环境变量覆盖。
//! 本示例仅做编译检查用，运行时若无服务将连接失败。

use rdkafka::config::ClientConfig;
use rdkafka::producer::{FutureProducer, FutureRecord, Producer};
use std::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let bootstrap = std::env::var("KAFKA_BOOTSTRAP").unwrap_or_else(|_| "localhost:9092".into());
    let topic = std::env::var("KAFKA_TOPIC").unwrap_or_else(|_| "rust-learning-topic".into());

    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", &bootstrap)
        .set("message.timeout.ms", "5000")
        .set("enable.idempotence", "true")
        .create()?;

    for i in 0..10 {
        let key = format!("key-{i}");
        let payload = format!("hello kafka {i}");
        let record = FutureRecord::to(&topic).payload(&payload).key(&key);

        match producer.send(record, Duration::from_secs(5)).await {
            Ok((partition, offset)) => {
                println!("sent message {i} to partition={partition} offset={offset}");
            }
            Err((e, _)) => {
                eprintln!("failed to send message {i}: {e}");
            }
        }
    }

    // 在关闭前刷出 librdkafka 内部队列中的剩余消息。
    producer.flush(Duration::from_secs(5))?;
    Ok(())
}
