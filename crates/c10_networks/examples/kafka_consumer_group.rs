//! rdkafka Consumer Group 消费示例
//!
//! 运行时需要 Kafka 服务与已存在的 topic。默认连接 `localhost:9092`；
//! 可通过 `KAFKA_BOOTSTRAP`、`KAFKA_TOPIC`、`KAFKA_GROUP_ID` 环境变量覆盖。
//! 本示例仅做编译检查用，运行时若无服务将连接失败。

use futures::StreamExt;
use rdkafka::config::ClientConfig;
use rdkafka::consumer::{CommitMode, Consumer, StreamConsumer};
use rdkafka::message::Message;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let bootstrap = std::env::var("KAFKA_BOOTSTRAP").unwrap_or_else(|_| "localhost:9092".into());
    let topic = std::env::var("KAFKA_TOPIC").unwrap_or_else(|_| "rust-learning-topic".into());
    let group = std::env::var("KAFKA_GROUP_ID").unwrap_or_else(|_| "rust-learning-group".into());

    let consumer: StreamConsumer = ClientConfig::new()
        .set("bootstrap.servers", &bootstrap)
        .set("group.id", &group)
        .set("enable.auto.commit", "false")
        .set("auto.offset.reset", "earliest")
        .create()?;

    consumer.subscribe(&[&topic])?;

    let mut stream = consumer.stream();
    while let Some(result) = stream.next().await {
        match result {
            Ok(msg) => {
                match msg.payload_view::<str>() {
                    Some(Ok(s)) => println!(
                        "topic={} partition={} offset={} key={:?} payload={}",
                        msg.topic(),
                        msg.partition(),
                        msg.offset(),
                        msg.key(),
                        s
                    ),
                    Some(Err(e)) => eprintln!("invalid utf-8 at offset {}: {e}", msg.offset()),
                    None => println!("empty payload at offset {}", msg.offset()),
                }
                if let Err(e) = consumer.commit_message(&msg, CommitMode::Async) {
                    eprintln!("commit failed at offset {}: {e}", msg.offset());
                }
            }
            Err(e) => eprintln!("consumer error: {e}"),
        }
    }

    Ok(())
}
