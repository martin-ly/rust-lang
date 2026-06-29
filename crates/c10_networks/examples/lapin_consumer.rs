//! lapin 从队列消费消息示例
//!
//! 运行时需要 RabbitMQ 服务与已存在的队列。默认连接 `amqp://127.0.0.1:5672/%2f`；
//! 可通过 `AMQP_ADDR`、`AMQP_QUEUE` 环境变量覆盖。
//! 本示例仅做编译检查用，运行时若无服务将连接失败。

use futures::StreamExt;
use lapin::options::*;
use lapin::types::FieldTable;
use lapin::{Connection, ConnectionProperties};

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let addr = std::env::var("AMQP_ADDR").unwrap_or_else(|_| "amqp://127.0.0.1:5672/%2f".into());
    let queue = std::env::var("AMQP_QUEUE").unwrap_or_else(|_| "rust-learning-queue".into());

    let conn = Connection::connect(&addr, ConnectionProperties::default()).await?;
    let channel = conn.create_channel().await?;

    channel
        .queue_declare(
            &queue,
            QueueDeclareOptions {
                durable: true,
                ..Default::default()
            },
            FieldTable::default(),
        )
        .await?;

    // 限制未确认消息数量，防止消费者过载。
    channel.basic_qos(10, BasicQosOptions::default()).await?;

    let mut consumer = channel
        .basic_consume(
            &queue,
            "rust-learning-consumer",
            BasicConsumeOptions {
                no_ack: false,
                ..Default::default()
            },
            FieldTable::default(),
        )
        .await?;

    while let Some(delivery) = consumer.next().await {
        let delivery = delivery?;
        match std::str::from_utf8(&delivery.data) {
            Ok(s) => println!("received: {s}"),
            Err(e) => eprintln!("invalid utf-8 payload: {e}"),
        }
        delivery.ack(BasicAckOptions::default()).await?;
    }

    Ok(())
}
