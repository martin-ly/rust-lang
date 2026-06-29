//! lapin 发布消息到队列示例
//!
//! 运行时需要 RabbitMQ 服务。默认连接 `amqp://127.0.0.1:5672/%2f`；
//! 可通过 `AMQP_ADDR` 环境变量覆盖。
//! 目标队列默认为 `rust-learning-queue`；可通过 `AMQP_QUEUE` 环境变量覆盖。
//! 本示例仅做编译检查用，运行时若无服务将连接失败。

use lapin::options::*;
use lapin::publisher_confirm::Confirmation;
use lapin::types::FieldTable;
use lapin::{BasicProperties, Connection, ConnectionProperties};

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

    // 开启 publisher confirm，等待 Broker 确认消息已成功路由。
    channel
        .confirm_select(ConfirmSelectOptions::default())
        .await?;

    for i in 0..10 {
        let payload = format!("hello lapin {i}");
        let confirm = channel
            .basic_publish(
                "",
                &queue,
                BasicPublishOptions::default(),
                payload.as_bytes(),
                BasicProperties::default(),
            )
            .await?;

        match confirm.await? {
            Confirmation::Ack(_) => println!("sent message {i}: {payload}"),
            Confirmation::Nack(_) => eprintln!("message {i} nacked by broker"),
            Confirmation::NotRequested => println!("sent message {i} (no confirm)"),
        }
    }

    Ok(())
}
