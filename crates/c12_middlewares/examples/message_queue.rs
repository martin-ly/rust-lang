//use c12_middlewares::prelude::*;
//use c12_middlewares::config::{NatsConfig, MqttConfig};

#[cfg(feature = "obs")]
fn init_tracing() {
    tracing_subscriber::fmt::init();
}

#[allow(dead_code)]
#[cfg(not(feature = "obs"))]
fn init_tracing() {}

#[cfg(feature = "tokio")]
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_tracing();

    println!("=== 消息队列示例 ===");

    // NATS 示例
    #[cfg(feature = "mq-nats")]
    {
        println!("\n--- NATS 发布/订阅 ---");
        let producer = c12_middlewares::mq::nats_client::NatsProducer::connect_with(
            NatsConfig::new("nats://127.0.0.1:4222", "demo.subject"),
        )
        .await?;

        let mut consumer = c12_middlewares::mq::nats_client::NatsConsumer::connect_with(
            NatsConfig::new("nats://127.0.0.1:4222", "demo.subject"),
        )
        .await?;

        producer.send("demo.subject", b"Hello NATS!").await?;
        if let Some(msg) = consumer.next().await? {
            println!("NATS 收到消息: {:?}", msg);
        }
    }

    // MQTT 示例
    #[cfg(feature = "mq-mqtt")]
    {
        println!("\n--- MQTT 发布/订阅 ---");
        let (producer, mut consumer) =
            c12_middlewares::mq::mqtt_client::MqttProducer::connect_with(MqttConfig::new(
                "127.0.0.1",
                1883,
                "demo_client",
            ))
            .await?;

        producer.send("demo/topic", b"Hello MQTT!").await?;
        if let Some(msg) = consumer.next().await? {
            println!("MQTT 收到消息: {:?}", msg);
        }
    }

    println!("\n消息队列示例完成！");
    Ok(())
}

#[cfg(not(feature = "tokio"))]
fn main() {
    println!("此示例需要 tokio 特性才能运行");
    println!("请使用: cargo run --example message_queue --features mq-nats,mq-mqtt,tokio");
}
