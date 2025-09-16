//! 消息队列演示示例
//!
//! 展示如何使用RabbitMQ、Kafka、NATS、MQTT和Redis进行消息传递。

use c13_microservice::{
    //Config,
    messaging::{Kafka, MQTT, NATS, RabbitMQ, Redis},
};
use tracing::info;
use tracing_subscriber;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt().with_env_filter("info").init();

    info!("启动消息队列演示示例");

    // RabbitMQ连接
    let mut rabbitmq = RabbitMQ::new("amqp://localhost:5672".to_string());
    rabbitmq.connect().await?;

    // Kafka连接
    let mut kafka = Kafka::new(vec!["localhost:9092".to_string()]);
    kafka.connect().await?;

    // NATS连接
    let nats = NATS::new("nats://localhost:4222".to_string());
    nats.connect().await?;

    // MQTT连接
    let mqtt = MQTT::new("localhost".to_string(), 1883);
    mqtt.connect().await?;

    // Redis连接
    let mut redis = Redis::new("redis://localhost:6379".to_string());
    redis.connect().await?;

    info!("所有消息队列连接成功");

    // 模拟消息传递操作
    simulate_messaging_operations().await?;

    Ok(())
}

async fn simulate_messaging_operations() -> Result<(), Box<dyn std::error::Error>> {
    info!("开始模拟消息传递操作");

    // 模拟RabbitMQ操作
    info!("发送消息到RabbitMQ");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

    // 模拟Kafka操作
    info!("发送消息到Kafka");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

    // 模拟NATS操作
    info!("发送消息到NATS");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

    // 模拟MQTT操作
    info!("发送消息到MQTT");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

    // 模拟Redis操作
    info!("发送消息到Redis");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

    info!("消息传递操作完成");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_rabbitmq() {
        let mq = RabbitMQ::new("test://url".to_string());
        assert_eq!(mq.url, "test://url");
    }

    #[tokio::test]
    async fn test_kafka() {
        let kafka = Kafka::new(vec!["test:9092".to_string()]);
        assert_eq!(kafka.brokers, vec!["test:9092"]);
    }

    #[tokio::test]
    async fn test_nats() {
        let nats = NATS::new("test://url".to_string());
        assert_eq!(nats.url, "test://url");
    }

    #[tokio::test]
    async fn test_mqtt() {
        let mqtt = MQTT::new("test".to_string(), 1883);
        assert_eq!(mqtt.broker, "test");
        assert_eq!(mqtt.port, 1883);
    }

    #[tokio::test]
    async fn test_redis() {
        let redis = Redis::new("test://url".to_string());
        assert_eq!(redis.url, "test://url");
    }
}
