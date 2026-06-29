use anyhow::Result;
use futures::StreamExt;
use redis::{AsyncCommands, Client};
use std::time::Duration;
use tokio::time::{sleep, timeout};
use tracing::{info, instrument};

/// Redis Pub/Sub 示例
///
/// 运行前需要启动本地 Redis 服务：
///   redis-server --port 6379
///
/// 本示例演示：
/// - 发布者通过 MultiplexedConnection 发布消息
/// - 订阅者通过 PubSub 接收消息
/// - 使用 on_message() Stream 异步消费
#[tokio::main(flavor = "multi_thread")]
async fn main() -> Result<()> {
    tracing_subscriber::fmt().with_env_filter("info").init();

    let redis_url = "redis://127.0.0.1:6379";
    let channel = "redis_pub_sub:demo";
    let message_count = 5;

    let subscriber = tokio::spawn(subscribe(redis_url, channel, message_count));

    // 给订阅者留出订阅完成的时间
    sleep(Duration::from_millis(200)).await;

    publish_messages(redis_url, channel, message_count).await?;

    // 等待订阅者完成或超时
    match timeout(Duration::from_secs(5), subscriber).await {
        Ok(Ok(Ok(()))) => info!("Subscriber finished successfully"),
        Ok(Ok(Err(e))) => return Err(e),
        Ok(Err(join_err)) => return Err(join_err.into()),
        Err(_) => info!("Subscriber timed out, but publisher completed"),
    }

    Ok(())
}

#[instrument]
async fn subscribe(redis_url: &str, channel: &str, expected: usize) -> Result<()> {
    let client = Client::open(redis_url)?;
    let mut pubsub = client.get_async_pubsub().await?;
    pubsub.subscribe(channel).await?;
    info!(channel, "Subscribed to channel");

    let mut stream = pubsub.on_message();
    let mut received = 0;

    while let Some(msg) = stream.next().await {
        let payload: String = msg.get_payload()?;
        info!(channel, payload, "Received message");
        received += 1;
        if received >= expected {
            break;
        }
    }

    info!(received, expected, "Subscription finished");
    Ok(())
}

#[instrument]
async fn publish_messages(redis_url: &str, channel: &str, count: usize) -> Result<()> {
    let client = Client::open(redis_url)?;
    let mut conn = client.get_multiplexed_async_connection().await?;

    for i in 1..=count {
        let message = format!("message-{i}");
        let _: i64 = conn.publish(channel, &message).await?;
        info!(channel, message, "Published message");
        sleep(Duration::from_millis(100)).await;
    }

    Ok(())
}
