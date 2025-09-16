#[cfg(feature = "kafka")]
use rdkafka::config::ClientConfig;
#[cfg(feature = "kafka")]
use rdkafka::producer::{FutureProducer, FutureRecord};
#[cfg(feature = "kafka")]
use std::env;
#[cfg(feature = "kafka")]
use std::time::Duration;

#[cfg(feature = "kafka")]
#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 可配置参数（环境变量，可选，带默认值）
    let broker = env::var("BROKER").unwrap_or_else(|_| "localhost:9092".into());
    let topic = env::var("TOPIC").unwrap_or_else(|_| "c17-iot".into());
    let key = env::var("KEY").unwrap_or_else(|_| "k".into());
    let count: usize = env::var("COUNT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(5);
    let timeout_ms: u64 = env::var("TIMEOUT_MS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(5000);
    let send_timeout = Duration::from_millis(
        env::var("SEND_AWAIT_MS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(0),
    );
    let max_retries: u32 = env::var("MAX_RETRIES")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(3);

    // 需要本地 Kafka (bootstrap.servers)
    let producer: FutureProducer = ClientConfig::new()
        .set("bootstrap.servers", &broker)
        .set("message.timeout.ms", &timeout_ms.to_string())
        .create()?;

    println!(
        "kafka_producer -> broker={} topic={} key={} count={} timeout_ms={} max_retries={} send_await_ms={}",
        broker,
        topic,
        key,
        count,
        timeout_ms,
        max_retries,
        send_timeout.as_millis()
    );

    for i in 0..count {
        let payload = format!("msg-{}", i);

        // 简单重试与退避
        let mut attempt: u32 = 0;
        let mut last_err: Option<String> = None;
        loop {
            let delivery = producer
                .send(
                    FutureRecord::to(&topic).payload(&payload).key(&key),
                    send_timeout,
                )
                .await;
            match delivery {
                Ok(report) => {
                    println!("delivered: {:?}", report);
                    break;
                }
                Err((e, _owned_msg)) => {
                    attempt += 1;
                    last_err = Some(format!("{}", e));
                    if attempt > max_retries {
                        eprintln!(
                            "send failed after {} attempts: payload='{}' err={}",
                            attempt - 1,
                            payload,
                            last_err.unwrap()
                        );
                        break;
                    }
                    let backoff =
                        Duration::from_millis((50u64) * (1u64 << (attempt - 1).min(5) as u64));
                    eprintln!(
                        "send error (attempt {}/{}): {} -> backing off {:?}",
                        attempt, max_retries, e, backoff
                    );
                    tokio::time::sleep(backoff).await;
                }
            }
        }
    }
    Ok(())
}

#[cfg(not(feature = "kafka"))]
fn main() {
    eprintln!(
        "示例未启用 'kafka' 特性。请使用: cargo run -p c17_iot --example kafka_producer --features kafka"
    );
}
