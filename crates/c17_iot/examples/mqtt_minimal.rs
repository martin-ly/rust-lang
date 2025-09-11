use rumqttc::{AsyncClient, Event, EventLoop, MqttOptions, Packet, QoS};
use tokio::time::{sleep, Duration};
use std::env;

async fn run() -> anyhow::Result<()> {
    let host = env::var("MQTT_HOST").unwrap_or_else(|_| "localhost".into());
    let port: u16 = env::var("MQTT_PORT").ok().and_then(|v| v.parse().ok()).unwrap_or(1883);
    let client_id = env::var("MQTT_CLIENT_ID").unwrap_or_else(|_| "c17-iot-client".into());
    let sub_topic = env::var("MQTT_SUB").unwrap_or_else(|_| "c17/demo".into());
    let pub_topic = env::var("MQTT_PUB").unwrap_or_else(|_| "c17/demo".into());
    let qos_num: u8 = env::var("MQTT_QOS").ok().and_then(|v| v.parse().ok()).unwrap_or(0);
    let iterations: usize = env::var("ITER").ok().and_then(|v| v.parse().ok()).unwrap_or(20);
    let poll_timeout_ms: u64 = env::var("POLL_TIMEOUT_MS").ok().and_then(|v| v.parse().ok()).unwrap_or(100);

    let qos = match qos_num { 2 => QoS::ExactlyOnce, 1 => QoS::AtLeastOnce, _ => QoS::AtMostOnce };

    let mut opts = MqttOptions::new(client_id, host, port);
    opts.set_keep_alive(Duration::from_secs(10));

    let (client, mut eventloop): (AsyncClient, EventLoop) = AsyncClient::new(opts, 10);

    client.subscribe(&sub_topic, qos).await?;
    client.publish(&pub_topic, qos, false, b"hello-iot").await?;

    // 简短事件轮询，验证收发
    let mut got_suback = false;
    let mut got_publish = false;
    let mut ticks: usize = 0;
    let deadline = tokio::time::Instant::now() + Duration::from_secs(2);
    while tokio::time::Instant::now() < deadline && ticks < iterations {
        match tokio::time::timeout(Duration::from_millis(poll_timeout_ms), eventloop.poll()).await {
            Ok(Ok(Event::Incoming(Packet::SubAck(_)))) => {
                got_suback = true;
            }
            Ok(Ok(Event::Incoming(Packet::Publish(p)))) => {
                println!("recv topic={} payload={:?}", p.topic, String::from_utf8_lossy(&p.payload));
                got_publish = true;
            }
            Ok(Ok(_)) => {}
            Ok(Err(e)) => {
                eprintln!("eventloop error: {e}");
                break;
            }
            Err(_) => {}
        }
        ticks += 1;
    }

    println!("mqtt ok: suback={} publish={} ", got_suback, got_publish);
    sleep(Duration::from_millis(50)).await;
    Ok(())
}

#[tokio::main]
async fn main() {
    if let Err(e) = run().await {
        eprintln!("error: {e:?}");
    }
}


