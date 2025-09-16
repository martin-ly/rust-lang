use rumqttc::{AsyncClient, EventLoop, MqttOptions, QoS, Transport};
use std::env;
use tokio::time::Duration;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 需要本地支持 TLS 的 MQTT Broker（自签或受信 CA），下方为跳过证书验证的演示配置
    // 生产环境请务必启用证书校验并加载 CA/客户端证书
    let host = env::var("MQTT_HOST").unwrap_or_else(|_| "localhost".into());
    let port: u16 = env::var("MQTT_PORT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(8883);
    let client_id = env::var("MQTT_CLIENT_ID").unwrap_or_else(|_| "c17-iot-tls".into());
    let sub_topic = env::var("MQTT_SUB").unwrap_or_else(|_| "c17/tls".into());
    let pub_topic = env::var("MQTT_PUB").unwrap_or_else(|_| "c17/tls".into());
    // 使用 Simple TLS 配置以保证示例可编译运行（演示用途）。
    let tls = rumqttc::TlsConfiguration::Simple {
        ca: Vec::new(),
        alpn: None,
        client_auth: None,
    };
    let mut opts = MqttOptions::new(client_id, host, port);
    opts.set_transport(Transport::Tls(tls));
    opts.set_keep_alive(Duration::from_secs(10));

    let (client, mut eventloop): (AsyncClient, EventLoop) = AsyncClient::new(opts, 10);
    client.subscribe(&sub_topic, QoS::AtLeastOnce).await?;
    client
        .publish(&pub_topic, QoS::AtLeastOnce, false, b"hello-tls")
        .await?;

    // 简短轮询
    for _ in 0..10 {
        match eventloop.poll().await {
            Ok(_ev) => {}
            Err(e) => {
                eprintln!("eventloop error: {e}");
                break;
            }
        }
    }
    Ok(())
}
