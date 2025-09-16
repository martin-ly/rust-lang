use rumqttc::{AsyncClient, EventLoop, MqttOptions, QoS, Transport};
// 证书加载留作扩展，当前示例使用空 CA 仅为演示编译
use std::env;
use tokio::time::Duration;

fn load_ca(path: &str) -> anyhow::Result<Vec<u8>> {
    use std::fs;
    let bytes = fs::read(path)?;
    Ok(bytes)
}

// 如需双向认证，可在此处扩展加载客户端证书与私钥逻辑

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 可配置 CA 路径与连接参数
    let ca_path = env::var("CA_PATH").unwrap_or_else(|_| "./examples/certs/ca.crt".into());
    let ca_bytes = load_ca(&ca_path).unwrap_or_else(|_| Vec::new());
    let host = env::var("MQTT_HOST").unwrap_or_else(|_| "localhost".into());
    let port: u16 = env::var("MQTT_PORT")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(8883);
    let client_id = env::var("MQTT_CLIENT_ID").unwrap_or_else(|_| "c17-iot-tls-strict".into());
    let sub_topic = env::var("MQTT_SUB").unwrap_or_else(|_| "c17/tls".into());
    let pub_topic = env::var("MQTT_PUB").unwrap_or_else(|_| "c17/tls".into());

    let tls = rumqttc::TlsConfiguration::Simple {
        ca: ca_bytes,
        alpn: None,
        client_auth: None,
    };

    let mut opts = MqttOptions::new(client_id, host, port);
    opts.set_transport(Transport::Tls(tls));
    opts.set_keep_alive(Duration::from_secs(10));

    let (client, mut eventloop): (AsyncClient, EventLoop) = AsyncClient::new(opts, 10);
    client.subscribe(&sub_topic, QoS::AtLeastOnce).await?;
    client
        .publish(&pub_topic, QoS::AtLeastOnce, false, b"hello-tls-strict")
        .await?;

    for _ in 0..10 {
        let _ = eventloop.poll().await;
    }
    Ok(())
}
