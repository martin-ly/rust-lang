#[cfg(feature = "mq-mqtt")]
use crate::mq::mq::{MessageConsumer, MessageProducer};

#[cfg(feature = "mq-mqtt")]
pub struct MqttProducer {
    client: rumqttc::AsyncClient,
}

#[cfg(feature = "mq-mqtt")]
pub struct MqttConsumer {
    eventloop: std::sync::Arc<tokio::sync::Mutex<rumqttc::EventLoop>>,
}

#[cfg(feature = "mq-mqtt")]
impl MqttProducer {
    pub async fn connect(host: &str, port: u16, client_id: &str) -> crate::error::Result<(Self, MqttConsumer)> {
        let mut opts = rumqttc::MqttOptions::new(client_id, host, port);
        opts.set_keep_alive(std::time::Duration::from_secs(5));
        let (client, eventloop) = rumqttc::AsyncClient::new(opts, 10);
        Ok((Self { client }, MqttConsumer { eventloop: std::sync::Arc::new(tokio::sync::Mutex::new(eventloop)) }))
    }

    pub async fn connect_with(cfg: crate::config::MqttConfig) -> crate::error::Result<(Self, MqttConsumer)> {
        let retry = cfg.retry.clone();
        crate::util::retry_async(&retry, || async {
            let mut opts = rumqttc::MqttOptions::new(cfg.client_id.clone(), cfg.host.clone(), cfg.port);
            opts.set_keep_alive(std::time::Duration::from_secs(5));
            let (client, eventloop) = rumqttc::AsyncClient::new(opts, 10);
            Ok((Self { client }, MqttConsumer { eventloop: std::sync::Arc::new(tokio::sync::Mutex::new(eventloop)) }))
        }).await
    }
}

#[cfg(feature = "mq-mqtt")]
#[async_trait::async_trait]
impl MessageProducer for MqttProducer {
    async fn send(&self, topic: &str, payload: &[u8]) -> crate::error::Result<()> {
        self.client.publish(topic, rumqttc::QoS::AtLeastOnce, false, payload).await?;
        Ok(())
    }
}

#[cfg(feature = "mq-mqtt")]
#[async_trait::async_trait]
impl MessageConsumer for MqttConsumer {
    async fn subscribe(&self, _topic: &str) -> crate::error::Result<()> { Ok(()) }
    async fn next(&mut self) -> crate::error::Result<Option<Vec<u8>>> {
        let mut eventloop = self.eventloop.lock().await;
        match eventloop.poll().await? {
            rumqttc::Event::Incoming(rumqttc::Packet::Publish(p)) => Ok(Some(p.payload.to_vec())),
            _ => Ok(None),
        }
    }
}

