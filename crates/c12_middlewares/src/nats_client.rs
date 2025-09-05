#[cfg(feature = "mq-nats")]
use crate::mq::{MessageConsumer, MessageProducer};

#[cfg(feature = "mq-nats")]
pub struct NatsProducer {
    client: async_nats::Client,
}

#[cfg(feature = "mq-nats")]
pub struct NatsConsumer {
    subscriber: async_nats::Subscriber,
}

#[cfg(feature = "mq-nats")]
impl NatsProducer {
    pub async fn connect(url: &str) -> crate::error::Result<Self> {
        let client = async_nats::connect(url).await?;
        Ok(Self { client })
    }

    pub async fn connect_with(cfg: crate::config::NatsConfig) -> crate::error::Result<Self> {
        let retry = cfg.retry.clone();
        let url = cfg.url.clone();
        crate::util::retry_async(&retry, || async {
            let client = async_nats::connect(url.as_str()).await?;
            Ok(Self { client })
        }).await
    }
}

#[cfg(feature = "mq-nats")]
impl NatsConsumer {
    pub async fn connect(url: &str, subject: &str) -> crate::error::Result<Self> {
        let client = async_nats::connect(url).await?;
        let subscriber = client.subscribe(subject.to_string()).await?;
        Ok(Self { subscriber })
    }

    pub async fn connect_with(cfg: crate::config::NatsConfig) -> crate::error::Result<Self> {
        let retry = cfg.retry.clone();
        let url = cfg.url.clone();
        let subject = cfg.subject.clone();
        crate::util::retry_async(&retry, || async {
            let client = async_nats::connect(url.as_str()).await?;
            let subscriber = client.subscribe(subject.to_string()).await?;
            Ok(Self { subscriber })
        }).await
    }
}

#[cfg(feature = "mq-nats")]
#[async_trait::async_trait]
impl MessageProducer for NatsProducer {
    async fn send(&self, topic: &str, payload: &[u8]) -> crate::error::Result<()> {
        self.client.publish(topic.to_string(), payload.into()).await?;
        Ok(())
    }
}

#[cfg(feature = "mq-nats")]
#[async_trait::async_trait]
impl MessageConsumer for NatsConsumer {
    async fn subscribe(&self, _topic: &str) -> crate::error::Result<()> { Ok(()) }
    async fn next(&mut self) -> crate::error::Result<Option<Vec<u8>>> {
        if let Some(msg) = self.subscriber.next().await { Ok(Some(msg.payload.to_vec())) } else { Ok(None) }
    }
}

