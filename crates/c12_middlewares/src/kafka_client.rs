#[cfg(feature = "mq-kafka")]
use crate::mq::{MessageConsumer, MessageProducer};

#[cfg(feature = "mq-kafka")]
pub struct KafkaProducer {
    inner: rdkafka::producer::FutureProducer,
}

#[cfg(feature = "mq-kafka")]
pub struct KafkaConsumer {
    inner: rdkafka::consumer::StreamConsumer,
    stream: rdkafka::util::AsyncRuntimeTokio,
}

#[cfg(feature = "mq-kafka")]
impl KafkaProducer {
    pub fn new(config: &[( &str, &str )]) -> anyhow::Result<Self> {
        let mut cfg = rdkafka::ClientConfig::new();
        for (k,v) in config { cfg.set(*k, *v); }
        let inner = cfg.create::<rdkafka::producer::FutureProducer>()?;
        Ok(Self { inner })
    }
}

#[cfg(feature = "mq-kafka")]
impl KafkaConsumer {
    pub fn new(config: &[( &str, &str )], topics: &[&str]) -> anyhow::Result<Self> {
        let mut cfg = rdkafka::ClientConfig::new();
        for (k,v) in config { cfg.set(*k, *v); }
        let inner = cfg.create::<rdkafka::consumer::StreamConsumer>()?;
        inner.subscribe(topics)?;
        Ok(Self { inner, stream: rdkafka::util::AsyncRuntimeTokio })
    }
}

#[cfg(feature = "mq-kafka")]
#[async_trait::async_trait]
impl MessageProducer for KafkaProducer {
    async fn send(&self, topic: &str, payload: &[u8]) -> crate::error::Result<()> {
        use rdkafka::producer::FutureRecord;
        self.inner
            .send(FutureRecord::to(topic).payload(payload), std::time::Duration::from_secs(0))
            .await
            .map_err(|(e, _)| e)?;
        Ok(())
    }
}

#[cfg(feature = "mq-kafka")]
#[async_trait::async_trait]
impl MessageConsumer for KafkaConsumer {
    async fn subscribe(&self, _topic: &str) -> crate::error::Result<()> { Ok(()) }
    async fn next(&mut self) -> crate::error::Result<Option<Vec<u8>>> {
        use rdkafka::Message;
        match self.inner.recv().await {
            Ok(m) => Ok(m.payload().map(|p| p.to_vec())),
            Err(e) => Err(e.into()),
        }
    }
}

