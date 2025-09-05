use async_trait::async_trait;
use crate::error::Result;

#[async_trait]
pub trait MessageProducer {
    async fn send(&self, topic: &str, payload: &[u8]) -> Result<()>;
}

#[async_trait]
pub trait MessageConsumer {
    async fn subscribe(&self, topic: &str) -> Result<()>;
    async fn next(&mut self) -> Result<Option<Vec<u8>>>;
}

