use async_trait::async_trait;
use crate::error::Result;

#[async_trait]
pub trait KeyValueStore {
    async fn get(&self, key: &str) -> Result<Option<Vec<u8>>>;
    async fn set(&self, key: &str, value: &[u8]) -> Result<()>;
    async fn del(&self, key: &str) -> Result<()>;
}

