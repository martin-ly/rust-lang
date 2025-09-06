use async_trait::async_trait;
use crate::error::Result;

#[async_trait]
pub trait KeyValueStore {
    async fn get(&self, key: &str) -> Result<Option<Vec<u8>>>;
    async fn set(&self, key: &str, value: &[u8]) -> Result<()>;
    async fn del(&self, key: &str) -> Result<()>;
    
    // 批量操作（默认实现）
    async fn mget(&self, keys: &[&str]) -> Result<Vec<Option<Vec<u8>>>> {
        let mut results = Vec::with_capacity(keys.len());
        for key in keys {
            results.push(self.get(key).await?);
        }
        Ok(results)
    }
    
    async fn mset(&self, pairs: &[(&str, &[u8])]) -> Result<()> {
        for (key, value) in pairs {
            self.set(key, value).await?;
        }
        Ok(())
    }
}

