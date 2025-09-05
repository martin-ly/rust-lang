#[cfg(feature = "kv-redis")]
use crate::kv::KeyValueStore;

#[cfg(feature = "kv-redis")]
use redis::aio::ConnectionManager;

#[cfg(feature = "kv-redis")]
pub struct RedisStore {
    manager: tokio::sync::Mutex<ConnectionManager>,
}

#[cfg(feature = "kv-redis")]
impl RedisStore {
    pub async fn connect(url: &str) -> crate::error::Result<Self> {
        let client = redis::Client::open(url)?;
        let conn = client.get_tokio_connection().await?;
        let manager = ConnectionManager::new(conn).await?;
        Ok(Self { manager: tokio::sync::Mutex::new(manager) })
    }

    pub async fn connect_with(cfg: crate::config::RedisConfig) -> crate::error::Result<Self> {
        let url = cfg.url.clone();
        let retry = cfg.retry.clone();
        crate::util::retry_async(&retry, || async {
            let client = redis::Client::open(url.as_str())?;
            let conn = client.get_tokio_connection().await?;
            let manager = ConnectionManager::new(conn).await?;
            Ok(Self { manager: tokio::sync::Mutex::new(manager) })
        }).await
    }
}

#[cfg(feature = "kv-redis")]
#[async_trait::async_trait]
impl KeyValueStore for RedisStore {
    async fn get(&self, key: &str) -> crate::error::Result<Option<Vec<u8>>> {
        let mut guard = self.manager.lock().await;
        let mut cmd = redis::cmd("GET");
        cmd.arg(key);
        let res: Option<Vec<u8>> = crate::util::maybe_timeout(2_000, async { Ok(cmd.query_async(&mut *guard).await?) }).await?;
        Ok(res)
    }

    async fn set(&self, key: &str, value: &[u8]) -> crate::error::Result<()> {
        let mut guard = self.manager.lock().await;
        let mut cmd = redis::cmd("SET");
        cmd.arg(key).arg(value);
        crate::util::maybe_timeout(2_000, async { Ok::<(), crate::error::Error>(cmd.query_async(&mut *guard).await?) }).await?;
        Ok(())
    }

    async fn del(&self, key: &str) -> crate::error::Result<()> {
        let mut guard = self.manager.lock().await;
        let mut cmd = redis::cmd("DEL");
        cmd.arg(key);
        let _: i64 = crate::util::maybe_timeout(2_000, async { Ok(cmd.query_async(&mut *guard).await?) }).await?;
        Ok(())
    }
}

