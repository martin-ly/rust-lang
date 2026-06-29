use anyhow::Result;
use redis::{Client, Script};
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::time::{sleep, timeout};
use tracing::{error, info, warn};

/// 基于 Redis 的分布式锁示例
///
/// 运行前需要启动本地 Redis 服务：
///   redis-server --port 6379
///
/// 设计要点：
/// - 使用 `SET key value NX EX seconds` 原子获取锁
/// - 使用 Lua 脚本确保只有锁持有者才能释放
/// - 锁值包含时间戳 + UUID，防止误释放其他客户端的锁
/// - 支持锁续期（extend）以应对长任务
#[derive(Clone)]
pub struct RedisDistributedLock {
    client: Client,
    lock_key: String,
    lock_value: String,
    ttl_seconds: u64,
}

impl RedisDistributedLock {
    pub fn new(redis_url: &str, lock_key: &str, ttl_seconds: u64) -> Result<Self> {
        let client = Client::open(redis_url)?;
        let lock_value = format!(
            "{}:{}",
            SystemTime::now().duration_since(UNIX_EPOCH)?.as_millis(),
            uuid::Uuid::new_v4()
        );

        Ok(Self {
            client,
            lock_key: lock_key.to_string(),
            lock_value,
            ttl_seconds,
        })
    }

    /// 非阻塞尝试获取锁
    pub async fn try_lock(&self) -> Result<bool> {
        let mut conn = self.client.get_multiplexed_async_connection().await?;

        let result: Option<String> = redis::cmd("SET")
            .arg(&self.lock_key)
            .arg(&self.lock_value)
            .arg("NX")
            .arg("EX")
            .arg(self.ttl_seconds)
            .query_async(&mut conn)
            .await?;

        Ok(result.is_some())
    }

    /// 阻塞获取锁，带指数退避重试
    pub async fn lock(&self, max_wait: Duration) -> Result<()> {
        let started = SystemTime::now();
        let mut backoff = Duration::from_millis(50);

        loop {
            if self.try_lock().await? {
                info!(lock_key = %self.lock_key, "Lock acquired successfully");
                return Ok(());
            }

            let elapsed = SystemTime::now().duration_since(started)?;
            if elapsed + backoff > max_wait {
                return Err(anyhow::anyhow!("Timeout waiting for lock"));
            }

            sleep(backoff).await;
            backoff = (backoff * 2).min(Duration::from_millis(500));
        }
    }

    /// 释放锁：只有当前持有者才能删除
    pub async fn unlock(&self) -> Result<()> {
        let mut conn = self.client.get_multiplexed_async_connection().await?;

        let script = r#"
            if redis.call("GET", KEYS[1]) == ARGV[1] then
                return redis.call("DEL", KEYS[1])
            else
                return 0
            end
        "#;

        let result: i32 = Script::new(script)
            .key(&self.lock_key)
            .arg(&self.lock_value)
            .invoke_async(&mut conn)
            .await?;

        if result > 0 {
            info!(lock_key = %self.lock_key, "Lock released successfully");
        } else {
            warn!(lock_key = %self.lock_key, "Lock was not held by this instance");
        }

        Ok(())
    }

    /// 续期锁：只有当前持有者才能延长 TTL
    pub async fn extend(&self, additional_seconds: u64) -> Result<bool> {
        let mut conn = self.client.get_multiplexed_async_connection().await?;

        let script = r#"
            if redis.call("GET", KEYS[1]) == ARGV[1] then
                return redis.call("EXPIRE", KEYS[1], ARGV[2])
            else
                return 0
            end
        "#;

        let new_ttl = self.ttl_seconds + additional_seconds;
        let result: i32 = Script::new(script)
            .key(&self.lock_key)
            .arg(&self.lock_value)
            .arg(new_ttl)
            .invoke_async(&mut conn)
            .await?;

        Ok(result > 0)
    }
}

#[tokio::main(flavor = "multi_thread")]
async fn main() -> Result<()> {
    tracing_subscriber::fmt().with_env_filter("info").init();

    let redis_url = "redis://127.0.0.1:6379";
    let lock_key = "redis_distributed_lock:demo";
    let client_count = 5;

    let mut handles = Vec::new();

    for client_id in 1..=client_count {
        let handle = tokio::spawn(async move {
            let lock = RedisDistributedLock::new(redis_url, lock_key, 10)?;

            info!(client_id, "Client attempting to acquire lock");

            match timeout(Duration::from_secs(5), lock.lock(Duration::from_secs(5))).await {
                Ok(Ok(())) => {
                    info!(client_id, "Client acquired lock, working...");

                    // 模拟业务工作
                    sleep(Duration::from_millis(1500)).await;

                    // 续期
                    if lock.extend(5).await? {
                        info!(client_id, "Client extended lock");
                    }

                    sleep(Duration::from_millis(1000)).await;

                    lock.unlock().await?;
                    info!(client_id, "Client released lock");
                }
                Ok(Err(e)) => {
                    error!(client_id, error = %e, "Client failed to acquire lock");
                }
                Err(_) => {
                    warn!(client_id, "Client timed out waiting for lock");
                }
            }

            Ok::<(), anyhow::Error>(())
        });

        handles.push(handle);
        sleep(Duration::from_millis(100)).await;
    }

    for handle in handles {
        if let Err(e) = handle.await? {
            error!(error = %e, "Task failed");
        }
    }

    info!("All clients finished");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tokio::time::sleep;

    #[tokio::test]
    async fn test_distributed_lock_basic() -> Result<()> {
        let lock = RedisDistributedLock::new("redis://127.0.0.1:6379", "test_lock", 5)?;

        assert!(lock.try_lock().await?);
        assert!(!lock.try_lock().await?);

        lock.unlock().await?;
        assert!(lock.try_lock().await?);
        lock.unlock().await?;

        Ok(())
    }

    #[tokio::test]
    async fn test_lock_extension() -> Result<()> {
        let lock = RedisDistributedLock::new("redis://127.0.0.1:6379", "test_extend_lock", 2)?;

        lock.try_lock().await?;
        assert!(lock.extend(5).await?);

        sleep(Duration::from_secs(3)).await;
        assert!(!lock.try_lock().await?);

        lock.unlock().await?;
        Ok(())
    }
}
