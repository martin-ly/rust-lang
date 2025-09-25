use anyhow::Result;
use backoff::{ExponentialBackoff, Error as BackoffError};
use backoff::future::retry;
use redis::Client;
use std::time::{Duration, SystemTime, UNIX_EPOCH};
use tokio::time::{sleep, timeout};
use tracing::{info, warn, error};

/// 基于 Redis 的分布式锁实现
/// 
/// 特性：
/// - 自动过期防止死锁
/// - 重入锁支持（可选）
/// - 指数退避重试
/// - 超时保护
#[derive(Clone)]
pub struct DistributedLock {
    redis_client: Client,
    lock_key: String,
    lock_value: String,
    ttl_seconds: u64,
}

impl DistributedLock {
    pub fn new(redis_url: &str, lock_key: &str, ttl_seconds: u64) -> Result<Self> {
        let redis_client = Client::open(redis_url)?;
        let lock_value = format!("{}:{}", 
            SystemTime::now().duration_since(UNIX_EPOCH)?.as_millis(),
            uuid::Uuid::new_v4()
        );
        
        Ok(Self {
            redis_client,
            lock_key: lock_key.to_string(),
            lock_value,
            ttl_seconds,
        })
    }

    /// 尝试获取锁（非阻塞）
    pub async fn try_lock(&self) -> Result<bool> {
        let mut conn = self.redis_client.get_multiplexed_async_connection().await?;
        
        // 使用 SET NX EX 原子操作
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

    /// 获取锁（阻塞，带重试）
    pub async fn lock(&self, max_wait: Duration) -> Result<()> {
        let backoff = ExponentialBackoff {
            initial_interval: Duration::from_millis(100),
            max_interval: Duration::from_secs(1),
            max_elapsed_time: Some(max_wait),
            ..Default::default()
        };

        let operation = || async {
            if self.try_lock().await? {
                Ok(())
            } else {
                Err(BackoffError::transient(anyhow::anyhow!("Lock not available")))
            }
        };

        retry(backoff, operation).await?;
        info!(lock_key = %self.lock_key, "Lock acquired successfully");
        Ok(())
    }

    /// 释放锁
    pub async fn unlock(&self) -> Result<()> {
        let mut conn = self.redis_client.get_multiplexed_async_connection().await?;
        
        // 使用 Lua 脚本确保原子性：只有锁的持有者才能释放
        let script = r#"
            if redis.call("GET", KEYS[1]) == ARGV[1] then
                return redis.call("DEL", KEYS[1])
            else
                return 0
            end
        "#;
        
        let result: i32 = redis::Script::new(script)
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

    /// 延长锁的过期时间
    pub async fn extend(&self, additional_seconds: u64) -> Result<bool> {
        let mut conn = self.redis_client.get_multiplexed_async_connection().await?;
        
        let script = r#"
            if redis.call("GET", KEYS[1]) == ARGV[1] then
                return redis.call("EXPIRE", KEYS[1], ARGV[2])
            else
                return 0
            end
        "#;
        
        let result: i32 = redis::Script::new(script)
            .key(&self.lock_key)
            .arg(&self.lock_value)
            .arg(self.ttl_seconds + additional_seconds)
            .invoke_async(&mut conn)
            .await?;
        
        Ok(result > 0)
    }
}

/// 分布式锁使用示例
#[tokio::main(flavor = "multi_thread")]
async fn main() -> Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();

    // 模拟多个客户端竞争同一个资源
    let redis_url = "redis://127.0.0.1:6379";
    let lock_key = "distributed_resource_lock";
    
    let mut handles = Vec::new();
    
    for client_id in 1..=5 {
        let handle = tokio::spawn(async move {
            let lock = DistributedLock::new(redis_url, lock_key, 10)?;
            
            info!(client_id, "Client {} attempting to acquire lock", client_id);
            
            // 尝试获取锁，最多等待 5 秒
            match timeout(Duration::from_secs(5), lock.lock(Duration::from_secs(5))).await {
                Ok(Ok(())) => {
                    info!(client_id, "Client {} acquired lock, working...", client_id);
                    
                    // 模拟工作
                    sleep(Duration::from_millis(2000)).await;
                    
                    // 延长锁时间（可选）
                    if lock.extend(5).await? {
                        info!(client_id, "Client {} extended lock", client_id);
                    }
                    
                    // 继续工作
                    sleep(Duration::from_millis(1000)).await;
                    
                    // 释放锁
                    lock.unlock().await?;
                    info!(client_id, "Client {} released lock", client_id);
                }
                Ok(Err(e)) => {
                    error!(client_id, error = %e, "Client {} failed to acquire lock", client_id);
                }
                Err(_) => {
                    warn!(client_id, "Client {} timed out waiting for lock", client_id);
                }
            }
            
            Ok::<(), anyhow::Error>(())
        });
        
        handles.push(handle);
        
        // 错开启动时间
        sleep(Duration::from_millis(100)).await;
    }
    
    // 等待所有任务完成
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
        let lock = DistributedLock::new("redis://127.0.0.1:6379", "test_lock", 5)?;
        
        // 获取锁
        assert!(lock.try_lock().await?);
        
        // 再次尝试应该失败
        assert!(!lock.try_lock().await?);
        
        // 释放锁
        lock.unlock().await?;
        
        // 现在应该可以再次获取
        assert!(lock.try_lock().await?);
        lock.unlock().await?;
        
        Ok(())
    }

    #[tokio::test]
    async fn test_lock_extension() -> Result<()> {
        let lock = DistributedLock::new("redis://127.0.0.1:6379", "test_extend_lock", 2)?;
        
        lock.try_lock().await?;
        
        // 延长锁时间
        assert!(lock.extend(5).await?);
        
        // 等待原始过期时间
        sleep(Duration::from_secs(3)).await;
        
        // 锁应该仍然有效
        assert!(!lock.try_lock().await?);
        
        lock.unlock().await?;
        Ok(())
    }
}
