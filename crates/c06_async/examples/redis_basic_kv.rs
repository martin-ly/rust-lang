use anyhow::Result;
use redis::{AsyncCommands, Client};
use std::time::Duration;
use tracing::{info, instrument};

/// Redis 基本 KV 操作示例
///
/// 运行前需要启动本地 Redis 服务：
///   redis-server --port 6379
///
/// 本示例演示：
/// - 连接建立（MultiplexedConnection）
/// - SET / GET / EXISTS / DEL
/// - 带过期时间的 SETEX
/// - 批量操作 MSET / MGET
#[tokio::main(flavor = "multi_thread")]
async fn main() -> Result<()> {
    tracing_subscriber::fmt().with_env_filter("info").init();

    let redis_url = "redis://127.0.0.1:6379";
    let client = Client::open(redis_url)?;
    let mut conn = client.get_multiplexed_async_connection().await?;

    // 基础字符串操作
    basic_string_ops(&mut conn).await?;

    // 过期键
    expiration_ops(&mut conn).await?;

    // 批量操作
    batch_ops(&mut conn).await?;

    info!("All basic KV operations completed successfully");
    Ok(())
}

#[instrument(skip(conn))]
async fn basic_string_ops(conn: &mut redis::aio::MultiplexedConnection) -> Result<()> {
    let key = "redis_basic_kv:demo";

    // SET 与 GET
    let _: () = conn.set(key, "hello redis").await?;
    let value: String = conn.get(key).await?;
    info!(key, value, "GET returned");

    // EXISTS
    let exists: bool = conn.exists(key).await?;
    info!(key, exists, "EXISTS returned");

    // DEL
    let deleted: i32 = conn.del(key).await?;
    info!(key, deleted, "DEL returned");

    let exists_after: bool = conn.exists(key).await?;
    info!(key, exists_after, "EXISTS after DEL returned");

    Ok(())
}

#[instrument(skip(conn))]
async fn expiration_ops(conn: &mut redis::aio::MultiplexedConnection) -> Result<()> {
    let key = "redis_basic_kv:expiring";

    // SETEX：设置 2 秒过期
    let _: () = conn.set_ex(key, "i will expire", 2).await?;

    let ttl: i64 = conn.ttl(key).await?;
    info!(key, ttl, "TTL returned");

    let value: String = conn.get(key).await?;
    info!(key, value, "Value before expiration");

    // 等待过期
    tokio::time::sleep(Duration::from_secs(3)).await;

    let after_expiry: Option<String> = conn.get(key).await?;
    info!(key, ?after_expiry, "Value after expiration");

    Ok(())
}

#[instrument(skip(conn))]
async fn batch_ops(conn: &mut redis::aio::MultiplexedConnection) -> Result<()> {
    let keys = ["redis_basic_kv:a", "redis_basic_kv:b", "redis_basic_kv:c"];

    // MSET
    let _: () = conn
        .mset(&[(keys[0], "alpha"), (keys[1], "beta"), (keys[2], "gamma")])
        .await?;

    // MGET
    let values: Vec<Option<String>> = conn.mget(&keys[..]).await?;
    info!(?keys, ?values, "MGET returned");

    // 清理
    let deleted: i32 = conn.del(&keys[..]).await?;
    info!(deleted, "Batch cleanup completed");

    Ok(())
}
