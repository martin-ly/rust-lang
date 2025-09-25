//use c12_middlewares::prelude::*;
//use c12_middlewares::config::{RedisConfig, PostgresConfig};

#[cfg(feature = "obs")]
fn init_tracing() {
    tracing_subscriber::fmt::init();
}

#[allow(dead_code)]
#[cfg(not(feature = "obs"))]
fn init_tracing() {}

#[cfg(feature = "tokio")]
#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    init_tracing();

    println!("=== c12_middlewares 基础使用示例 ===");

    // Redis 示例
    #[cfg(feature = "kv-redis")]
    {
        println!("\n--- Redis 操作 ---");
        let store = c12_middlewares::cache::redis_client::RedisStore::connect_with(
            RedisConfig::new("redis://127.0.0.1:6379"),
        )
        .await?;

        store.set("demo_key", b"Hello Redis!").await?;
        let value = store.get("demo_key").await?;
        println!("Redis GET: {:?}", value);
        store.del("demo_key").await?;
    }

    // Postgres 示例
    #[cfg(feature = "sql-postgres")]
    {
        println!("\n--- Postgres 操作 ---");
        let db = c12_middlewares::database::postgres_client::PostgresDb::connect_with(
            PostgresConfig::new("postgres://user:pass@localhost/db"),
        )
        .await?;

        // 事务示例
        db.begin().await?;
        let _ = db
            .execute("CREATE TABLE IF NOT EXISTS demo (id SERIAL PRIMARY KEY, name TEXT)")
            .await?;
        let _ = db
            .execute("INSERT INTO demo (name) VALUES ('test')")
            .await?;
        let rows = db.query("SELECT * FROM demo").await?;
        println!("Postgres 查询结果: {} 行", rows.len());
        db.commit().await?;
    }

    println!("\n示例完成！");
    Ok(())
}

#[cfg(not(feature = "tokio"))]
fn main() {
    println!("此示例需要 tokio 特性才能运行");
    println!("请使用: cargo run --example basic_usage --features kv-redis,sql-postgres,tokio");
}
