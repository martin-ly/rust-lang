#[cfg(any(feature = "kv-redis", feature = "sql-postgres", feature = "mq-kafka"))]
use c11_libraries::prelude::*;
#[cfg(feature = "kv-redis")]
use c11_libraries::config::RedisConfig;
#[cfg(feature = "sql-postgres")]
use c11_libraries::config::PostgresConfig;
#[cfg(feature = "mq-kafka")]
use c11_libraries::config::KafkaConfig;

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

    println!("=== c12_middlewares 综合功能演示 ===");

    // Redis 批量操作演示
    #[cfg(feature = "kv-redis")]
    {
        println!("\n--- Redis 批量操作 ---");
        let store = c11_libraries::cache::redis_client::RedisStore::connect_with(
            RedisConfig::new("redis://127.0.0.1:6379"),
        )
        .await?;

        // 批量设置
        let pairs: &[(&str, &[u8])] = &[
            ("key1", b"value1"),
            ("key2", b"value2"),
            ("key3", b"value3"),
        ];
        store.mset(pairs).await?;
        println!("批量设置完成");

        // 批量获取
        let keys = ["key1", "key2", "key3"];
        let values = store.mget(&keys).await?;
        for (key, value) in keys.iter().zip(values.iter()) {
            println!("{}: {:?}", key, value);
        }
    }

    // Postgres 事务与批量操作演示
    #[cfg(feature = "sql-postgres")]
    {
        println!("\n--- Postgres 事务与批量操作 ---");
        let db = c11_libraries::database::postgres_client::PostgresDb::connect_with(
            PostgresConfig::new("postgres://user:pass@localhost/db"),
        )
        .await?;

        // 开始事务
        db.begin().await?;

        // 批量执行 SQL
        let sqls = [
            "CREATE TABLE IF NOT EXISTS demo_users (id SERIAL PRIMARY KEY, name TEXT, age INT)",
            "INSERT INTO demo_users (name, age) VALUES ('Alice', 25)",
            "INSERT INTO demo_users (name, age) VALUES ('Bob', 30)",
        ];
        let results = db.batch_execute(&sqls).await?;
        println!("批量执行结果: {:?}", results);

        // 查询数据
        let rows = db.query("SELECT * FROM demo_users").await?;
        for row in rows {
            let id = row.get_int("id").unwrap_or(0);
            let name = row.get_string("name").map_or("", |v| v);
            let age = row.get_int("age").unwrap_or(0);
            println!("用户: id={}, name={}, age={}", id, name, age);
        }

        // 提交事务
        db.commit().await?;
        println!("事务提交完成");
    }

    // Kafka 配置化演示
    #[cfg(feature = "mq-kafka")]
    {
        println!("\n--- Kafka 配置化使用 ---");
        let kafka_config = KafkaConfig::new("localhost:9092", "demo_group");

        let producer = c12_middlewares::mq::kafka_client::KafkaProducer::new_with_config(
            kafka_config.clone(),
        )?;
        let consumer = c12_middlewares::mq::kafka_client::KafkaConsumer::new_with_config(
            kafka_config,
            &["demo_topic"],
        )?;

        producer
            .send("demo_topic", b"Hello Kafka with config!")
            .await?;
        println!("Kafka 消息发送完成");

        // 注意：实际使用中需要处理消息消费
        // if let Some(msg) = consumer.next().await? {
        //     println!("收到消息: {:?}", msg);
        // }
    }

    println!("\n=== 综合演示完成 ===");
    Ok(())
}

#[cfg(not(feature = "tokio"))]
fn main() {
    println!("此示例需要 tokio 特性才能运行");
    println!(
        "请使用: cargo run --example comprehensive_demo --features kv-redis,sql-postgres,tokio"
    );
}
