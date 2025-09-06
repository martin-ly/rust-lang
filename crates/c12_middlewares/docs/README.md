# c12_middlewares

与成熟开源中间件对标的统一接口与特性开关集合，面向 Rust 1.89：

- Key-Value: Redis（`kv-redis`）
- SQL: Postgres（`sql-postgres`）、MySQL（`sql-mysql`）、SQLite（`sql-sqlite`）
- 消息与流: NATS（`mq-nats`）、Kafka（`mq-kafka`）、MQTT（`mq-mqtt`）
- 代理: Pingora（`proxy-pingora`）

## 安装与特性

在工作区添加依赖，并按需开启特性：

```toml
c12_middlewares = { version = "0.1", features = ["kv-redis", "sql-postgres"] }
```

也可使用聚合特性：

```toml
features = ["full"]
```

### 统一接口

- `kv::KeyValueStore`
- `sql::SqlDatabase`
- `mq::{MessageProducer, MessageConsumer}`

### 配置与重试

提供统一配置结构（`config::*`）与通用异步重试（`util::retry_async`）：

### 错误处理

统一错误类型 `c12_middlewares::Error`，支持各中间件错误自动转换：

```rust
use c12_middlewares::Error;

match result {
    Ok(v) => println!("成功: {:?}", v),
    Err(Error::Redis(e)) => println!("Redis 错误: {}", e),
    Err(Error::Postgres(e)) => println!("Postgres 错误: {}", e),
    Err(e) => println!("其他错误: {}", e),
}
```

### 可观测性

启用 `obs` 特性获得 tracing 支持：

```rust
// 在 main 中初始化
#[cfg(feature = "obs")]
tracing_subscriber::fmt::init();

// 自动在关键操作中记录 span
```

### 事务支持

Postgres/MySQL 支持基础事务：

```rust
db.begin().await?;
db.execute("INSERT INTO users (name) VALUES ('Alice')").await?;
db.execute("INSERT INTO profiles (user_id, bio) VALUES (1, 'Hello')").await?;
db.commit().await?; // 或 db.rollback().await? 回滚
```

### 类型映射

改进的 SQL 行访问：

```rust
let rows = db.query("SELECT id, name, age FROM users").await?;
for row in rows {
    let id: i64 = row.get_int("id").unwrap_or(0);
    let name: &str = row.get_string("name").map_or("", |v| v);
    let age: f64 = row.get_float("age").unwrap_or(0.0);
}
```

### 批量操作

支持批量操作以提高性能：

```rust
// Redis 批量操作
let pairs: &[(&str, &[u8])] = &[("key1", b"value1"), ("key2", b"value2")];
store.mset(pairs).await?;
let values = store.mget(&["key1", "key2"]).await?;

// SQL 批量执行
let sqls = ["INSERT INTO users (name) VALUES ('Alice')", "INSERT INTO users (name) VALUES ('Bob')"];
let results = db.batch_execute(&sqls).await?;
```

### 配置化使用

所有中间件都支持配置化：

```rust
// Kafka 配置化
let kafka_config = KafkaConfig::new("localhost:9092", "my_group");
let producer = KafkaProducer::new_with_config(kafka_config)?;

// Redis 配置化
let redis_config = RedisConfig::new("redis://localhost:6379").with_pool_size(10);
let store = RedisStore::connect_with(redis_config).await?;
```

```rust
use c12_middlewares::config::{RedisConfig, PostgresConfig, NatsConfig, MqttConfig};

// Redis with config + retry
let store = c12_middlewares::redis_client::RedisStore::connect_with(
    RedisConfig::new("redis://127.0.0.1:6379")
).await?;

// Postgres with config + retry
let pg = c12_middlewares::postgres_client::PostgresDb::connect_with(
    PostgresConfig::new("postgres://user:pass@localhost/db")
).await?;

// NATS with config + retry
let prod = c12_middlewares::nats_client::NatsProducer::connect_with(
    NatsConfig::new("nats://127.0.0.1:4222", "subject")
).await?;

// MQTT with config + retry
let (_p, _c) = c12_middlewares::mqtt_client::MqttProducer::connect_with(
    MqttConfig::new("127.0.0.1", 1883, "client-1")
).await?;
```

### 示例

运行示例二进制打印启用特性：

```bash
cargo run -p c12_middlewares --no-default-features --features kv-redis
```

运行完整示例：

```bash
# 基础使用示例（Redis + Postgres + 事务）
cargo run --example basic_usage --features kv-redis,sql-postgres,tokio,obs

# 消息队列示例（NATS + MQTT）
cargo run --example message_queue --features mq-nats,mq-mqtt,tokio,obs

# 综合功能演示（批量操作 + 配置化）
cargo run --example comprehensive_demo --features kv-redis,sql-postgres,tokio

# 仅检查编译（不运行）
cargo check --example basic_usage --features kv-redis,sql-postgres,tokio
```

更多具体中间件接入示例将陆续补充。
