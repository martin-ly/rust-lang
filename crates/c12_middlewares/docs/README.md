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

更多具体中间件接入示例将陆续补充。
