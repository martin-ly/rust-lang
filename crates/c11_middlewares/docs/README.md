# c12_middlewares

与成熟开源中间件对标的统一接口与特性开关集合，面向 Rust 1.89：

> 适用范围：Rust 1.89+；文档风格遵循 `../../c10_networks/docs/STYLE.md`。

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

### 特性矩阵（概览）

- `kv-redis`: 连接/池化、超时、批量（MGET/MSET）、Pipeline、Lua、Pub/Sub
- `sql-postgres`: 执行/查询、事务、批量、类型映射、配置化、可观测
- `sql-mysql`: 执行/查询、事务、类型映射、配置化
- `sql-sqlite`: 轻量内嵌/文件 DB、事务
- `mq-nats`: 发送/订阅、低延迟；JetStream 草案中
- `mq-kafka`: 最小可用草案（参见 `kafka_pingora.md` 路线图）
- `mq-mqtt`: QoS0/1/2、会话
- `proxy-pingora`: 最小反代草案；路由/中间件/TLS 逐步完善
- `obs`: tracing 可观测增强（建议与 `tokio` 搭配）

### 统一接口

- `kv::KeyValueStore`
- `sql::SqlDatabase`
- `mq::{MessageProducer, MessageConsumer}`

### 配置与重试

提供统一配置结构（`config::*`）与通用异步重试（`util::retry_async`）：

### 可观测性

启用 `obs` 特性获得 tracing 支持：

```rust
// 在 main 中初始化
#[cfg(feature = "obs")]
tracing_subscriber::fmt::init();

// 关键操作自动记录 span
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
let sqls = [
    "INSERT INTO users (name) VALUES ('Alice')",
    "INSERT INTO users (name) VALUES ('Bob')",
];
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

## 平台兼容

- 操作系统：Linux、macOS、Windows（x86_64/arm64，以依赖库支持为准）
- 运行时：建议 `tokio` 1.x；启用 `obs` 时需 `tracing` 生态
- Kafka：需系统安装 `librdkafka`（Windows 可通过 vcpkg/预编译包，WSL 推荐）
- SQLite：Windows 与 Linux 路径/权限差异较大，建议使用绝对路径

## 版本与特性依赖

- Rust：1.89+
- 必选特性：按需启用 `kv-redis`、`sql-*`、`mq-*`、`proxy-pingora`
- 可选特性：`obs` 用于 tracing；与 `tokio`/`tracing-subscriber` 协作

## 故障排查（Troubleshooting）

- 连接失败：
  - 校验网络可达与鉴权；增加连接超时；本地优先用 `localhost`/环回地址
  - 容器/WSL：确认端口映射、DNS 与防火墙策略
- 超时与重试：
  - 对非幂等写操作避免自动重试；为幂等读操作设置最大重试次数与退避
- 资源与池化：
  - 连接池过小会导致队列等待，过大可能放大后端压力；以 P95/P99 为依据调参
- 可观测性：
  - 启用 `obs` 查看关键 span；关注错误分布、慢查询/慢命令

## 安全与合规

- 传输层安全：
  - Kafka/SQL/Redis 等在公有网络建议启用 TLS；校验证书与主机名
- 鉴权与凭据：
  - 使用最小权限账户；凭据通过环境变量/密钥管理服务注入，避免硬编码
- 数据安全：
  - 谨慎在日志中打印敏感字段；按需启用字段脱敏与审计

## 性能基线与建议

- Redis：优先使用 MGET/MSET/Pipeline；热点键启用 TTL 与就地更新，避免大 key
- SQL：为热点查询建索引；批量写入与参数化优先；长事务拆分
- MQ：消费者幂等与批量确认；对堆积实施背压与限速

## 本地环境快速启动

```powershell
# Windows PowerShell 示例（如使用 WSL/Docker 视环境调整）
# Redis（Docker）
docker run -p 6379:6379 --name redis -d redis:7

# Postgres（Docker）
docker run -e POSTGRES_PASSWORD=pass -e POSTGRES_USER=user -e POSTGRES_DB=db \
  -p 5432:5432 --name pg -d postgres:16

# NATS（Docker）
docker run -p 4222:4222 --name nats -d nats:2
```

## 示例与命令

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

## 子文档

- Redis: `docs/redis.md`
- SQL: `docs/sql.md`
- 消息与流: `docs/mq.md`
- Pingora: `docs/pingora.md`
- Kafka 与 Pingora 现状与路线图: `docs/kafka_pingora.md`

> 更多具体中间件接入示例与最佳实践将陆续补充，如需优先支持某项能力，请在 issue 中注明场景、SLO 与 MVP 范围。
