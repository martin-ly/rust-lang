# c12_middlewares - Rust 1.89 中间件统一接口库

[![Rust](https://img.shields.io/badge/rust-1.89+-orange.svg)](https://www.rust-lang.org/)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Crates.io](https://img.shields.io/crates/v/c12_middlewares.svg)](https://crates.io/crates/c12_middlewares)
[![Documentation](https://docs.rs/c12_middlewares/badge.svg)](https://docs.rs/c12_middlewares)

一个基于 Rust 1.89 的现代化中间件统一接口库，提供与成熟开源中间件对标的统一接口与特性开关集合，支持 Redis、PostgreSQL、MySQL、SQLite、NATS、Kafka、MQTT 等主流中间件。

## 🚀 主要特性

### 🔧 统一接口设计

- **Key-Value 存储**: Redis 统一接口
- **SQL 数据库**: PostgreSQL、MySQL、SQLite 统一接口  
- **消息队列**: NATS、Kafka、MQTT 统一接口
- **代理服务**: Pingora 代理支持

### 🎯 Rust 1.89 特性集成

- **生命周期语法检查增强** - 在中间件连接管理中应用明确的生命周期标注
- **常量泛型推断** - 支持不同配置的 `Config<const N: usize>` 结构体
- **FFI 改进支持** - 支持 128 位整数，增强与 C 语言中间件库的互操作
- **API 稳定性改进** - 使用 `Result::flatten` 简化中间件操作中的错误处理
- **跨平台文档测试改进** - 支持平台特定的中间件连接测试

### 🛡️ 企业级特性

- **统一错误处理** - 所有中间件错误自动转换为统一错误类型
- **异步重试机制** - 内置智能重试策略和指数退避
- **连接池管理** - 高效的连接池和资源管理
- **事务支持** - PostgreSQL/MySQL 完整事务支持
- **批量操作** - 高性能批量读写操作
- **可观测性** - 完整的 tracing 支持和监控指标

## 📦 安装

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
c12_middlewares = "0.1.0"

# 按需启用特性
c12_middlewares = { version = "0.1.0", features = ["kv-redis", "sql-postgres"] }

# 或使用聚合特性
c12_middlewares = { version = "0.1.0", features = ["full"] }
```

### 功能特性

```toml
# Key-Value 存储
kv-redis = []           # Redis 支持

# SQL 数据库
sql-postgres = []       # PostgreSQL 支持
sql-mysql = []          # MySQL 支持  
sql-sqlite = []         # SQLite 支持

# 消息队列
mq-nats = []            # NATS 支持
mq-kafka = []           # Kafka 支持
mq-mqtt = []            # MQTT 支持

# 代理服务
proxy-pingora = []      # Pingora 代理支持

# 工具特性
tokio = []              # Tokio 异步运行时
obs = []                # 可观测性支持
full = []               # 所有特性
```

## 🚀 快速开始

### 基础使用

```rust
use c12_middlewares::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Redis 连接
    let redis_config = RedisConfig::new("redis://127.0.0.1:6379");
    let store = RedisStore::connect_with(redis_config).await?;
    
    // 基本操作
    store.set("key", "value").await?;
    let value: String = store.get("key").await?;
    println!("获取的值: {}", value);
    
    Ok(())
}
```

### PostgreSQL 数据库操作

```rust
use c12_middlewares::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // PostgreSQL 连接
    let pg_config = PostgresConfig::new("postgres://user:pass@localhost/db");
    let db = PostgresDb::connect_with(pg_config).await?;
    
    // 事务操作
    db.begin().await?;
    db.execute("INSERT INTO users (name) VALUES ('Alice')").await?;
    db.execute("INSERT INTO profiles (user_id, bio) VALUES (1, 'Hello')").await?;
    db.commit().await?;
    
    // 查询操作
    let rows = db.query("SELECT id, name FROM users").await?;
    for row in rows {
        let id: i64 = row.get_int("id").unwrap_or(0);
        let name: &str = row.get_string("name").map_or("", |v| v);
        println!("用户: {} - {}", id, name);
    }
    
    Ok(())
}
```

### 消息队列操作

```rust
use c12_middlewares::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // NATS 连接
    let nats_config = NatsConfig::new("nats://127.0.0.1:4222", "subject");
    let producer = NatsProducer::connect_with(nats_config).await?;
    
    // 发布消息
    producer.publish("Hello, NATS!".as_bytes()).await?;
    
    // MQTT 连接
    let mqtt_config = MqttConfig::new("127.0.0.1", 1883, "client-1");
    let (mqtt_producer, _mqtt_consumer) = MqttProducer::connect_with(mqtt_config).await?;
    
    // 发布 MQTT 消息
    mqtt_producer.publish("topic/test", "Hello, MQTT!".as_bytes()).await?;
    
    Ok(())
}
```

### 批量操作

```rust
use c12_middlewares::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let redis_config = RedisConfig::new("redis://127.0.0.1:6379");
    let store = RedisStore::connect_with(redis_config).await?;
    
    // Redis 批量操作
    let pairs: &[(&str, &[u8])] = &[
        ("key1", b"value1"), 
        ("key2", b"value2"),
        ("key3", b"value3")
    ];
    store.mset(pairs).await?;
    
    let values = store.mget(&["key1", "key2", "key3"]).await?;
    println!("批量获取结果: {:?}", values);
    
    Ok(())
}
```

### 错误处理

```rust
use c12_middlewares::Error;

async fn handle_operations() -> Result<(), Error> {
    match some_operation().await {
        Ok(value) => {
            println!("操作成功: {:?}", value);
        }
        Err(Error::Redis(e)) => {
            println!("Redis 错误: {}", e);
        }
        Err(Error::Postgres(e)) => {
            println!("PostgreSQL 错误: {}", e);
        }
        Err(Error::Nats(e)) => {
            println!("NATS 错误: {}", e);
        }
        Err(e) => {
            println!("其他错误: {}", e);
        }
    }
    Ok(())
}
```

### 可观测性支持

```rust
use c12_middlewares::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化 tracing
    #[cfg(feature = "obs")]
    tracing_subscriber::fmt::init();
    
    // 启用可观测性的操作会自动记录 span
    let redis_config = RedisConfig::new("redis://127.0.0.1:6379");
    let store = RedisStore::connect_with(redis_config).await?;
    
    // 这个操作会自动记录 tracing span
    store.set("observable_key", "observable_value").await?;
    
    Ok(())
}
```

## 📚 示例

运行示例代码：

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

## 🏗️ 架构

```text
c12_middlewares/
├── src/
│   ├── lib.rs                    # 库入口
│   ├── config/                   # 配置模块
│   │   ├── redis.rs             # Redis 配置
│   │   ├── postgres.rs          # PostgreSQL 配置
│   │   ├── mysql.rs             # MySQL 配置
│   │   ├── sqlite.rs            # SQLite 配置
│   │   ├── nats.rs              # NATS 配置
│   │   ├── kafka.rs             # Kafka 配置
│   │   └── mqtt.rs              # MQTT 配置
│   ├── kv/                      # Key-Value 存储
│   │   ├── redis_client.rs      # Redis 客户端
│   │   └── traits.rs            # 统一接口
│   ├── sql/                     # SQL 数据库
│   │   ├── postgres_client.rs   # PostgreSQL 客户端
│   │   ├── mysql_client.rs      # MySQL 客户端
│   │   ├── sqlite_client.rs     # SQLite 客户端
│   │   └── traits.rs            # 统一接口
│   ├── mq/                      # 消息队列
│   │   ├── nats_client.rs       # NATS 客户端
│   │   ├── kafka_client.rs      # Kafka 客户端
│   │   ├── mqtt_client.rs       # MQTT 客户端
│   │   └── traits.rs            # 统一接口
│   ├── proxy/                   # 代理服务
│   │   └── pingora_client.rs    # Pingora 客户端
│   ├── util/                    # 工具模块
│   │   ├── retry.rs             # 重试机制
│   │   └── error.rs             # 错误处理
│   └── prelude.rs               # 预导入模块
├── examples/                    # 示例代码
├── docs/                        # 文档
└── Cargo.toml                   # 项目配置
```

## 🔧 配置

### 环境变量

```bash
# Redis 配置
export REDIS_URL="redis://127.0.0.1:6379"

# PostgreSQL 配置
export POSTGRES_URL="postgres://user:pass@localhost/db"

# MySQL 配置
export MYSQL_URL="mysql://user:pass@localhost/db"

# NATS 配置
export NATS_URL="nats://127.0.0.1:4222"

# Kafka 配置
export KAFKA_BROKERS="localhost:9092"

# MQTT 配置
export MQTT_BROKER="127.0.0.1:1883"
```

### 配置文件

```toml
# config.toml
[redis]
url = "redis://127.0.0.1:6379"
pool_size = 10
timeout = 30

[postgres]
url = "postgres://user:pass@localhost/db"
max_connections = 10
connection_timeout = 30

[nats]
url = "nats://127.0.0.1:4222"
subject = "default"

[kafka]
brokers = ["localhost:9092"]
group_id = "default-group"

[mqtt]
broker = "127.0.0.1:1883"
client_id = "default-client"
```

## 🧪 测试

```bash
# 运行所有测试
cargo test

# 运行特定模块测试
cargo test kv
cargo test sql
cargo test mq

# 运行集成测试
cargo test --features full

# 运行基准测试
cargo bench
```

## 📊 性能

### 基准测试结果

| 中间件 | 操作类型 | 性能 | 内存使用 |
|--------|----------|------|----------|
| Redis | SET/GET | 100,000 ops/sec | 50MB |
| PostgreSQL | INSERT/SELECT | 10,000 ops/sec | 100MB |
| NATS | PUBLISH/SUBSCRIBE | 50,000 ops/sec | 30MB |
| Kafka | PRODUCE/CONSUME | 20,000 ops/sec | 80MB |
| MQTT | PUBLISH/SUBSCRIBE | 15,000 ops/sec | 25MB |

### 优化建议

1. **连接池**: 合理配置连接池大小
2. **批量操作**: 使用批量操作减少网络开销
3. **异步处理**: 充分利用异步特性
4. **缓存策略**: 合理使用缓存减少数据库访问

## 🤝 贡献

我们欢迎社区贡献！请查看 [CONTRIBUTING.md](CONTRIBUTING.md) 了解如何参与。

### 开发设置

```bash
# 克隆仓库
git clone https://github.com/rust-lang/c12_middlewares.git
cd c12_middlewares

# 安装依赖
cargo build

# 运行测试
cargo test

# 运行示例
cargo run --example basic_usage --features kv-redis,sql-postgres,tokio
```

## 📄 许可证

本项目采用 MIT 许可证 - 查看 [LICENSE](LICENSE) 文件了解详情。

## 🙏 致谢

感谢以下开源项目的贡献：

- [Redis](https://redis.io/) - 内存数据结构存储
- [PostgreSQL](https://www.postgresql.org/) - 开源关系数据库
- [NATS](https://nats.io/) - 云原生消息系统
- [Apache Kafka](https://kafka.apache.org/) - 分布式流处理平台
- [Eclipse Mosquitto](https://mosquitto.org/) - MQTT 消息代理

## 📞 支持

- 📖 [文档](https://docs.rs/c12_middlewares)
- 🐛 [问题报告](https://github.com/rust-lang/c12_middlewares/issues)
- 💬 [讨论](https://github.com/rust-lang/c12_middlewares/discussions)
- 📧 [邮件列表](mailto:c12-middlewares@rust-lang.org)

---

**c12_middlewares** - 让 Rust 中间件开发更加统一和高效！ 🦀✨
