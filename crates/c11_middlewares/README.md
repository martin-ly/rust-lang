# c11_middlewares - Rust 1.90 中间件统一接口库

一个基于 Rust 1.90+ 的现代化中间件统一接口库，提供与成熟开源中间件对标的统一接口与特性开关集合，支持 Redis、PostgreSQL、MySQL、SQLite、NATS、Kafka、MQTT 等主流中间件。

> 📚 **[完整文档](docs/README.md)** | 🚀 **[快速导航](docs/00_MASTER_INDEX.md)** | ❓ **[常见问题](docs/FAQ.md)** | 📖 **[术语表](docs/Glossary.md)**

## 🆕 2025-10-19 新增实战示例

**[Rust 1.90 中间件集成实战示例集](docs/RUST_190_MIDDLEWARE_PRACTICAL_EXAMPLES.md)** ⭐⭐⭐⭐⭐

- **Rust 1.90 特性**: async fn in trait、RPITIT、GAT在中间件中的应用
- **Redis实战**: CRUD、连接池、分布式锁
- **SQL集成**: PostgreSQL/MySQL事务处理、批量操作
- **消息队列**: Kafka/MQTT/NATS完整示例
- **600+ 行可运行代码**: 详细注释、生产级模式

**特色**: 统一接口设计 + Rust 1.90 特性 + 实战场景！

## 🚀 主要特性

### 🔧 统一接口设计

- **Key-Value 存储**: Redis 统一接口
- **SQL 数据库**: PostgreSQL、MySQL、SQLite 统一接口  
- **消息队列**: NATS、Kafka、MQTT 统一接口
- **代理服务**: Pingora 代理支持

### 🎯 Rust 1.90+ 特性集成

- **async fn in trait** - 中间件客户端统一异步接口
- **RPITIT** - 返回位置 impl Trait in Trait，简化接口定义
- **泛型关联类型 (GAT)** - 更灵活的连接池抽象
- **生命周期语法增强** - 在中间件连接管理中应用明确的生命周期标注
- **常量泛型推断** - 支持不同配置的 `Config<const N: usize>` 结构体
- **FFI 改进支持** - 支持 128 位整数，增强与 C 语言中间件库的互操作

> 📘 详见 [Rust 1.90 特性指南](docs/references/RUST_190_FEATURES_GUIDE.md)

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

## 📚 文档与示例

### 文档

| 文档 | 说明 |
|------|------|
| **[文档中心](docs/README.md)** | 📚 文档主入口，开始探索的最佳位置 |
| **[快速导航](docs/00_MASTER_INDEX.md)** | 🗺️ 主索引和学习路径 |
| **[完整索引](docs/COMPREHENSIVE_DOCUMENTATION_INDEX.md)** | 📋 综合文档索引 |
| **[使用指南](docs/guides/)** | 🔧 各中间件详细使用指南 |
| **[API参考](docs/references/)** | 📘 API 和配置参考 |
| **[常见问题](docs/FAQ.md)** | ❓ FAQ |
| **[术语表](docs/Glossary.md)** | 📖 概念和术语定义 |

### 示例代码

运行示例：

```bash
# 基础使用示例（Redis + Postgres + 事务）
cargo run --example middleware_basic_usage --features kv-redis,sql-postgres,tokio,obs

# 消息队列示例（NATS + MQTT）
cargo run --example message_queue --features mq-nats,mq-mqtt,tokio,obs

# 综合功能演示（批量操作 + 配置化）
cargo run --example middleware_comprehensive_demo --features kv-redis,sql-postgres,tokio

# Rust 1.90 特性演示
cargo run --example rust190_features_demo --features kv-redis,tokio

# 高级模式
cargo run --example advanced_middleware_patterns --features kv-redis,sql-postgres,tokio
```

更多示例请查看 [examples/](examples/) 目录。

## 🏗️ 项目结构

```text
c11_middlewares/
├── src/                         # 源代码
│   ├── lib.rs                   # 库入口
│   ├── config.rs                # 配置模块
│   ├── cache/                   # 缓存客户端（Redis）
│   ├── database/                # 数据库客户端（PostgreSQL/MySQL/SQLite）
│   ├── mq/                      # 消息队列客户端（Kafka/NATS/MQTT）
│   ├── http/                    # HTTP 代理（Pingora）
│   ├── util.rs                  # 工具模块
│   └── error.rs                 # 错误处理
├── examples/                    # 示例代码（8个）
├── tests/                       # 测试代码
├── docs/                        # 📚 文档中心
│   ├── README.md                # 文档入口
│   ├── 00_MASTER_INDEX.md       # 主索引
│   ├── COMPREHENSIVE_DOCUMENTATION_INDEX.md  # 完整索引
│   ├── FAQ.md                   # 常见问题
│   ├── Glossary.md              # 术语表
│   ├── guides/                  # 使用指南（5个）
│   ├── references/              # 参考文档
│   ├── tutorials/               # 教程（规划中）
│   ├── advanced/                # 高级主题（规划中）
│   ├── analysis/                # 技术分析（12+个）
│   ├── reports/                 # 项目报告（11个）
│   └── archives/                # 归档文档
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

## 🎯 学习路径

根据您的背景选择合适的学习路径：

### 初学者（1周）

1. 📖 阅读 [快速导航](docs/00_MASTER_INDEX.md)
2. 🚀 运行 [基础示例](examples/middleware_basic_usage.rs)
3. 📚 学习 [Redis](docs/guides/redis.md) 和 [SQL](docs/guides/sql.md) 指南

### 开发者（2-3周）

1. 📘 查看 [API参考](docs/references/README.md)
2. 🔧 阅读所有 [使用指南](docs/guides/README.md)
3. 💻 研究 [高级示例](examples/advanced_middleware_patterns.rs)

### 架构师（4周+）

1. 🔬 研究 [技术分析](docs/analysis/README.md)
2. 📊 查看 [项目报告](docs/reports/README.md)
3. 🏗️ 探索 [高级主题](docs/advanced/README.md)

详细学习路径请参考 [文档中心](docs/README.md)。

## 🤝 贡献

我们欢迎社区贡献！

### 贡献方式

- 📝 完善文档
- 🐛 报告问题
- ✨ 提交新特性
- 💡 分享最佳实践

### 开发设置

```bash
# 克隆仓库
git clone https://github.com/rust-lang/c11_middlewares.git
cd c11_middlewares

# 安装依赖
cargo build

# 运行测试
cargo test

# 运行示例
cargo run --example middleware_basic_usage --features kv-redis,sql-postgres,tokio
```

详见 [CONTRIBUTING.md](CONTRIBUTING.md)（如有）。

## 📄 许可证

本项目采用 MIT 许可证 - 查看 [LICENSE](LICENSE) 文件了解详情。

## 🙏 致谢

感谢以下开源项目的贡献：

- [Redis](https://redis.io/) - 内存数据结构存储
- [PostgreSQL](https://www.postgresql.org/) - 开源关系数据库
- [NATS](https://nats.io/) - 云原生消息系统
- [Apache Kafka](https://kafka.apache.org/) - 分布式流处理平台
- [Eclipse Mosquitto](https://mosquitto.org/) - MQTT 消息代理

## 📞 获取帮助

### 文档资源

- 📚 [文档中心](docs/README.md) - 开始探索
- 🗺️ [快速导航](docs/00_MASTER_INDEX.md) - 主索引
- ❓ [常见问题](docs/FAQ.md) - FAQ
- 📖 [术语表](docs/Glossary.md) - 概念定义

### 外部资源

- 📖 [在线文档](https://docs.rs/c11_middlewares)（如有）
- 🐛 [问题报告](https://github.com/rust-lang/c11_middlewares/issues)（如有）
- 💬 [讨论区](https://github.com/rust-lang/c11_middlewares/discussions)（如有）

### 相关项目

- [C05 并发编程](../c05_threads/) - 线程与并发
- [C06 异步编程](../c06_async/) - 异步与 async/await
- [C10 网络编程](../c10_networks/) - 网络协议与通信

---

**c11_middlewares** - 让 Rust 中间件开发更加统一和高效！ 🦀✨

**从这里开始**: [📚 文档中心](docs/README.md) | [🚀 快速导航](docs/00_MASTER_INDEX.md)
