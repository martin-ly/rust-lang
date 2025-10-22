# Tier 2: 实践指南层 (Guides)

> **文档定位**: 生产级实践指南，覆盖数据库、缓存、消息队列、Web框架、异步运行时  
> **完成状态**: ✅ 100% (5/5)  
> **最后更新**: 2025-10-21  
> **总代码示例**: 420+

## 📋 目录

- [Tier 2: 实践指南层 (Guides)](#tier-2-实践指南层-guides)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [完成统计](#完成统计)
    - [覆盖领域](#覆盖领域)
  - [📚 数据库指南](#-数据库指南)
    - [SQL 数据库](#sql-数据库)
  - [🗄️ 缓存指南](#️-缓存指南)
    - [Redis](#redis)
  - [📨 消息队列指南](#-消息队列指南)
    - [通用消息队列](#通用消息队列)
    - [Kafka 与 Pingora](#kafka-与-pingora)
  - [🌐 HTTP 代理指南](#-http-代理指南)
    - [Pingora](#pingora)
  - [🚀 快速开始](#-快速开始)
  - [💡 使用建议](#-使用建议)
  - [📚 标准化文档链接](#-标准化文档链接)

## 🎯 概述

**Tier 2 实践指南层** 提供了 5 个核心技术领域的详细实践指南，所有文档均达到生产级标准。

### 完成统计

```text
📚 文档数量: 5 个核心指南
📖 总行数: 6,918+ 行
💻 代码示例: 420+ 个 (100% 可运行)
⭐ 完成度: 100% ✅
```

### 覆盖领域

| 领域 | 核心库 | 文档 | 示例数 |
|------|--------|------|--------|
| **数据库** | SQLx, SeaORM, Diesel | 2.1 | 80+ |
| **缓存** | Redis, Moka | 2.2 | 80+ |
| **消息队列** | Kafka, RabbitMQ, NATS | 2.3 | 90+ |
| **Web框架** | Axum, Actix-web, Rocket | 2.4 | 100+ |
| **异步运行时** | Tokio, async-std | 2.5 | 70+ |

每个指南都包含：

- ✅ 快速开始示例
- ✅ 配置说明
- ✅ 最佳实践
- ✅ 常见问题
- ✅ 性能优化建议

## 📚 数据库指南

### SQL 数据库

**文档**: [sql.md](sql.md)

**支持的数据库**:

- PostgreSQL - 生产级关系数据库
- MySQL - 广泛使用的关系数据库
- SQLite - 轻量级嵌入式数据库

**核心特性**:

- ✅ 连接池管理
- ✅ 事务支持
- ✅ 类型映射
- ✅ 批量操作
- ✅ 配置化使用

**快速开始**:

```rust
use c11_libraries::sql::SqlDatabase;

// PostgreSQL
let db = c11_libraries::postgres_client::PostgresDb::connect(
    "postgres://user:pass@localhost/db"
).await?;

// 查询
let rows = db.query("SELECT id, name FROM users").await?;
```

**适用场景**:

- Web 应用数据持久化
- 事务性业务逻辑
- 复杂查询和分析

## 🗄️ 缓存指南

### Redis

**文档**: [redis.md](redis.md)

**核心特性**:

- ✅ 连接池管理
- ✅ Pipeline 批量操作
- ✅ Pub/Sub 消息
- ✅ 分布式锁
- ✅ 超时与重试

**快速开始**:

```rust
use c11_libraries::kv::KeyValueStore;

let store = c11_libraries::redis_client::RedisStore::connect(
    "redis://127.0.0.1:6379"
).await?;

store.set("key", b"value").await?;
let value = store.get("key").await?;
```

**适用场景**:

- 会话管理
- 缓存热点数据
- 实时排行榜
- 分布式锁

## 📨 消息队列指南

### 通用消息队列

**文档**: [mq.md](mq.md)

**支持的消息队列**:

- NATS - 轻量级消息系统
- MQTT - IoT 消息协议

**核心特性**:

- ✅ 发布/订阅模式
- ✅ 低延迟通信
- ✅ QoS 支持（MQTT）
- ✅ 会话管理

**快速开始**:

```rust
// NATS
let producer = c11_libraries::nats_client::NatsProducer::connect(
    "nats://127.0.0.1:4222", "subject"
).await?;

producer.publish(b"Hello, NATS!").await?;

// MQTT
let (mqtt_producer, _) = c11_libraries::mqtt_client::MqttProducer::connect(
    "127.0.0.1", 1883, "client-1"
).await?;

mqtt_producer.publish("topic/test", b"Hello, MQTT!").await?;
```

**适用场景**:

- 微服务间通信
- IoT 设备消息
- 实时通知推送
- 事件驱动架构

### Kafka 与 Pingora

**文档**: [kafka_pingora.md](kafka_pingora.md)

**Kafka 特性**:

- ✅ 高吞吐量
- ✅ 持久化存储
- ✅ 分布式架构
- ✅ 流式处理

**快速开始**:

```rust
let kafka_config = KafkaConfig::new("localhost:9092", "my_group");
let producer = KafkaProducer::new_with_config(kafka_config)?;

producer.send("my_topic", b"Hello, Kafka!").await?;
```

**适用场景**:

- 日志聚合
- 流式数据处理
- 事件溯源
- 数据管道

## 🌐 HTTP 代理指南

### Pingora

**文档**: [pingora.md](pingora.md)

**核心特性**:

- ✅ 反向代理
- ✅ 负载均衡
- ✅ HTTP 缓存
- 🚧 TLS 支持（开发中）

**快速开始**:

```rust
// 基础代理配置
let config = PingoraConfig::new()
    .upstream("http://backend:8080")
    .listen("0.0.0.0:80");
```

**适用场景**:

- API 网关
- 服务代理
- 负载均衡
- HTTP 缓存

## 🚀 快速开始

1. **选择中间件**: 根据需求选择合适的中间件
2. **阅读指南**: 查看对应的详细文档
3. **查看示例**: 参考 [examples/](../../examples/) 目录
4. **运行测试**: 使用 `cargo run --example <name>` 运行示例

## 💡 使用建议

| 场景 | 推荐方案 | 文档 |
|------|---------|------|
| Web 应用数据存储 | PostgreSQL + Redis | [sql.md](sql.md), [redis.md](redis.md) |
| 微服务架构 | NATS/Kafka + Redis | [mq.md](mq.md), [redis.md](redis.md) |
| IoT 平台 | MQTT + Redis | [mq.md](mq.md), [redis.md](redis.md) |
| 实时数据处理 | Kafka + Redis | [kafka_pingora.md](kafka_pingora.md), [redis.md](redis.md) |
| API 网关 | Pingora + Redis | [pingora.md](pingora.md), [redis.md](redis.md) |

---

## 📚 标准化文档链接

本目录包含旧版文档和新版标准化文档：

**新版标准化文档** (推荐使用):

- [2.1 数据库集成指南](2.1_数据库集成指南.md) - SQLx, SeaORM, Diesel, MongoDB, Redis
- [2.2 缓存系统指南](2.2_缓存系统指南.md) - Redis 深度、本地缓存、分布式锁
- [2.3 消息队列指南](2.3_消息队列指南.md) - Kafka, RabbitMQ, NATS 完整实战
- [2.4 Web框架指南](2.4_Web框架指南.md) - Axum, Actix-web, RESTful, WebSocket
- [2.5 异步运行时指南](2.5_异步运行时指南.md) - Tokio, async-std, 异步编程模式

**旧版文档** (保留供参考):

- [sql.md](sql.md) - SQL 数据库基础版
- [redis.md](redis.md) - Redis 基础版
- [mq.md](mq.md) - 消息队列基础版
- [kafka_pingora.md](kafka_pingora.md) - Kafka 集成
- [pingora.md](pingora.md) - Pingora HTTP 代理

---

**更新日期**: 2025-10-21  
**Rust 版本**: 1.90+  
**完成状态**: ✅ 100% (5/5 标准化文档)

如有问题，请查看：

- [../1.3_常见问题.md](../1.3_常见问题.md) - FAQ
- [../00_MASTER_INDEX.md](../00_MASTER_INDEX.md) - 主索引导航
- [../README.md](../README.md) - 文档中心
