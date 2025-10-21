# 中间件使用指南

> 本目录包含各类中间件的详细使用指南和最佳实践

## 📋 目录

- [中间件使用指南](#中间件使用指南)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
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

## 🎯 概述

本目录提供了各类中间件的详细使用指南，包括：

- **数据库集成**：PostgreSQL、MySQL、SQLite
- **缓存系统**：Redis
- **消息队列**：Kafka、NATS、MQTT
- **HTTP 代理**：Pingora

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

**更新日期**: 2025-10-19  
**Rust 版本**: 1.90+

如有问题，请查看：

- [FAQ.md](../FAQ.md) - 常见问题
- [COMPREHENSIVE_DOCUMENTATION_INDEX.md](../COMPREHENSIVE_DOCUMENTATION_INDEX.md) - 完整文档索引
