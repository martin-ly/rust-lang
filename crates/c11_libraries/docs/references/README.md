# Tier 3: 参考层 (References)

> **文档定位**: 技术选型参考、性能基准、架构模式、Rust 特性解析  
> **完成状态**: ✅ 100% (5/5)  
> **最后更新**: 2025-10-21  
> **总行数**: 6,813+

## 📋 目录

- [Tier 3: 参考层 (References)](#tier-3-参考层-references)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [📚 Rust 特性](#-rust-特性)
    - [Rust 1.90 特性指南](#rust-190-特性指南)
  - [🔧 API 参考](#-api-参考)
    - [核心接口](#核心接口)
    - [配置模块](#配置模块)
    - [工具模块](#工具模块)
  - [⚙️ 配置参考](#️-配置参考)
    - [Redis 配置](#redis-配置)
    - [SQL 配置](#sql-配置)
    - [消息队列配置](#消息队列配置)
  - [📖 使用方式](#-使用方式)
  - [📚 标准化参考文档 (Tier 3)](#-标准化参考文档-tier-3)
  - [🔬 延伸阅读：深度分析 (Analysis)](#-延伸阅读深度分析-analysis)
    - [与 Tier 3 相关的深度分析](#与-tier-3-相关的深度分析)
    - [为什么要阅读 Analysis？](#为什么要阅读-analysis)
    - [推荐阅读顺序](#推荐阅读顺序)

## 🎯 概述

本目录提供了项目的参考文档，包括：

- **Rust 特性**: Rust 1.90+ 新特性及其在项目中的应用
- **API 参考**: 核心接口、配置、工具模块的详细说明
- **配置参考**: 各中间件的配置选项和最佳实践

## 📚 Rust 特性

### Rust 1.90 特性指南

**文档**: [RUST_190_FEATURES_GUIDE.md](RUST_190_FEATURES_GUIDE.md)

**主要内容**:

- ✅ Rust 1.90 核心特性介绍
- ✅ 特性在项目中的应用示例
- ✅ 最佳实践和使用建议
- ✅ 性能优化技巧

**涵盖特性**:

- `async fn` in trait
- 返回位置 impl Trait in Trait (RPITIT)
- 泛型关联类型 (GAT)
- 生命周期语法增强
- 常量泛型推断
- FFI 改进（128位整数）

**快速示例**:

```rust
// async fn in trait
trait MiddlewareClient {
    async fn connect(&self) -> Result<Connection>;
}

// 常量泛型推断
struct Config<const N: usize> {
    pool_size: usize,
}
```

## 🔧 API 参考

### 核心接口

| 接口 | 模块 | 说明 |
|------|------|------|
| `KeyValueStore` | `kv` | Key-Value 存储统一接口 |
| `SqlDatabase` | `sql` | SQL 数据库统一接口 |
| `MessageProducer` | `mq` | 消息生产者接口 |
| `MessageConsumer` | `mq` | 消息消费者接口 |

**KeyValueStore 接口**:

```rust
pub trait KeyValueStore {
    async fn set(&self, key: &str, value: &[u8]) -> Result<()>;
    async fn get(&self, key: &str) -> Result<Option<Vec<u8>>>;
    async fn delete(&self, key: &str) -> Result<()>;
    async fn exists(&self, key: &str) -> Result<bool>;
    async fn mget(&self, keys: &[&str]) -> Result<Vec<Option<Vec<u8>>>>;
    async fn mset(&self, pairs: &[(&str, &[u8])]) -> Result<()>;
}
```

**SqlDatabase 接口**:

```rust
pub trait SqlDatabase {
    async fn execute(&self, sql: &str) -> Result<u64>;
    async fn query(&self, sql: &str) -> Result<Vec<Row>>;
    async fn begin(&self) -> Result<()>;
    async fn commit(&self) -> Result<()>;
    async fn rollback(&self) -> Result<()>;
    async fn batch_execute(&self, sqls: &[&str]) -> Result<Vec<u64>>;
}
```

### 配置模块

| 配置结构 | 模块 | 说明 |
|---------|------|------|
| `RedisConfig` | `config` | Redis 连接配置 |
| `PostgresConfig` | `config` | PostgreSQL 连接配置 |
| `MysqlConfig` | `config` | MySQL 连接配置 |
| `SqliteConfig` | `config` | SQLite 连接配置 |
| `NatsConfig` | `config` | NATS 连接配置 |
| `KafkaConfig` | `config` | Kafka 连接配置 |
| `MqttConfig` | `config` | MQTT 连接配置 |

**配置示例**:

```rust
// Redis 配置
let redis_config = RedisConfig::new("redis://127.0.0.1:6379")
    .with_pool_size(10)
    .with_timeout_ms(5000);

// PostgreSQL 配置
let pg_config = PostgresConfig::new("postgres://user:pass@localhost/db")
    .with_max_connections(20)
    .with_connection_timeout_ms(3000);
```

### 工具模块

| 工具 | 模块 | 说明 |
|------|------|------|
| `retry_async` | `util` | 异步重试机制 |
| `Error` | `error` | 统一错误类型 |

**重试机制示例**:

```rust
use c11_libraries::util::retry_async;

let result = retry_async(
    || async { 
        // 可能失败的操作
        middleware.connect().await 
    },
    3, // 最大重试次数
    Duration::from_millis(100), // 初始退避时间
).await?;
```

## ⚙️ 配置参考

### Redis 配置

**基础配置**:

```rust
RedisConfig::new("redis://127.0.0.1:6379")
    .with_pool_min_max(1, 16)        // 连接池大小
    .with_connect_timeout_ms(2_000)   // 连接超时
    .with_cmd_timeout_ms(1_000)       // 命令超时
```

**配置选项**:

| 选项 | 默认值 | 说明 |
|------|--------|------|
| `pool_size` | 10 | 连接池大小 |
| `timeout_ms` | 5000 | 超时时间（毫秒） |
| `max_retries` | 3 | 最大重试次数 |

### SQL 配置

**PostgreSQL 配置**:

```rust
PostgresConfig::new("postgres://user:pass@localhost/db")
    .with_max_connections(20)              // 最大连接数
    .with_connection_timeout_ms(3000)      // 连接超时
    .with_statement_timeout_ms(30000)      // 语句超时
```

**MySQL 配置**:

```rust
MysqlConfig::new("mysql://user:pass@localhost/db")
    .with_pool_size(15)
    .with_timeout_ms(5000)
```

**SQLite 配置**:

```rust
SqliteConfig::new("data.db")
    .in_memory(false)                      // 是否内存数据库
    .read_only(false)                      // 是否只读
```

### 消息队列配置

**NATS 配置**:

```rust
NatsConfig::new("nats://127.0.0.1:4222", "subject")
    .with_max_reconnects(5)
    .with_reconnect_delay_ms(1000)
```

**Kafka 配置**:

```rust
KafkaConfig::new("localhost:9092", "my_group")
    .with_session_timeout_ms(6000)
    .with_message_timeout_ms(5000)
```

**MQTT 配置**:

```rust
MqttConfig::new("127.0.0.1", 1883, "client-1")
    .with_keep_alive_secs(60)
    .with_clean_session(true)
```

## 📖 使用方式

**查找 API**:

1. 确定需要使用的中间件类型
2. 查找对应的接口定义
3. 查看配置选项
4. 参考使用指南中的示例

**配置中间件**:

1. 创建对应的配置对象
2. 设置必要的配置选项
3. 使用配置对象初始化中间件客户端
4. 调用接口方法

**错误处理**:

```rust
use c11_libraries::Error;

match middleware.operation().await {
    Ok(value) => println!("Success: {:?}", value),
    Err(Error::Redis(e)) => eprintln!("Redis error: {}", e),
    Err(Error::Postgres(e)) => eprintln!("Postgres error: {}", e),
    Err(e) => eprintln!("Other error: {}", e),
}
```

---

## 📚 标准化参考文档 (Tier 3)

**新版标准化文档** (推荐使用):

1. **[3.1 Rust 1.90 特性全解析](3.1_Rust_1.90_特性全解析.md)** (1,097 行)
   - Rust 1.90 新特性详解
   - 编译器改进和性能优化
   - 迁移指南和最佳实践

2. **[3.2 开源库生态全景图](3.2_开源库生态全景图.md)** (1,085 行)
   - 250+ 库分类和对比
   - 5 层架构生态体系
   - 技术选型指南

3. **[3.3 库成熟度评估矩阵](3.3_库成熟度评估矩阵.md)** (978 行)
   - 7 维度评估体系
   - 170+ 库成熟度评分
   - 技术选型决策树

4. **[3.4 性能基准测试报告](3.4_性能基准测试报告.md)** (1,430 行)
   - 9 大类性能对比
   - 标准化测试方法
   - 生产级优化建议

5. **[3.5 架构设计模式集](3.5_架构设计模式集.md)** (2,223 行)
   - 30+ 架构设计模式
   - 微服务、数据、并发、可靠性
   - 生产级实战案例

**旧版文档** (保留供参考):

- [RUST_190_FEATURES_GUIDE.md](RUST_190_FEATURES_GUIDE.md) - Rust 1.90 基础特性

---

## 🔬 延伸阅读：深度分析 (Analysis)

> 想要更深入的理论研究和详细数据？查看 **Analysis 目录**的深度分析报告！

### 与 Tier 3 相关的深度分析

| Tier 3 文档 | 对应 Analysis 深度分析 | 关系 |
|------------|----------------------|------|
| **3.3 库成熟度评估矩阵** | [05_ecosystem_maturity_assessment.md](../analysis/rust190_ecosystem/05_ecosystem_maturity/ecosystem_maturity_assessment.md) | 📊 评估方法论详解 |
| **3.4 性能基准测试报告** | [03_performance_analysis.md](../analysis/rust190_ecosystem/03_performance_benchmarks/performance_analysis.md) | 📈 详细测试数据 |

### 为什么要阅读 Analysis？

- ✅ **更深层次的理解**: Analysis 提供学术级的理论框架和研究方法
- ✅ **详细的原始数据**: 包含完整的测试数据、统计分析和回归测试
- ✅ **对比研究**: 跨语言、跨框架的详细对比分析
- ✅ **评估方法论**: 深入理解评估体系的设计思路和指标构建

### 推荐阅读顺序

**性能优化场景**:

```text
1. 3.4 性能基准测试报告 (快速参考)
2. analysis/03_performance_analysis.md (详细数据)
3. 相关代码示例 (实践验证)
```

**技术选型场景**:

```text
1. 3.3 库成熟度评估矩阵 (选型指南)
2. analysis/05_ecosystem_maturity_assessment.md (评估方法论)
3. 3.2 开源库生态全景图 (生态全貌)
```

**完整 Analysis 导航**: [../analysis/README.md](../analysis/README.md)

---

**更新日期**: 2025-10-22  
**Rust 版本**: 1.90+  
**完成状态**: ✅ 100% (5/5 标准化文档)

如有问题，请查看：

- [../1.1_主索引导航.md](../1.1_主索引导航.md) - 主索引
- [../1.3_常见问题.md](../1.3_常见问题.md) - FAQ
- [../00_MASTER_INDEX.md](../00_MASTER_INDEX.md) - 完整索引
- [../analysis/README.md](../analysis/README.md) - 深度分析档案
