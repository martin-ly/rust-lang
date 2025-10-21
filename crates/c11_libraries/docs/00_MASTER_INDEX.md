# C11 开发库: 主索引 (Master Index)

> **文档定位**: 开发库学习路径总导航，快速定位数据库、缓存、消息队列等资源  
> **使用方式**: 作为学习起点，根据需求选择合适的中间件和集成方案  
> **相关文档**: [README](./README.md) | [FAQ](./FAQ.md) | [Glossary](./Glossary.md)

**最后更新**: 2025-10-19  
**适用版本**: Rust 1.90+  
**文档类型**: 📚 导航索引

---

## 📋 快速导航

### 🎯 按角色导航

| 角色 | 推荐路径 | 关键文档 |
|------|---------|---------|
| **初学者** | README → SQL基础 → Redis入门 | 基础集成 |
| **中级开发者** | 数据库连接池 → 消息队列 → 性能优化 | 生产实践 |
| **架构师** | Rust 1.90特性 → 性能对比 → 架构选型 | 技术选型 |
| **研究者** | 形式化验证 → 跨行业分析 → 生态成熟度 | 理论研究 |

### 📚 按中间件类型导航

| 类型 | 文档 | 支持的中间件 |
|------|------|-------------|
| **关系数据库** | [sql.md](./sql.md) | PostgreSQL, MySQL, SQLite |
| **缓存** | [redis.md](./redis.md) | Redis |
| **消息队列** | [mq.md](./mq.md), [kafka_pingora.md](./kafka_pingora.md) | Kafka, MQTT, NATS |
| **HTTP代理** | [pingora.md](./pingora.md) | Pingora (Cloudflare) |

---

## 🏗️ 核心内容结构

### 第一部分：数据库集成

#### 1. SQL数据库

| 数据库 | 文档 | 驱动 | 源码 |
|-------|------|------|------|
| **PostgreSQL** | [guides/sql.md](./guides/sql.md) | `tokio-postgres` | `src/database/postgres_client.rs` |
| **MySQL** | [guides/sql.md](./guides/sql.md) | `mysql_async` | `src/database/mysql_client.rs` |
| **SQLite** | [guides/sql.md](./guides/sql.md) | `rusqlite` | `src/database/sqlite_client.rs` |

**特性**:

- 异步连接池
- 预编译语句
- 事务支持
- ORM集成（可选）

#### 2. NoSQL/缓存

| 中间件 | 文档 | 驱动 | 源码 |
|--------|------|------|------|
| **Redis** | [guides/redis.md](./guides/redis.md) | `redis` | `src/cache/redis_client.rs` |

**特性**:

- 连接池管理
- Pipeline 批量操作
- Pub/Sub 消息
- 分布式锁

### 第二部分：消息队列

#### 3. 消息中间件

| 类型 | 文档 | 驱动 | 说明 |
|------|------|------|------|
| **Kafka** | [guides/kafka_pingora.md](./guides/kafka_pingora.md) | `rdkafka` | 高吞吐量分布式队列 |
| **MQTT** | [guides/mq.md](./guides/mq.md) | `rumqttc` | IoT消息协议 |
| **NATS** | [guides/mq.md](./guides/mq.md) | `async-nats` | 轻量级消息系统 |

**源码**: `src/mq/`

### 第三部分：HTTP中间件

#### 4. Pingora 集成

| 功能 | 说明 | 源码 |
|------|------|------|
| **反向代理** | HTTP/HTTPS代理 | `src/http/pingora_proxy.rs` |
| **负载均衡** | 多种策略 | - |
| **缓存** | HTTP缓存 | - |

**文档**: [guides/pingora.md](./guides/pingora.md)

### 第四部分：Rust 1.90 特性

#### 5. 最新特性集成

| 特性 | 应用 | 文档 |
|------|------|------|
| **async fn in trait** | 中间件客户端trait | `src/enhanced_config.rs` |
| **RPITIT** | 配置构建器 | `src/rust190_optimizations.rs` |
| **泛型关联类型** | 连接池抽象 | - |

**文档**: [references/RUST_190_FEATURES_GUIDE.md](./references/RUST_190_FEATURES_GUIDE.md)

---

## 📖 实践示例

### 可运行示例 (examples/)

| 示例 | 文件 | 说明 | 运行命令 |
|------|------|------|----------|
| **基础使用** | `middleware_basic_usage.rs` | 快速开始 | `cargo run --example middleware_basic_usage` |
| **综合示例** | `middleware_comprehensive_demo.rs` | 完整功能 | `cargo run --example middleware_comprehensive_demo` |
| **高级模式** | `advanced_middleware_patterns.rs` | 高级用法 | `cargo run --example advanced_middleware_patterns` |
| **消息队列** | `message_queue.rs` | MQ示例 | `cargo run --example message_queue` |
| **Rust 1.90** | `rust190_features_demo.rs` | 最新特性 | `cargo run --example rust190_features_demo` |
| **性能对比** | `glommio_performance_comparison.rs` | glommio对比 | `cargo run --example glommio_performance_comparison` |

---

## 🧪 测试与验证

### 测试套件 (tests/)

| 测试 | 文件 | 说明 |
|------|------|------|
| **集成测试** | `simple_integration_tests.rs` | 基础功能测试 |

### 性能基准 (benches/)

```bash
# 运行所有基准测试
cargo bench -p c11_middlewares

# 运行高级基准测试
cargo bench --bench advanced_benchmarking_demo
```

---

## 📚 学习路径

### 🚀 初学者路径 (1周)

1. **起步**: [README](./README.md) | [文档中心](./README.md)
2. **SQL基础**: [guides/sql.md](./guides/sql.md)
3. **Redis入门**: [guides/redis.md](./guides/redis.md)
4. **实践**: 运行基础示例

**推荐阅读顺序**:

```text
docs/README.md (文档中心)
  ↓
guides/sql.md (PostgreSQL/MySQL)
  ↓
guides/redis.md
  ↓
examples/middleware_basic_usage.rs
```

### 🎓 中级路径 (2-3周)

1. **消息队列**: [guides/mq.md](./guides/mq.md)
2. **Kafka**: [guides/kafka_pingora.md](./guides/kafka_pingora.md)
3. **Pingora**: [guides/pingora.md](./guides/pingora.md)
4. **性能优化**: 基准测试分析

**推荐阅读顺序**:

```text
guides/mq.md
  ↓
guides/kafka_pingora.md
  ↓
examples/message_queue.rs
  ↓
性能基准测试
```

### 🔬 高级路径 (4周+)

1. **Rust 1.90特性**: [references/RUST_190_FEATURES_GUIDE.md](./references/RUST_190_FEATURES_GUIDE.md)
2. **运行时分析**: glommio集成
3. **跨行业分析**: [analysis/rust190_ecosystem/02_cross_industry_analysis/](./analysis/rust190_ecosystem/02_cross_industry_analysis/)
4. **形式化验证**: [analysis/rust190_ecosystem/01_formal_verification/](./analysis/rust190_ecosystem/01_formal_verification/)

---

## 🎯 按场景导航

### Web应用开发

| 需求 | 推荐方案 | 文档 |
|------|---------|------|
| 数据持久化 | PostgreSQL + Diesel/sqlx | [guides/sql.md](./guides/sql.md) |
| 会话管理 | Redis | [guides/redis.md](./guides/redis.md) |
| 异步任务 | Redis + Celery-like | [guides/mq.md](./guides/mq.md) |

### 微服务架构

| 需求 | 推荐方案 | 文档 |
|------|---------|------|
| 服务间通信 | Kafka/NATS | [guides/kafka_pingora.md](./guides/kafka_pingora.md) |
| API网关 | Pingora | [guides/pingora.md](./guides/pingora.md) |
| 配置中心 | Redis | [guides/redis.md](./guides/redis.md) |

### 实时数据处理

| 需求 | 推荐方案 | 文档 |
|------|---------|------|
| 流式处理 | Kafka | [guides/kafka_pingora.md](./guides/kafka_pingora.md) |
| 实时缓存 | Redis | [guides/redis.md](./guides/redis.md) |
| IoT消息 | MQTT | [guides/mq.md](./guides/mq.md) |

---

## 🔗 相关资源

### 项目文档

- **[文档中心](./README.md)** - 📚 文档主入口
- **[完整索引](./COMPREHENSIVE_DOCUMENTATION_INDEX.md)** - 📋 综合文档索引
- [顶层 README](../README.md) - 项目概述
- [常见问题](./FAQ.md) - FAQ
- [术语表](./Glossary.md) - 概念定义

### 使用指南

- [SQL 数据库](./guides/sql.md) - PostgreSQL/MySQL/SQLite
- [Redis 缓存](./guides/redis.md) - Redis 使用指南
- [消息队列](./guides/mq.md) - NATS/MQTT
- [Kafka](./guides/kafka_pingora.md) - Kafka 集成
- [Pingora](./guides/pingora.md) - HTTP 代理

### 参考文档

- [Rust 1.90 特性](./references/RUST_190_FEATURES_GUIDE.md) - Rust 特性指南
- [API 文档](./references/README.md) - API 和配置参考

### 教程资源

- [教程中心](./tutorials/README.md) - 系统化教程（规划中）

### 高级主题

- [高级主题](./advanced/README.md) - 深度技术内容（规划中）

### 技术分析

- [分析中心](./analysis/README.md) - 技术分析总览
- [生态系统分析](./reports/COMPREHENSIVE_RUST_190_ECOSYSTEM_ANALYSIS.md)
- [形式化验证](./analysis/rust190_ecosystem/01_formal_verification/formal_verification_framework.md)
- [跨行业对比](./analysis/rust190_ecosystem/02_cross_industry_analysis/cross_industry_comparison.md)
- [性能分析](./analysis/rust190_ecosystem/03_performance_benchmarks/performance_analysis.md)
- [安全分析](./analysis/rust190_ecosystem/04_security_analysis/security_comprehensive_analysis.md)

### 项目报告

- [进度报告](./reports/COMPREHENSIVE_PROGRESS_REPORT_2025_09_28.md) - 项目状态
- [技术报告](./reports/) - 所有技术报告
- [修复总结](./reports/) - 问题修复记录

---

## 📊 项目统计

### 代码规模

- **数据库模块**: PostgreSQL, MySQL, SQLite
- **缓存模块**: Redis
- **消息队列**: Kafka, MQTT, NATS
- **HTTP中间件**: Pingora
- **示例程序**: 6+ 可运行示例
- **测试用例**: 集成测试套件

### 文档规模

- **核心文档**: 7 个主要文档
- **分析文档**: 5+ 深度分析
- **示例代码**: 完整的文档注释

---

## 🆕 最新更新

### 2025-10-19

- ✅ 重组文档结构
- ✅ 创建清晰的目录分类
- ✅ 建立完整的文档索引体系
- ✅ 更新所有文档链接

### 2025年9月

- ✅ 集成 Rust 1.90 特性
- ✅ 添加 Pingora 支持
- ✅ 完善性能基准测试
- ✅ glommio 运行时集成
- ✅ 完成大量技术分析报告

---

## 📞 获取帮助

### 问题解决

1. **查看 FAQ**: [FAQ.md](./FAQ.md) - 常见问题解答
2. **查看术语表**: [Glossary.md](./Glossary.md) - 核心概念定义
3. **查看示例**: examples/ - 可运行的示例代码
4. **运行测试**: `cargo test` - 验证功能

---

**文档维护**: Rust 学习社区  
**更新频率**: 跟随项目进度持续更新  
**文档版本**: v2.0  
**最后更新**: 2025-10-19  
**Rust 版本**: 1.90+

---

## 📍 其他重要文档

- **[文档中心](./README.md)** - 文档总入口
- **[完整文档索引](./COMPREHENSIVE_DOCUMENTATION_INDEX.md)** - 查找所有文档
- **[使用指南汇总](./guides/README.md)** - 中间件使用指南
- **[参考文档汇总](./references/README.md)** - API 和配置参考
- **[教程中心](./tutorials/README.md)** - 系统化教程
- **[高级主题汇总](./advanced/README.md)** - 深度技术内容
- **[技术分析汇总](./analysis/README.md)** - 技术分析和研究
- **[项目报告汇总](./reports/README.md)** - 进度和技术报告
