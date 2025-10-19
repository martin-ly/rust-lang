# C11 中间件集成 - 文档中心

> 欢迎来到 C11 中间件集成项目文档中心！本文档是您探索项目的起点。

[![Rust](https://img.shields.io/badge/rust-1.90+-orange.svg)](https://www.rust-lang.org/)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](../../LICENSE)
[![Documentation](https://img.shields.io/badge/docs-latest-blue.svg)](.)

## 🎯 项目简介

C11 中间件集成项目提供了一个统一的 Rust 接口来集成各类主流中间件，包括：

- **数据库**: PostgreSQL、MySQL、SQLite
- **缓存**: Redis
- **消息队列**: Kafka、NATS、MQTT
- **HTTP 代理**: Pingora

**核心特性**:
- ✅ 统一的接口设计
- ✅ Rust 1.90+ 特性支持
- ✅ 异步非阻塞
- ✅ 连接池管理
- ✅ 配置化使用
- ✅ 完整的可观测性

## 🚀 快速开始

### 5 分钟快速体验

```rust
use c11_middlewares::prelude::*;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Redis 示例
    let redis_config = RedisConfig::new("redis://127.0.0.1:6379");
    let store = RedisStore::connect_with(redis_config).await?;
    store.set("hello", b"world").await?;
    
    // PostgreSQL 示例
    let pg_config = PostgresConfig::new("postgres://user:pass@localhost/db");
    let db = PostgresDb::connect_with(pg_config).await?;
    let rows = db.query("SELECT * FROM users LIMIT 10").await?;
    
    println!("✅ 中间件集成成功！");
    Ok(())
}
```

### 运行示例

```bash
# 基础使用示例
cargo run --example middleware_basic_usage --features kv-redis,sql-postgres,tokio

# 消息队列示例
cargo run --example message_queue --features mq-nats,mq-mqtt,tokio

# Rust 1.90 特性演示
cargo run --example rust190_features_demo --features kv-redis,tokio
```

## 📚 文档导航

### 🗺️ 主要入口

| 文档 | 说明 | 适合人群 |
|------|------|---------|
| [00_MASTER_INDEX.md](00_MASTER_INDEX.md) | 快速导航和学习路径 | 所有用户 ⭐推荐 |
| [COMPREHENSIVE_DOCUMENTATION_INDEX.md](COMPREHENSIVE_DOCUMENTATION_INDEX.md) | 完整文档索引 | 需要全面了解 |
| [FAQ.md](FAQ.md) | 常见问题解答 | 遇到问题时 |
| [Glossary.md](Glossary.md) | 术语表 | 查询概念定义 |

### 📖 按主题浏览

#### 🔧 使用指南

> 详见 [guides/README.md](guides/README.md)

| 指南 | 说明 |
|------|------|
| [guides/sql.md](guides/sql.md) | SQL 数据库集成（PostgreSQL/MySQL/SQLite） |
| [guides/redis.md](guides/redis.md) | Redis 缓存使用 |
| [guides/mq.md](guides/mq.md) | 消息队列（NATS/MQTT） |
| [guides/kafka_pingora.md](guides/kafka_pingora.md) | Kafka 与 Pingora |
| [guides/pingora.md](guides/pingora.md) | Pingora HTTP 代理 |

#### 📘 参考文档

> 详见 [references/README.md](references/README.md)

| 文档 | 说明 |
|------|------|
| [references/RUST_190_FEATURES_GUIDE.md](references/RUST_190_FEATURES_GUIDE.md) | Rust 1.90 特性指南 |
| API 文档 | 使用 `cargo doc --open` 查看 |

#### 📖 教程学习

> 详见 [tutorials/README.md](tutorials/README.md)

系统化的教程内容（规划中）：
- 🚀 快速入门系列
- 🎓 进阶教程系列
- 💼 实战案例系列

#### 🎓 高级主题

> 详见 [advanced/README.md](advanced/README.md)

深度技术内容（规划中）：
- ⚡ 性能优化
- 🏗️ 架构设计
- 🛡️ 可靠性工程
- 🔒 安全实践
- 📊 监控运维

#### 🔬 技术分析

> 详见 [analysis/README.md](analysis/README.md)

深度技术分析和研究：
- Rust 1.90 生态系统分析
- 形式化验证框架
- 跨行业对比分析
- 性能基准测试
- 安全综合分析
- 生态成熟度评估

#### 📊 项目报告

> 详见 [reports/README.md](reports/README.md)

项目进度和技术报告：
- 📈 进度报告（2份）
- 🔬 技术报告（5份）
- 🛠️ 修复总结（4份）

## 🎯 按场景查找

### Web 应用开发

**需求**: 构建 Web 应用，需要数据库和缓存

**推荐路径**:
1. 阅读 [guides/sql.md](guides/sql.md) - PostgreSQL 集成
2. 阅读 [guides/redis.md](guides/redis.md) - Redis 缓存
3. 运行 `examples/middleware_comprehensive_demo.rs`

### 微服务架构

**需求**: 构建微服务，需要消息队列

**推荐路径**:
1. 阅读 [guides/mq.md](guides/mq.md) - NATS/MQTT
2. 阅读 [guides/kafka_pingora.md](guides/kafka_pingora.md) - Kafka
3. 运行 `examples/message_queue.rs`

### IoT 平台

**需求**: IoT 设备数据采集和处理

**推荐路径**:
1. 阅读 [guides/mq.md](guides/mq.md) - MQTT 协议
2. 阅读 [guides/redis.md](guides/redis.md) - Redis 缓存
3. 参考 IoT 相关示例

### 实时数据处理

**需求**: 处理大量实时数据流

**推荐路径**:
1. 阅读 [guides/kafka_pingora.md](guides/kafka_pingora.md) - Kafka
2. 阅读 [guides/redis.md](guides/redis.md) - Redis
3. 查看性能优化文档

## 👥 按角色导航

### 新手用户

**您是 Rust 初学者或刚接触本项目？**

**推荐路径**:
1. 📖 阅读 [00_MASTER_INDEX.md](00_MASTER_INDEX.md)
2. 🚀 运行基础示例
3. 📚 按初学者路径学习（约1周）

**资源**:
- [guides/](guides/) - 中间件使用指南
- [FAQ.md](FAQ.md) - 常见问题
- [examples/](../examples/) - 示例代码

### 开发者

**您有 Rust 经验，想使用项目开发应用？**

**推荐路径**:
1. 📘 查看 [references/](references/) API 参考
2. 🔧 阅读 [guides/](guides/) 详细指南
3. 💻 参考 [examples/](../examples/) 示例

**资源**:
- [guides/](guides/) - 详细使用指南
- [references/](references/) - API 和配置参考
- [advanced/](advanced/) - 高级主题

### 架构师

**您负责技术选型和架构设计？**

**推荐路径**:
1. 🔬 阅读 [analysis/](analysis/) 技术分析
2. 📊 查看 [reports/](reports/) 项目报告
3. 🏗️ 参考 [advanced/](advanced/) 架构设计

**资源**:
- [analysis/rust190_ecosystem/](analysis/rust190_ecosystem/) - 生态系统分析
- [reports/](reports/) - 技术报告
- [advanced/](advanced/) - 架构设计主题

### 研究者

**您对技术深度和理论感兴趣？**

**推荐路径**:
1. 🔬 深入 [analysis/](analysis/) 技术分析
2. 📊 研究性能基准测试
3. 🔒 查看形式化验证框架

**资源**:
- [analysis/rust190_ecosystem/01_formal_verification/](analysis/rust190_ecosystem/01_formal_verification/) - 形式化验证
- [analysis/rust190_ecosystem/02_cross_industry_analysis/](analysis/rust190_ecosystem/02_cross_industry_analysis/) - 跨行业分析
- [analysis/rust190_ecosystem/03_performance_benchmarks/](analysis/rust190_ecosystem/03_performance_benchmarks/) - 性能分析

## 📊 文档统计

### 文档数量

- **核心文档**: 4个（README、FAQ、Glossary、Master Index）
- **使用指南**: 5个（SQL、Redis、MQ、Kafka、Pingora）
- **参考文档**: 2个（Rust 特性、API 文档）
- **技术分析**: 12+ 个
- **项目报告**: 11个
- **示例代码**: 8个

### 内容覆盖

| 领域 | 完成度 | 文档数量 |
|------|--------|---------|
| 数据库 | ✅ 完成 | 1个指南 + 示例 |
| 缓存 | ✅ 完成 | 1个指南 + 示例 |
| 消息队列 | ✅ 完成 | 2个指南 + 示例 |
| HTTP 代理 | 🚧 开发中 | 2个指南 |
| 教程 | 📝 规划中 | 框架已建立 |
| 高级主题 | 📝 规划中 | 框架已建立 |

### 最近更新

- **2025-10-19**: 文档结构重组，创建新的导航体系
- **2025-09-28**: 大量技术报告和分析文档
- **持续更新**: 跟随项目进度更新

## 🔍 搜索帮助

**查找特定主题**:
1. 使用 [00_MASTER_INDEX.md](00_MASTER_INDEX.md) 快速定位
2. 使用 [COMPREHENSIVE_DOCUMENTATION_INDEX.md](COMPREHENSIVE_DOCUMENTATION_INDEX.md) 全面查找
3. 查看各子目录的 README

**查找错误解决方案**:
1. 查看 [FAQ.md](FAQ.md) 常见问题
2. 查看 [reports/](reports/) 修复总结
3. 搜索相关中间件的指南文档

**查找示例代码**:
1. 浏览 [examples/](../examples/) 目录
2. 查看各指南中的代码示例
3. 运行 `cargo run --example <name>` 测试

## 🤝 贡献文档

我们欢迎文档贡献！

**如何贡献**:
1. 在对应目录创建或更新文档
2. 遵循现有文档格式和风格
3. 更新相关的索引和 README
4. 提交 Pull Request

**文档标准**:
- 使用清晰的标题和目录
- 提供代码示例
- 包含使用说明
- 标注适用版本

## 📞 获取帮助

**遇到问题？**

1. 查看 [FAQ.md](FAQ.md) - 常见问题解答
2. 查看 [Glossary.md](Glossary.md) - 术语定义
3. 浏览相关的使用指南
4. 查看示例代码
5. 提交 Issue

**反馈建议？**

- 提交 Issue 描述问题或建议
- 提交 Pull Request 贡献代码或文档
- 参与社区讨论

## 🔗 相关资源

### 项目资源

- [主项目 README](../README.md) - 项目概述
- [Cargo.toml](../Cargo.toml) - 依赖配置
- [examples/](../examples/) - 示例代码
- [src/](../src/) - 源代码

### 外部资源

- [Rust 官方文档](https://doc.rust-lang.org/)
- [Tokio 文档](https://tokio.rs/)
- [Redis 文档](https://redis.io/docs/)
- [PostgreSQL 文档](https://www.postgresql.org/docs/)

### 相关章节

- [C05 并发编程](../../c05_threads/) - 线程与并发
- [C06 异步编程](../../c06_async/) - 异步编程
- [C10 网络编程](../../c10_networks/) - 网络协议

---

**文档版本**: v2.0  
**最后更新**: 2025-10-19  
**Rust 版本**: 1.90+  
**维护团队**: Rust 学习社区

---

**让 Rust 中间件集成更简单！** 🦀✨

**开始探索**: 从 [00_MASTER_INDEX.md](00_MASTER_INDEX.md) 开始您的旅程！
