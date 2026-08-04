# 数据库示例（Database Examples）索引

## 📊 目录

- [数据库示例（Database Examples）索引](#数据库示例database-examples索引)
  - [📊 目录](#-目录)
  - [目的](#目的)
  - [核心示例](#核心示例)
    - [关系型数据库](#关系型数据库)
    - [NoSQL 数据库](#nosql-数据库)
    - [数据库操作](#数据库操作)
    - [数据库设计](#数据库设计)
  - [实践与样例](#实践与样例)
    - [文件级清单（精选）](#文件级清单精选)
  - [相关索引](#相关索引)
  - [导航](#导航)

## 目的

- 提供 Rust 数据库开发的实用示例。
- 展示如何构建高性能的数据库应用。

## 核心示例

### 关系型数据库

- PostgreSQL 集成示例
- MySQL 集成示例
- SQLite 集成示例
- 数据库连接池示例

### NoSQL 数据库

- MongoDB 集成示例
- Redis 集成示例
- Cassandra 集成示例
- DynamoDB 集成示例

### 数据库操作

- CRUD 操作示例
- 事务处理示例
- 查询优化示例
- 数据迁移示例

### 数据库设计

- 数据模型设计
- 索引优化
- 查询性能优化
- 数据一致性

## 实践与样例

- 数据库示例：参见 [crates/c77_database](../../../crates/c77_database/)
- 数据存储：[crates/c78_data_storage](../../../crates/c78_data_storage/)
- 数据访问：[crates/c79_data_access](../../../crates/c79_data_access/)

### 文件级清单（精选）

- `crates/c77_database/src/`：
  - `relational_databases.rs`：关系型数据库示例
  - `nosql_databases.rs`：NoSQL 数据库示例
  - `database_operations.rs`：数据库操作示例
  - `database_design.rs`：数据库设计示例
- `crates/c78_data_storage/src/`：
  - `data_persistence.rs`：数据持久化示例
  - `data_caching.rs`：数据缓存示例
  - `data_synchronization.rs`：数据同步示例

## 相关索引

- 理论基础（并发模型）：[`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- 编程范式（异步）：[`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- 应用领域（大数据分析）：[`../../04_application_domains/07_big_data_analytics/00_index.md`](../../04_application_domains/07_big_data_analytics/00_index.md)

## 导航

- 返回实用示例：[`../00_index.md`](../00_index.md)
- 嵌入式示例：[`../10_embedded_examples/00_index.md`](../10_embedded_examples/00_index.md)
- 消息队列示例：[`../12_messaging_examples/00_index.md`](../12_messaging_examples/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
