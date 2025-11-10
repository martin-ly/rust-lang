# 数据库示例（Database Examples）索引

> **创建日期**: 2025-10-31
> **最后更新**: 2025-11-10
> **Rust 版本**: 1.91.0 (Edition 2024) ✅
> **状态**: 已完善 ✅

---

## 📊 目录

- [数据库示例（Database Examples）索引](#数据库示例database-examples索引)
  - [📊 目录](#-目录)
  - [🎯 目的](#-目的)
    - [核心价值](#核心价值)
  - [📚 核心示例](#-核心示例)
    - [1. 关系型数据库（Relational Databases）](#1-关系型数据库relational-databases)
    - [2. NoSQL 数据库（NoSQL Databases）](#2-nosql-数据库nosql-databases)
    - [3. 数据库操作（Database Operations）](#3-数据库操作database-operations)
    - [4. 数据库设计（Database Design）](#4-数据库设计database-design)
  - [💻 实践与样例](#-实践与样例)
    - [代码示例位置](#代码示例位置)
    - [文件级清单（精选）](#文件级清单精选)
      - [`crates/c77_database/src/`](#cratesc77_databasesrc)
      - [`crates/c78_data_storage/src/`](#cratesc78_data_storagesrc)
    - [快速开始示例](#快速开始示例)
  - [🔗 相关索引](#-相关索引)
  - [🧭 导航](#-导航)

## 🎯 目的

本模块提供 Rust 数据库开发的实用示例，涵盖关系型数据库、NoSQL 数据库、数据库操作和数据库设计等核心主题。所有示例均基于 Rust 1.91.0 和当前最佳实践。

### 核心价值

- **数据库开发**: 专注于数据库应用开发实践
- **最佳实践**: 基于 Rust 社区最新数据库实践
- **完整覆盖**: 涵盖多个数据库场景
- **易于理解**: 提供详细的数据库开发说明和代码示例

## 📚 核心示例

### 1. 关系型数据库（Relational Databases）

**推荐库**: `sqlx`, `diesel`, `sea-orm`, `rusqlite`

- **PostgreSQL 集成**: PostgreSQL 数据库操作
- **MySQL 集成**: MySQL 数据库操作
- **SQLite 集成**: SQLite 数据库操作
- **数据库连接池**: 连接池管理、连接复用

**相关资源**:

- [sqlx 文档](https://docs.rs/sqlx/)
- [diesel 文档](https://diesel.rs/)
- [sea-orm 文档](https://www.sea-ql.org/SeaORM/)
- [rusqlite 文档](https://docs.rs/rusqlite/)

### 2. NoSQL 数据库（NoSQL Databases）

**推荐库**: `mongodb`, `redis`, `cassandra-driver`, `rusoto_dynamodb`

- **MongoDB 集成**: MongoDB 数据库操作
- **Redis 集成**: Redis 缓存和消息队列
- **Cassandra 集成**: Cassandra 数据库操作
- **DynamoDB 集成**: DynamoDB 数据库操作

**相关资源**:

- [mongodb 文档](https://docs.rs/mongodb/)
- [redis 文档](https://docs.rs/redis/)
- [cassandra-driver 文档](https://docs.rs/cassandra-driver/)
- [rusoto_dynamodb 文档](https://docs.rs/rusoto_dynamodb/)

### 3. 数据库操作（Database Operations）

**推荐库**: `sqlx`, `diesel`, `sea-orm`, `tokio-postgres`

- **CRUD 操作**: 创建、读取、更新、删除操作
- **事务处理**: 事务管理、回滚处理
- **查询优化**: 查询优化、索引使用
- **数据迁移**: 数据库迁移、版本管理

**相关资源**:

- [sqlx 文档](https://docs.rs/sqlx/)
- [diesel 文档](https://diesel.rs/)
- [sea-orm 文档](https://www.sea-ql.org/SeaORM/)
- [tokio-postgres 文档](https://docs.rs/tokio-postgres/)

### 4. 数据库设计（Database Design）

**推荐库**: `diesel`, `sea-orm`, `sqlx`

- **数据模型设计**: 数据模型设计、关系映射
- **索引优化**: 索引设计、查询优化
- **查询性能优化**: 查询优化、性能分析
- **数据一致性**: 数据一致性、约束管理

**相关资源**:

- [diesel 文档](https://diesel.rs/)
- [sea-orm 文档](https://www.sea-ql.org/SeaORM/)
- [sqlx 文档](https://docs.rs/sqlx/)

## 💻 实践与样例

### 代码示例位置

- **数据库示例**: [crates/c77_database](../../../crates/c77_database/)
- **数据存储**: [crates/c78_data_storage](../../../crates/c78_data_storage/)
- **数据访问**: [crates/c79_data_access](../../../crates/c79_data_access/)

### 文件级清单（精选）

#### `crates/c77_database/src/`

- `relational_databases.rs` - 关系型数据库示例
- `nosql_databases.rs` - NoSQL 数据库示例
- `database_operations.rs` - 数据库操作示例
- `database_design.rs` - 数据库设计示例

#### `crates/c78_data_storage/src/`

- `data_persistence.rs` - 数据持久化示例
- `data_caching.rs` - 数据缓存示例
- `data_synchronization.rs` - 数据同步示例

### 快速开始示例

```rust
// SQLx 数据库操作示例
use sqlx::PgPool;

#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    let pool = PgPool::connect("postgres://user:pass@localhost/db").await?;

    let row = sqlx::query!("SELECT * FROM users WHERE id = $1", 1)
        .fetch_one(&pool)
        .await?;

    println!("用户: {}", row.name);
    Ok(())
}
```

```rust
// Diesel ORM 示例
use diesel::prelude::*;

#[derive(Queryable)]
struct User {
    id: i32,
    name: String,
}

fn get_user(conn: &mut PgConnection) -> QueryResult<User> {
    users::table
        .filter(users::id.eq(1))
        .first(conn)
}
```

---

## 🔗 相关索引

- **理论基础（并发模型）**: [`../../01_theoretical_foundations/04_concurrency_models/00_index.md`](../../01_theoretical_foundations/04_concurrency_models/00_index.md)
- **编程范式（异步）**: [`../../02_programming_paradigms/02_async/00_index.md`](../../02_programming_paradigms/02_async/00_index.md)
- **应用领域（大数据分析）**: [`../../04_application_domains/07_big_data_analytics/00_index.md`](../../04_application_domains/07_big_data_analytics/00_index.md)

---

## 🧭 导航

- **返回实用示例**: [`../00_index.md`](../00_index.md)
- **嵌入式示例**: [`../10_embedded_examples/00_index.md`](../10_embedded_examples/00_index.md)
- **消息队列示例**: [`../12_messaging_examples/00_index.md`](../12_messaging_examples/00_index.md)
- **返回项目根**: [`../../README.md`](../../README.md)

---

**最后更新**: 2025-11-10
**维护者**: 项目维护者
**状态**: 已完善 ✅
