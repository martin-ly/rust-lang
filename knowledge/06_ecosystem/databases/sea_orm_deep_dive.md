# Sea-ORM 深度解析

> **版本**: Sea-ORM 1.x
> **Rust 版本**: 1.94.0+
> **难度**: 中级
> **预计阅读时间**: 40分钟

---

## 📋 目录

- [Sea-ORM 深度解析](#sea-orm-深度解析)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
    - [核心特性](#核心特性)
    - [适用场景](#适用场景)
  - [🏗️ 架构设计](#️-架构设计)
    - [核心概念](#核心概念)
    - [与 Diesel/SQLx 对比](#与-dieselsqlx-对比)
  - [🚀 快速开始](#-快速开始)
    - [安装配置](#安装配置)
    - [CLI 工具](#cli-工具)
  - [📐 实体定义](#-实体定义)
    - [基本实体](#基本实体)
    - [关系定义](#关系定义)
    - [复合主键](#复合主键)
  - [💾 CRUD 操作](#-crud-操作)
    - [Create](#create)
    - [Read](#read)
    - [Update](#update)
    - [Delete](#delete)
  - [🔗 关联查询](#-关联查询)
    - [Eager Loading](#eager-loading)
    - [Lazy Loading](#lazy-loading)
  - [⚡ 性能优化](#-性能优化)
    - [连接池](#连接池)
    - [查询优化](#查询优化)
  - [🧪 测试策略](#-测试策略)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 概述

Sea-ORM 是一个异步、动态的 Rust ORM，专为现代 Rust 生态系统设计。

### 核心特性

| 特性 | 说明 |
|------|------|
| **异步原生** | 基于 `async/await`，无需阻塞线程 |
| **类型安全** | 编译时实体校验，运行时动态查询 |
| **多数据库** | 支持 PostgreSQL、MySQL、SQLite |
| **代码生成** | CLI 工具自动生成实体代码 |
| **关系支持** | 完整的一对多、多对多关系 |

### 适用场景

```
Sea-ORM 适用场景:
├── ✅ 异步 Web 应用 (Axum/Actix/Rocket)
├── ✅ 微服务架构
├── ✅ 需要动态查询的场景
├── ✅ 快速原型开发
└── ❌ 极致性能要求的场景 (考虑 SQLx/Diesel)
```

---

## 🏗️ 架构设计

### 核心概念

```rust
// 实体 (Entity) - 对应数据库表
#[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
#[sea_orm(table_name = "posts")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i32,
    pub title: String,
    pub content: Option<String>,
}

// 关系 (Relation) - 定义表间关联
#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {
    #[sea_orm(has_many = "super::comment::Entity")]
    Comments,
}
```

### 与 Diesel/SQLx 对比

| 特性 | Sea-ORM | Diesel | SQLx |
|------|---------|--------|------|
| **同步/异步** | 异步 | 同步 | 异步 |
| **查询类型** | 动态 | 编译时 | 编译时 |
| **类型安全** | 中等 | 高 | 高 |
| **学习曲线** | 平缓 | 陡峭 | 中等 |
| **性能** | 中等 | 高 | 高 |
| **灵活性** | 高 | 中 | 中 |

---

## 🚀 快速开始

### 安装配置

```toml
[dependencies]
sea-orm = { version = "1.0", features = [
    "sqlx-postgres",
    "runtime-tokio-rustls",
    "macros"
] }
tokio = { version = "1", features = ["full"] }
```

### CLI 工具

```bash
# 安装 Sea-ORM CLI
cargo install sea-orm-cli

# 生成实体代码
sea-orm-cli generate entity \
    -u postgres://user:pass@localhost/db \
    -o src/entities
```

---

## 📐 实体定义

### 基本实体

```rust
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i32,

    #[sea_orm(column_type = "Text")]
    pub username: String,

    #[sea_orm(column_type = "Text", nullable)]
    pub email: Option<String>,

    #[sea_orm(default_value = "CURRENT_TIMESTAMP")]
    pub created_at: DateTimeWithTimeZone,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

### 关系定义

```rust
// user.rs - 用户实体
#[derive(DeriveEntityModel)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i32,
    pub username: String,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {
    #[sea_orm(has_many = "super::post::Entity")]
    Posts,
}

impl Related<super::post::Entity> for Entity {
    fn to() -> RelationDef {
        Relation::Posts.def()
    }
}

// post.rs - 文章实体
#[derive(DeriveEntityModel)]
#[sea_orm(table_name = "posts")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i32,
    pub title: String,
    pub user_id: i32,  // 外键
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {
    #[sea_orm(
        belongs_to = "super::user::Entity",
        from = "Column::UserId",
        to = "super::user::Column::Id"
    )]
    User,
}

impl Related<super::user::Entity> for Entity {
    fn to() -> RelationDef {
        Relation::User.def()
    }
}
```

### 复合主键

```rust
#[derive(DeriveEntityModel)]
#[sea_orm(table_name = "order_items")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub order_id: i32,
    #[sea_orm(primary_key)]
    pub product_id: i32,
    pub quantity: i32,
}
```

---

## 💾 CRUD 操作

### Create

```rust
use sea_orm::{ActiveModelTrait, Set};

// 插入单条记录
let user = user::ActiveModel {
    username: Set("alice".to_owned()),
    email: Set(Some("alice@example.com".to_owned())),
    ..Default::default()
};

let result = user.insert(&db).await?;
println!("Inserted user id: {}", result.id);

// 批量插入
let users = vec![
    user::ActiveModel {
        username: Set("bob".to_owned()),
        ..Default::default()
    },
    user::ActiveModel {
        username: Set("charlie".to_owned()),
        ..Default::default()
    },
];

user::Entity::insert_many(users)
    .exec(&db)
    .await?;
```

### Read

```rust
use sea_orm::{EntityTrait, QueryFilter, ColumnTrait};

// 查询所有
let users: Vec<user::Model> = user::Entity::find()
    .all(&db)
    .await?;

// 根据主键查询
let user: Option<user::Model> = user::Entity::find_by_id(1)
    .one(&db)
    .await?;

// 条件查询
let users: Vec<user::Model> = user::Entity::find()
    .filter(user::Column::Username.contains("alice"))
    .filter(user::Column::Email.is_not_null())
    .all(&db)
    .await?;

// 分页查询
let paginator = user::Entity::find()
    .paginate(&db, 10);  // 每页10条

let users = paginator.fetch_page(0).await?;  // 第1页
let num_pages = paginator.num_pages().await?;
```

### Update

```rust
use sea_orm::{ActiveModelTrait, Set, ModelTrait};

// 方式1: 通过 ActiveModel
let mut user: user::ActiveModel = user::Entity::find_by_id(1)
    .one(&db)
    .await?
    .ok_or("User not found")?
    .into();

user.username = Set("alice_updated".to_owned());
user.update(&db).await?;

// 方式2: 批量更新
user::Entity::update_many()
    .col_expr(user::Column::Email, Expr::value(None::<String>))
    .filter(user::Column::Username.contains("test"))
    .exec(&db)
    .await?;
```

### Delete

```rust
use sea_orm::{ModelTrait, EntityTrait};

// 删除单条
let user: user::Model = user::Entity::find_by_id(1)
    .one(&db)
    .await?
    .ok_or("User not found")?;

user.delete(&db).await?;

// 批量删除
user::Entity::delete_many()
    .filter(user::Column::Username.contains("temp"))
    .exec(&db)
    .await?;
```

---

## 🔗 关联查询

### Eager Loading

```rust
use sea_orm::{EntityTrait, Related};

// 加载用户及其所有文章
let users_with_posts: Vec<(user::Model, Vec<post::Model>)> = user::Entity::find()
    .find_with_related(post::Entity)
    .all(&db)
    .await?;

for (user, posts) in users_with_posts {
    println!("User: {}", user.username);
    for post in posts {
        println!("  - {}", post.title);
    }
}

// 嵌套 Eager Loading
let result: Vec<(user::Model, Vec<(post::Model, Vec<comment::Model>)>)> =
    user::Entity::find()
        .find_with_related(post::Entity)
        .all(&db)
        .await?;
```

### Lazy Loading

```rust
// 先查询用户
let user: user::Model = user::Entity::find_by_id(1)
    .one(&db)
    .await?
    .ok_or("User not found")?;

// 按需加载文章
let posts: Vec<post::Model> = user.find_related(post::Entity)
    .all(&db)
    .await?;
```

---

## ⚡ 性能优化

### 连接池

```rust
use sea_orm::{Database, DatabaseOptions, ConnectOptions};
use std::time::Duration;

let mut opt = ConnectOptions::new("postgres://user:pass@localhost/db".to_owned());
opt.max_connections(100)
    .min_connections(5)
    .connect_timeout(Duration::from_secs(8))
    .acquire_timeout(Duration::from_secs(8))
    .idle_timeout(Duration::from_secs(8))
    .max_lifetime(Duration::from_secs(8));

let db = Database::connect(opt).await?;
```

### 查询优化

```rust
use sea_orm::{QuerySelect, QueryOrder};

// 只选择需要的列
let users: Vec<user::Model> = user::Entity::find()
    .select_only()
    .column(user::Column::Id)
    .column(user::Column::Username)
    .all(&db)
    .await?;

// 使用索引的排序
let users: Vec<user::Model> = user::Entity::find()
    .order_by_asc(user::Column::CreatedAt)
    .limit(10)
    .all(&db)
    .await?;

// 原始 SQL 查询（复杂查询）
let results = db.query_all(
    Statement::from_sql_and_values(
        DbBackend::Postgres,
        r#"SELECT * FROM users WHERE id = $1"#,
        [1.into()]
    )
).await?;
```

---

## 🧪 测试策略

```rust
#[cfg(test)]
mod tests {
    use sea_orm::{Database, DatabaseBackend, MockDatabase, Transaction};
    use super::*;

    #[tokio::test]
    async fn test_find_user() {
        let db = MockDatabase::new(DatabaseBackend::Postgres)
            .append_query_results([
                vec![user::Model {
                    id: 1,
                    username: "alice".to_owned(),
                    email: Some("alice@example.com".to_owned()),
                    created_at: chrono::Utc::now().into(),
                }],
            ])
            .into_connection();

        let user = user::Entity::find_by_id(1)
            .one(&db)
            .await
            .unwrap();

        assert_eq!(user.unwrap().username, "alice");
    }
}
```

---

## 🔗 参考资源

- [Sea-ORM 官方文档](https://www.sea-ql.org/SeaORM/)
- [Sea-ORM GitHub](https://github.com/SeaQL/sea-orm)
- [Sea-ORM 示例](https://github.com/SeaQL/sea-orm/tree/master/examples)
- [SeaORM Recipes](https://www.sea-ql.org/sea-orm-cookbook/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-19
**状态**: ✅ 已完成
