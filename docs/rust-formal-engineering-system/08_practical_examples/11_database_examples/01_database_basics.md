# 数据库基础（Database Basics）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [数据库基础](#数据库基础database-basics)
  - [概述](#概述)
  - [使用 SQLx](#使用-sqlx)
  - [使用 Diesel](#使用-diesel)
  - [使用 SeaORM](#使用-seaorm)
  - [实践示例](#实践示例)
  - [最佳实践](#最佳实践)
  - [参考资料](#参考资料)

---

## 概述

Rust 提供了多个优秀的数据库访问库，包括 SQLx、Diesel 和 SeaORM。本示例展示如何使用这些库进行数据库操作。

## 使用 SQLx

### 基本连接

```rust
use sqlx::postgres::PgPoolOptions;

#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    let pool = PgPoolOptions::new()
        .max_connections(5)
        .connect("postgres://user:password@localhost/database")
        .await?;

    // 使用连接池
    let row: (i64,) = sqlx::query_as("SELECT $1")
        .bind(150_i64)
        .fetch_one(&pool)
        .await?;

    println!("结果: {}", row.0);
    Ok(())
}
```

### 查询操作

```rust
use sqlx::{PgPool, Row};

#[derive(Debug)]
struct User {
    id: i32,
    name: String,
    email: String,
}

async fn get_users(pool: &PgPool) -> Result<Vec<User>, sqlx::Error> {
    let users = sqlx::query_as!(
        User,
        "SELECT id, name, email FROM users"
    )
    .fetch_all(pool)
    .await?;

    Ok(users)
}

async fn get_user_by_id(pool: &PgPool, id: i32) -> Result<Option<User>, sqlx::Error> {
    let user = sqlx::query_as!(
        User,
        "SELECT id, name, email FROM users WHERE id = $1",
        id
    )
    .fetch_optional(pool)
    .await?;

    Ok(user)
}
```

### 插入和更新

```rust
async fn create_user(
    pool: &PgPool,
    name: &str,
    email: &str,
) -> Result<i32, sqlx::Error> {
    let id = sqlx::query!(
        "INSERT INTO users (name, email) VALUES ($1, $2) RETURNING id",
        name,
        email
    )
    .fetch_one(pool)
    .await?
    .id;

    Ok(id)
}

async fn update_user(
    pool: &PgPool,
    id: i32,
    name: &str,
) -> Result<(), sqlx::Error> {
    sqlx::query!(
        "UPDATE users SET name = $1 WHERE id = $2",
        name,
        id
    )
    .execute(pool)
    .await?;

    Ok(())
}
```

## 使用 Diesel

### 模型定义

```rust
use diesel::prelude::*;
use diesel::pg::PgConnection;

#[derive(Queryable, Selectable, Insertable)]
#[diesel(table_name = users)]
pub struct User {
    pub id: i32,
    pub name: String,
    pub email: String,
}

diesel::table! {
    users {
        id -> Integer,
        name -> Text,
        email -> Text,
    }
}

// 查询
pub fn get_users(conn: &mut PgConnection) -> QueryResult<Vec<User>> {
    use diesel::prelude::*;
    users::table.load::<User>(conn)
}

// 插入
pub fn create_user(
    conn: &mut PgConnection,
    name: &str,
    email: &str,
) -> QueryResult<User> {
    use diesel::prelude::*;

    let new_user = NewUser {
        name: name.to_string(),
        email: email.to_string(),
    };

    diesel::insert_into(users::table)
        .values(&new_user)
        .get_result(conn)
}

#[derive(Insertable)]
#[diesel(table_name = users)]
struct NewUser {
    name: String,
    email: String,
}
```

## 使用 SeaORM

### 实体定义

```rust
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i32,
    pub name: String,
    pub email: String,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {}

impl ActiveModelBehavior for ActiveModel {}
```

### 查询操作

```rust
use sea_orm::{Database, EntityTrait, DbErr};

#[tokio::main]
async fn main() -> Result<(), DbErr> {
    let db = Database::connect("postgres://user:password@localhost/database").await?;

    // 查询所有用户
    let users = Entity::find().all(&db).await?;

    // 查询单个用户
    let user = Entity::find_by_id(1).one(&db).await?;

    Ok(())
}
```

## 实践示例

### 示例 1：用户管理系统

```rust
use sqlx::PgPool;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct CreateUserRequest {
    pub name: String,
    pub email: String,
}

pub struct UserService {
    pool: PgPool,
}

impl UserService {
    pub fn new(pool: PgPool) -> Self {
        UserService { pool }
    }

    pub async fn create_user(
        &self,
        request: CreateUserRequest,
    ) -> Result<i32, sqlx::Error> {
        let id = sqlx::query!(
            "INSERT INTO users (name, email) VALUES ($1, $2) RETURNING id",
            request.name,
            request.email
        )
        .fetch_one(&self.pool)
        .await?
        .id;

        Ok(id)
    }

    pub async fn get_user(&self, id: i32) -> Result<Option<User>, sqlx::Error> {
        let user = sqlx::query_as!(
            User,
            "SELECT id, name, email FROM users WHERE id = $1",
            id
        )
        .fetch_optional(&self.pool)
        .await?;

        Ok(user)
    }

    pub async fn list_users(&self) -> Result<Vec<User>, sqlx::Error> {
        let users = sqlx::query_as!(
            User,
            "SELECT id, name, email FROM users ORDER BY id"
        )
        .fetch_all(&self.pool)
        .await?;

        Ok(users)
    }

    pub async fn update_user(
        &self,
        id: i32,
        name: Option<String>,
        email: Option<String>,
    ) -> Result<(), sqlx::Error> {
        if let Some(name) = name {
            sqlx::query!(
                "UPDATE users SET name = $1 WHERE id = $2",
                name,
                id
            )
            .execute(&self.pool)
            .await?;
        }

        if let Some(email) = email {
            sqlx::query!(
                "UPDATE users SET email = $1 WHERE id = $2",
                email,
                id
            )
            .execute(&self.pool)
            .await?;
        }

        Ok(())
    }

    pub async fn delete_user(&self, id: i32) -> Result<(), sqlx::Error> {
        sqlx::query!("DELETE FROM users WHERE id = $1", id)
            .execute(&self.pool)
            .await?;

        Ok(())
    }
}
```

### 示例 2：事务处理

```rust
use sqlx::PgPool;

pub async fn transfer_funds(
    pool: &PgPool,
    from_account: i32,
    to_account: i32,
    amount: i64,
) -> Result<(), sqlx::Error> {
    let mut tx = pool.begin().await?;

    // 扣除源账户
    sqlx::query!(
        "UPDATE accounts SET balance = balance - $1 WHERE id = $2",
        amount,
        from_account
    )
    .execute(&mut *tx)
    .await?;

    // 增加目标账户
    sqlx::query!(
        "UPDATE accounts SET balance = balance + $1 WHERE id = $2",
        amount,
        to_account
    )
    .execute(&mut *tx)
    .await?;

    tx.commit().await?;
    Ok(())
}
```

## 最佳实践

### 1. 使用连接池

```rust
use sqlx::postgres::PgPoolOptions;

let pool = PgPoolOptions::new()
    .max_connections(10)
    .min_connections(2)
    .connect(&database_url)
    .await?;
```

### 2. 参数化查询

```rust
// ✅ 正确：使用参数化查询
sqlx::query!("SELECT * FROM users WHERE id = $1", user_id)
    .fetch_one(&pool)
    .await?;

// ❌ 错误：字符串拼接（SQL 注入风险）
sqlx::query(&format!("SELECT * FROM users WHERE id = {}", user_id))
    .fetch_one(&pool)
    .await?;
```

### 3. 错误处理

```rust
use sqlx::Error;

async fn handle_database_error() -> Result<(), String> {
    match perform_query().await {
        Ok(result) => Ok(result),
        Err(Error::Database(e)) => {
            eprintln!("数据库错误: {}", e);
            Err("数据库操作失败".to_string())
        }
        Err(e) => {
            eprintln!("其他错误: {}", e);
            Err("操作失败".to_string())
        }
    }
}
```

## 参考资料

- [数据库示例索引](./00_index.md)
- [实践示例索引](../00_index.md)
- [SQLx 文档](https://docs.rs/sqlx/)
- [Diesel 文档](https://diesel.rs/)
- [SeaORM 文档](https://www.sea-ql.org/SeaORM/)

---

**导航**:
- 返回索引: [`00_index.md`](./00_index.md)
- 返回实践示例: [`../00_index.md`](../00_index.md)
