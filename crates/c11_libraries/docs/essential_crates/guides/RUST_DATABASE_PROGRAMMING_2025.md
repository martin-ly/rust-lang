# Rust 数据库开发深入指南 2025

> **最后更新**: 2025-10-20  
> **Rust 版本**: 1.83+  
> **难度**: ⭐⭐⭐⭐ (中高级)

## 📊 目录

- [Rust 数据库开发深入指南 2025](#rust-数据库开发深入指南-2025)
  - [📊 目录](#-目录)
  - [📋 目录1](#-目录1)
  - [1. 数据库生态概览](#1-数据库生态概览)
  - [2. SQLx 深入](#2-sqlx-深入)
    - [2.1 基础设置](#21-基础设置)
    - [2.2 编译时查询验证](#22-编译时查询验证)
    - [2.3 批量操作](#23-批量操作)
  - [3. Diesel ORM](#3-diesel-orm)
    - [3.1 设置和迁移](#31-设置和迁移)
    - [3.2 模型定义](#32-模型定义)
    - [3.3 CRUD 操作](#33-crud-操作)
    - [3.4 关联查询](#34-关联查询)
  - [4. SeaORM 现代化 ORM](#4-seaorm-现代化-orm)
    - [4.1 实体定义](#41-实体定义)
    - [4.2 CRUD 操作](#42-crud-操作)
    - [4.3 关联查询](#43-关联查询)
  - [5. 连接池管理](#5-连接池管理)
    - [5.1 连接池配置](#51-连接池配置)
    - [5.2 连接池监控](#52-连接池监控)
  - [6. 事务处理](#6-事务处理)
    - [6.1 SQLx 事务](#61-sqlx-事务)
    - [6.2 Diesel 事务](#62-diesel-事务)
    - [6.3 SeaORM 事务](#63-seaorm-事务)
  - [7. 迁移管理](#7-迁移管理)
    - [7.1 SQLx 迁移](#71-sqlx-迁移)
    - [7.2 Diesel 迁移](#72-diesel-迁移)
  - [8. 查询优化](#8-查询优化)
    - [8.1 索引优化](#81-索引优化)
    - [8.2 N+1 查询问题](#82-n1-查询问题)
    - [8.3 批量操作优化](#83-批量操作优化)
  - [9. NoSQL 数据库](#9-nosql-数据库)
    - [9.1 MongoDB](#91-mongodb)
    - [9.2 Redis](#92-redis)
  - [10. 实战案例](#10-实战案例)
    - [10.1 用户认证系统](#101-用户认证系统)
    - [10.2 博客系统](#102-博客系统)
  - [11. 最佳实践](#11-最佳实践)
  - [12. 常见陷阱](#12-常见陷阱)
  - [13. 参考资源](#13-参考资源)

## 📋 目录1

- [Rust 数据库开发深入指南 2025](#rust-数据库开发深入指南-2025)
  - [📊 目录](#-目录)
  - [📋 目录1](#-目录1)
  - [1. 数据库生态概览](#1-数据库生态概览)
  - [2. SQLx 深入](#2-sqlx-深入)
    - [2.1 基础设置](#21-基础设置)
    - [2.2 编译时查询验证](#22-编译时查询验证)
    - [2.3 批量操作](#23-批量操作)
  - [3. Diesel ORM](#3-diesel-orm)
    - [3.1 设置和迁移](#31-设置和迁移)
    - [3.2 模型定义](#32-模型定义)
    - [3.3 CRUD 操作](#33-crud-操作)
    - [3.4 关联查询](#34-关联查询)
  - [4. SeaORM 现代化 ORM](#4-seaorm-现代化-orm)
    - [4.1 实体定义](#41-实体定义)
    - [4.2 CRUD 操作](#42-crud-操作)
    - [4.3 关联查询](#43-关联查询)
  - [5. 连接池管理](#5-连接池管理)
    - [5.1 连接池配置](#51-连接池配置)
    - [5.2 连接池监控](#52-连接池监控)
  - [6. 事务处理](#6-事务处理)
    - [6.1 SQLx 事务](#61-sqlx-事务)
    - [6.2 Diesel 事务](#62-diesel-事务)
    - [6.3 SeaORM 事务](#63-seaorm-事务)
  - [7. 迁移管理](#7-迁移管理)
    - [7.1 SQLx 迁移](#71-sqlx-迁移)
    - [7.2 Diesel 迁移](#72-diesel-迁移)
  - [8. 查询优化](#8-查询优化)
    - [8.1 索引优化](#81-索引优化)
    - [8.2 N+1 查询问题](#82-n1-查询问题)
    - [8.3 批量操作优化](#83-批量操作优化)
  - [9. NoSQL 数据库](#9-nosql-数据库)
    - [9.1 MongoDB](#91-mongodb)
    - [9.2 Redis](#92-redis)
  - [10. 实战案例](#10-实战案例)
    - [10.1 用户认证系统](#101-用户认证系统)
    - [10.2 博客系统](#102-博客系统)
  - [11. 最佳实践](#11-最佳实践)
  - [12. 常见陷阱](#12-常见陷阱)
  - [13. 参考资源](#13-参考资源)

---

## 1. 数据库生态概览

**Rust 数据库库对比:**

| 库          | 类型   | 异步  | 编译时验证 | 学习曲线 | 性能  | 推荐场景                |
|-------------|--------|-------|------------|----------|-------|-------------------------|
| **SQLx**    | 查询构建器 | ✅  | ✅         | ⭐⭐   | ⭐⭐⭐⭐⭐ | 灵活的 SQL 查询         |
| **Diesel**  | ORM    | ❌    | ✅         | ⭐⭐⭐ | ⭐⭐⭐⭐   | 类型安全的 ORM          |
| **SeaORM**  | ORM    | ✅    | ✅         | ⭐⭐⭐ | ⭐⭐⭐⭐   | 现代化异步 ORM          |
| **rbatis**  | ORM    | ✅    | ❌         | ⭐⭐   | ⭐⭐⭐⭐   | 类似 MyBatis 的动态 SQL |
| **mongodb** | Driver | ✅    | ❌         | ⭐⭐   | ⭐⭐⭐⭐   | MongoDB 官方驱动        |
| **redis**   | Driver | ✅    | ❌         | ⭐     | ⭐⭐⭐⭐⭐ | Redis 缓存              |

**支持的数据库:**

- **关系型**: PostgreSQL, MySQL, MariaDB, SQLite
- **NoSQL**: MongoDB, Redis, Cassandra
- **时序**: InfluxDB, TimescaleDB
- **图**: Neo4j

---

## 2. SQLx 深入

### 2.1 基础设置

**Cargo.toml:**

```toml
[dependencies]
sqlx = { version = "0.7", features = ["runtime-tokio", "postgres", "migrate", "uuid", "chrono"] }
tokio = { version = "1.0", features = ["full"] }
uuid = { version = "1.0", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }
```

**连接数据库:**

```rust
use sqlx::postgres::PgPoolOptions;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 创建连接池
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let pool = PgPoolOptions::new()
        .max_connections(5)
        .acquire_timeout(Duration::from_secs(3))
        .connect("postgresql://user:pass@localhost/db")
        .await?;
    
    println!("数据库连接成功！");
    
    Ok(())
}
```

### 2.2 编译时查询验证

**宏查询 (编译时验证):**

```rust
use sqlx::{FromRow, query_as};
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(Debug, FromRow)]
struct User {
    id: Uuid,
    email: String,
    name: String,
    created_at: DateTime<Utc>,
}

#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    let pool = /* ... */;
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // query!: 编译时验证 SQL (需要 DATABASE_URL 环境变量)
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let user = sqlx::query_as!(
        User,
        "SELECT id, email, name, created_at FROM users WHERE email = $1",
        "user@example.com"
    )
    .fetch_one(&pool)
    .await?;
    
    println!("用户: {:?}", user);
    
    Ok(())
}
```

**动态查询:**

```rust
use sqlx::{query_as, Row};

async fn find_users(
    pool: &sqlx::PgPool,
    filters: Vec<(&str, &str)>,
) -> Result<Vec<User>, sqlx::Error> {
    let mut query = String::from("SELECT id, email, name, created_at FROM users WHERE 1=1");
    
    for (key, _) in &filters {
        query.push_str(&format!(" AND {} = $", key));
    }
    
    let mut query_builder = query_as::<_, User>(&query);
    
    for (_, value) in filters {
        query_builder = query_builder.bind(value);
    }
    
    query_builder.fetch_all(pool).await
}
```

### 2.3 批量操作

```rust
use sqlx::{Postgres, QueryBuilder};

async fn insert_many_users(
    pool: &sqlx::PgPool,
    users: &[(String, String)],
) -> Result<(), sqlx::Error> {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // QueryBuilder: 构建批量插入
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let mut query_builder: QueryBuilder<Postgres> = QueryBuilder::new(
        "INSERT INTO users(email, name) "
    );
    
    query_builder.push_values(users, |mut b, user| {
        b.push_bind(&user.0).push_bind(&user.1);
    });
    
    query_builder.build().execute(pool).await?;
    
    Ok(())
}
```

---

## 3. Diesel ORM

### 3.1 设置和迁移

**Cargo.toml:**

```toml
[dependencies]
diesel = { version = "2.1", features = ["postgres", "uuid", "chrono"] }
diesel_migrations = "2.1"
```

**schema.rs (自动生成):**

```rust
// @generated automatically by Diesel CLI.

diesel::table! {
    users (id) {
        id -> Uuid,
        email -> Text,
        name -> Text,
        created_at -> Timestamptz,
    }
}

diesel::table! {
    posts (id) {
        id -> Uuid,
        user_id -> Uuid,
        title -> Text,
        content -> Text,
        published -> Bool,
        created_at -> Timestamptz,
    }
}

diesel::joinable!(posts -> users (user_id));
diesel::allow_tables_to_appear_in_same_query!(users, posts);
```

### 3.2 模型定义

```rust
use diesel::prelude::*;
use uuid::Uuid;
use chrono::{DateTime, Utc};

#[derive(Queryable, Identifiable, Debug)]
#[diesel(table_name = users)]
pub struct User {
    pub id: Uuid,
    pub email: String,
    pub name: String,
    pub created_at: DateTime<Utc>,
}

#[derive(Insertable)]
#[diesel(table_name = users)]
pub struct NewUser<'a> {
    pub email: &'a str,
    pub name: &'a str,
}

#[derive(Queryable, Identifiable, Associations, Debug)]
#[diesel(belongs_to(User))]
#[diesel(table_name = posts)]
pub struct Post {
    pub id: Uuid,
    pub user_id: Uuid,
    pub title: String,
    pub content: String,
    pub published: bool,
    pub created_at: DateTime<Utc>,
}
```

### 3.3 CRUD 操作

```rust
use diesel::prelude::*;
use diesel::pg::PgConnection;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Create
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn create_user(conn: &mut PgConnection, email: &str, name: &str) -> QueryResult<User> {
    use crate::schema::users;
    
    let new_user = NewUser { email, name };
    
    diesel::insert_into(users::table)
        .values(&new_user)
        .get_result(conn)
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Read
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn get_user_by_email(conn: &mut PgConnection, email: &str) -> QueryResult<User> {
    use crate::schema::users::dsl::*;
    
    users
        .filter(email.eq(email))
        .first::<User>(conn)
}

fn list_users(conn: &mut PgConnection, limit: i64) -> QueryResult<Vec<User>> {
    use crate::schema::users::dsl::*;
    
    users
        .order(created_at.desc())
        .limit(limit)
        .load::<User>(conn)
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Update
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn update_user_name(conn: &mut PgConnection, user_id: Uuid, new_name: &str) -> QueryResult<User> {
    use crate::schema::users::dsl::*;
    
    diesel::update(users.find(user_id))
        .set(name.eq(new_name))
        .get_result(conn)
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Delete
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn delete_user(conn: &mut PgConnection, user_id: Uuid) -> QueryResult<usize> {
    use crate::schema::users::dsl::*;
    
    diesel::delete(users.find(user_id))
        .execute(conn)
}
```

### 3.4 关联查询

```rust
use diesel::prelude::*;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 获取用户及其所有文章
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn get_user_with_posts(conn: &mut PgConnection, user_id: Uuid) -> QueryResult<(User, Vec<Post>)> {
    use crate::schema::{users, posts};
    
    let user = users::table
        .find(user_id)
        .first::<User>(conn)?;
    
    let user_posts = Post::belonging_to(&user)
        .load::<Post>(conn)?;
    
    Ok((user, user_posts))
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// JOIN 查询
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn get_published_posts_with_authors(conn: &mut PgConnection) -> QueryResult<Vec<(Post, User)>> {
    use crate::schema::{posts, users};
    
    posts::table
        .inner_join(users::table)
        .filter(posts::published.eq(true))
        .select((Post::as_select(), User::as_select()))
        .load::<(Post, User)>(conn)
}
```

---

## 4. SeaORM 现代化 ORM

### 4.1 实体定义

```rust
use sea_orm::entity::prelude::*;

#[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key, auto_increment = false)]
    pub id: Uuid,
    #[sea_orm(unique)]
    pub email: String,
    pub name: String,
    pub created_at: DateTimeUtc,
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

impl ActiveModelBehavior for ActiveModel {}
```

### 4.2 CRUD 操作

```rust
use sea_orm::*;
use uuid::Uuid;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Create
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn create_user(db: &DatabaseConnection, email: &str, name: &str) -> Result<Model, DbErr> {
    let user = ActiveModel {
        id: Set(Uuid::new_v4()),
        email: Set(email.to_owned()),
        name: Set(name.to_owned()),
        created_at: Set(chrono::Utc::now()),
    };
    
    user.insert(db).await
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Read
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn find_user_by_email(db: &DatabaseConnection, email: &str) -> Result<Option<Model>, DbErr> {
    Entity::find()
        .filter(Column::Email.eq(email))
        .one(db)
        .await
}

async fn list_users(db: &DatabaseConnection, page: u64, per_page: u64) -> Result<Vec<Model>, DbErr> {
    Entity::find()
        .order_by_desc(Column::CreatedAt)
        .paginate(db, per_page)
        .fetch_page(page)
        .await
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Update
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn update_user_name(db: &DatabaseConnection, id: Uuid, new_name: &str) -> Result<Model, DbErr> {
    let user: ActiveModel = Entity::find_by_id(id)
        .one(db)
        .await?
        .ok_or(DbErr::RecordNotFound(format!("User {} not found", id)))?
        .into();
    
    let mut user: ActiveModel = user;
    user.name = Set(new_name.to_owned());
    
    user.update(db).await
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Delete
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn delete_user(db: &DatabaseConnection, id: Uuid) -> Result<DeleteResult, DbErr> {
    Entity::delete_by_id(id).exec(db).await
}
```

### 4.3 关联查询

```rust
use sea_orm::*;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 预加载关联数据
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn find_users_with_posts(db: &DatabaseConnection) -> Result<Vec<(Model, Vec<post::Model>)>, DbErr> {
    Entity::find()
        .find_with_related(post::Entity)
        .all(db)
        .await
}

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// JOIN 查询
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
async fn find_posts_with_author(db: &DatabaseConnection) -> Result<Vec<(post::Model, Model)>, DbErr> {
    post::Entity::find()
        .find_also_related(Entity)
        .all(db)
        .await
        .map(|rows| {
            rows.into_iter()
                .filter_map(|(post, user)| user.map(|u| (post, u)))
                .collect()
        })
}
```

---

## 5. 连接池管理

### 5.1 连接池配置

```rust
use sqlx::postgres::PgPoolOptions;
use std::time::Duration;

async fn create_pool() -> Result<sqlx::PgPool, sqlx::Error> {
    PgPoolOptions::new()
        .max_connections(20)              // 最大连接数
        .min_connections(5)               // 最小连接数
        .acquire_timeout(Duration::from_secs(3)) // 获取连接超时
        .idle_timeout(Duration::from_secs(600))  // 空闲连接超时
        .max_lifetime(Duration::from_secs(1800)) // 连接最大生命周期
        .test_before_acquire(true)        // 获取前测试连接
        .connect("postgresql://user:pass@localhost/db")
        .await
}
```

### 5.2 连接池监控

```rust
use sqlx::PgPool;

async fn print_pool_stats(pool: &PgPool) {
    println!("连接池统计:");
    println!("  - 活跃连接: {}", pool.size());
    println!("  - 空闲连接: {}", pool.num_idle());
}
```

---

## 6. 事务处理

### 6.1 SQLx 事务

```rust
use sqlx::{PgPool, Postgres, Transaction};

async fn transfer_money(
    pool: &PgPool,
    from_user_id: i32,
    to_user_id: i32,
    amount: i32,
) -> Result<(), sqlx::Error> {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 开始事务
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let mut tx: Transaction<Postgres> = pool.begin().await?;
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 扣款
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    sqlx::query!("UPDATE accounts SET balance = balance - $1 WHERE user_id = $2", amount, from_user_id)
        .execute(&mut *tx)
        .await?;
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 加款
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    sqlx::query!("UPDATE accounts SET balance = balance + $1 WHERE user_id = $2", amount, to_user_id)
        .execute(&mut *tx)
        .await?;
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 提交事务
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    tx.commit().await?;
    
    Ok(())
}
```

### 6.2 Diesel 事务

```rust
use diesel::prelude::*;
use diesel::result::Error;

fn transfer_money_diesel(
    conn: &mut PgConnection,
    from_user_id: i32,
    to_user_id: i32,
    amount: i32,
) -> Result<(), Error> {
    conn.transaction(|conn| {
        // 扣款
        diesel::sql_query("UPDATE accounts SET balance = balance - $1 WHERE user_id = $2")
            .bind::<diesel::sql_types::Integer, _>(amount)
            .bind::<diesel::sql_types::Integer, _>(from_user_id)
            .execute(conn)?;
        
        // 加款
        diesel::sql_query("UPDATE accounts SET balance = balance + $1 WHERE user_id = $2")
            .bind::<diesel::sql_types::Integer, _>(amount)
            .bind::<diesel::sql_types::Integer, _>(to_user_id)
            .execute(conn)?;
        
        Ok(())
    })
}
```

### 6.3 SeaORM 事务

```rust
use sea_orm::*;

async fn transfer_money_seaorm(
    db: &DatabaseConnection,
    from_user_id: i32,
    to_user_id: i32,
    amount: i32,
) -> Result<(), DbErr> {
    let txn = db.begin().await?;
    
    // 扣款
    account::Entity::update_many()
        .filter(account::Column::UserId.eq(from_user_id))
        .col_expr(account::Column::Balance, Expr::col(account::Column::Balance).sub(amount))
        .exec(&txn)
        .await?;
    
    // 加款
    account::Entity::update_many()
        .filter(account::Column::UserId.eq(to_user_id))
        .col_expr(account::Column::Balance, Expr::col(account::Column::Balance).add(amount))
        .exec(&txn)
        .await?;
    
    txn.commit().await?;
    
    Ok(())
}
```

---

## 7. 迁移管理

### 7.1 SQLx 迁移

**创建迁移文件:**

```bash
# 创建迁移目录
mkdir migrations

# 创建迁移文件
sqlx migrate add create_users_table
```

**migrations/20250120000001_create_users_table.sql:**

```sql
-- Add migration script here
CREATE TABLE users (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    email TEXT UNIQUE NOT NULL,
    name TEXT NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);

CREATE INDEX idx_users_email ON users(email);
```

**运行迁移:**

```rust
use sqlx::migrate::Migrator;
use std::path::Path;

#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    let pool = /* ... */;
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 运行迁移
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let migrator = Migrator::new(Path::new("./migrations")).await?;
    migrator.run(&pool).await?;
    
    println!("迁移完成！");
    
    Ok(())
}
```

### 7.2 Diesel 迁移

**创建迁移:**

```bash
# 初始化 Diesel
diesel setup

# 创建迁移
diesel migration generate create_users

# 运行迁移
diesel migration run

# 回滚迁移
diesel migration revert
```

**up.sql:**

```sql
CREATE TABLE users (
    id UUID PRIMARY KEY DEFAULT gen_random_uuid(),
    email TEXT UNIQUE NOT NULL,
    name TEXT NOT NULL,
    created_at TIMESTAMPTZ NOT NULL DEFAULT NOW()
);
```

**down.sql:**

```sql
DROP TABLE users;
```

---

## 8. 查询优化

### 8.1 索引优化

```sql
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 单列索引
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
CREATE INDEX idx_users_email ON users(email);

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 复合索引 (顺序很重要!)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
CREATE INDEX idx_posts_user_created ON posts(user_id, created_at DESC);

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- 部分索引 (条件索引)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
CREATE INDEX idx_posts_published ON posts(created_at) WHERE published = true;

-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-- GIN 索引 (全文搜索)
-- ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
CREATE INDEX idx_posts_content_fts ON posts USING GIN (to_tsvector('english', content));
```

### 8.2 N+1 查询问题

**❌ 错误: N+1 查询**:

```rust
// 1 次查询获取所有用户
let users = user::Entity::find().all(db).await?;

// N 次查询获取每个用户的文章 (N+1 问题)
for user in users {
    let posts = post::Entity::find()
        .filter(post::Column::UserId.eq(user.id))
        .all(db)
        .await?;
}
```

**✅ 正确: 预加载**:

```rust
// 2 次查询: 1次获取用户, 1次获取所有文章
let users_with_posts = user::Entity::find()
    .find_with_related(post::Entity)
    .all(db)
    .await?;
```

### 8.3 批量操作优化

```rust
// ❌ 错误: 逐条插入
for user in users {
    user.insert(db).await?;
}

// ✅ 正确: 批量插入
user::Entity::insert_many(users)
    .exec(db)
    .await?;
```

---

## 9. NoSQL 数据库

### 9.1 MongoDB

```rust
use mongodb::{Client, options::ClientOptions, bson::doc};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
struct User {
    #[serde(rename = "_id", skip_serializing_if = "Option::is_none")]
    id: Option<mongodb::bson::oid::ObjectId>,
    email: String,
    name: String,
}

#[tokio::main]
async fn main() -> mongodb::error::Result<()> {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 连接 MongoDB
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let client_options = ClientOptions::parse("mongodb://localhost:27017").await?;
    let client = Client::with_options(client_options)?;
    
    let db = client.database("mydb");
    let collection = db.collection::<User>("users");
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 插入文档
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let user = User {
        id: None,
        email: "user@example.com".to_string(),
        name: "张三".to_string(),
    };
    
    collection.insert_one(user, None).await?;
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 查询文档
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let user = collection
        .find_one(doc! { "email": "user@example.com" }, None)
        .await?;
    
    println!("用户: {:?}", user);
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 更新文档
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    collection
        .update_one(
            doc! { "email": "user@example.com" },
            doc! { "$set": { "name": "李四" } },
            None,
        )
        .await?;
    
    Ok(())
}
```

### 9.2 Redis

```rust
use redis::AsyncCommands;

#[tokio::main]
async fn main() -> redis::RedisResult<()> {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 连接 Redis
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let client = redis::Client::open("redis://127.0.0.1/")?;
    let mut con = client.get_multiplexed_async_connection().await?;
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 基本操作
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    con.set("key", "value").await?;
    let value: String = con.get("key").await?;
    println!("值: {}", value);
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 设置过期时间
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    con.set_ex("session:123", "user_data", 3600).await?; // 1小时过期
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 列表操作
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    con.lpush("queue", "task1").await?;
    con.lpush("queue", "task2").await?;
    let task: String = con.rpop("queue", None).await?;
    println!("任务: {}", task);
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 哈希操作
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    con.hset("user:1", "name", "张三").await?;
    con.hset("user:1", "email", "zhangsan@example.com").await?;
    let name: String = con.hget("user:1", "name").await?;
    println!("姓名: {}", name);
    
    Ok(())
}
```

---

## 10. 实战案例

### 10.1 用户认证系统

```rust
use sqlx::PgPool;
use argon2::{Argon2, PasswordHash, PasswordVerifier};
use uuid::Uuid;

#[derive(Debug)]
struct User {
    id: Uuid,
    email: String,
    password_hash: String,
}

async fn register_user(
    pool: &PgPool,
    email: &str,
    password: &str,
) -> Result<User, Box<dyn std::error::Error>> {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 生成密码哈希
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let salt = uuid::Uuid::new_v4().to_string();
    let password_hash = argon2::hash_encoded(
        password.as_bytes(),
        salt.as_bytes(),
        &argon2::Config::default(),
    )?;
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 插入数据库
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let user = sqlx::query_as!(
        User,
        "INSERT INTO users (id, email, password_hash) VALUES ($1, $2, $3) RETURNING id, email, password_hash",
        Uuid::new_v4(),
        email,
        password_hash,
    )
    .fetch_one(pool)
    .await?;
    
    Ok(user)
}

async fn login_user(
    pool: &PgPool,
    email: &str,
    password: &str,
) -> Result<User, Box<dyn std::error::Error>> {
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 查询用户
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let user = sqlx::query_as!(
        User,
        "SELECT id, email, password_hash FROM users WHERE email = $1",
        email,
    )
    .fetch_one(pool)
    .await?;
    
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    // 验证密码
    // ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
    let parsed_hash = PasswordHash::new(&user.password_hash)?;
    Argon2::default().verify_password(password.as_bytes(), &parsed_hash)?;
    
    Ok(user)
}
```

### 10.2 博客系统

完整代码示例请参考前面创建的 `RUST_FULLSTACK_PROJECT_2025.md` 指南中的博客平台案例。

---

## 11. 最佳实践

1. **使用连接池**
2. **编译时验证** (SQLx 的 `query!` 宏)
3. **索引优化** (分析慢查询，添加合适的索引)
4. **批量操作** (减少往返次数)
5. **预加载关联数据** (避免 N+1 查询)
6. **使用事务** (保证数据一致性)
7. **错误处理** (使用 Result 类型)
8. **监控查询性能** (使用 EXPLAIN 分析)
9. **使用预编译语句** (防止 SQL 注入)
10. **定期备份数据库**

---

## 12. 常见陷阱

1. **忘记使用连接池**
2. **N+1 查询问题**
3. **未添加索引导致慢查询**
4. **事务未正确提交/回滚**
5. **SQL 注入漏洞** (使用参数化查询)
6. **连接泄漏** (忘记释放连接)
7. **过度使用 ORM** (复杂查询使用原生 SQL)
8. **未处理数据库错误**

---

## 13. 参考资源

- **SQLx**: [https://github.com/launchbadge/sqlx](https://github.com/launchbadge/sqlx)
- **Diesel**: [https://diesel.rs/](https://diesel.rs/)
- **SeaORM**: [https://www.sea-ql.org/SeaORM/](https://www.sea-ql.org/SeaORM/)
- **MongoDB Rust Driver**: [https://www.mongodb.com/docs/drivers/rust/](https://www.mongodb.com/docs/drivers/rust/)
- **Redis Rust**: [https://redis.rs/](https://redis.rs/)

---

> **完成！** 🎉  
> 本指南涵盖了 Rust 数据库开发的核心内容，包括 SQLx、Diesel、SeaORM、连接池、事务、迁移、查询优化、NoSQL 数据库、实战案例、最佳实践和常见陷阱。
