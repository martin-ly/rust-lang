# 数据库访问

> **核心库**: sqlx, diesel, sea-orm, mongodb, redis  
> **适用场景**: SQL数据库、NoSQL、ORM、连接池

---

## 📋 库选择

| 库 | 类型 | 异步 | 编译时检查 | 推荐度 |
|-----|------|------|-----------|--------|
| **sqlx** | SQL | ✅ | ✅ | ⭐⭐⭐⭐⭐ |
| **diesel** | ORM | ❌ | ✅ | ⭐⭐⭐⭐⭐ |
| **sea-orm** | ORM | ✅ | ✅ | ⭐⭐⭐⭐ |
| **mongodb** | NoSQL | ✅ | ❌ | ⭐⭐⭐⭐ |
| **redis** | 缓存 | ✅ | ❌ | ⭐⭐⭐⭐⭐ |

---

## 🔷 SQLx - 异步SQL

```rust
use sqlx::{PgPool, FromRow};
use serde::{Serialize, Deserialize};

#[derive(Debug, FromRow, Serialize, Deserialize)]
struct User {
    id: i32,
    name: String,
    email: String,
}

#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    // 连接池
    let pool = PgPool::connect("postgres://user:pass@localhost/db").await?;
    
    // 查询
    let user = sqlx::query_as::<_, User>("SELECT * FROM users WHERE id = $1")
        .bind(1)
        .fetch_one(&pool)
        .await?;
    
    println!("{:?}", user);
    
    // 插入
    sqlx::query("INSERT INTO users (name, email) VALUES ($1, $2)")
        .bind("Alice")
        .bind("alice@example.com")
        .execute(&pool)
        .await?;
    
    Ok(())
}
```

---

## ⚙️ Diesel - 类型安全ORM

```rust
use diesel::prelude::*;
use diesel::pg::PgConnection;

#[derive(Queryable)]
struct User {
    id: i32,
    name: String,
    email: String,
}

fn main() {
    let conn = PgConnection::establish("postgres://localhost/db")
        .expect("Error connecting to database");
    
    use schema::users::dsl::*;
    
    let results = users
        .filter(id.eq(1))
        .load::<User>(&conn)
        .expect("Error loading users");
    
    for user in results {
        println!("{}: {}", user.name, user.email);
    }
}
```

---

## 🌊 SeaORM - 现代异步ORM

```rust
use sea_orm::*;

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

#[tokio::main]
async fn main() -> Result<(), DbErr> {
    let db = Database::connect("postgres://localhost/db").await?;
    
    // 查询
    let user = Entity::find_by_id(1).one(&db).await?;
    
    // 插入
    let user = ActiveModel {
        name: Set("Alice".to_owned()),
        email: Set("alice@example.com".to_owned()),
        ..Default::default()
    };
    user.insert(&db).await?;
    
    Ok(())
}
```

---

## 🗄️ MongoDB

```rust
use mongodb::{Client, options::ClientOptions};
use serde::{Serialize, Deserialize};

#[derive(Debug, Serialize, Deserialize)]
struct User {
    name: String,
    email: String,
}

#[tokio::main]
async fn main() -> mongodb::error::Result<()> {
    let client_options = ClientOptions::parse("mongodb://localhost:27017").await?;
    let client = Client::with_options(client_options)?;
    
    let db = client.database("mydb");
    let collection = db.collection::<User>("users");
    
    // 插入
    let user = User {
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
    };
    collection.insert_one(user, None).await?;
    
    // 查询
    let mut cursor = collection.find(None, None).await?;
    while let Some(user) = cursor.next().await {
        println!("{:?}", user?);
    }
    
    Ok(())
}
```

---

## 🔴 Redis

```rust
use redis::AsyncCommands;

#[tokio::main]
async fn main() -> redis::RedisResult<()> {
    let client = redis::Client::open("redis://127.0.0.1/")?;
    let mut con = client.get_async_connection().await?;
    
    // 设置值
    con.set("key", "value").await?;
    
    // 获取值
    let value: String = con.get("key").await?;
    println!("Value: {}", value);
    
    // Hash操作
    con.hset("user:1", "name", "Alice").await?;
    let name: String = con.hget("user:1", "name").await?;
    
    Ok(())
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20

