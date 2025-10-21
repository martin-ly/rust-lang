# ORM 框架

> **核心库**: sea-orm, rbatis, ormx  
> **适用场景**: 对象关系映射、数据库抽象、查询构建

---

## 📋 ORM 对比

| 库 | 异步 | 数据库 | 特点 | 推荐度 |
|-----|------|--------|------|--------|
| **sea-orm** | ✅ | 多种 | 现代、活跃 | ⭐⭐⭐⭐⭐ |
| **rbatis** | ✅ | 多种 | 类MyBatis | ⭐⭐⭐⭐ |
| **diesel** | ❌ | 多种 | 成熟稳定 | ⭐⭐⭐⭐⭐ |

---

## 🌊 SeaORM - 现代异步

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
    pub created_at: DateTimeUtc,
}

#[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
pub enum Relation {
    #[sea_orm(has_many = "super::post::Entity")]
    Post,
}

impl ActiveModelBehavior for ActiveModel {}
```

### CRUD 操作

```rust
use sea_orm::*;

#[tokio::main]
async fn main() -> Result<(), DbErr> {
    let db = Database::connect("postgres://localhost/db").await?;
    
    // Create
    let user = user::ActiveModel {
        name: Set("Alice".to_owned()),
        email: Set("alice@example.com".to_owned()),
        ..Default::default()
    };
    let user = user.insert(&db).await?;
    
    // Read
    let users = user::Entity::find()
        .filter(user::Column::Name.contains("Alice"))
        .all(&db)
        .await?;
    
    // Update
    let mut user: user::ActiveModel = user.into();
    user.email = Set("newemail@example.com".to_owned());
    user.update(&db).await?;
    
    // Delete
    user.delete(&db).await?;
    
    Ok(())
}
```

---

## 📝 rbatis - 类MyBatis

```rust
use rbatis::Rbatis;
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize)]
pub struct User {
    pub id: i32,
    pub name: String,
}

#[tokio::main]
async fn main() {
    let rb = Rbatis::new();
    rb.link("mysql://root:pass@localhost:3306/db").await.unwrap();
    
    // SQL查询
    let users: Vec<User> = rb.fetch_list("SELECT * FROM users WHERE id > ?", &[1]).await.unwrap();
    
    println!("{:?}", users);
}
```

---

## 💡 最佳实践

### 事务处理

```rust
use sea_orm::*;

async fn transfer_money(
    db: &DatabaseConnection,
    from_id: i32,
    to_id: i32,
    amount: f64
) -> Result<(), DbErr> {
    let txn = db.begin().await?;
    
    // 扣款
    // ... 业务逻辑
    
    // 加款
    // ... 业务逻辑
    
    txn.commit().await?;
    Ok(())
}
```

### 关系查询

```rust
use sea_orm::*;

async fn get_user_with_posts(db: &DatabaseConnection, user_id: i32) 
    -> Result<(user::Model, Vec<post::Model>), DbErr> 
{
    let user_with_posts = user::Entity::find_by_id(user_id)
        .find_with_related(post::Entity)
        .all(db)
        .await?;
    
    Ok(user_with_posts.into_iter().next().unwrap())
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
