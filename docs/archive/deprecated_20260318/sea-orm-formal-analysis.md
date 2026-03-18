# Sea-ORM数据库ORM形式化分析

> **主题**: 现代异步ORM
> **形式化框架**: 实体关系 + 类型安全查询 + 迁移系统
> **参考**: Sea-ORM Documentation (<https://www.sea-ql.org/SeaORM>)

---

## 目录

- [Sea-ORM数据库ORM形式化分析](#sea-orm数据库orm形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 实体模型](#2-实体模型)
    - [定义 ENTITY-1 ( 实体结构 )](#定义-entity-1--实体结构-)
    - [定义 ENTITY-2 ( 主键约束 )](#定义-entity-2--主键约束-)
    - [定理 ENTITY-T1 ( 标识唯一性 )](#定理-entity-t1--标识唯一性-)
  - [3. 类型安全查询](#3-类型安全查询)
    - [定义 QUERY-1 ( 查询构建器 )](#定义-query-1--查询构建器-)
    - [定义 QUERY-2 ( 类型检查 )](#定义-query-2--类型检查-)
    - [定理 QUERY-T1 ( 编译时类型安全 )](#定理-query-t1--编译时类型安全-)
  - [4. 关系映射](#4-关系映射)
    - [定义 REL-1 ( 关系类型 )](#定义-rel-1--关系类型-)
    - [定义 REL-2 ( 外键约束 )](#定义-rel-2--外键约束-)
    - [定理 REL-T1 ( 引用完整性 )](#定理-rel-t1--引用完整性-)
  - [5. 迁移系统](#5-迁移系统)
    - [定义 MIGRATION-1 ( 迁移操作 )](#定义-migration-1--迁移操作-)
    - [定理 MIGRATION-T1 ( 可逆性 )](#定理-migration-t1--可逆性-)
  - [6. 定理与证明](#6-定理与证明)
    - [定理 ORM-T1 ( SQL注入防护 )](#定理-orm-t1--sql注入防护-)
    - [定理 ORM-T2 ( 连接池安全 )](#定理-orm-t2--连接池安全-)
  - [7. 代码示例](#7-代码示例)
    - [示例1: CRUD操作](#示例1-crud操作)
    - [示例2: 复杂查询](#示例2-复杂查询)
    - [示例3: 事务](#示例3-事务)
    - [示例4: 迁移](#示例4-迁移)

---

## 1. 引言

Sea-ORM特点：

- 完全异步
- 类型安全查询构建器
- 支持多种数据库
- 迁移系统
- 实体生成

---

## 2. 实体模型

### 定义 ENTITY-1 ( 实体结构 )

```rust
#[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
#[sea_orm(table_name = "users")]
pub struct Model {
    #[sea_orm(primary_key)]
    pub id: i32,
    pub username: String,
    pub email: String,
    #[sea_orm(default_value = "CURRENT_TIMESTAMP")]
    pub created_at: DateTime,
}
```

**形式化**:

$$
\text{Entity} = \{ (c_i : T_i, \text{constraints}_i) \mid i = 1..n \}
$$

### 定义 ENTITY-2 ( 主键约束 )

$$
\text{PrimaryKey}(E) = \{ c \mid \text{unique}(c) \land \text{non-null}(c) \}
$$

### 定理 ENTITY-T1 ( 标识唯一性 )

主键唯一标识实体实例。

$$
\forall e_1, e_2 : E.\ pk(e_1) = pk(e_2) \to e_1 = e_2
$$

---

## 3. 类型安全查询

### 定义 QUERY-1 ( 查询构建器 )

```rust
User::find()
    .filter(user::Column::Username.eq("alice"))
    .filter(user::Column::Age.gte(18))
    .order_by_asc(user::Column::CreatedAt)
    .all(db)
    .await
```

**形式化**:

$$
\text{Query} = \text{Select} \times \text{Filter}^* \times \text{Order} \times \text{Limit}
$$

### 定义 QUERY-2 ( 类型检查 )

$$
\text{Column}::\text{op} : T \to \text{Condition} \text{ where op compatible with } T
$$

### 定理 QUERY-T1 ( 编译时类型安全 )

查询条件类型在编译时验证。

$$
\text{User}::\text{Column}::\text{Age}::\text{eq}(s : \text{String}) \to \text{compile\_error}
$$

---

## 4. 关系映射

### 定义 REL-1 ( 关系类型 )

| 关系 | 基数 | 描述 |
| :--- | :--- | :--- |
| HasOne | 1:1 | 一对一 |
| HasMany | 1:N | 一对多 |
| BelongsTo | N:1 | 多对一 |
| ManyToMany | N:M | 多对多 |

### 定义 REL-2 ( 外键约束 )

$$
\text{ForeignKey}(E, F) = \{ (e, f) \mid e.fk = f.pk \}
$$

### 定理 REL-T1 ( 引用完整性 )

外键引用必须指向存在的实体。

$$
\forall e : E.\ e.fk \neq \text{null} \to \exists f : F.\ f.pk = e.fk
$$

---

## 5. 迁移系统

### 定义 MIGRATION-1 ( 迁移操作 )

```rust
manager
    .create_table(
        Table::create()
            .table(User::Table)
            .col(ColumnDef::new(User::Id).integer().not_null().auto_increment().primary_key())
            .col(ColumnDef::new(User::Username).string().not_null().unique_key())
            .to_owned(),
    )
    .await
```

**形式化**:

$$
\text{Migration} = \{ \text{up} : \text{Schema} \to \text{Schema}', \text{down} : \text{Schema}' \to \text{Schema} \}
$$

### 定理 MIGRATION-T1 ( 可逆性 )

迁移必须是可逆的。

$$
\text{down}(\text{up}(s)) = s
$$

---

## 6. 定理与证明

### 定理 ORM-T1 ( SQL注入防护 )

参数化查询防止SQL注入。

$$
\forall q : \text{Query}.\ q \text{ uses parameter binding}
$$

**证明**: 所有用户输入通过参数绑定，不直接拼接SQL。$\square$

### 定理 ORM-T2 ( 连接池安全 )

连接池管理保证连接有效性。

$$
\forall c \in \text{Pool}.\ c \text{ valid } \lor \text{recreate}(c)
$$

---

## 7. 代码示例

### 示例1: CRUD操作

```rust
use sea_orm::{entity::*, query::*, DbConn};

// Create
let user = user::ActiveModel {
    username: Set("alice".to_owned()),
    email: Set("alice@example.com".to_owned()),
    ..Default::default()
};
let user: user::Model = user.insert(db).await?;

// Read
let user = User::find_by_id(1).one(db).await?;

// Update
let mut user: user::ActiveModel = user.into();
user.email = Set("new@example.com".to_owned());
let user: user::Model = user.update(db).await?;

// Delete
let result = User::delete_by_id(1).exec(db).await?;
```

### 示例2: 复杂查询

```rust
// 分页查询
let paginator = User::find()
    .filter(user::Column::Status.eq(Status::Active))
    .order_by_asc(user::Column::CreatedAt)
    .paginate(db, 10);

let users = paginator.fetch_page(0).await?;
let num_pages = paginator.num_pages().await?;

// 聚合查询
let count = User::find()
    .filter(user::Column::Status.eq(Status::Active))
    .count(db)
    .await?;

// 连接查询
let users_with_posts: Vec<(user::Model, Vec<post::Model>)> = User::find()
    .find_with_related(Post)
    .all(db)
    .await?;
```

### 示例3: 事务

```rust
use sea_orm::{TransactionTrait, DbErr};

db.transaction::<_, _, DbErr>(|txn| {
    Box::pin(async move {
        let user = user::ActiveModel {
            username: Set("bob".to_owned()),
            ..Default::default()
        }.insert(txn).await?;

        let profile = profile::ActiveModel {
            user_id: Set(user.id),
            bio: Set("Hello".to_owned()),
            ..Default::default()
        }.insert(txn).await?;

        Ok((user, profile))
    })
}).await
```

### 示例4: 迁移

```rust
use sea_orm_migration::prelude::*;

pub struct Migration;

impl MigrationName for Migration {
    fn name(&self) -> &str {
        "m20220101_000001_create_user_table"
    }
}

#[async_trait::async_trait]
impl MigrationTrait for Migration {
    async fn up(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .create_table(
                Table::create()
                    .table(User::Table)
                    .if_not_exists()
                    .col(
                        ColumnDef::new(User::Id)
                            .integer()
                            .not_null()
                            .auto_increment()
                            .primary_key(),
                    )
                    .col(ColumnDef::new(User::Username).string().not_null().unique_key())
                    .col(ColumnDef::new(User::Email).string().not_null())
                    .col(ColumnDef::new(User::CreatedAt).timestamp().not_null())
                    .to_owned(),
            )
            .await
    }

    async fn down(&self, manager: &SchemaManager) -> Result<(), DbErr> {
        manager
            .drop_table(Table::drop().table(User::Table).to_owned())
            .await
    }
}
```

---

**维护者**: Rust Database Formal Methods Team
**创建日期**: 2026-03-05
**Sea-ORM版本**: 1.0+
**状态**: ✅ 已对齐
