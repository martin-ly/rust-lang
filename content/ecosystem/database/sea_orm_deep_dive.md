# Sea-ORM 深度解析

> **定位**: Rust 异步 ORM 生态标杆
> **版本**: Sea-ORM 1.x (兼容 Rust 1.95.0+)
> **适用场景**: 异步数据库访问、类型安全查询、迁移管理

---

## 📋 目录

- [Sea-ORM 深度解析](#sea-orm-深度解析)
  - [📋 目录](#-目录)
  - [🎯 架构概览](#-架构概览)
  - [⚙️ 核心概念](#️-核心概念)
    - [1. Entity (实体)](#1-entity-实体)
    - [2. Model (模型)](#2-model-模型)
    - [3. ActiveModel (活跃模型)](#3-activemodel-活跃模型)
    - [4. Relation (关系)](#4-relation-关系)
  - [🔧 查询构建器](#-查询构建器)
    - [类型安全查询](#类型安全查询)
    - [原始 SQL（逃生舱）](#原始-sql逃生舱)
  - [🔄 迁移系统](#-迁移系统)
  - [📊 与 SQLx 对比](#-与-sqlx-对比)
  - [🔗 参考资源](#-参考资源)
  - [**状态**: ✅ 已完善](#状态--已完善)

---

## 🎯 架构概览

```
┌─────────────────────────────────────────┐
│           Application Layer             │
│  (Axum / Actix-web / Poem / Tauri)     │
├─────────────────────────────────────────┤
│              Sea-ORM Layer              │
│  ┌─────────┐ ┌─────────┐ ┌─────────┐ │
│  │ Entity  │ │ Query   │ │ Migrator│ │
│  │ (类型)  │ │ Builder │ │ (迁移)  │ │
│  └────┬────┘ └────┬────┘ └────┬────┘ │
│       └─────────────┴─────────────┘   │
│              SeaQuery (SQL 生成)        │
├─────────────────────────────────────────┤
│         SQLx / native-tls / rustls      │
├─────────────────────────────────────────┤
│      PostgreSQL / MySQL / SQLite        │
└─────────────────────────────────────────┘
```

**设计哲学**:

- **类型安全**: 查询在编译期验证（通过 Entity 代码生成）
- **异步优先**: 所有数据库操作均为 `async`
- **数据库无关**: 同一套 API 支持 PG/MySQL/SQLite
- **灵活查询**: 从类型安全的链式 API 到原始 SQL

---

## ⚙️ 核心概念

### 1. Entity (实体)

Entity 是数据库表的 Rust 类型表示：

```rust
// 由 sea-orm-cli generate entity 生成
pub mod cake {
    use sea_orm::entity::prelude::*;

    #[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
    #[sea_orm(table_name = "cake")]
    pub struct Model {
        #[sea_orm(primary_key)]
        pub id: i32,
        pub name: String,
    }

    #[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
    pub enum Relation {
        #[sea_orm(has_many = "super::fruit::Entity")]
        Fruit,
    }

    impl Related<super::fruit::Entity> for Entity {
        fn to() -> RelationDef {
            Relation::Fruit.def()
        }
    }

    impl ActiveModelBehavior for ActiveModel {}
}
```

---

### 2. Model (模型)

`Model` 是查询返回的不可变数据结构：

```rust
let cake: Option<cake::Model> = Cake::find_by_id(1).one(&db).await?;

if let Some(cake) = cake {
    println!("Cake: {}", cake.name);
    // cake.name = "new".to_string(); // ❌ 编译错误: Model 不可变
}
```

---

### 3. ActiveModel (活跃模型)

`ActiveModel` 用于插入和更新：

```rust
// 插入
let apple = fruit::ActiveModel {
    name: Set("Apple".to_owned()),
    cake_id: Set(Some(1)),
    ..Default::default()
};
let apple: fruit::Model = apple.insert(&db).await?;

// 更新
let mut apple: fruit::ActiveModel = apple.into();
apple.name = Set("Green Apple".to_owned());
let apple: fruit::Model = apple.update(&db).await?;

// 删除
apple.delete(&db).await?;
```

**关键区别**:

| | Model | ActiveModel |
|---|-------|-------------|
| 用途 | 查询结果 | 插入/更新/删除 |
| 可变性 | 不可变 | 字段级可变 |
| 字段类型 | `T` | `ActiveValue<T>` |

---

### 4. Relation (关系)

```rust
// 一对多: Cake → Fruit
let cake_with_fruits: Vec<(cake::Model, Vec<fruit::Model>)> =
    Cake::find()
        .find_with_related(Fruit)
        .all(&db)
        .await?;

// 多对一: Fruit → Cake
let fruits_with_cakes: Vec<(fruit::Model, Option<cake::Model>)> =
    Fruit::find()
        .find_also_related(Cake)
        .all(&db)
        .await?;

// 懒加载
let cake: cake::Model = Cake::find_by_id(1).one(&db).await?.unwrap();
let fruits: Vec<fruit::Model> = cake.find_related(Fruit).all(&db).await?;
```

---

## 🔧 查询构建器

### 类型安全查询

```rust
// 条件查询
let cakes: Vec<cake::Model> = Cake::find()
    .filter(cake::Column::Name.contains("Chocolate"))
    .filter(cake::Column::Id.gte(10))
    .order_by_asc(cake::Column::Name)
    .limit(10)
    .offset(20)
    .all(&db)
    .await?;

// 聚合
let count: i64 = Cake::find().count(&db).await?;

// 分页
let paginator = Cake::find()
    .filter(cake::Column::Name.like("%cake%"))
    .paginate(&db, 50);

let num_pages = paginator.num_pages().await?;
for page in paginator.fetch_page(0).await? {
    println!("{:?}", page);
}
```

### 原始 SQL（逃生舱）

```rust
use sea_orm::{ConnectionTrait, Statement};

let stmt = Statement::from_sql_and_values(
    DbBackend::Postgres,
    r#"SELECT * FROM cake WHERE id = $1"#,
    [1.into()],
);
let cake = Cake::find_by_statement(stmt).one(&db).await?;
```

---

## 🔄 迁移系统

```rust
// migration/src/lib.rs
use sea_orm_migration::prelude::*;

pub struct Migrator;

#[async_trait::async_trait]
impl MigratorTrait for Migrator {
    fn migrations() -> Vec<Box<dyn MigrationTrait>> {
        vec![
            Box::new(m20220101_000001_create_cake_table::Migration),
            Box::new(m20220101_000002_create_fruit_table::Migration),
        ]
    }
}

// 运行迁移
Migrator::up(&db, None).await?;  // 升级
Migrator::down(&db, Some(1)).await?;  // 回退 1 步
```

---

## 📊 与 SQLx 对比

| 维度 | Sea-ORM | SQLx |
|------|---------|------|
| 抽象层级 | 高 (ORM) | 低 (查询构建器) |
| 类型安全 | 编译期 (代码生成) | 编译期 (宏检查) |
| 查询灵活性 | 中等 (结构化) | 高 (原始 SQL) |
| 迁移系统 | 内置 | 需配合 sqlx-migrate |
| 学习曲线 | 中等 | 较低 |
| 运行时开销 | 略高 | 较低 |
| 适用场景 | CRUD 密集型 | 复杂查询 / 性能敏感 |

**选择决策树**:

```
需要复杂查询 / 性能优先? ──是──→ SQLx
                └──否──→ 需要关系映射 / 快速开发? ──是──→ Sea-ORM
                                      └──否──→ diesel (同步)
```

---

## 🔗 参考资源

- [Sea-ORM 官方文档](https://www.sea-ql.org/SeaORM/)
- [Sea-ORM Cookbook](https://www.sea-ql.org/sea-orm-cookbook/)
- [项目 C10 网络模块](../../crates/c10_networks/)
- [SQLx 深度解析](./sqlx_deep_dive.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-05-08
**状态**: ✅ 已完善
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
