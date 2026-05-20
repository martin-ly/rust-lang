//! # 数据库交互 Hands-On 演示
//!
//! 本示例整合 Rust 数据库生态三大核心库：
//! - **SQLx**: 编译时检查的异步 SQL 工具包（本示例使用运行时查询以零配置运行）
//! - **Sea-ORM**: 异步动态 ORM，支持关系映射与迁移
//! - **Redis**: 高性能缓存与消息队列
//!
//! 使用 SQLite 内存模式，无需安装外部数据库即可运行。
//!
//! ## 运行
//!
//! ```bash
//! cargo run -p c06_async --example database_ecosystem_demo
//! ```
//!
//! [来源: SQLx 官方文档](https://docs.rs/sqlx)
//! [来源: Sea-ORM 官方文档](https://docs.rs/sea-orm)
//! [来源: Redis rs 官方文档](https://docs.rs/redis)

use anyhow::Result;
use sea_orm::{
    entity::prelude::*, query::*, ActiveValue, Database, DatabaseBackend,
    DatabaseConnection, Schema,
};
use sqlx::sqlite::SqlitePool;

// ============================================================
// Sea-ORM Entity 定义
// ============================================================

mod user_entity {
    use sea_orm::entity::prelude::*;

    #[derive(Clone, Debug, PartialEq, DeriveEntityModel)]
    #[sea_orm(table_name = "users")]
    pub struct Model {
        #[sea_orm(primary_key, auto_increment = true)]
        pub id: i32,
        pub username: String,
        pub email: String,
        pub created_at: DateTimeUtc,
    }

    #[derive(Copy, Clone, Debug, EnumIter, DeriveRelation)]
    pub enum Relation {}

    impl ActiveModelBehavior for ActiveModel {}
}

use user_entity::Entity as User;

#[tokio::main]
async fn main() -> Result<()> {
    println!("🗄️  数据库交互生态演示\n");

    demo_01_sqlx_sqlite().await?;
    demo_02_sea_orm_crud().await?;
    demo_03_redis_cache().await?;
    demo_04_connection_pool_pattern().await?;

    println!("\n✅ 数据库生态演示完成！");
    Ok(())
}

/// ## 演示 1: SQLx + SQLite 内存数据库
///
/// 直接使用 SQL 进行创建表、插入、查询操作。
async fn demo_01_sqlx_sqlite() -> Result<()> {
    println!("📦 演示 1: SQLx 原始 SQL 操作 (SQLite 内存模式)");
    println!("---------------------------------------------------");

    let pool = SqlitePool::connect("sqlite::memory:").await?;

    // 创建表
    sqlx::query(
        r#"
        CREATE TABLE products (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            name TEXT NOT NULL,
            price REAL NOT NULL,
            stock INTEGER DEFAULT 0
        )
        "#,
    )
    .execute(&pool)
    .await?;
    println!("✓ 创建 products 表");

    // 插入数据
    let rows_affected = sqlx::query(
        "INSERT INTO products (name, price, stock) VALUES (?1, ?2, ?3), (?4, ?5, ?6)",
    )
    .bind("Rust 编程语言")
    .bind(89.50f64)
    .bind(100i32)
    .bind("Cargo 指南")
    .bind(45.00f64)
    .bind(50i32)
    .execute(&pool)
    .await?
    .rows_affected();
    println!("✓ 插入 {} 行数据", rows_affected);

    // 查询数据
    let rows = sqlx::query_as::<_, (i64, String, f64, i32)>(
        "SELECT id, name, price, stock FROM products WHERE price > ?1",
    )
    .bind(50.0f64)
    .fetch_all(&pool)
    .await?;

    println!("\n价格 > 50 的商品:");
    for (id, name, price, stock) in rows {
        println!("  [#{}] {} — ¥{:.2} (库存: {})", id, name, price, stock);
    }

    // 事务演示
    let mut tx = pool.begin().await?;
    sqlx::query("UPDATE products SET stock = stock - ?1 WHERE id = ?2")
        .bind(1i32)
        .bind(1i64)
        .execute(&mut *tx)
        .await?;
    tx.commit().await?;
    println!("\n✓ 事务: 库存扣减成功");

    pool.close().await;
    println!();
    Ok(())
}

/// ## 演示 2: Sea-ORM CRUD 与关系映射
///
/// 使用 ORM 进行类型安全的增删改查。
async fn demo_02_sea_orm_crud() -> Result<()> {
    println!("🌊 演示 2: Sea-ORM 类型安全 CRUD");
    println!("----------------------------------");

    let db = Database::connect("sqlite::memory:").await?;

    // 自动建表（Schema API）
    let schema = Schema::new(DatabaseBackend::Sqlite);
    let stmt = schema.create_table_from_entity(User);
    db.execute(db.get_database_backend().build(&stmt)).await?;
    println!("✓ 自动创建 users 表 (Sea-ORM Schema)");

    // Create
    let alice = user_entity::ActiveModel {
        username: ActiveValue::Set("alice".to_string()),
        email: ActiveValue::Set("alice@example.com".to_string()),
        created_at: ActiveValue::Set(chrono::Utc::now()),
        ..Default::default()
    };
    let alice_inserted = User::insert(alice).exec(&db).await?;
    println!("✓ 插入用户 Alice, id = {}", alice_inserted.last_insert_id);

    let bob = user_entity::ActiveModel {
        username: ActiveValue::Set("bob".to_string()),
        email: ActiveValue::Set("bob@example.com".to_string()),
        created_at: ActiveValue::Set(chrono::Utc::now()),
        ..Default::default()
    };
    let bob_inserted = User::insert(bob).exec(&db).await?;
    println!("✓ 插入用户 Bob, id = {}", bob_inserted.last_insert_id);

    // Read (Query)
    let users: Vec<user_entity::Model> = User::find().all(&db).await?;
    println!("\n所有用户:");
    for u in &users {
        println!(
            "  [#{}] {} <{}> 创建于 {}",
            u.id,
            u.username,
            u.email,
            u.created_at.format("%Y-%m-%d %H:%M:%S")
        );
    }

    // Update
    let mut alice_model: user_entity::ActiveModel = User::find_by_id(alice_inserted.last_insert_id)
        .one(&db)
        .await?
        .unwrap()
        .into();
    alice_model.email = ActiveValue::Set("alice.new@example.com".to_string());
    alice_model.update(&db).await?;
    println!("\n✓ 更新 Alice 的邮箱");

    // Delete
    User::delete_by_id(bob_inserted.last_insert_id)
        .exec(&db)
        .await?;
    println!("✓ 删除 Bob");

    // 最终查询
    let remaining = User::find().count(&db).await?;
    println!("\n剩余用户数量: {}", remaining);

    db.close().await?;
    println!();
    Ok(())
}

/// ## 演示 3: Redis 缓存模式
///
/// 演示 Redis 连接、基本 KV 操作和缓存模式。
/// 如果没有运行中的 Redis 服务器，将优雅降级为模拟模式。
async fn demo_03_redis_cache() -> Result<()> {
    println!("🔴 演示 3: Redis 缓存模式");
    println!("--------------------------");

    match redis::Client::open("redis://127.0.0.1:6379/") {
        Ok(client) => match client.get_multiplexed_tokio_connection().await {
            Ok(mut conn) => {
                println!("✓ 连接到 Redis");

                // 基本 KV 操作
                redis::cmd("SET")
                    .arg("rust:demo:key")
                    .arg("hello from rust!")
                    .query_async::<_, ()>(&mut conn)
                    .await?;
                println!("✓ SET rust:demo:key = 'hello from rust!'");

                let value: String = redis::cmd("GET")
                    .arg("rust:demo:key")
                    .query_async(&mut conn)
                    .await?;
                println!("✓ GET rust:demo:key = '{}'", value);

                // 哈希表操作（模拟对象缓存）
                let _: () = redis::cmd("HSET")
                    .arg("user:1001")
                    .arg("name")
                    .arg("Alice")
                    .arg("role")
                    .arg("admin")
                    .query_async(&mut conn)
                    .await?;
                println!("✓ HSET user:1001 {{ name: Alice, role: admin }}");

                // 设置过期时间 (TTL)
                let _: () = redis::cmd("EXPIRE")
                    .arg("rust:demo:key")
                    .arg(60i32)
                    .query_async(&mut conn)
                    .await?;
                println!("✓ EXPIRE rust:demo:key 60s");

                // 缓存模式: 缓存击穿保护 —— 使用 SET NX (只有不存在时才设置)
                let locked: bool = redis::cmd("SET")
                    .arg("cache:lock:resource_a")
                    .arg("1")
                    .arg("NX")
                    .arg("EX")
                    .arg(10i32)
                    .query_async(&mut conn)
                    .await
                    .unwrap_or(false);
                println!("✓ 分布式锁获取: {}", locked);

                // 清理演示数据
                let _: () = redis::cmd("DEL")
                    .arg("rust:demo:key")
                    .arg("user:1001")
                    .arg("cache:lock:resource_a")
                    .query_async(&mut conn)
                    .await?;
                println!("✓ 清理演示数据");
            }
            Err(e) => {
                println!("⚠️  无法连接 Redis 服务器: {}", e);
                println!("   提示: 启动本地 Redis 后重新运行本示例");
                println!("   docker run -d -p 6379:6379 redis:alpine");
            }
        },
        Err(e) => {
            println!("⚠️  Redis 客户端初始化失败: {}", e);
        }
    }

    println!();
    Ok(())
}

/// ## 演示 4: 连接池与缓存模式整合
///
/// 展示生产环境中的典型架构：数据库 + Redis 缓存的组合查询。
async fn demo_04_connection_pool_pattern() -> Result<()> {
    println!("🏗️  演示 4: 连接池与缓存模式整合");
    println!("-----------------------------------");

    // SQLite 连接池
    let sqlite_pool = SqlitePool::connect("sqlite::memory:").await?;

    sqlx::query(
        "CREATE TABLE articles (id INTEGER PRIMARY KEY, title TEXT, content TEXT, views INTEGER DEFAULT 0)"
    )
    .execute(&sqlite_pool)
    .await?;

    sqlx::query("INSERT INTO articles (title, content) VALUES (?1, ?2), (?3, ?4)")
        .bind("Rust 所有权系统")
        .bind("所有权是 Rust 最核心的特性...")
        .bind("异步编程指南")
        .bind("Tokio 是 Rust 的事实标准异步运行时...")
        .execute(&sqlite_pool)
        .await?;

    // 模拟 "缓存优先" 查询模式
    println!("模拟缓存优先查询模式 (Cache-Aside):");

    // 第 1 次查询 — 缓存未命中，查数据库
    let article = fetch_article_with_cache(&sqlite_pool, 1).await?;
    println!("  第 1 次查询 (缓存未命中): {:?}", article);

    // 第 2 次查询 — 假设缓存命中
    let article = fetch_article_with_cache(&sqlite_pool, 1).await?;
    println!("  第 2 次查询 (缓存命中模拟): {:?}", article);

    sqlite_pool.close().await;
    println!();
    Ok(())
}

/// 模拟 Cache-Aside 模式：先查缓存，未命中再查数据库
async fn fetch_article_with_cache(
    pool: &SqlitePool,
    id: i64,
) -> Result<Option<(i64, String, String)>> {
    // 实际生产环境: 先查 Redis
    // let cached: Option<String> = redis::cmd("GET")
    //     .arg(format!("article:{}", id))
    //     .query_async(&mut conn).await?;

    // 演示：直接查数据库
    let row = sqlx::query_as::<_, (i64, String, String)>(
        "SELECT id, title, content FROM articles WHERE id = ?1",
    )
    .bind(id)
    .fetch_optional(pool)
    .await?;

    // 实际生产环境: 写入 Redis 缓存
    // if let Some(ref data) = row {
    //     redis::cmd("SETEX").arg(format!("article:{}", id))
    //         .arg(300).arg(serialize(data)).query_async(&mut conn).await?;
    // }

    Ok(row)
}
