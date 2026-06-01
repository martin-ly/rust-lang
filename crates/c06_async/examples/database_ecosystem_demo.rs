//! # 数据库交互 Hands-On 演示
//! # database Hands-On demonstration
//! 本示例整合 Rust 数据库生态三大核心库：
//! this example integration Rust database ecosystem core library ：
//! - **Sea-ORM**: 异步动态 ORM，支持关系映射与迁移
//! - **Sea-ORM**: async ORM，and
//! 使用 SQLite 内存模式，无需安装外部数据库即可运行。
//! SQLite memory ，outside database Run 。
//! ## 运行
//! ## Run
//! ```bash
//! cargo run -p c06_async --example database_ecosystem_demo
//! ```
//!
//! [来源: SQLx 官方文档](https://docs.rs/sqlx)
//! [source: SQLx 官方文档](https://docs.rs/sqlx)
//! [来源: Sea-ORM 官方文档](https://docs.rs/sea-orm)
//! [source: Sea-ORM 官方文档](https://docs.rs/sea-orm)
//! [来源: Redis rs 官方文档](https://docs.rs/redis)
//! [source: Redis rs 官方文档](https://docs.rs/redis)

use anyhow::Result;
use sea_orm::{ConnectionTrait, Database, DbBackend, Statement};
use sqlx::sqlite::SqlitePool;

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
/// ## demonstration 1: SQLx + SQLite in-memory database
/// 直接使用 SQL 进行创建表、插入、查询操作。
/// SQL 、、。
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

/// 使用 ORM 进行类型安全的增删改查。
/// ORM type 。
async fn demo_02_sea_orm_crud() -> Result<()> {
    println!("🌊 演示 2: Sea-ORM 类型安全 CRUD");
    println!("----------------------------------");

    let db = Database::connect("sqlite::memory:").await?;

    // 手动建表（使用原始 SQL）
    db.execute_unprepared(
        r#"
        CREATE TABLE users (
            id INTEGER PRIMARY KEY AUTOINCREMENT,
            username TEXT NOT NULL,
            email TEXT NOT NULL
        )
        "#,
    )
    .await?;
    println!("✓ 创建 users 表");

    // 插入数据
    let result = db.execute_unprepared(
        "INSERT INTO users (username, email) VALUES ('alice', 'alice@example.com')",
    ).await?;
    println!("✓ 插入用户 Alice, rows affected = {}", result.rows_affected());

    db.execute_unprepared(
        "INSERT INTO users (username, email) VALUES ('bob', 'bob@example.com')",
    ).await?;
    println!("✓ 插入用户 Bob");

    // 查询所有用户
    let stmt = Statement::from_string(
        DbBackend::Sqlite,
        "SELECT id, username, email FROM users".to_string(),
    );
    let rows = db.query_all_raw(stmt).await?;

    println!("\n所有用户:");
    for row in &rows {
        let id: i32 = row.try_get_by_index(0)?;
        let username: String = row.try_get_by_index(1)?;
        let email: String = row.try_get_by_index(2)?;
        println!("  [#{}] {} <{}>", id, username, email);
    }

    // 更新
    db.execute_unprepared(
        "UPDATE users SET email = 'alice.new@example.com' WHERE username = 'alice'",
    ).await?;
    println!("\n✓ 更新 Alice 的邮箱");

    // 删除
    db.execute_unprepared("DELETE FROM users WHERE username = 'bob'").await?;
    println!("✓ 删除 Bob");

    // 最终计数
    let count_stmt = Statement::from_string(
        DbBackend::Sqlite,
        "SELECT COUNT(*) as cnt FROM users".to_string(),
    );
    let count_row = db.query_one_raw(count_stmt).await?.unwrap();
    let remaining: i64 = count_row.try_get_by_index(0)?;
    println!("\n剩余用户数量: {}", remaining);

    db.close().await?;
    println!();
    Ok(())
}

/// ## 演示 3: Redis 缓存模式
/// ## demonstration 3: Redis
/// ## Demonstration of 3: Redis 缓存模式
/// 演示 Redis 连接、基本 KV 操作和缓存模式。
/// demonstration Redis 、this KV and 。
async fn demo_03_redis_cache() -> Result<()> {
    println!("🔴 演示 3: Redis 缓存模式");
    println!("--------------------------");

    match redis::Client::open("redis://127.0.0.1:6379/") {
        Ok(client) => {
            match client.get_multiplexed_async_connection().await {
                Ok(mut conn) => {
                    println!("✓ 连接到 Redis");

                    // 基本 KV 操作
                    let _: () = redis::cmd("SET")
                        .arg("rust:demo:key")
                        .arg("hello from rust!")
                        .query_async(&mut conn)
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

                    // 清理演示数据
                    let _: () = redis::cmd("DEL")
                        .arg("rust:demo:key")
                        .arg("user:1001")
                        .query_async(&mut conn)
                        .await?;
                    println!("✓ 清理演示数据");
                }
                Err(e) => {
                    println!("⚠️  无法连接 Redis 服务器: {}", e);
                    println!("   提示: 启动本地 Redis 后重新运行本示例");
                    println!("   docker run -d -p 6379:6379 redis:alpine");
                }
            }
        }
        Err(e) => {
            println!("⚠️  Redis 客户端初始化失败: {}", e);
        }
    }

    println!();
    Ok(())
}

/// ## 演示 4: 连接池与缓存模式整合
/// ## demonstration 4: and integration
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
/// Cache-Aside ：，in database
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
