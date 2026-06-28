# SQLx 深度解析

> **定位**: Rust 异步 SQL 工具包，编译时查询检查标杆
> **版本**: SQLx 0.8.x (兼容 Rust 1.96.0+)
> **适用场景**: 类型安全 SQL、高性能查询、轻量级数据访问

---

## 📋 目录

- [SQLx 深度解析](#sqlx-深度解析)
  - [📋 目录](#-目录)
  - [🎯 编译时查询检查原理](#-编译时查询检查原理)
    - [宏展开流程](#宏展开流程)
    - [离线模式 (Offline Mode)](#离线模式-offline-mode)
  - [⚙️ query! / query\_as! 宏用法](#️-query--query_as-宏用法)
    - [query! 匿名结果](#query-匿名结果)
    - [query\_as! 映射结构体](#query_as-映射结构体)
    - [query\_scalar! 单列查询](#query_scalar-单列查询)
  - [🔌 连接池配置](#-连接池配置)
  - [🔄 事务处理](#-事务处理)
    - [基本事务](#基本事务)
    - [嵌套事务与保存点](#嵌套事务与保存点)
  - [🗃️ 迁移系统 (sqlx-cli)](#️-迁移系统-sqlx-cli)
  - [📊 与 Sea-ORM / Diesel 对比](#-与-sea-orm--diesel-对比)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 编译时查询检查原理

SQLx 的核心创新在于**编译期验证 SQL 查询**，无需代码生成或 DSL：

```text
┌─────────────────────────────────────────┐
│         编译时宏展开 (proc-macro)        │
│  ┌─────────┐    ┌──────────────────┐    │
│  │ query!  │───→│ 解析 SQL 语句     │   │
│  │ 宏调用  │    │ 提取参数占位符     │   │
│  └─────────┘    └────────┬─────────┘   │
│                          ↓             │
│  ┌──────────────────────────────────┐  │
│  │  通过 DATABASE_URL 连接真实数据库  │  │
│  │  - 验证表/列存在性                 │  │
│  │  - 推导返回类型的 Rust 映射        │  │
│  │  - 检查参数类型兼容性              │  │
│  └──────────────────────────────────┘  │
│                          ↓             │
│  ┌──────────────────────────────────┐  │
│  │ 生成结构体 + 绑定代码              │  │
│  │ 写入 .sqlx/query-*.json (离线缓存) │  │
│  └──────────────────────────────────┘   │
└─────────────────────────────────────────┘
                    ↓
            运行时直接执行预准备语句
```

### 宏展开流程

```rust
// 编译时，SQLx 宏会执行以下操作：
let row = sqlx::query!("SELECT id, name FROM users WHERE id = $1", user_id)
    .fetch_one(&pool)
    .await?;

// 1. 解析 SQL，识别出两个输出列: id, name
// 2. 查询数据库元数据，获取列类型: id → INT8, name → VARCHAR
// 3. 生成匿名结构体:
//    struct _QueryResult {
//        id: i64,
//        name: String,
//    }
// 4. 验证 user_id 的类型与 $1 兼容
// 5. 生成参数绑定和结果映射代码
```

**编译失败示例**:

```rust
// ❌ 列名拼写错误: 编译期报错
sqlx::query!("SELECT idd FROM users WHERE id = $1", 1)
//    error: column "idd" does not exist

// ❌ 类型不匹配: 编译期报错
sqlx::query!("SELECT id FROM users WHERE id = $1", "not_a_number")
//    error: expected types `i64`, found `&str`
```

### 离线模式 (Offline Mode)

在无数据库连接的环境（如 CI）中编译：

```bash
# 1. 有数据库时生成查询元数据
SQLX_OFFLINE=true cargo build

# 2. 提交 .sqlx/ 目录到版本控制
# 3. CI 中无需数据库即可编译
```

```toml
# Cargo.toml
[dependencies]
sqlx = { version = "0.8", features = ["runtime-tokio", "postgres", "offline"] }
```

---

## ⚙️ query! / query_as! 宏用法

### query! 匿名结果

返回匿名结构体，字段由 SQL 推导：

```rust
use sqlx::query;

// 匿名结果: row.id, row.name
let row = query!("SELECT id, name FROM users WHERE id = $1", user_id)
    .fetch_one(&pool)
    .await?;

println!("User: {} (id={})", row.name, row.id);
// row.name 类型: String
// row.id 类型: i64
// 由数据库 schema 自动推导
```

**处理 NULL**: 可为空的列推导为 `Option<T>`

```rust
let row = query!("SELECT name, avatar_url FROM users WHERE id = $1", id)
    .fetch_one(&pool)
    .await?;

// avatar_url 可为空 → Option<String>
if let Some(url) = row.avatar_url {
    println!("Avatar: {}", url);
}
```

### query_as! 映射结构体

将查询结果映射到自定义结构体：

```rust
use sqlx::FromRow;

#[derive(Debug, FromRow)]
struct User {
    id: i64,
    name: String,
    email: String,
    created_at: chrono::DateTime<chrono::Utc>,
}

// 编译时验证结构体字段与查询结果匹配
let user = sqlx::query_as!(User,
    "SELECT id, name, email, created_at FROM users WHERE id = $1",
    user_id
)
.fetch_one(&pool)
.await?;
```

**字段重命名**: 使用 `AS` 或 `#[sqlx(rename = "...")]`

```rust
#[derive(Debug, FromRow)]
struct UserDto {
    #[sqlx(rename = "user_name")]
    name: String,
}

let dto = sqlx::query_as!(UserDto,
    "SELECT name AS user_name FROM users WHERE id = $1",
    id
)
.fetch_one(&pool)
.await?;
```

### query_scalar! 单列查询

返回单一标量值：

```rust
// 计数
let count: i64 = sqlx::query_scalar!("SELECT COUNT(*) FROM users")
    .fetch_one(&pool)
    .await?;

// 单列列表
let names: Vec<String> = sqlx::query_scalar!("SELECT name FROM users")
    .fetch_all(&pool)
    .await?;
```

---

## 🔌 连接池配置

```rust
use sqlx::postgres::{PgPool, PgPoolOptions};
use std::time::Duration;

async fn create_pool(database_url: &str) -> Result<PgPool, sqlx::Error> {
    PgPoolOptions::new()
        // 最大连接数: 根据 CPU 核心数和 DB 负载调整
        .max_connections(100)
        // 最小空闲连接: 保持预热
        .min_connections(5)
        // 获取连接超时
        .acquire_timeout(Duration::from_secs(3))
        // 空闲连接回收时间
        .idle_timeout(Duration::from_secs(600))
        // 连接最大生命周期
        .max_lifetime(Duration::from_secs(1800))
        // 获取前测试连接可用性
        .test_before_acquire(true)
        // 连接后执行初始化语句
        .after_connect(|conn, _meta| {
            Box::pin(async move {
                sqlx::query("SET application_name = 'my_app'")
                    .execute(conn)
                    .await?;
                Ok(())
            })
        })
        .connect(database_url)
        .await
}
```

**连接池最佳实践**:

| 参数 | 生产建议 | 说明 |
|------|----------|------|
| max_connections | CPU * 2 ~ 4 | 避免压垮数据库 |
| min_connections | 5 ~ 10 | 减少冷启动延迟 |
| acquire_timeout | 3s | 防止级联阻塞 |
| idle_timeout | 600s | 平衡复用与资源释放 |
| max_lifetime | 1800s | 定期回收避免连接泄漏 |

---

## 🔄 事务处理

### 基本事务

```rust
use sqlx::{Postgres, Transaction};

async fn transfer(
    pool: &PgPool,
    from: i64,
    to: i64,
    amount: f64,
) -> Result<(), sqlx::Error> {
    // 开启事务
    let mut tx = pool.begin().await?;

    // 使用 &mut *tx 获取内部连接引用
    let balance: f64 = sqlx::query_scalar(
        "SELECT balance FROM accounts WHERE id = $1 FOR UPDATE"
    )
    .bind(from)
    .fetch_one(&mut *tx)
    .await?;

    if balance < amount {
        // 回滚 (也可显式调用 tx.rollback().await?)
        return Err(sqlx::Error::RowNotFound);
    }

    sqlx::query("UPDATE accounts SET balance = balance - $1 WHERE id = $2")
        .bind(amount)
        .bind(from)
        .execute(&mut *tx)
        .await?;

    sqlx::query("UPDATE accounts SET balance = balance + $1 WHERE id = $2")
        .bind(amount)
        .bind(to)
        .execute(&mut *tx)
        .await?;

    // 提交
    tx.commit().await?;
    Ok(())
}
```

### 嵌套事务与保存点

```rust
async fn nested_operation(pool: &PgPool) -> Result<(), sqlx::Error> {
    let mut tx = pool.begin().await?;

    // 外层操作
    sqlx::query("INSERT INTO logs (msg) VALUES ('start')")
        .execute(&mut *tx)
        .await?;

    // 创建保存点 (模拟嵌套事务)
    sqlx::query("SAVEPOINT sp1").execute(&mut *tx).await?;

    match risky_sub_operation(&mut tx).await {
        Ok(_) => {
            sqlx::query("RELEASE SAVEPOINT sp1")
                .execute(&mut *tx)
                .await?;
        }
        Err(_) => {
            sqlx::query("ROLLBACK TO SAVEPOINT sp1")
                .execute(&mut *tx)
                .await?;
            // 保存点回滚，外层事务仍有效
        }
    }

    tx.commit().await
}
```

---

## 🗃️ 迁移系统 (sqlx-cli)

SQLx 提供 `sqlx-cli` 工具管理数据库迁移：

```bash
# 安装
 cargo install sqlx-cli --features postgres

# 创建迁移
sqlx migrate add create_users_table

# 运行迁移
sqlx migrate run --database-url $DATABASE_URL

# 回滚
sqlx migrate revert --database-url $DATABASE_URL
```

**迁移文件结构**:

```text
migrations/
├── 20240101000001_create_users_table.sql
└── 20240101000002_create_posts_table.sql
```

```sql
-- 20240101000001_create_users_table.sql
CREATE TABLE IF NOT EXISTS users (
    id BIGSERIAL PRIMARY KEY,
    name VARCHAR(255) NOT NULL,
    email VARCHAR(255) UNIQUE NOT NULL,
    created_at TIMESTAMPTZ DEFAULT NOW()
);

-- 可选: 添加 down 迁移
-- 回滚时执行 (sqlx migrate revert)
DROP TABLE IF EXISTS users;
```

**程序内嵌入迁移**:

```rust
use sqlx::migrate;

async fn run_migrations(pool: &PgPool) -> Result<(), sqlx::migrate::MigrateError> {
    // 嵌入 migrations/ 目录到二进制
    migrate!("./migrations")
        .run(pool)
        .await
}
```

---

## 📊 与 Sea-ORM / Diesel 对比

| 维度 | SQLx | Sea-ORM | Diesel |
|------|------|---------|--------|
| 抽象层级 | 低 (原始 SQL + 宏) | 高 (ORM) | 中高 (ORM + Query DSL) |
| 类型安全 | 编译期 (宏检查) | 编译期 (代码生成) | 编译期 (类型系统) |
| 异步支持 | ✅ 原生 | ✅ 原生 | ⚠️ 需 `diesel-async` |
| 查询灵活性 | ⭐⭐⭐⭐⭐ 任意 SQL | ⭐⭐⭐ 结构化 API | ⭐⭐⭐⭐ Query DSL |
| 迁移系统 | sqlx-cli (外部) | 内置 Migrator | diesel_cli (外部) |
| 学习曲线 | 较低 (需写 SQL) | 中等 | 较高 (类型系统复杂) |
| 运行时开销 | 最低 | 略高 | 低 |
| 适用场景 | 复杂查询 / 性能敏感 | CRUD 密集型 / 快速开发 | 类型安全偏好 / 同步场景 |

**选择决策树**:

```text
需要复杂 SQL / 手写查询优化? ──是──→ SQLx
                └──否──→ 需要异步 + 快速开发? ──是──→ Sea-ORM
                                      └──否──→ 类型系统极致安全? ──是──→ Diesel
                                                        └──否──→ SQLx (通用)
```

---

## 🔗 参考资源

- [SQLx 官方文档](https://docs.rs/sqlx/latest/sqlx/)
- [SQLx GitHub](https://github.com/launchbadge/sqlx)
- [sqlx-cli 迁移指南](https://github.com/launchbadge/sqlx/blob/main/sqlx-cli/README.md)
- [Sea-ORM 深度解析](sea_orm_deep_dive.md)
- [项目 C02 类型系统模块](../../crates/c02_type_system)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
