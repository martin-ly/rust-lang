> **EN**: sqlx — Compile-Time Checked Async SQL Toolkit
> **Summary**: sqlx is the Rust SQL toolkit that uses procedural macros to check SQL queries against a live database schema at compile time, providing type-safe async database access without an ORM DSL.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **生态版本**: sqlx 0.9.0
> **Bloom 层级**: L6
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **P** — Procedure
> **前置概念**:
> [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) ·
> [Lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) ·
> [Generics](../../02_intermediate/01_generics/01_generics.md) ·
> [Async](../../03_advanced/01_async/01_async.md) ·
> [Procedural Macros](../../02_intermediate/06_macros_and_metaprogramming/05_procedural_macros.md)
> **后置概念**:
> [Core Crates Index](./01_core_crates.md) ·
> [Database Access](../06_data_and_distributed/02_database_access.md) ·
> [Database Systems](../06_data_and_distributed/04_database_systems.md)
> **主要来源**:
> [sqlx on crates.io](https://crates.io/crates/sqlx) (P2) ·
> [docs.rs/sqlx](https://docs.rs/sqlx) (P2) ·
> [sqlx GitHub](https://github.com/launchbadge/sqlx) (P2) ·
> [The Rust Reference — Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html) (P0) ·
> [The Rust Async Book](https://rust-lang.github.io/async-book/) (P0)

# sqlx：编译期类型安全的异步 SQL 工具包

## 一、权威定义

> **[sqlx on crates.io](https://crates.io/crates/sqlx)** 官方定义：
> “The Rust SQL Toolkit. An async, pure Rust SQL crate featuring compile-time checked queries without a DSL. Supports PostgreSQL, MySQL, and SQLite.”

**核心判定**：sqlx 不是传统 ORM，而是一个**异步、纯 Rust 的 SQL 工具包**。它通过过程宏（procedural macro）在编译期连接数据库，验证 SQL 语法、返回列类型与参数类型，从而把大量运行时 SQL 错误提前到编译期暴露。它是 Rust “宏系统 + 类型安全”理念在数据库访问领域的工业级实现。

## 二、关键类型与 Traits

| 类型 / Trait | 角色与作用 |
|:---|:---|
| `Pool<DB>` | 数据库连接池，内部基于 `Arc`，可低成本 `Clone` 并在多个任务间共享。 |
| `PgPool` / `MySqlPool` / `SqlitePool` | 对应 PostgreSQL、MySQL、SQLite 的连接池类型别名。 |
| `query!` | 编译期检查 SQL 与参数类型的宏；返回匿名结构体或 `()`。 |
| `query_as!` | 编译期检查并将结果行映射到指定 Rust 类型的宏。 |
| `migrate!` | 在编译期嵌入 `migrations/` 目录并生成迁移管理器的宏。 |
| `FromRow` | 允许手动将数据库行映射到 Rust 结构体的 trait；`query_as!` 内部依赖它。 |
| `Executor` | 抽象“可执行 SQL 的对象”，`Pool`、`Connection`、`Transaction` 均实现它。 |
| `Transaction<'_, DB>` | 事务句柄，必须通过 `commit()` 或 `rollback()` 结束。 |

## 三、惯用法与示例

### 3.1 最小可用示例：单条查询

```rust,ignore
// Cargo.toml
// [dependencies]
// sqlx = { version = "0.9", features = ["runtime-tokio", "postgres"] }
// tokio = { version = "1", features = ["full"] }

use sqlx::PgPool;

#[tokio::main]
async fn main() -> Result<(), sqlx::Error> {
    let pool = PgPool::connect("postgres://user:pass@localhost/db").await?;
    let id = 1i64;

    // 编译期会检查 SQL 语法、$1 类型与 id 类型是否匹配、返回列 name 是否存在
    let row = sqlx::query!("SELECT name FROM users WHERE id = $1", id)
        .fetch_one(&pool)
        .await?;

    println!("user name: {}", row.name.unwrap_or_default());
    Ok(())
}
```

### 3.2 实战惯用法：Repository + 事务

```rust,ignore
// Cargo.toml
// sqlx = { version = "0.9", features = ["runtime-tokio", "postgres"] }

use sqlx::{PgPool, query, query_as, Transaction, Postgres};

#[derive(sqlx::FromRow)]
struct User {
    id: i64,
    name: String,
}

struct UserRepo {
    pool: PgPool,
}

impl UserRepo {
    async fn find(&self, id: i64) -> Result<Option<User>, sqlx::Error> {
        query_as!(User, "SELECT id, name FROM users WHERE id = $1", id)
            .fetch_optional(&self.pool)
            .await
    }

    async fn rename(&self, id: i64, new_name: &str) -> Result<(), sqlx::Error> {
        // begin() 获取事务句柄，必须 mut 才能执行后续查询
        let mut tx: Transaction<'_, Postgres> = self.pool.begin().await?;

        query!("UPDATE users SET name = $1 WHERE id = $2", new_name, id)
            .execute(&mut *tx)
            .await?;

        tx.commit().await?;
        Ok(())
    }
}
```

## 四、常见陷阱与边界测试

### 陷阱 1：未提供编译期数据库连接

`query!` / `query_as!` 在编译时需要访问数据库以验证 SQL。如果既没有设置 `DATABASE_URL`，也没有使用 `cargo sqlx prepare` 生成的离线数据，编译会直接失败。

❌ **错误做法**

```rust,ignore
// 环境变量 DATABASE_URL 未设置，也没有 sqlx-data.json
let row = sqlx::query!("SELECT name FROM users WHERE id = $1", 1i64)
    .fetch_one(&pool)
    .await?;
```

✅ **正确做法**

```bash
# 开发/CI 中设置 DATABASE_URL
export DATABASE_URL="postgres://user:pass@localhost/db"

# 或在 CI 中使用离线模式
cargo sqlx prepare -- --lib
# 并启用 sqlx 的 offline feature
```

```toml
[dependencies]
sqlx = { version = "0.9", features = ["runtime-tokio", "postgres", "offline"] }
```

### 陷阱 2：sqlx 0.9 不再提供组合式 runtime+TLS feature

0.9 版本删除了 `runtime-tokio-native-tls` 这类组合 feature，必须分别声明运行时和 TLS 后端。

❌ **错误做法**

```toml
[dependencies]
sqlx = { version = "0.9", features = ["runtime-tokio-native-tls", "postgres"] }
```

✅ **正确做法**

```toml
[dependencies]
sqlx = { version = "0.9", features = [
    "runtime-tokio",
    "tls-rustls",
    "postgres",
] }
```

也可选用 `tls-native-tls`、`runtime-async-std` 或 `runtime-tokio-current-thread`。

### 陷阱 3：`query_as!` 的列名与结构体字段不匹配

`query_as!` 要求查询返回的列名与目标结构体字段名一一对应；类型不一致或列缺失都会在编译期报错。

❌ **错误做法**

```rust,ignore
#[derive(sqlx::FromRow)]
struct User {
    id: i64,
    username: String, // 数据库列名为 name
}

// 编译错误：列 name 无法映射到字段 username
let user = sqlx::query_as!(User, "SELECT id, name FROM users WHERE id = $1", 1i64)
    .fetch_one(&pool)
    .await?;
```

✅ **正确做法**

```rust,ignore
#[derive(sqlx::FromRow)]
struct User {
    id: i64,
    name: String,
}

let user = sqlx::query_as!(User, "SELECT id, name FROM users WHERE id = $1", 1i64)
    .fetch_one(&pool)
    .await?;
```

或者在 SQL 中使用别名：`SELECT id, name AS username FROM users ...`。

## 五、版本说明

- **当前稳定版本**：`sqlx 0.9.0`（发布于 2026-05；crates.io 标注最低 Rust 版本为 1.94.0）。
- **MSRV 政策**：明确声明于 `Cargo.toml` 的 `rust-version`，本项目使用 Rust 1.97.0+，完全兼容。
- **0.9 关键变更**：
  - 删除组合式 `runtime-*-tls` feature，运行时与 TLS 必须分开选择。
  - 增加 `runtime-tokio-current-thread` 等更细粒度的运行时选项。
- **Edition 2024 注意**：async 闭包与 `async fn` in trait 已稳定，可与 sqlx 的 async API 自然配合；但 `query!` / `query_as!` 仍是过程宏，仍需编译期数据库连接或离线数据。
- **离线模式**：生产/CI 推荐 `cargo sqlx prepare` 生成 `sqlx-data.json`，避免在构建环境暴露真实数据库。

## 六、思维导图（Mindmap）

```mermaid
mindmap
  root((sqlx))
    目的定位
      异步纯 Rust SQL 工具包
      无 ORM DSL
      编译期查询检查
    核心抽象
      Pool / PgPool / MySqlPool / SqlitePool
      Executor / Transaction
      FromRow
    关键宏
      query!
      query_as!
      migrate!
    数据库后端
      PostgreSQL
      MySQL
      SQLite
    迁移与离线
      cargo sqlx prepare
      sqlx-data.json
      offline feature
    常见陷阱
      DATABASE_URL / 离线数据缺失
      0.9 feature 拆分
      列名-字段名不匹配
```

## 七、嵌入式测验

### 测验 1：`query!` 的编译期保证（理解层）

`sqlx::query!` 在编译期主要保证什么？

- A. 数据库连接在运行时一定可用
- B. SQL 语法与返回列类型符合数据库 schema
- C. 查询计划已被优化
- D. 所有索引已建立

<details>
<summary>✅ 答案</summary>

**B. SQL 语法与返回列类型符合数据库 schema**。

`query!` 在编译期连接数据库，验证 SQL 语法、参数类型、返回列名与类型；它不能保证运行时连接可用（A）、查询计划优化（C）或索引存在（D）。
</details>

---

### 测验 2：sqlx 0.9 的合法 feature 组合（应用层）

在 sqlx 0.9 中，使用 Tokio + PostgreSQL + rustls 时应选择哪些 feature？

- A. `runtime-tokio`
- B. `tls-rustls`
- C. `postgres`
- D. `runtime-tokio-native-tls`

<details>
<summary>✅ 答案</summary>

**A、B、C**。

0.9 删除了 `runtime-tokio-native-tls` 这类组合 feature，必须分别声明运行时（`runtime-tokio`）、TLS 后端（`tls-rustls` / `tls-native-tls`）和数据库后端（`postgres` / `mysql` / `sqlite`）。
</details>

---

### 测验 3：`query_as!` 的字段映射（应用层）

判断正误：`query_as!(User, "SELECT id, name FROM users ...")` 要求 `User` 的字段名与查询列名一致，但列的顺序可以任意。

<details>
<summary>✅ 答案</summary>

**错误**。

`query_as!` 主要按**名称**将列映射到结构体字段，因此列的顺序通常不影响映射；但字段名必须与列名（或别名）完全一致，且类型必须兼容。最安全的做法是让字段名、列名、类型全部对齐。
</details>

---

### 测验 4：编译期检查的前提条件（理解层）

在没有 `DATABASE_URL` 环境变量且未启用离线模式的情况下，使用 `query!` 会发生什么？

- A. 编译通过，运行时才报错
- B. 编译失败，提示无法验证 SQL
- C. 自动连接到本地默认数据库
- D. 退化为普通字符串 SQL，不再做类型检查

<details>
<summary>✅ 答案</summary>

**B. 编译失败，提示无法验证 SQL**。

`query!` / `query_as!` 是编译期宏，需要 `DATABASE_URL` 或 `sqlx-data.json` 才能验证查询；两者都缺失时会在编译期报错。
</details>

## 八、国际权威来源

- **P0 — Rust 官方文档**
  - [The Rust Reference — Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)：解释 `query!` / `query_as!` 背后的过程宏机制。
  - [The Rust Async Book](https://rust-lang.github.io/async-book/)：sqlx 基于 async/await 与 `Future` 的根基。
  - 状态：官方域名可访问，属 P0 权威来源。

- **P2 — Crate 官方文档与仓库**
  - [sqlx on crates.io](https://crates.io/crates/sqlx)：版本、MSRV、下载量与 feature 说明（已验证可访问，v0.9.0）。
  - [docs.rs/sqlx](https://docs.rs/sqlx)：API 文档与类型说明（在线可访问）。
  - [launchbadge/sqlx on GitHub](https://github.com/launchbadge/sqlx)：源码、CHANGELOG、迁移示例（在线可访问）。
  - [sqlx.rs](https://sqlx.rs)：项目官网与入门指南（在线可访问）。

## 九、相关概念链接

| 概念 | 文件 | 关系 |
|:---|:---|:---|
| 所有权 | [`../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) | `Pool` 与 `Transaction` 的生命周期管理根基 |
| 生命周期 | [`../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) | 连接借用与 `Transaction<'_>` |
| 泛型 | [`../../02_intermediate/01_generics/01_generics.md`](../../02_intermediate/01_generics/01_generics.md) | `Pool<DB>`、`Executor` 等泛型抽象 |
| Async 编程 | [`../../03_advanced/01_async/01_async.md`](../../03_advanced/01_async/01_async.md) | sqlx 的异步 API 根基 |
| 过程宏 | [`../../02_intermediate/06_macros_and_metaprogramming/05_procedural_macros.md`](../../02_intermediate/06_macros_and_metaprogramming/05_procedural_macros.md) | `query!` / `query_as!` 的实现机制 |
| Core Crates 索引 | [`./01_core_crates.md`](./01_core_crates.md) | 本页所属的 crate 谱系导览 |
| 数据库访问 | [`../06_data_and_distributed/02_database_access.md`](../06_data_and_distributed/02_database_access.md) | Rust 数据库访问模式对比 |
| 数据库系统 | [`../06_data_and_distributed/04_database_systems.md`](../06_data_and_distributed/04_database_systems.md) | 关系型/NoSQL 数据库的工程选型 |
| Rust vs C# | [`../../05_comparative/02_managed_languages/06_rust_vs_csharp.md`](../../05_comparative/02_managed_languages/06_rust_vs_csharp.md) | 类型安全数据库访问与企业生态的跨语言对比。

## 国际化权威来源补充（International Authority Sources）

- https://dl.acm.org/doi/book/10.5555/186897
