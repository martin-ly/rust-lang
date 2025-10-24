# SQL 数据库

> 适用范围：Rust 1.89+；示例需按需启用特性（`sql-postgres|sql-mysql|sql-sqlite`），风格遵循 `../../c10_networks/docs/STYLE.md`。


## 📊 目录

- [支持矩阵与特性](#支持矩阵与特性)
- [快速开始（Postgres）](#快速开始postgres)
- [MySQL 与 SQLite 示例](#mysql-与-sqlite-示例)
- [事务（Transaction）](#事务transaction)
- [批量执行与参数化](#批量执行与参数化)
  - [参数化查询示例](#参数化查询示例)
- [连接、超时与重试](#连接超时与重试)
  - [连接池调优](#连接池调优)
  - [隔离级别与一致性](#隔离级别与一致性)
- [错误与类型映射](#错误与类型映射)
- [迁移与模式管理](#迁移与模式管理)
- [性能建议](#性能建议)
- [FAQ](#faq)


- Postgres（`sql-postgres`）
- MySQL（`sql-mysql`）
- SQLite（`sql-sqlite`）

接口：`sql::SqlDatabase`

## 支持矩阵与特性

- `sql-postgres`: 连接/查询/执行/事务/批量执行/基础类型映射
- `sql-mysql`: 连接/查询/执行/事务/基础类型映射（批量执行依实现约束）
- `sql-sqlite`: 轻量内嵌/文件数据库，支持查询/执行/事务
- `obs`: 集成 tracing span（建议与 `tokio` 搭配）

> 选择最小可用集：生产建议 `sql-postgres` 或 `sql-mysql`，本地快速验证可用 `sql-sqlite`。

## 快速开始（Postgres）

```rust
use c12_middlewares::sql::SqlDatabase;

# async fn demo() -> anyhow::Result<()> {
#[cfg(feature = "sql-postgres")]
{
    let db = c12_middlewares::postgres_client::PostgresDb::connect(
        "postgres://user:pass@localhost/db"
    ).await?;

    // DDL / DML
    let _ = db.execute("CREATE TABLE IF NOT EXISTS t(id INT)").await?;
    let _ = db.execute("INSERT INTO t(id) VALUES (1)").await?;

    // 查询
    let rows = db.query("SELECT id FROM t").await?;
    for row in rows {
        let id: i64 = row.get_int("id").unwrap_or_default();
        assert_eq!(id, 1);
    }
}
Ok(())
}
```

## MySQL 与 SQLite 示例

```rust
# async fn demo_mysql() -> anyhow::Result<()> {
#[cfg(feature = "sql-mysql")]
{
    let db = c12_middlewares::mysql_client::MySqlDb::connect(
        "mysql://user:pass@127.0.0.1:3306/db"
    ).await?;
    db.execute("CREATE TABLE IF NOT EXISTS t(id INT)").await?;
    db.execute("INSERT INTO t(id) VALUES (1)").await?;
    let rows = db.query("SELECT id FROM t").await?;
    let _ = rows.len();
}
Ok(())
}
```

```rust
# async fn demo_sqlite() -> anyhow::Result<()> {
#[cfg(feature = "sql-sqlite")]
{
    // 内存数据库："sqlite::memory:"；也可使用文件路径，如 "sqlite://data.db"
    let db = c12_middlewares::sqlite_client::SqliteDb::connect(
        "sqlite::memory:"
    ).await?;
    db.execute("CREATE TABLE t(id INTEGER)").await?;
    db.execute("INSERT INTO t(id) VALUES (1)").await?;
    let rows = db.query("SELECT id FROM t").await?;
    let _ = rows.len();
}
Ok(())
}
```

## 事务（Transaction）

```rust
# async fn tx() -> anyhow::Result<()> {
#[cfg(any(feature = "sql-postgres", feature = "sql-mysql", feature = "sql-sqlite"))]
{
    // 以 Postgres 为例；MySQL/SQLite 请替换为对应客户端
    let db = c12_middlewares::postgres_client::PostgresDb::connect(
        "postgres://user:pass@localhost/db"
    ).await?;
    db.begin().await?;
    if let Err(e) = db.execute("INSERT INTO users (name) VALUES ('Alice')").await {
        db.rollback().await?;
        return Err(e.into());
    }
    db.commit().await?;
}
Ok(())
}
```

- 隔离级别：当前示例使用后端默认隔离级别；如需指定，参考对应后端客户端扩展接口。
- 错误即回滚：建议显式处理错误，确保 `commit/rollback` 成对出现。

## 批量执行与参数化

- 批量执行：减少往返提高吞吐（支持度因后端而异）

```rust
# async fn batch_exec(db: &impl c12_middlewares::sql::SqlDatabase) -> anyhow::Result<()> {
let stmts = [
    "INSERT INTO logs (msg) VALUES ('a')",
    "INSERT INTO logs (msg) VALUES ('b')",
];
let results = db.batch_execute(&stmts).await?;
let _ = results.len();
Ok(())
}
```

- 参数化查询：请优先使用参数化（示例接口以后端实现为准），避免 SQL 注入。

### 参数化查询示例

```rust
# async fn param_query(db: &impl c12_middlewares::sql::SqlDatabase) -> anyhow::Result<()> {
// 伪代码：实际接口以后端实现为准
let name = "Alice";
let age: i64 = 30;
let rows = db.query_params("SELECT id FROM users WHERE name=$1 AND age>$2", &[&name, &age]).await?;
let _ = rows.len();
Ok(())
}
```

## 连接、超时与重试

- 连接：提供 `connect(url)` 与 `connect_with(config)` 两种方式
- 超时：建议通过后端配置或连接选项设置（连接超时 / 查询超时）
- 重试：对幂等的只读查询可结合 `util::retry_async`，避免对非幂等写操作盲目重试

```rust
use c12_middlewares::config::PostgresConfig;

# async fn cfg() -> anyhow::Result<()> {
#[cfg(feature = "sql-postgres")]
{
    let cfg = PostgresConfig::new("postgres://user:pass@localhost/db")
        .with_connect_timeout_ms(3_000)
        .with_query_timeout_ms(5_000)
        .with_pool_min_max(1, 8);
    let db = c12_middlewares::postgres_client::PostgresDb::connect_with(cfg).await?;
    let _ = db.query("SELECT 1").await?;
}
Ok(())
}
```

### 连接池调优

- 起步建议：`min=1, max=8`；根据 P95/P99 延迟与池等待队列调整
- 将长查询/报表负载与在线事务分离为不同池或连接实例

### 隔离级别与一致性

- Postgres 默认 `READ COMMITTED`；需要更强一致性可选择 `REPEATABLE READ` 或 `SERIALIZABLE`
- MySQL（InnoDB）默认 `REPEATABLE READ`；避免长事务导致的锁等待与死锁
- SQLite 受单写者限制，适合嵌入式/边缘与只读负载

```sql
-- Postgres 设置事务隔离级别示例
BEGIN TRANSACTION ISOLATION LEVEL REPEATABLE READ;
-- ...
COMMIT;
```

## 错误与类型映射

- 统一错误类型：`c12_middlewares::Error::{Postgres, MySql, Sqlite, ...}`
- 常用类型读取：`row.get_int("col")`、`row.get_string("col")`、`row.get_float("col")`
- 空值处理：返回 `Option<T>` 或为 `unwrap_or` 提供缺省

```rust
let rows = db.query("SELECT id, name, age FROM users").await?;
for row in rows {
    let id: i64 = row.get_int("id").unwrap_or(0);
    let name: &str = row.get_string("name").unwrap_or("");
    let age: f64 = row.get_float("age").unwrap_or(0.0);
}
```

## 迁移与模式管理

- 建议使用外部迁移工具（如 `sqlx-cli`、`refinery`、`liquibase`）；在本库中保持“运行期访问”与“迁移执行”解耦
- 在 CI 中加入“只读检查”与“迁移校验”，与应用启动顺序解耦

## 性能建议

- 优先使用参数化与批量
- 为热点查询添加索引，避免 N+1
- 合理设置连接池大小与超时，观察 P95/P99 指标

## FAQ

- Q: 如何在本地快速验证？
  - A: 选择 `sql-sqlite` 并使用 `sqlite::memory:`，零依赖、启动快。
- Q: 如何避免长事务导致锁等待？
  - A: 将大事务拆分，减少锁时间；只在必要范围内开启事务。
- Q: 是否支持预编译语句与占位参数？
  - A: 具体以后端实现为准；优先使用参数化接口，避免字符串拼接。
