# SQL 数据库

- Postgres（`sql-postgres`）
- MySQL（`sql-mysql`）
- SQLite（`sql-sqlite`）

接口：`sql::SqlDatabase`

示例（以 Postgres 为例）：

```rust
use c12_middlewares::sql::SqlDatabase;

# async fn demo() -> anyhow::Result<()> {
#[cfg(feature = "sql-postgres")]
{
    let db = c12_middlewares::postgres_client::PostgresDb::connect("postgres://user:pass@localhost/db").await?;
    let _ = db.execute("CREATE TABLE t(id INT)").await?;
    let _rows = db.query("SELECT 1").await?;
}
Ok(())
}
```
