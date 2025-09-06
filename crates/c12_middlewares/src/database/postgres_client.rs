#[cfg(feature = "sql-postgres")]
use crate::database::sql::{SqlDatabase, SqlRow};

#[cfg(feature = "sql-postgres")]
pub struct PostgresDb {
    client: tokio_postgres::Client,
}

#[cfg(feature = "sql-postgres")]
impl PostgresDb {
    pub async fn connect(url: &str) -> crate::error::Result<Self> {
        let (client, connection) = tokio_postgres::connect(url, tokio_postgres::NoTls).await?;
        tokio::spawn(async move {
            if let Err(e) = connection.await { eprintln!("postgres connection error: {e}"); }
        });
        Ok(Self { client })
    }

    pub async fn connect_with(cfg: crate::config::PostgresConfig) -> crate::error::Result<Self> {
        let url = cfg.url.clone();
        let retry = cfg.retry.clone();
        crate::util::retry_async(&retry, || async {
            let (client, connection) = tokio_postgres::connect(url.as_str(), tokio_postgres::NoTls).await?;
            tokio::spawn(async move {
                if let Err(e) = connection.await { eprintln!("postgres connection error: {e}"); }
            });
            Ok(Self { client })
        }).await
    }
}

#[cfg(feature = "sql-postgres")]
#[async_trait::async_trait]
impl SqlDatabase for PostgresDb {
    async fn execute(&self, sql: &str) -> crate::error::Result<u64> {
        let rows = self.client.execute(sql, &[]).await?;
        Ok(rows)
    }

    async fn query(&self, sql: &str) -> crate::error::Result<Vec<SqlRow>> {
        let rows = self.client.query(sql, &[]).await?;
        let mut out = Vec::with_capacity(rows.len());
        for row in rows {
            let mut cols = Vec::with_capacity(row.len());
            for (i, col) in row.columns().iter().enumerate() {
                let name = col.name().to_string();
                // 将值以字符串形式导出（演示用，真实项目应做类型映射）
                let v: String = match row.try_get::<usize, String>(i) {
                    Ok(s) => s,
                    Err(_) => "<unprintable>".to_string(),
                };
                cols.push((name, v));
            }
            out.push(SqlRow(cols));
        }
        Ok(out)
    }

    async fn begin(&self) -> crate::error::Result<()> {
        let _ = self.execute("BEGIN").await?; Ok(())
    }
    async fn commit(&self) -> crate::error::Result<()> {
        let _ = self.execute("COMMIT").await?; Ok(())
    }
    async fn rollback(&self) -> crate::error::Result<()> {
        let _ = self.execute("ROLLBACK").await?; Ok(())
    }
}

