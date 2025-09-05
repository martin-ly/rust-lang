#[cfg(feature = "sql-mysql")]
use crate::sql::{SqlDatabase, SqlRow};

#[cfg(feature = "sql-mysql")]
pub struct MysqlDb {
    pool: mysql_async::Pool,
}

#[cfg(feature = "sql-mysql")]
impl MysqlDb {
    pub async fn connect(url: &str) -> crate::error::Result<Self> {
        let pool = mysql_async::Pool::new(url);
        Ok(Self { pool })
    }
}

#[cfg(feature = "sql-mysql")]
#[async_trait::async_trait]
impl SqlDatabase for MysqlDb {
    async fn execute(&self, sql: &str) -> crate::error::Result<u64> {
        #[cfg(feature = "obs")]
        let _span = tracing::info_span!("mysql_execute").entered();
        let mut conn = self.pool.get_conn().await?;
        crate::util::maybe_timeout(5_000, async {
            conn.query_drop(sql).await?;
            Ok(())
        }).await?;
        let affected = conn.affected_rows();
        Ok(affected)
    }

    async fn query(&self, sql: &str) -> crate::error::Result<Vec<SqlRow>> {
        #[cfg(feature = "obs")]
        let _span = tracing::info_span!("mysql_query").entered();
        let mut conn = self.pool.get_conn().await?;
        let rows: Vec<mysql_async::Row> = crate::util::maybe_timeout(5_000, async { Ok(conn.query(sql).await?) }).await?;
        let mut out = Vec::with_capacity(rows.len());
        for row in rows {
            let cols = row.columns_ref().iter().enumerate().map(|(i, c)| {
                let name = c.name_str().to_string();
                let val = row.as_ref(i).map(|v| format!("{v:?}")).unwrap_or_default();
                (name, val)
            }).collect();
            out.push(SqlRow(cols));
        }
        Ok(out)
    }

    async fn begin(&self) -> crate::error::Result<()> { self.execute("BEGIN").await.map(|_| ()) }
    async fn commit(&self) -> crate::error::Result<()> { self.execute("COMMIT").await.map(|_| ()) }
    async fn rollback(&self) -> crate::error::Result<()> { self.execute("ROLLBACK").await.map(|_| ()) }
}

