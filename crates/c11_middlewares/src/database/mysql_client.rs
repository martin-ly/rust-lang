#[cfg(feature = "sql-mysql")]
use crate::database::sql::{SqlDatabase, SqlRow};

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
        let mut conn = self.pool.get_conn().await?;
        conn.query_drop(sql).await?;
        let affected = conn.affected_rows();
        Ok(affected)
    }

    async fn query(&self, sql: &str) -> crate::error::Result<Vec<SqlRow>> {
        let mut conn = self.pool.get_conn().await?;
        let rows: Vec<mysql_async::Row> = conn.query(sql).await?;
        let mut out = Vec::with_capacity(rows.len());
        for row in rows {
            let cols = row
                .columns_ref()
                .iter()
                .enumerate()
                .map(|(i, c)| {
                    let name = c.name_str().to_string();
                    let val = row.as_ref(i).map(|v| format!("{v:?}")).unwrap_or_default();
                    (name, val)
                })
                .collect();
            out.push(SqlRow(cols));
        }
        Ok(out)
    }

    async fn begin(&self) -> crate::error::Result<()> {
        self.execute("BEGIN").await.map(|_| ())
    }
    async fn commit(&self) -> crate::error::Result<()> {
        self.execute("COMMIT").await.map(|_| ())
    }
    async fn rollback(&self) -> crate::error::Result<()> {
        self.execute("ROLLBACK").await.map(|_| ())
    }
}
