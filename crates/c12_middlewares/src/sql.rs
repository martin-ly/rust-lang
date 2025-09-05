use async_trait::async_trait;
use crate::error::Result;

pub struct SqlRow(pub Vec<(String, String)>);

#[async_trait]
pub trait SqlDatabase {
    async fn execute(&self, sql: &str) -> Result<u64>;
    async fn query(&self, sql: &str) -> Result<Vec<SqlRow>>;

    /// 事务接口（最小化示例）：
    /// begin -> execute/query... -> commit 或 rollback
    async fn begin(&self) -> Result<()> { Ok(()) }
    async fn commit(&self) -> Result<()> { Ok(()) }
    async fn rollback(&self) -> Result<()> { Ok(()) }
}

