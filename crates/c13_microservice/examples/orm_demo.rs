//! ORM演示示例
//! 
//! 展示如何使用SQLx、Diesel和SeaORM进行数据库操作。

use c13_microservice::{
    //Config,
    lib_simple::orm::{SqlxDatabase, DieselDatabase, SeaOrmDatabase},
};
use tracing_subscriber;
use tracing::info;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();
    
    info!("启动ORM演示示例");
    
    // SQLx数据库连接
    let sqlx_db = SqlxDatabase::new(
        "postgresql://user:password@localhost:5432/microservice".to_string()
    );
    sqlx_db.connect().await?;
    
    // Diesel数据库连接
    let diesel_db = DieselDatabase::new(
        "postgresql://user:password@localhost:5432/microservice".to_string()
    );
    diesel_db.connect().await?;
    
    // SeaORM数据库连接
    let sea_orm_db = SeaOrmDatabase::new(
        "postgresql://user:password@localhost:5432/microservice".to_string()
    );
    sea_orm_db.connect().await?;
    
    info!("所有ORM数据库连接成功");
    
    // 模拟数据库操作
    simulate_database_operations().await?;
    
    Ok(())
}

async fn simulate_database_operations() -> Result<(), Box<dyn std::error::Error>> {
    info!("开始模拟数据库操作");
    
    // 模拟SQLx操作
    info!("执行SQLx查询操作");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    // 模拟Diesel操作
    info!("执行Diesel查询操作");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    // 模拟SeaORM操作
    info!("执行SeaORM查询操作");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    info!("数据库操作完成");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_sqlx_database() {
        let db = SqlxDatabase::new("test://url".to_string());
        assert_eq!(db.url, "test://url");
    }
    
    #[tokio::test]
    async fn test_diesel_database() {
        let db = DieselDatabase::new("test://url".to_string());
        assert_eq!(db.url, "test://url");
    }
    
    #[tokio::test]
    async fn test_sea_orm_database() {
        let db = SeaOrmDatabase::new("test://url".to_string());
        assert_eq!(db.url, "test://url");
    }
}
