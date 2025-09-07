//! 服务发现演示示例
//! 
//! 展示如何使用Consul和etcd进行服务发现和配置管理。

use c13_microservice::{
    //Config,
    discovery::{
        Consul,
        Etcd,
    },
};
use tracing_subscriber;
use tracing::info;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();
    
    info!("启动服务发现演示示例");
    
    // Consul连接
    let consul = Consul::new("http://localhost:8500".to_string());
    consul.connect().await?;
    
    // etcd连接
    let etcd = Etcd::new(vec!["http://localhost:2379".to_string()]);
    etcd.connect().await?;
    
    info!("所有服务发现连接成功");
    
    // 模拟服务发现操作
    simulate_discovery_operations().await?;
    
    Ok(())
}

async fn simulate_discovery_operations() -> Result<(), Box<dyn std::error::Error>> {
    info!("开始模拟服务发现操作");
    
    // 模拟Consul操作
    info!("注册服务到Consul");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    info!("从Consul发现服务");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    // 模拟etcd操作
    info!("存储配置到etcd");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    info!("从etcd读取配置");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
    
    info!("服务发现操作完成");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_consul() {
        let consul = Consul::new("test://url".to_string());
        assert_eq!(consul.address, "test://url");
    }
    
    #[tokio::test]
    async fn test_etcd() {
        let etcd = Etcd::new(vec!["test://url".to_string()]);
        assert_eq!(etcd.endpoints, vec!["test://url"]);
    }
}
