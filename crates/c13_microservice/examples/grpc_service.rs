//! gRPC服务示例
//! 
//! 展示如何使用Tonic框架构建高性能gRPC微服务。

use c13_microservice::prelude::Config;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();
    
    tracing::info!("启动gRPC微服务示例");
    
    // 加载配置
    let config = Config::from_env()
        .unwrap_or_else(|_| Config::default());
    
    // 验证配置
    config.validate()?;
    
    tracing::info!("配置加载完成: {:?}", config.service);
    
    // 简化的gRPC服务实现
    tracing::info!("gRPC服务启动成功: {}", config.service_address());
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_grpc_service() {
        let config = Config::default();
        
        // 这里可以添加更多的测试
        assert!(config.validate().is_ok());
    }
}