//! 简化的Axum REST API示例
//!
//! 展示如何使用简化的Axum框架构建现代REST API微服务。

use c13_microservice::lib_simple::{AxumMicroservice, Config};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt().with_env_filter("info").init();

    tracing::info!("启动简化的Axum REST API微服务示例");

    // 加载配置
    let config = Config::from_env().unwrap_or_else(|_| Config::default());

    // 验证配置
    config.validate()?;

    tracing::info!("配置加载完成: {:?}", config.service);

    // 创建微服务
    let microservice = AxumMicroservice::new(config);

    // 启动服务器
    microservice.serve().await?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_simple_axum() {
        let config = Config::default();
        let microservice = AxumMicroservice::new(config);

        // 这里可以添加更多的测试
        assert!(true);
    }
}
