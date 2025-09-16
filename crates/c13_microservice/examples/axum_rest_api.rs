//! Axum REST API示例
//!
//! 展示如何使用Axum框架构建现代REST API微服务。

use c13_microservice::{
    axum::AxumMicroservice,
    config::Config,
    //MiddlewareBuilder, CorsConfig, RateLimitConfig,
};
use tracing::info;
use tracing_subscriber;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt().with_env_filter("info").init();

    info!("启动Axum REST API微服务示例");

    // 加载配置
    let config = Config::from_env().unwrap_or_else(|_| Config::default());

    // 验证配置
    config.validate()?;

    info!("配置加载完成: {:?}", config.service);

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
    async fn test_axum_rest_api() {
        let config = Config::default();
        let microservice = AxumMicroservice::new(config);

        // 这里可以添加更多的测试
        assert!(true);
    }
}
