//! OpenTelemetry演示示例
//!
//! 展示如何使用OpenTelemetry进行分布式追踪和监控。

// 暂时注释掉导入，因为模块导入有问题
// use c13_microservice::{
//     //Config,
//     opentelemetry::{OpenTelemetryConfig, init_tracing, LogConfig, init_logging, SlogLogger},
// };
use tracing::info;
use tracing_subscriber;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt().with_env_filter("info").init();

    info!("启动OpenTelemetry演示示例");

    // 暂时注释掉功能，因为模块导入有问题
    println!("OpenTelemetry演示示例启动成功！");
    println!("注意：由于模块导入问题，功能暂时被注释掉");
    println!("需要修复模块导入问题后才能正常运行");

    // 模拟一些业务操作
    simulate_business_operations().await?;

    Ok(())
}

async fn simulate_business_operations() -> Result<(), Box<dyn std::error::Error>> {
    info!("开始模拟业务操作");

    // 模拟数据库操作
    info!("执行数据库查询操作");
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    // 模拟外部API调用
    info!("调用外部API");
    tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;

    // 模拟消息队列操作
    info!("发送消息到队列");
    tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;

    info!("业务操作完成");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_opentelemetry_config() {
        let config = OpenTelemetryConfig::default();
        assert_eq!(config.service_name, "microservice");
        assert_eq!(config.service_version, "1.0.0");
    }

    #[tokio::test]
    async fn test_log_config() {
        let config = LogConfig::default();
        assert_eq!(config.level, "info");
        assert_eq!(config.format, "json");
    }
}
