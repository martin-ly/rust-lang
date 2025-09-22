//! 配置管理示例
//! 
//! 展示如何使用配置管理系统

use c19_ai::config::{ConfigManager, ConfigSource};
// use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建配置管理器
    let config_manager = ConfigManager::new()
        .add_source(ConfigSource::File("examples/config.json".to_string()));

    // 加载配置
    config_manager.load_all().await?;

    // 获取配置值
    let server_host: Option<String> = config_manager.get("server.host").await?;
    let server_port: Option<i64> = config_manager.get("server.port").await?;
    let cache_ttl: u64 = config_manager.get_or_default("cache.default_ttl", 3600).await?;

    println!("服务器配置:");
    println!("  主机: {:?}", server_host);
    println!("  端口: {:?}", server_port);
    println!("  缓存TTL: {} 秒", cache_ttl);

    // 设置配置值
    config_manager.set("custom.setting", "example_value").await?;
    
    // 检查配置是否存在
    if config_manager.has("custom.setting").await {
        println!("自定义配置已设置");
    }

    // 获取所有配置
    let all_configs = config_manager.get_all().await;
    println!("总配置项数量: {}", all_configs.len());

    // 显示部分配置
    for (key, value) in all_configs.iter().take(5) {
        println!("  {}: {:?}", key, value);
    }

    Ok(())
}
