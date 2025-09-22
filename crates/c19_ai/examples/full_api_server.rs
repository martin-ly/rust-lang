//! 完整的API服务器示例
//! 
//! 展示如何使用完整的API系统

use c19_ai::api::{create_app_routes, handlers::AppState};
use c19_ai::config::{ConfigManager, ConfigSource};
use c19_ai::auth::manager::AuthManager;
use c19_ai::database::DatabaseManager;
use c19_ai::cache::manager::CacheManager;
use c19_ai::storage::manager::StorageManager;
use axum::Router;
use std::sync::Arc;
use std::time::SystemTime;
use tokio::net::TcpListener;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    env_logger::init();

    // 创建配置管理器
    let config_manager = ConfigManager::new()
        .add_source(ConfigSource::File("examples/config.json".to_string()));
    config_manager.load_all().await?;

    // 创建各个管理器
    let auth_manager = Arc::new(AuthManager::new());
    let db_manager = Arc::new(DatabaseManager::new());
    let cache_manager = Arc::new(CacheManager::new());
    let storage_manager = Arc::new(StorageManager::new());

    // 创建应用状态
    let state = AppState {
        config_manager: Arc::new(config_manager),
        auth_manager,
        db_manager,
        cache_manager,
        storage_manager,
        start_time: SystemTime::now(),
    };

    // 创建路由
    let app = create_app_routes(state);

    // 获取服务器配置
    let host: String = "0.0.0.0".to_string();
    let port: i64 = 8080;

    // 启动服务器
    let listener = TcpListener::bind(format!("{}:{}", host, port)).await?;
    println!("🚀 C19 AI API服务器启动在 http://{}:{}", host, port);
    println!("📊 健康检查: http://{}:{}/health", host, port);
    println!("📈 统计信息: http://{}:{}/api/v1/stats", host, port);
    println!("⚙️  配置管理: http://{}:{}/api/v1/configs", host, port);
    println!("🔐 用户认证: http://{}:{}/api/v1/auth/login", host, port);
    println!("🤖 模型管理: http://{}:{}/api/v1/models", host, port);
    println!("🧠 推理服务: http://{}:{}/api/v1/inference", host, port);

    axum::serve(listener, app).await?;

    Ok(())
}
