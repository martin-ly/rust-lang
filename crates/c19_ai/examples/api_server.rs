//! API服务器示例
//! 
//! 展示如何创建一个简单的API服务器

use c19_ai::config::{ConfigManager, ConfigSource};
use axum::{
    extract::State,
    http::StatusCode,
    response::Json,
    routing::{get, post},
    Router,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::net::TcpListener;

#[derive(Clone)]
struct AppState {
    config_manager: Arc<ConfigManager>,
}

#[derive(Serialize)]
struct HealthResponse {
    status: String,
    version: String,
    timestamp: String,
}

#[derive(Serialize)]
struct ConfigResponse {
    key: String,
    value: serde_json::Value,
}

#[derive(Deserialize)]
struct SetConfigRequest {
    key: String,
    value: serde_json::Value,
}

/// 健康检查端点
async fn health_check() -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "healthy".to_string(),
        version: "0.3.0".to_string(),
        timestamp: chrono::Utc::now().to_rfc3339(),
    })
}

/// 获取配置端点
async fn get_config(
    State(state): State<AppState>,
    axum::extract::Path(key): axum::extract::Path<String>,
) -> Result<Json<ConfigResponse>, StatusCode> {
    match state.config_manager.get::<serde_json::Value>(&key).await {
        Ok(Some(value)) => Ok(Json(ConfigResponse { key, value })),
        Ok(None) => Err(StatusCode::NOT_FOUND),
        Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
    }
}

/// 设置配置端点
async fn set_config(
    State(state): State<AppState>,
    Json(request): Json<SetConfigRequest>,
) -> Result<StatusCode, StatusCode> {
    match state.config_manager.set(&request.key, request.value).await {
        Ok(_) => Ok(StatusCode::OK),
        Err(_) => Err(StatusCode::INTERNAL_SERVER_ERROR),
    }
}

/// 获取所有配置端点
async fn get_all_configs(
    State(state): State<AppState>,
) -> Result<Json<serde_json::Value>, StatusCode> {
    let configs = state.config_manager.get_all().await;
    let json_configs = serde_json::to_value(configs)
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;
    Ok(Json(json_configs))
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    env_logger::init();

    // 创建配置管理器
    let config_manager = ConfigManager::new()
        .add_source(ConfigSource::File("examples/config.json".to_string()));

    // 加载配置
    config_manager.load_all().await?;

    // 获取服务器配置
    let host: String = config_manager.get_or_default("server.host", "0.0.0.0".to_string()).await?;
    let port: i64 = config_manager.get_or_default("server.port", 8080).await?;

    // 创建应用状态
    let state = AppState {
        config_manager: Arc::new(config_manager),
    };

    // 创建路由
    let app = Router::new()
        .route("/health", get(health_check))
        .route("/config/:key", get(get_config))
        .route("/config", post(set_config))
        .route("/configs", get(get_all_configs))
        .with_state(state);

    // 启动服务器
    let listener = TcpListener::bind(format!("{}:{}", host, port)).await?;
    println!("服务器启动在 http://{}:{}", host, port);
    println!("健康检查: http://{}:{}/health", host, port);
    println!("获取配置: http://{}:{}/config/<key>", host, port);
    println!("设置配置: POST http://{}:{}/config", host, port);
    println!("所有配置: http://{}:{}/configs", host, port);

    axum::serve(listener, app).await?;

    Ok(())
}