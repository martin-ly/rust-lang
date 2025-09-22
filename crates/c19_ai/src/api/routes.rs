//! API路由配置
//! 
//! 定义所有API端点的路由

use super::handlers::{AppState, *};
use super::health::{health_check as health_check_handler, detailed_health_check, get_metrics};
use axum::{
    routing::{get, post, put, delete},
    Router,
};

/// 创建API路由
pub fn create_routes(state: AppState) -> Router {
    Router::new()
        // 健康检查和统计
        .route("/health", get(health_check_handler))
        .route("/health/detailed", get(detailed_health_check))
        .route("/metrics", get(get_metrics))
        .route("/stats", get(get_stats))
        
        // 配置管理
        .route("/config/:key", get(get_config))
        .route("/config/:key", put(set_config))
        .route("/configs", get(get_all_configs))
        
        // 用户认证
        .route("/auth/login", post(login))
        .route("/auth/register", post(register))
        .route("/users/:user_id", get(get_user_info))
        
        // 模型管理
        .route("/models", get(get_models))
        .route("/models", post(create_model))
        
        // 推理服务
        .route("/inference", post(inference))
        
        .with_state(state)
}

/// 创建带版本前缀的API路由
pub fn create_versioned_routes(state: AppState) -> Router {
    Router::new()
        .nest("/api/v1", create_routes(state))
}

/// 创建完整的应用路由
pub fn create_app_routes(state: AppState) -> Router {
    Router::new()
        .merge(create_versioned_routes(state))
        .route("/", get(health_check_handler))
}