//! API路由模块
//! 
//! 定义所有API端点的路由

use axum::{
    routing::{get, post, put, delete},
    Router,
};

pub mod v1;

/// 创建API路由
pub fn create_routes() -> Router {
    Router::new()
        .nest("/api/v1", v1::create_v1_routes())
        .route("/health", get(health_check))
        .route("/ready", get(readiness_check))
        .route("/live", get(liveness_check))
}

/// 健康检查端点
async fn health_check() -> &'static str {
    "OK"
}

/// 就绪检查端点
async fn readiness_check() -> &'static str {
    "Ready"
}

/// 存活检查端点
async fn liveness_check() -> &'static str {
    "Alive"
}
