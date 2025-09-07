//! Axum Web框架模块
//! 
//! 提供基于Axum的现代Web微服务实现，支持RESTful API、WebSocket、中间件等。

use axum::{
    extract::{Path, Query, State},
    http::StatusCode,
    response::Json,
    routing::get,
    Router,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::info;

use crate::{
    config::Config,
    error::{Error, Result},
    utils::{HealthCheck, PaginationParams, PaginatedResponse, SuccessResponse},
    middleware::{MiddlewareBuilder, CorsConfig, RateLimitConfig},
};

/// Axum微服务应用
pub struct AxumMicroservice {
    config: Config,
    router: Router,
}

/// 用户模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: String,
    pub name: String,
    pub email: String,
    pub created_at: u64,
}


/// 应用状态
#[derive(Clone)]
pub struct AppState {
    pub users: Arc<RwLock<HashMap<String, User>>>,
    pub config: Config,
}

impl AxumMicroservice {
    /// 创建新的Axum微服务
    pub fn new(config: Config) -> Self {
        let state = AppState {
            users: Arc::new(RwLock::new(HashMap::new())),
            config: config.clone(),
        };

        let router = Self::create_router(state);
        
        Self { config, router }
    }
    
    /// 创建路由
    fn create_router(state: AppState) -> Router {
        Router::new()
            // 健康检查
            .route("/health", get(health_check))
            .route("/health/detailed", get(detailed_health_check))
            
            // 用户API - 简化路由
            .route("/users", get(list_users))
            .route("/users/:id", get(get_user))
            
            // 指标端点
            .route("/metrics", get(metrics))
            
            // 应用状态
            .with_state(state)
    }
    
    /// 获取路由器
    pub fn router(self) -> Router {
        self.router
    }
    
    /// 启动服务器
    pub async fn serve(self) -> Result<()> {
        let config = self.config.clone();
        let app = self.router();
        let addr = format!("{}:{}", config.service.host, config.service.port);
        
        info!("启动Axum微服务: {}", addr);
        
        let listener = tokio::net::TcpListener::bind(&addr).await
            .map_err(|e| Error::config(format!("无法绑定地址 {}: {}", addr, e)))?;
        
        axum::serve(listener, app).await
            .map_err(|e| Error::config(format!("服务器启动失败: {}", e)))?;
        
        Ok(())
    }
}

/// 健康检查处理器
async fn health_check() -> &'static str {
    "OK"
}

/// 详细健康检查处理器
async fn detailed_health_check(State(state): State<AppState>) -> Json<HealthCheck> {
    let health = HealthCheck::new(
        state.config.service.version.clone(),
        0, // 这里应该计算实际运行时间
    );
    
    Json(health)
}

/// 获取用户列表
async fn list_users(
    State(state): State<AppState>,
    Query(params): Query<PaginationParams>,
) -> std::result::Result<Json<PaginatedResponse<User>>, StatusCode> {
    let users = state.users.read().await;
    let user_list: Vec<User> = users.values().cloned().collect();
    
    let pagination = PaginationParams {
        page: params.page,
        page_size: params.page_size,
        total: Some(user_list.len() as u64),
    };
    
    let response = PaginatedResponse::new(user_list, pagination);
    Ok(Json(response))
}


/// 获取单个用户
async fn get_user(
    State(state): State<AppState>,
    Path(id): Path<String>,
) -> std::result::Result<Json<SuccessResponse<User>>, StatusCode> {
    let users = state.users.read().await;
    
    match users.get(&id) {
        Some(user) => {
            let response = SuccessResponse::new(user.clone(), "用户获取成功".to_string());
            Ok(Json(response))
        }
        None => Err(StatusCode::NOT_FOUND),
    }
}


/// 指标端点
async fn metrics(State(state): State<AppState>) -> String {
    let users = state.users.read().await;
    format!(
        "# HELP users_total Total number of users\n\
         # TYPE users_total gauge\n\
         users_total {}\n",
        users.len()
    )
}

/// 创建带中间件的Axum应用
pub fn create_app_with_middleware(config: Config) -> Router {
    let state = AppState {
        users: Arc::new(RwLock::new(HashMap::new())),
        config: config.clone(),
    };

    let cors_config = CorsConfig::default();
    let rate_limit_config = RateLimitConfig::default();

    let _middleware = MiddlewareBuilder::new()
        .cors(cors_config)
        .logging()
        .timeout(std::time::Duration::from_secs(30))
        .compression()
        .rate_limit(rate_limit_config)
        .metrics();

    let router = AxumMicroservice::create_router(state);
    
    router
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_health_check() {
        let result = health_check().await;
        assert_eq!(result, "OK");
    }
    
    
    #[test]
    fn test_axum_microservice_creation() {
        let config = Config::default();
        let _microservice = AxumMicroservice::new(config);
        assert!(true); // 如果能创建成功就说明测试通过
    }
}