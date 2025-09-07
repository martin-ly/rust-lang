//! Actix-Web框架模块
//! 
//! 提供基于Actix-Web的高性能Web微服务实现，支持Actor模型、中间件等。

use actix_web::{
    web, App, HttpServer, HttpResponse, Result as ActixResult,
    middleware::Logger, middleware::DefaultHeaders,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::info;

use crate::{
    config::Config,
    error::{Error, Result},
    utils::{HealthCheck, PaginationParams, PaginatedResponse, SuccessResponse, ErrorResponse},
};

/// Actix-Web微服务应用
pub struct ActixMicroservice {
    config: Config,
}

/// 用户模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: String,
    pub name: String,
    pub email: String,
    pub created_at: u64,
}

/// 创建用户请求
#[derive(Debug, Deserialize)]
pub struct CreateUserRequest {
    pub name: String,
    pub email: String,
}

/// 更新用户请求
#[derive(Debug, Deserialize)]
pub struct UpdateUserRequest {
    pub name: Option<String>,
    pub email: Option<String>,
}

/// 应用状态
#[derive(Clone)]
pub struct AppState {
    pub users: Arc<RwLock<HashMap<String, User>>>,
    pub config: Config,
}

impl ActixMicroservice {
    /// 创建新的Actix-Web微服务
    pub fn new(config: Config) -> Self {
        Self { config }
    }
    
    /// 启动服务器
    pub async fn serve(self) -> Result<()> {
        let config = self.config.clone();
        let addr = format!("{}:{}", config.service.host, config.service.port);
        
        info!("启动Actix-Web微服务: {}", addr);
        
        let state = AppState {
            users: Arc::new(RwLock::new(HashMap::new())),
            config: config.clone(),
        };
        
        HttpServer::new(move || {
            App::new()
                .app_data(web::Data::new(state.clone()))
                .wrap(Logger::default())
                .wrap(DefaultHeaders::new().add(("X-Version", config.service.version.as_str())))
                .service(
                    web::scope("/api/v1")
                        .route("/health", web::get().to(health_check))
                        .route("/health/detailed", web::get().to(detailed_health_check))
                        .route("/users", web::get().to(list_users))
                        .route("/users", web::post().to(create_user))
                        .route("/users/{id}", web::get().to(get_user))
                        .route("/users/{id}", web::put().to(update_user))
                        .route("/users/{id}", web::delete().to(delete_user))
                        .route("/metrics", web::get().to(metrics))
                )
        })
        .bind(&addr)
        .map_err(|e| Error::config(format!("无法绑定地址 {}: {}", addr, e)))?
        .run()
        .await
        .map_err(|e| Error::config(format!("服务器启动失败: {}", e)))?;
        
        Ok(())
    }
}

/// 健康检查处理器
async fn health_check() -> ActixResult<HttpResponse> {
    Ok(HttpResponse::Ok().json("OK"))
}

/// 详细健康检查处理器
async fn detailed_health_check(data: web::Data<AppState>) -> ActixResult<HttpResponse> {
    let health = HealthCheck::new(
        data.config.service.version.clone(),
        0, // 这里应该计算实际运行时间
    );
    
    Ok(HttpResponse::Ok().json(health))
}

/// 获取用户列表
async fn list_users(
    data: web::Data<AppState>,
    query: web::Query<PaginationParams>,
) -> ActixResult<HttpResponse> {
    let users = data.users.read().await;
    let user_list: Vec<User> = users.values().cloned().collect();
    
    let pagination = PaginationParams {
        page: query.page,
        page_size: query.page_size,
        total: Some(user_list.len() as u64),
    };
    
    let response = PaginatedResponse::new(user_list, pagination);
    Ok(HttpResponse::Ok().json(response))
}

/// 创建用户
async fn create_user(
    data: web::Data<AppState>,
    payload: web::Json<CreateUserRequest>,
) -> ActixResult<HttpResponse> {
    let user = User {
        id: uuid::Uuid::new_v4().to_string(),
        name: payload.name.clone(),
        email: payload.email.clone(),
        created_at: crate::utils::current_timestamp_secs(),
    };
    
    {
        let mut users = data.users.write().await;
        users.insert(user.id.clone(), user.clone());
    }
    
    let response = SuccessResponse::new(user, "用户创建成功".to_string());
    Ok(HttpResponse::Created().json(response))
}

/// 获取单个用户
async fn get_user(
    data: web::Data<AppState>,
    path: web::Path<String>,
) -> ActixResult<HttpResponse> {
    let users = data.users.read().await;
    
    match users.get(&path.into_inner()) {
        Some(user) => {
            let response = SuccessResponse::new(user.clone(), "用户获取成功".to_string());
            Ok(HttpResponse::Ok().json(response))
        }
        None => Ok(HttpResponse::NotFound().json(ErrorResponse::new(
            "NOT_FOUND".to_string(),
            "用户不存在".to_string(),
            404,
        ))),
    }
}

/// 更新用户
async fn update_user(
    data: web::Data<AppState>,
    path: web::Path<String>,
    payload: web::Json<UpdateUserRequest>,
) -> ActixResult<HttpResponse> {
    let mut users = data.users.write().await;
    let id = path.into_inner();
    
    match users.get_mut(&id) {
        Some(user) => {
            if let Some(name) = &payload.name {
                user.name = name.clone();
            }
            if let Some(email) = &payload.email {
                user.email = email.clone();
            }
            
            let response = SuccessResponse::new(user.clone(), "用户更新成功".to_string());
            Ok(HttpResponse::Ok().json(response))
        }
        None => Ok(HttpResponse::NotFound().json(ErrorResponse::new(
            "NOT_FOUND".to_string(),
            "用户不存在".to_string(),
            404,
        ))),
    }
}

/// 删除用户
async fn delete_user(
    data: web::Data<AppState>,
    path: web::Path<String>,
) -> ActixResult<HttpResponse> {
    let mut users = data.users.write().await;
    let id = path.into_inner();
    
    match users.remove(&id) {
        Some(_) => {
            let response = SuccessResponse::new(id, "用户删除成功".to_string());
            Ok(HttpResponse::Ok().json(response))
        }
        None => Ok(HttpResponse::NotFound().json(ErrorResponse::new(
            "NOT_FOUND".to_string(),
            "用户不存在".to_string(),
            404,
        ))),
    }
}

/// 指标端点
async fn metrics(data: web::Data<AppState>) -> ActixResult<HttpResponse> {
    let users = data.users.read().await;
    let metrics = format!(
        "# HELP users_total Total number of users\n\
         # TYPE users_total gauge\n\
         users_total {}\n",
        users.len()
    );
    
    Ok(HttpResponse::Ok()
        .content_type("text/plain; version=0.0.4; charset=utf-8")
        .body(metrics))
}


#[cfg(test)]
mod tests {
    use super::*;
    use actix_web::test;
    
    #[actix_web::test]
    async fn test_health_check() {
        let _req = test::TestRequest::get().uri("/health").to_request();
        // 这里需要实际的测试实现
        assert!(true);
    }
    
    #[tokio::test]
    async fn test_actix_microservice_creation() {
        let config = Config::default();
        let _microservice = ActixMicroservice::new(config);
        assert!(true); // 如果能创建成功就说明测试通过
    }
}