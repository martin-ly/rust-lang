//! 高级Web服务示例
//! 
//! 展示现代Rust Web服务的高级特性，包括：
//! - 微服务架构
//! - 中间件集成
//! - 错误处理
//! - 监控和可观测性
//! - 安全特性

use axum::{
    extract::{Path, Query, State},
    http::{HeaderMap, StatusCode},
    middleware,
    response::Json,
    routing::{get, post, put, delete},
    Router,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use tower::ServiceBuilder;
use tower_http::{
    cors::CorsLayer,
    trace::TraceLayer,
    compression::CompressionLayer,
    timeout::TimeoutLayer,
};
use tracing::{info, warn, error};
use uuid::Uuid;

/// 用户服务状态
#[derive(Clone)]
pub struct AppState {
    pub users: Arc<RwLock<HashMap<Uuid, User>>>,
    pub metrics: Arc<RwLock<Metrics>>,
}

/// 用户模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: Uuid,
    pub name: String,
    pub email: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub updated_at: chrono::DateTime<chrono::Utc>,
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

/// 用户查询参数
#[derive(Debug, Deserialize)]
pub struct UserQuery {
    pub page: Option<u32>,
    pub limit: Option<u32>,
    pub search: Option<String>,
}

/// 用户响应
#[derive(Debug, Serialize)]
pub struct UserResponse {
    pub user: User,
    pub links: HashMap<String, String>,
}

/// 用户列表响应
#[derive(Debug, Serialize)]
pub struct UserListResponse {
    pub users: Vec<User>,
    pub pagination: PaginationInfo,
    pub links: HashMap<String, String>,
}

/// 分页信息
#[derive(Debug, Serialize)]
pub struct PaginationInfo {
    pub page: u32,
    pub limit: u32,
    pub total: u32,
    pub total_pages: u32,
}

/// 指标数据
#[derive(Debug, Clone, Default)]
pub struct Metrics {
    pub request_count: u64,
    pub error_count: u64,
    pub response_time_sum: u64,
    pub active_connections: u32,
}

/// 健康检查响应
#[derive(Debug, Serialize)]
pub struct HealthResponse {
    pub status: String,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub version: String,
    pub metrics: Metrics,
}

/// 错误响应
#[derive(Debug, Serialize)]
pub struct ErrorResponse {
    pub error: String,
    pub message: String,
    pub request_id: String,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

/// 创建用户
async fn create_user(
    State(state): State<AppState>,
    headers: HeaderMap,
    Json(payload): Json<CreateUserRequest>,
) -> Result<(StatusCode, Json<UserResponse>), (StatusCode, Json<ErrorResponse>)> {
    let request_id = get_request_id(&headers);
    
    info!(request_id = %request_id, "创建用户请求: {:?}", payload);
    
    // 验证输入
    if payload.name.is_empty() || payload.email.is_empty() {
        return Err(create_error_response(
            StatusCode::BAD_REQUEST,
            "VALIDATION_ERROR",
            "用户名和邮箱不能为空",
            request_id,
        ));
    }
    
    // 检查邮箱是否已存在
    let users = state.users.read().await;
    if users.values().any(|user| user.email == payload.email) {
        return Err(create_error_response(
            StatusCode::CONFLICT,
            "EMAIL_EXISTS",
            "邮箱已存在",
            request_id,
        ));
    }
    drop(users);
    
    // 创建用户
    let user = User {
        id: Uuid::new_v4(),
        name: payload.name,
        email: payload.email,
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
    };
    
    // 保存用户
    {
        let mut users = state.users.write().await;
        users.insert(user.id, user.clone());
    }
    
    // 更新指标
    {
        let mut metrics = state.metrics.write().await;
        metrics.request_count += 1;
    }
    
    // 创建响应链接
    let mut links = HashMap::new();
    links.insert("self".to_string(), format!("/users/{}", user.id));
    links.insert("update".to_string(), format!("/users/{}", user.id));
    links.insert("delete".to_string(), format!("/users/{}", user.id));
    
    let response = UserResponse { user, links };
    
    info!(request_id = %request_id, "用户创建成功");
    Ok((StatusCode::CREATED, Json(response)))
}

/// 获取用户
async fn get_user(
    State(state): State<AppState>,
    headers: HeaderMap,
    Path(user_id): Path<Uuid>,
) -> Result<Json<UserResponse>, (StatusCode, Json<ErrorResponse>)> {
    let request_id = get_request_id(&headers);
    
    info!(request_id = %request_id, user_id = %user_id, "获取用户请求");
    
    let users = state.users.read().await;
    let user = users.get(&user_id).cloned();
    drop(users);
    
    match user {
        Some(user) => {
            let mut links = HashMap::new();
            links.insert("self".to_string(), format!("/users/{}", user.id));
            links.insert("update".to_string(), format!("/users/{}", user.id));
            links.insert("delete".to_string(), format!("/users/{}", user.id));
            
            let response = UserResponse { user, links };
            Ok(Json(response))
        }
        None => Err(create_error_response(
            StatusCode::NOT_FOUND,
            "USER_NOT_FOUND",
            "用户不存在",
            request_id,
        )),
    }
}

/// 更新用户
async fn update_user(
    State(state): State<AppState>,
    headers: HeaderMap,
    Path(user_id): Path<Uuid>,
    Json(payload): Json<UpdateUserRequest>,
) -> Result<Json<UserResponse>, (StatusCode, Json<ErrorResponse>)> {
    let request_id = get_request_id(&headers);
    
    info!(request_id = %request_id, user_id = %user_id, "更新用户请求: {:?}", payload);
    
    let mut users = state.users.write().await;
    let user = users.get_mut(&user_id);
    
    match user {
        Some(user) => {
            if let Some(name) = payload.name {
                user.name = name;
            }
            if let Some(email) = payload.email {
                user.email = email;
            }
            user.updated_at = chrono::Utc::now();
            
            let user = user.clone();
            drop(users);
            
            let mut links = HashMap::new();
            links.insert("self".to_string(), format!("/users/{}", user.id));
            links.insert("update".to_string(), format!("/users/{}", user.id));
            links.insert("delete".to_string(), format!("/users/{}", user.id));
            
            let response = UserResponse { user, links };
            Ok(Json(response))
        }
        None => Err(create_error_response(
            StatusCode::NOT_FOUND,
            "USER_NOT_FOUND",
            "用户不存在",
            request_id,
        )),
    }
}

/// 删除用户
async fn delete_user(
    State(state): State<AppState>,
    headers: HeaderMap,
    Path(user_id): Path<Uuid>,
) -> Result<StatusCode, (StatusCode, Json<ErrorResponse>)> {
    let request_id = get_request_id(&headers);
    
    info!(request_id = %request_id, user_id = %user_id, "删除用户请求");
    
    let mut users = state.users.write().await;
    let removed = users.remove(&user_id);
    drop(users);
    
    match removed {
        Some(_) => {
            info!(request_id = %request_id, user_id = %user_id, "用户删除成功");
            Ok(StatusCode::NO_CONTENT)
        }
        None => Err(create_error_response(
            StatusCode::NOT_FOUND,
            "USER_NOT_FOUND",
            "用户不存在",
            request_id,
        )),
    }
}

/// 获取用户列表
async fn list_users(
    State(state): State<AppState>,
    headers: HeaderMap,
    Query(params): Query<UserQuery>,
) -> Result<Json<UserListResponse>, (StatusCode, Json<ErrorResponse>)> {
    let request_id = get_request_id(&headers);
    
    info!(request_id = %request_id, "获取用户列表请求: {:?}", params);
    
    let page = params.page.unwrap_or(1);
    let limit = params.limit.unwrap_or(10).min(100); // 限制最大100条
    let offset = (page - 1) * limit;
    
    let users = state.users.read().await;
    let mut user_list: Vec<User> = users.values().cloned().collect();
    drop(users);
    
    // 搜索过滤
    if let Some(search) = params.search {
        user_list.retain(|user| {
            user.name.to_lowercase().contains(&search.to_lowercase()) ||
            user.email.to_lowercase().contains(&search.to_lowercase())
        });
    }
    
    let total = user_list.len() as u32;
    let total_pages = (total + limit - 1) / limit;
    
    // 分页
    let start = offset as usize;
    let end = (start + limit as usize).min(user_list.len());
    let users = user_list[start..end].to_vec();
    
    let pagination = PaginationInfo {
        page,
        limit,
        total,
        total_pages,
    };
    
    let mut links = HashMap::new();
    links.insert("self".to_string(), format!("/users?page={}&limit={}", page, limit));
    if page > 1 {
        links.insert("prev".to_string(), format!("/users?page={}&limit={}", page - 1, limit));
    }
    if page < total_pages {
        links.insert("next".to_string(), format!("/users?page={}&limit={}", page + 1, limit));
    }
    
    let response = UserListResponse {
        users,
        pagination,
        links,
    };
    
    Ok(Json(response))
}

/// 健康检查
async fn health_check(
    State(state): State<AppState>,
) -> Json<HealthResponse> {
    let metrics = state.metrics.read().await.clone();
    drop(metrics);
    
    let response = HealthResponse {
        status: "healthy".to_string(),
        timestamp: chrono::Utc::now(),
        version: env!("CARGO_PKG_VERSION").to_string(),
        metrics,
    };
    
    Json(response)
}

/// 获取指标
async fn get_metrics(
    State(state): State<AppState>,
) -> Json<Metrics> {
    let metrics = state.metrics.read().await.clone();
    Json(metrics)
}

/// 获取请求ID
fn get_request_id(headers: &HeaderMap) -> String {
    headers
        .get("x-request-id")
        .and_then(|h| h.to_str().ok())
        .map(|s| s.to_string())
        .unwrap_or_else(|| Uuid::new_v4().to_string())
}

/// 创建错误响应
fn create_error_response(
    status: StatusCode,
    error: &str,
    message: &str,
    request_id: String,
) -> (StatusCode, Json<ErrorResponse>) {
    let response = ErrorResponse {
        error: error.to_string(),
        message: message.to_string(),
        request_id,
        timestamp: chrono::Utc::now(),
    };
    
    (status, Json(response))
}

/// 请求ID中间件
async fn request_id_middleware(
    mut request: axum::extract::Request,
    next: middleware::Next,
) -> axum::response::Response {
    let request_id = request
        .headers()
        .get("x-request-id")
        .cloned()
        .unwrap_or_else(|| {
            axum::http::HeaderValue::from_str(&Uuid::new_v4().to_string()).unwrap()
        });
    
    request.headers_mut().insert("x-request-id", request_id);
    next.run(request).await
}

/// 指标中间件
async fn metrics_middleware(
    State(state): State<AppState>,
    request: axum::extract::Request,
    next: middleware::Next,
) -> axum::response::Response {
    let start = std::time::Instant::now();
    
    let response = next.run(request).await;
    
    let duration = start.elapsed();
    let status = response.status();
    
    // 更新指标
    {
        let mut metrics = state.metrics.write().await;
        metrics.request_count += 1;
        if status.is_client_error() || status.is_server_error() {
            metrics.error_count += 1;
        }
        metrics.response_time_sum += duration.as_millis() as u64;
    }
    
    response
}

/// 创建应用路由
fn create_app(state: AppState) -> Router {
    Router::new()
        .route("/health", get(health_check))
        .route("/metrics", get(get_metrics))
        .route("/users", post(create_user))
        .route("/users", get(list_users))
        .route("/users/:id", get(get_user))
        .route("/users/:id", put(update_user))
        .route("/users/:id", delete(delete_user))
        .layer(
            ServiceBuilder::new()
                .layer(TraceLayer::new_for_http())
                .layer(CompressionLayer::new())
                .layer(TimeoutLayer::new(std::time::Duration::from_secs(30)))
                .layer(CorsLayer::permissive())
        )
        .layer(middleware::from_fn_with_state(
            state.clone(),
            request_id_middleware,
        ))
        .layer(middleware::from_fn_with_state(
            state.clone(),
            metrics_middleware,
        ))
        .with_state(state)
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
        .init();
    
    // 创建应用状态
    let state = AppState {
        users: Arc::new(RwLock::new(HashMap::new())),
        metrics: Arc::new(RwLock::new(Metrics::default())),
    };
    
    // 创建应用
    let app = create_app(state);
    
    // 启动服务器
    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await?;
    info!("服务器启动在 http://0.0.0.0:3000");
    
    axum::serve(listener, app).await?;
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use axum::{
        body::Body,
        http::{Request, StatusCode},
    };
    use tower::ServiceExt;
    
    async fn create_test_app() -> Router {
        let state = AppState {
            users: Arc::new(RwLock::new(HashMap::new())),
            metrics: Arc::new(RwLock::new(Metrics::default())),
        };
        create_app(state)
    }
    
    #[tokio::test]
    async fn test_create_user() {
        let app = create_test_app().await;
        
        let user_data = CreateUserRequest {
            name: "测试用户".to_string(),
            email: "test@example.com".to_string(),
        };
        
        let request = Request::builder()
            .method("POST")
            .uri("/users")
            .header("content-type", "application/json")
            .body(Body::from(serde_json::to_string(&user_data).unwrap()))
            .unwrap();
        
        let response = app.oneshot(request).await.unwrap();
        assert_eq!(response.status(), StatusCode::CREATED);
    }
    
    #[tokio::test]
    async fn test_get_user_not_found() {
        let app = create_test_app().await;
        
        let request = Request::builder()
            .method("GET")
            .uri("/users/00000000-0000-0000-0000-000000000000")
            .body(Body::empty())
            .unwrap();
        
        let response = app.oneshot(request).await.unwrap();
        assert_eq!(response.status(), StatusCode::NOT_FOUND);
    }
    
    #[tokio::test]
    async fn test_health_check() {
        let app = create_test_app().await;
        
        let request = Request::builder()
            .method("GET")
            .uri("/health")
            .body(Body::empty())
            .unwrap();
        
        let response = app.oneshot(request).await.unwrap();
        assert_eq!(response.status(), StatusCode::OK);
    }
}
