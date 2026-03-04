# Rust Web 开发

Web 开发是 Rust 应用最广泛的领域之一。从高性能的 HTTP 服务器到 WebAssembly 前端应用，Rust 正在改变 Web 开发的技术栈。本文档将深入介绍 Rust 在 Web 开发领域的应用。

## 目录

- [Rust Web 开发](#rust-web-开发)
  - [目录](#目录)
  - [Web 开发生态概览](#web-开发生态概览)
    - [Rust Web 生态特点](#rust-web-生态特点)
    - [主要框架对比](#主要框架对比)
  - [后端框架详解](#后端框架详解)
    - [Axum 框架](#axum-框架)
    - [Actix-web 框架](#actix-web-框架)
  - [WebAssembly 开发](#webassembly-开发)
    - [wasm-bindgen 基础](#wasm-bindgen-基础)
    - [Yew 框架](#yew-框架)
  - [全栈框架](#全栈框架)
    - [Leptos 全栈应用](#leptos-全栈应用)
  - [API 设计与实现](#api-设计与实现)
    - [REST API 最佳实践](#rest-api-最佳实践)
  - [数据库集成](#数据库集成)
    - [SQLx 异步数据库](#sqlx-异步数据库)
  - [认证与授权](#认证与授权)
    - [JWT 认证](#jwt-认证)
  - [实时通信](#实时通信)
    - [WebSocket 实现](#websocket-实现)
  - [部署与运维](#部署与运维)
    - [Docker 部署](#docker-部署)
    - [Kubernetes 配置](#kubernetes-配置)
  - [最佳实践](#最佳实践)
    - [1. 错误处理](#1-错误处理)
    - [2. 配置管理](#2-配置管理)
  - [总结](#总结)

---

## Web 开发生态概览

### Rust Web 生态特点

| 特性 | Rust 实现 | 其他语言对比 |
|------|-----------|--------------|
| 性能 | 原生代码，无 GC 暂停 | 比 Go/Node.js 快 10-100 倍 |
| 内存安全 | 编译时保证 | Java/Go 运行时检查，C/C++ 无保证 |
| 并发模型 | async/await，多线程 | 比 Python/Node.js 更易用 |
| 资源占用 | 极低内存占用 | 适合容器化部署 |
| 编译时检查 | 类型安全、所有权检查 | 减少运行时错误 |

### 主要框架对比

| 框架 | 特点 | 适用场景 | 性能 | 学习曲线 |
|------|------|----------|------|----------|
| Actix-web | Actor 模型，极致性能 | 高并发 API | ⭐⭐⭐⭐⭐ | 中等 |
| Axum | 模块化，Tower 生态 | 微服务 | ⭐⭐⭐⭐⭐ | 中等 |
| Rocket | 开发体验优秀 | 快速开发 | ⭐⭐⭐⭐ | 简单 |
| Warp | 函数式路由 | 复杂路由 | ⭐⭐⭐⭐⭐ | 陡峭 |
| Tide | 异步优先 | 中小型项目 | ⭐⭐⭐⭐ | 简单 |

---

## 后端框架详解

### Axum 框架

Axum 是由 Tokio 团队开发的 Web 框架，与 Tower 生态系统深度集成。

```rust
//! Axum 完整示例

use axum::{
    routing::{get, post, put, delete},
    Router, Json, extract::{Path, State, Query},
    middleware::{self, Next},
    response::{Response, IntoResponse},
    http::{Request, StatusCode, HeaderMap},
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;
use chrono::{DateTime, Utc};
use uuid::Uuid;
use tower_http::{cors::CorsLayer, trace::TraceLayer, compression::CompressionLayer};

// ==================== 数据模型 ====================

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: String,
    pub username: String,
    pub email: String,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Deserialize)]
pub struct CreateUserRequest {
    pub username: String,
    pub email: String,
}

#[derive(Debug, Deserialize)]
pub struct UpdateUserRequest {
    pub username: Option<String>,
    pub email: Option<String>,
}

#[derive(Debug, Deserialize)]
pub struct ListUsersQuery {
    pub page: Option<usize>,
    pub per_page: Option<usize>,
    pub search: Option<String>,
}

#[derive(Debug, Serialize)]
pub struct PaginatedResponse<T> {
    pub data: Vec<T>,
    pub total: usize,
    pub page: usize,
    pub per_page: usize,
    pub total_pages: usize,
}

#[derive(Debug, Serialize)]
pub struct ApiError {
    pub code: String,
    pub message: String,
    pub details: Option<serde_json::Value>,
}

// ==================== 应用状态 ====================

pub struct AppState {
    users: RwLock<HashMap<String, User>>,
    config: AppConfig,
}

#[derive(Debug, Clone)]
pub struct AppConfig {
    pub jwt_secret: String,
    pub database_url: String,
}

impl AppState {
    pub fn new(config: AppConfig) -> Self {
        Self {
            users: RwLock::new(HashMap::new()),
            config,
        }
    }
}

// ==================== 错误处理 ====================

pub enum AppError {
    NotFound(String),
    BadRequest(String),
    Internal(String),
    Unauthorized,
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let (status, error_code, message) = match self {
            AppError::NotFound(msg) => (StatusCode::NOT_FOUND, "NOT_FOUND", msg),
            AppError::BadRequest(msg) => (StatusCode::BAD_REQUEST, "BAD_REQUEST", msg),
            AppError::Internal(msg) => (StatusCode::INTERNAL_SERVER_ERROR, "INTERNAL_ERROR", msg),
            AppError::Unauthorized => (StatusCode::UNAUTHORIZED, "UNAUTHORIZED", "Unauthorized".to_string()),
        };

        let body = Json(ApiError {
            code: error_code.to_string(),
            message,
            details: None,
        });

        (status, body).into_response()
    }
}

// ==================== 处理器 ====================

/// 创建用户
async fn create_user(
    State(state): State<Arc<AppState>>,
    Json(req): Json<CreateUserRequest>,
) -> Result<(StatusCode, Json<User>), AppError> {
    // 验证输入
    if req.username.is_empty() || req.username.len() > 50 {
        return Err(AppError::BadRequest("Invalid username".to_string()));
    }
    if !req.email.contains('@') {
        return Err(AppError::BadRequest("Invalid email".to_string()));
    }

    let user = User {
        id: Uuid::new_v4().to_string(),
        username: req.username,
        email: req.email,
        created_at: Utc::now(),
        updated_at: Utc::now(),
    };

    let mut users = state.users.write().await;

    // 检查用户名是否已存在
    if users.values().any(|u| u.username == user.username) {
        return Err(AppError::BadRequest("Username already exists".to_string()));
    }

    let id = user.id.clone();
    users.insert(id, user.clone());

    Ok((StatusCode::CREATED, Json(user)))
}

/// 获取单个用户
async fn get_user(
    State(state): State<Arc<AppState>>,
    Path(user_id): Path<String>,
) -> Result<Json<User>, AppError> {
    let users = state.users.read().await;

    users.get(&user_id)
        .cloned()
        .map(Json)
        .ok_or_else(|| AppError::NotFound(format!("User {} not found", user_id)))
}

/// 列出用户（支持分页和搜索）
async fn list_users(
    State(state): State<Arc<AppState>>,
    Query(query): Query<ListUsersQuery>,
) -> Json<PaginatedResponse<User>> {
    let users = state.users.read().await;

    let page = query.page.unwrap_or(1).max(1);
    let per_page = query.per_page.unwrap_or(10).clamp(1, 100);

    let mut user_list: Vec<User> = users.values().cloned().collect();

    // 搜索过滤
    if let Some(search) = query.search {
        let search_lower = search.to_lowercase();
        user_list.retain(|u| {
            u.username.to_lowercase().contains(&search_lower) ||
            u.email.to_lowercase().contains(&search_lower)
        });
    }

    let total = user_list.len();
    let total_pages = (total + per_page - 1) / per_page;

    // 分页
    let start = (page - 1) * per_page;
    let end = (start + per_page).min(total);
    let data = if start < total {
        user_list[start..end].to_vec()
    } else {
        vec![]
    };

    Json(PaginatedResponse {
        data,
        total,
        page,
        per_page,
        total_pages,
    })
}

/// 更新用户
async fn update_user(
    State(state): State<Arc<AppState>>,
    Path(user_id): Path<String>,
    Json(req): Json<UpdateUserRequest>,
) -> Result<Json<User>, AppError> {
    let mut users = state.users.write().await;

    let user = users.get_mut(&user_id)
        .ok_or_else(|| AppError::NotFound(format!("User {} not found", user_id)))?;

    if let Some(username) = req.username {
        if username.is_empty() || username.len() > 50 {
            return Err(AppError::BadRequest("Invalid username".to_string()));
        }
        user.username = username;
    }

    if let Some(email) = req.email {
        if !email.contains('@') {
            return Err(AppError::BadRequest("Invalid email".to_string()));
        }
        user.email = email;
    }

    user.updated_at = Utc::now();

    Ok(Json(user.clone()))
}

/// 删除用户
async fn delete_user(
    State(state): State<Arc<AppState>>,
    Path(user_id): Path<String>,
) -> Result<StatusCode, AppError> {
    let mut users = state.users.write().await;

    users.remove(&user_id)
        .ok_or_else(|| AppError::NotFound(format!("User {} not found", user_id)))?;

    Ok(StatusCode::NO_CONTENT)
}

// ==================== 中间件 ====================

async fn auth_middleware<B>(
    headers: HeaderMap,
    request: Request<B>,
    next: Next<B>,
) -> Result<Response, AppError> {
    let auth_header = headers.get("authorization")
        .and_then(|h| h.to_str().ok())
        .ok_or(AppError::Unauthorized)?;

    if !auth_header.starts_with("Bearer ") {
        return Err(AppError::Unauthorized);
    }

    let token = &auth_header[7..];

    // 验证 JWT（简化示例）
    if token.is_empty() {
        return Err(AppError::Unauthorized);
    }

    Ok(next.run(request).await)
}

async fn rate_limit_middleware<B>(
    request: Request<B>,
    next: Next<B>,
) -> Response {
    // 速率限制逻辑
    next.run(request).await
}

// ==================== 应用构建 ====================

pub fn create_app(state: Arc<AppState>) -> Router {
    Router::new()
        // 健康检查
        .route("/health", get(health_check))
        // 用户 API
        .route("/api/v1/users", post(create_user).get(list_users))
        .route("/api/v1/users/:user_id", get(get_user).put(update_user).delete(delete_user))
        // 嵌套路由
        .nest("/api/v1/posts", posts_routes())
        // 中间件
        .layer(middleware::from_fn(auth_middleware))
        .layer(TraceLayer::new_for_http())
        .layer(CompressionLayer::new())
        .layer(CorsLayer::permissive())
        // 状态
        .with_state(state)
}

fn posts_routes() -> Router<Arc<AppState>> {
    Router::new()
        .route("/", get(list_posts).post(create_post))
        .route("/:post_id", get(get_post).put(update_post).delete(delete_post))
        .route("/:post_id/comments", get(list_comments).post(create_comment))
}

async fn health_check() -> &'static str { "OK" }
async fn list_posts() -> &'static str { "Posts list" }
async fn create_post() -> &'static str { "Post created" }
async fn get_post() -> &'static str { "Post detail" }
async fn update_post() -> &'static str { "Post updated" }
async fn delete_post() -> &'static str { "Post deleted" }
async fn list_comments() -> &'static str { "Comments list" }
async fn create_comment() -> &'static str { "Comment created" }

// ==================== 启动 ====================

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();

    let config = AppConfig {
        jwt_secret: std::env::var("JWT_SECRET").unwrap_or_else(|_| "secret".to_string()),
        database_url: std::env::var("DATABASE_URL").unwrap_or_else(|_| "postgres://localhost/db".to_string()),
    };

    let state = Arc::new(AppState::new(config));
    let app = create_app(state);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    println!("Server listening on {}", listener.local_addr().unwrap());

    axum::serve(listener, app).await.unwrap();
}
```

### Actix-web 框架

Actix-web 是基于 Actor 模型的高性能 Web 框架。

```rust
//! Actix-web 完整示例

use actix_web::{
    web, App, HttpServer, HttpRequest, HttpResponse, Error,
    middleware::{Logger, Compress, DefaultHeaders},
    http::header::{self, ContentType},
};
use actix_web::error::{ErrorBadRequest, ErrorNotFound, ErrorInternalServerError};
use serde::{Deserialize, Serialize};
use sqlx::{PgPool, Row};
use validator::Validate;
use jsonwebtoken::{encode, decode, Header, Validation, EncodingKey, DecodingKey};
use std::sync::Arc;
use bcrypt::{hash, verify, DEFAULT_COST};

// ==================== 数据模型 ====================

#[derive(Debug, Serialize, Deserialize, sqlx::FromRow)]
pub struct User {
    pub id: i64,
    pub username: String,
    pub email: String,
    pub password_hash: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Deserialize, Validate)]
pub struct RegisterRequest {
    #[validate(length(min = 3, max = 50))]
    pub username: String,
    #[validate(email)]
    pub email: String,
    #[validate(length(min = 8))]
    pub password: String,
}

#[derive(Debug, Deserialize)]
pub struct LoginRequest {
    pub username: String,
    pub password: String,
}

#[derive(Debug, Serialize)]
pub struct AuthResponse {
    pub token: String,
    pub user: UserInfo,
}

#[derive(Debug, Serialize)]
pub struct UserInfo {
    pub id: i64,
    pub username: String,
    pub email: String,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: i64,
    pub username: String,
    pub exp: usize,
}

// ==================== 应用状态 ====================

pub struct AppState {
    pub db: PgPool,
    pub jwt_secret: String,
}

// ==================== 服务层 ====================

pub struct UserService {
    db: PgPool,
    jwt_secret: String,
}

impl UserService {
    pub fn new(db: PgPool, jwt_secret: String) -> Self {
        Self { db, jwt_secret }
    }

    pub async fn register(&self, req: RegisterRequest) -> Result<User, Error> {
        // 验证输入
        req.validate().map_err(|e| ErrorBadRequest(e))?;

        // 检查用户名是否已存在
        let existing = sqlx::query("SELECT id FROM users WHERE username = $1 OR email = $2")
            .bind(&req.username)
            .bind(&req.email)
            .fetch_optional(&self.db)
            .await
            .map_err(|e| ErrorInternalServerError(e))?;

        if existing.is_some() {
            return Err(ErrorBadRequest("Username or email already exists"));
        }

        // 哈希密码
        let password_hash = hash(&req.password, DEFAULT_COST)
            .map_err(|e| ErrorInternalServerError(e))?;

        // 创建用户
        let user = sqlx::query_as::<_, User>(
            "INSERT INTO users (username, email, password_hash) VALUES ($1, $2, $3) RETURNING *"
        )
        .bind(&req.username)
        .bind(&req.email)
        .bind(&password_hash)
        .fetch_one(&self.db)
        .await
        .map_err(|e| ErrorInternalServerError(e))?;

        Ok(user)
    }

    pub async fn login(&self, req: LoginRequest) -> Result<AuthResponse, Error> {
        let user = sqlx::query_as::<_, User>("SELECT * FROM users WHERE username = $1")
            .bind(&req.username)
            .fetch_optional(&self.db)
            .await
            .map_err(|e| ErrorInternalServerError(e))?
            .ok_or_else(|| ErrorBadRequest("Invalid credentials"))?;

        // 验证密码
        if !verify(&req.password, &user.password_hash)
            .map_err(|e| ErrorInternalServerError(e))? {
            return Err(ErrorBadRequest("Invalid credentials"));
        }

        // 生成 JWT
        let claims = Claims {
            sub: user.id,
            username: user.username.clone(),
            exp: (chrono::Utc::now() + chrono::Duration::hours(24)).timestamp() as usize,
        };

        let token = encode(
            &Header::default(),
            &claims,
            &EncodingKey::from_secret(self.jwt_secret.as_bytes())
        ).map_err(|e| ErrorInternalServerError(e))?;

        Ok(AuthResponse {
            token,
            user: UserInfo {
                id: user.id,
                username: user.username,
                email: user.email,
            },
        })
    }

    pub async fn get_user(&self, user_id: i64) -> Result<User, Error> {
        sqlx::query_as::<_, User>("SELECT * FROM users WHERE id = $1")
            .bind(user_id)
            .fetch_optional(&self.db)
            .await
            .map_err(|e| ErrorInternalServerError(e))?
            .ok_or_else(|| ErrorNotFound("User not found"))
    }
}

// ==================== 处理器 ====================

async fn register(
    state: web::Data<Arc<AppState>>,
    req: web::Json<RegisterRequest>,
) -> Result<HttpResponse, Error> {
    let service = UserService::new(state.db.clone(), state.jwt_secret.clone());
    let user = service.register(req.into_inner()).await?;

    Ok(HttpResponse::Created().json(UserInfo {
        id: user.id,
        username: user.username,
        email: user.email,
    }))
}

async fn login(
    state: web::Data<Arc<AppState>>,
    req: web::Json<LoginRequest>,
) -> Result<HttpResponse, Error> {
    let service = UserService::new(state.db.clone(), state.jwt_secret.clone());
    let response = service.login(req.into_inner()).await?;

    Ok(HttpResponse::Ok().json(response))
}

async fn get_profile(
    state: web::Data<Arc<AppState>>,
    req: HttpRequest,
) -> Result<HttpResponse, Error> {
    // 从请求头提取 JWT
    let auth_header = req.headers().get(header::AUTHORIZATION)
        .and_then(|h| h.to_str().ok())
        .ok_or_else(|| ErrorBadRequest("Missing authorization header"))?;

    if !auth_header.starts_with("Bearer ") {
        return Err(ErrorBadRequest("Invalid authorization header"));
    }

    let token = &auth_header[7..];

    // 验证 JWT
    let claims = decode::<Claims>(
        token,
        &DecodingKey::from_secret(state.jwt_secret.as_bytes()),
        &Validation::default()
    ).map_err(|_| ErrorBadRequest("Invalid token"))?.claims;

    // 获取用户信息
    let service = UserService::new(state.db.clone(), state.jwt_secret.clone());
    let user = service.get_user(claims.sub).await?;

    Ok(HttpResponse::Ok().json(UserInfo {
        id: user.id,
        username: user.username,
        email: user.email,
    }))
}

// ==================== 中间件 ====================

async fn auth_validator(
    req: HttpRequest,
    credentials: web::Data<Arc<AppState>>,
) -> Result<HttpRequest, Error> {
    // 验证逻辑
    Ok(req)
}

// ==================== 应用配置 ====================

pub fn config(cfg: &mut web::ServiceConfig) {
    cfg.service(
        web::scope("/api/v1")
            .route("/auth/register", web::post().to(register))
            .route("/auth/login", web::post().to(login))
            .route("/users/profile", web::get().to(get_profile))
    );
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    env_logger::init();

    // 连接数据库
    let database_url = std::env::var("DATABASE_URL")
        .unwrap_or_else(|_| "postgres://localhost/myapp".to_string());

    let pool = PgPool::connect(&database_url).await
        .expect("Failed to connect to database");

    let state = Arc::new(AppState {
        db: pool,
        jwt_secret: std::env::var("JWT_SECRET").unwrap_or_else(|_| "secret".to_string()),
    });

    println!("Server starting on http://127.0.0.1:8080");

    HttpServer::new(move || {
        App::new()
            .app_data(web::Data::new(state.clone()))
            .wrap(Logger::default())
            .wrap(Compress::default())
            .wrap(DefaultHeaders::new().add(("X-Version", "1.0")))
            .configure(config)
    })
    .bind(("127.0.0.1", 8080))?
    .workers(4)
    .run()
    .await
}
```

---

## WebAssembly 开发

### wasm-bindgen 基础

```rust
//! WebAssembly 前端开发

use wasm_bindgen::prelude::*;
use wasm_bindgen_futures::spawn_local;
use web_sys::{console, window, Document, HtmlElement, Event, MouseEvent};
use serde::{Serialize, Deserialize};
use js_sys::{JSON, Promise};

// ==================== JavaScript 互操作 ====================

#[wasm_bindgen]
extern "C" {
    // 调用 JavaScript 的 alert
    #[wasm_bindgen(js_namespace = console)]
    fn log(s: &str);

    #[wasm_bindgen(js_namespace = console)]
    fn error(s: &str);

    // 访问浏览器 API
    #[wasm_bindgen(js_namespace = localStorage)]
    fn getItem(key: &str) -> Option<String>;

    #[wasm_bindgen(js_namespace = localStorage)]
    fn setItem(key: &str, value: &str);

    // 自定义 JS 函数
    #[wasm_bindgen(js_name = fetchData)]
    async fn fetch_data(url: &str) -> Result<JsValue, JsValue>;
}

#[wasm_bindgen(module = "/js/utils.js")]
extern "C" {
    fn formatDate(timestamp: i64) -> String;
    fn calculateHash(data: &str) -> String;
}

// ==================== Rust 导出到 JS ====================

#[wasm_bindgen]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TodoItem {
    id: u32,
    title: String,
    completed: bool,
    created_at: i64,
}

#[wasm_bindgen]
impl TodoItem {
    #[wasm_bindgen(constructor)]
    pub fn new(id: u32, title: String) -> Self {
        Self {
            id,
            title,
            completed: false,
            created_at: js_sys::Date::now() as i64,
        }
    }

    #[wasm_bindgen(getter)]
    pub fn id(&self) -> u32 { self.id }

    #[wasm_bindgen(getter)]
    pub fn title(&self) -> String { self.title.clone() }

    #[wasm_bindgen(setter)]
    pub fn set_title(&mut self, title: String) { self.title = title; }

    #[wasm_bindgen(getter)]
    pub fn completed(&self) -> bool { self.completed }

    #[wasm_bindgen]
    pub fn toggle(&mut self) { self.completed = !self.completed; }

    #[wasm_bindgen(js_name = toJSON)]
    pub fn to_json(&self) -> String {
        serde_json::to_string(self).unwrap_or_default()
    }
}

/// Todo 应用管理器
#[wasm_bindgen]
pub struct TodoApp {
    todos: Vec<TodoItem>,
    next_id: u32,
}

#[wasm_bindgen]
impl TodoApp {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        console_log("TodoApp initialized");
        Self { todos: Vec::new(), next_id: 1 }
    }

    #[wasm_bindgen(js_name = addTodo)]
    pub fn add_todo(&mut self, title: String) -> u32 {
        let id = self.next_id;
        self.todos.push(TodoItem::new(id, title));
        self.next_id += 1;
        self.save_to_storage();
        id
    }

    #[wasm_bindgen(js_name = removeTodo)]
    pub fn remove_todo(&mut self, id: u32) -> bool {
        if let Some(pos) = self.todos.iter().position(|t| t.id == id) {
            self.todos.remove(pos);
            self.save_to_storage();
            true
        } else {
            false
        }
    }

    #[wasm_bindgen(js_name = toggleTodo)]
    pub fn toggle_todo(&mut self, id: u32) -> bool {
        if let Some(todo) = self.todos.iter_mut().find(|t| t.id == id) {
            todo.toggle();
            self.save_to_storage();
            true
        } else {
            false
        }
    }

    #[wasm_bindgen(js_name = getTodos)]
    pub fn get_todos(&self) -> JsValue {
        serde_wasm_bindgen::to_value(&self.todos).unwrap_or(JsValue::NULL)
    }

    #[wasm_bindgen(js_name = getStats)]
    pub fn get_stats(&self) -> JsValue {
        let total = self.todos.len();
        let completed = self.todos.iter().filter(|t| t.completed).count();

        let stats = serde_json::json!({
            "total": total,
            "completed": completed,
            "pending": total - completed
        });

        serde_wasm_bindgen::to_value(&stats).unwrap_or(JsValue::NULL)
    }

    fn save_to_storage(&self) {
        if let Ok(json) = serde_json::to_string(&self.todos) {
            setItem("todos", &json);
        }
    }

    #[wasm_bindgen(js_name = loadFromStorage)]
    pub fn load_from_storage(&mut self) {
        if let Some(json) = getItem("todos") {
            if let Ok(todos) = serde_json::from_str::<Vec<TodoItem>>(&json) {
                self.todos = todos;
                self.next_id = self.todos.iter().map(|t| t.id).max().unwrap_or(0) + 1;
            }
        }
    }
}

// ==================== DOM 操作 ====================

/// DOM 操作工具函数
#[wasm_bindgen]
pub fn setup_dom() {
    let window = window().expect("no global window exists");
    let document = window.document().expect("should have a document");

    // 创建容器
    let container = document.create_element("div").unwrap();
    container.set_id("app-container");
    container.set_class_name("container");

    // 创建标题
    let heading = document.create_element("h1").unwrap();
    heading.set_text_content(Some("Rust + WebAssembly Todo App"));
    container.append_child(&heading).unwrap();

    // 创建输入框
    let input = document.create_element("input").unwrap();
    input.set_attribute("type", "text").unwrap();
    input.set_attribute("placeholder", "Add a todo...").unwrap();
    input.set_id("todo-input");
    container.append_child(&input).unwrap();

    // 创建添加按钮
    let button = document.create_element("button").unwrap();
    button.set_text_content(Some("Add"));
    button.set_id("add-btn");

    // 添加点击事件
    let closure = Closure::wrap(Box::new(move |_event: MouseEvent| {
        console_log("Button clicked!");
        add_todo_from_input();
    }) as Box<dyn FnMut(_)>);

    button.add_event_listener_with_callback("click", closure.as_ref().unchecked_ref()).unwrap();
    closure.forget(); // 记住释放内存

    container.append_child(&button).unwrap();

    // 创建列表
    let list = document.create_element("ul").unwrap();
    list.set_id("todo-list");
    container.append_child(&list).unwrap();

    // 添加到 body
    document.body().unwrap().append_child(&container).unwrap();
}

fn add_todo_from_input() {
    let window = window().unwrap();
    let document = window.document().unwrap();

    if let Some(input) = document.get_element_by_id("todo-input") {
        if let Ok(input_el) = input.dyn_into::<web_sys::HtmlInputElement>() {
            let value = input_el.value();
            if !value.is_empty() {
                console_log(&format!("Adding todo: {}", value));
                input_el.set_value("");
            }
        }
    }
}

// ==================== 异步操作 ====================

#[wasm_bindgen]
pub async fn fetch_user_data(user_id: u32) -> Result<JsValue, JsValue> {
    let url = format!("https://api.example.com/users/{}", user_id);

    let window = window().unwrap();
    let resp_value = wasm_bindgen_futures::JsFuture::from(
        window.fetch_with_str(&url)
    ).await?;

    let resp: web_sys::Response = resp_value.dyn_into()?;
    let json = wasm_bindgen_futures::JsFuture::from(
        resp.json()?
    ).await?;

    Ok(json)
}

#[wasm_bindgen]
pub fn start_async_task() {
    spawn_local(async {
        match fetch_user_data(1).await {
            Ok(data) => {
                console_log(&format!("User data: {:?}", data));
            }
            Err(e) => {
                console_error(&format!("Error: {:?}", e));
            }
        }
    });
}

// ==================== 辅助函数 ====================

#[wasm_bindgen]
extern "C" {
    #[wasm_bindgen(js_namespace = console, js_name = log)]
    fn console_log(s: &str);

    #[wasm_bindgen(js_namespace = console, js_name = error)]
    fn console_error(s: &str);
}

use wasm_bindgen::closure::Closure;
```

### Yew 框架

```rust
//! Yew 框架 - React-like 的 Rust 前端框架

use yew::prelude::*;
use serde::{Deserialize, Serialize};
use web_sys::HtmlInputElement;

// ==================== 状态管理 ====================

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct Todo {
    pub id: usize,
    pub text: String,
    pub completed: bool,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Filter {
    All,
    Active,
    Completed,
}

// ==================== 消息定义 ====================

pub enum Msg {
    AddTodo,
    UpdateInput(String),
    ToggleTodo(usize),
    DeleteTodo(usize),
    SetFilter(Filter),
    ClearCompleted,
}

// ==================== 组件 ====================

pub struct TodoApp {
    todos: Vec<Todo>,
    input_value: String,
    filter: Filter,
    next_id: usize,
}

impl Component for TodoApp {
    type Message = Msg;
    type Properties = ();

    fn create(_ctx: &Context<Self>) -> Self {
        Self {
            todos: vec![
                Todo { id: 1, text: "Learn Rust".to_string(), completed: false },
                Todo { id: 2, text: "Build a Web App".to_string(), completed: true },
            ],
            input_value: String::new(),
            filter: Filter::All,
            next_id: 3,
        }
    }

    fn update(&mut self, _ctx: &Context<Self>, msg: Self::Message) -> bool {
        match msg {
            Msg::AddTodo => {
                if !self.input_value.trim().is_empty() {
                    self.todos.push(Todo {
                        id: self.next_id,
                        text: self.input_value.clone(),
                        completed: false,
                    });
                    self.next_id += 1;
                    self.input_value.clear();
                    true
                } else {
                    false
                }
            }
            Msg::UpdateInput(value) => {
                self.input_value = value;
                false
            }
            Msg::ToggleTodo(id) => {
                if let Some(todo) = self.todos.iter_mut().find(|t| t.id == id) {
                    todo.completed = !todo.completed;
                    true
                } else {
                    false
                }
            }
            Msg::DeleteTodo(id) => {
                self.todos.retain(|t| t.id != id);
                true
            }
            Msg::SetFilter(filter) => {
                self.filter = filter;
                true
            }
            Msg::ClearCompleted => {
                self.todos.retain(|t| !t.completed);
                true
            }
        }
    }

    fn view(&self, ctx: &Context<Self>) -> Html {
        let filtered_todos: Vec<&Todo> = self.todos.iter()
            .filter(|t| match self.filter {
                Filter::All => true,
                Filter::Active => !t.completed,
                Filter::Completed => t.completed,
            })
            .collect();

        let completed_count = self.todos.iter().filter(|t| t.completed).count();
        let active_count = self.todos.len() - completed_count;

        html! {
            <div class="todo-app">
                <h1>{ "Todos" }</h1>

                <div class="input-container">
                    <input
                        type="text"
                        placeholder="What needs to be done?"
                        value={self.input_value.clone()}
                        oninput={ctx.link().callback(|e: InputEvent| {
                            let input: HtmlInputElement = e.target_unchecked_into();
                            Msg::UpdateInput(input.value())
                        })}
                        onkeypress={ctx.link().callback(|e: KeyboardEvent| {
                            if e.key() == "Enter" {
                                Msg::AddTodo
                            } else {
                                Msg::UpdateInput(String::new())
                            }
                        })}
                    />
                    <button onclick={ctx.link().callback(|_| Msg::AddTodo)}>
                        { "Add" }
                    </button>
                </div>

                <ul class="todo-list">
                    { for filtered_todos.iter().map(|todo| {
                        let id = todo.id;
                        html! {
                            <li key={todo.id} class={if todo.completed { "completed" } else { "" }}>
                                <input
                                    type="checkbox"
                                    checked={todo.completed}
                                    onclick={ctx.link().callback(move |_| Msg::ToggleTodo(id))}
                                />
                                <span>{ &todo.text }</span>
                                <button
                                    class="delete-btn"
                                    onclick={ctx.link().callback(move |_| Msg::DeleteTodo(id))}
                                >
                                    { "x" }
                                </button>
                            </li>
                        }
                    })}
                </ul>

                <div class="footer">
                    <span>{ format!("{} items left", active_count) }</span>

                    <div class="filters">
                        <button
                            class={if self.filter == Filter::All { "active" } else { "" }}
                            onclick={ctx.link().callback(|_| Msg::SetFilter(Filter::All))}
                        >
                            { "All" }
                        </button>
                        <button
                            class={if self.filter == Filter::Active { "active" } else { "" }}
                            onclick={ctx.link().callback(|_| Msg::SetFilter(Filter::Active))}
                        >
                            { "Active" }
                        </button>
                        <button
                            class={if self.filter == Filter::Completed { "active" } else { "" }}
                            onclick={ctx.link().callback(|_| Msg::SetFilter(Filter::Completed))}
                        >
                            { "Completed" }
                        </button>
                    </div>

                    { if completed_count > 0 {
                        html! {
                            <button
                                class="clear-completed"
                                onclick={ctx.link().callback(|_| Msg::ClearCompleted)}
                            >
                                { format!("Clear completed ({})", completed_count) }
                            </button>
                        }
                    } else {
                        html! {}
                    }}
                </div>
            </div>
        }
    }
}

fn main() {
    yew::Renderer::<TodoApp>::new().render();
}
```

---

## 全栈框架

### Leptos 全栈应用

```rust
//! Leptos 全栈框架示例

use leptos::*;
use leptos_router::*;
use serde::{Serialize, Deserialize};

// ==================== 数据模型 ====================

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Post {
    pub id: u64,
    pub title: String,
    pub content: String,
    pub author: String,
    pub created_at: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CreatePostRequest {
    pub title: String,
    pub content: String,
}

// ==================== API 端点 ====================

#[server(GetPosts, "/api")]
pub async fn get_posts() -> Result<Vec<Post>, ServerFnError> {
    // 实际应用：从数据库获取
    Ok(vec![
        Post {
            id: 1,
            title: "Hello Leptos".to_string(),
            content: "This is a full-stack Rust framework".to_string(),
            author: "Developer".to_string(),
            created_at: "2024-01-01".to_string(),
        },
    ])
}

#[server(CreatePost, "/api")]
pub async fn create_post(req: CreatePostRequest) -> Result<Post, ServerFnError> {
    // 实际应用：保存到数据库
    Ok(Post {
        id: 2,
        title: req.title,
        content: req.content,
        author: "Current User".to_string(),
        created_at: "2024-01-02".to_string(),
    })
}

#[server(GetPost, "/api")]
pub async fn get_post(id: u64) -> Result<Post, ServerFnError> {
    // 实际应用：从数据库获取
    Ok(Post {
        id,
        title: "Sample Post".to_string(),
        content: "Post content here".to_string(),
        author: "Author".to_string(),
        created_at: "2024-01-01".to_string(),
    })
}

// ==================== 组件 ====================

#[component]
pub fn App() -> impl IntoView {
    provide_meta_context();

    view! {
        <Stylesheet id="leptos" href="/pkg/leptos_start.css"/>
        <Title text="Leptos Blog"/>

        <Router>
            <nav>
                <A href="/">"Home"</A>
                <A href="/posts">"Posts"</A>
                <A href="/about">"About"</A>
            </nav>

            <main>
                <Routes>
                    <Route path="/" view=HomePage/>
                    <Route path="/posts" view=PostsPage/>
                    <Route path="/posts/:id" view=PostDetailPage/>
                    <Route path="/posts/new" view=CreatePostPage/>
                    <Route path="/about" view=AboutPage/>
                    <Route path="/*any" view=NotFound/>
                </Routes>
            </main>
        </Router>
    }
}

#[component]
fn HomePage() -> impl IntoView {
    view! {
        <h1>"Welcome to Leptos Blog"</h1>
        <p>"A full-stack Rust application"</p>
        <A href="/posts">"View Posts"</A>
    }
}

#[component]
fn PostsPage() -> impl IntoView {
    let posts = create_resource(|| (), |_| get_posts());

    view! {
        <h1>"Posts"</h1>
        <A href="/posts/new">"Create New Post"</A>

        <Suspense fallback=move || view! { <p>"Loading..."</p> }>
            {move || posts.get().map(|result| match result {
                Ok(posts) => view! {
                    <div class="posts-list">
                        {posts.into_iter().map(|post| view! {
                            <article key={post.id}>
                                <h2><A href=format!("/posts/{}", post.id)>{post.title}</A></h2>
                                <p>{&post.content[..post.content.len().min(100)]}{"..."}</p>
                                <small>"By "{post.author}" on "{post.created_at}</small>
                            </article>
                        }).collect::<Vec<_>>()}
                    </div>
                }.into_any(),
                Err(e) => view! { <p>"Error: "{e.to_string()}</p> }.into_any(),
            })}
        </Suspense>
    }
}

#[component]
fn PostDetailPage() -> impl IntoView {
    let params = use_params_map();
    let id = move || params.with(|p| p.get("id").cloned().unwrap_or_default().parse::<u64>().unwrap_or(0));

    let post = create_resource(id, |id| get_post(id));

    view! {
        <Suspense fallback=move || view! { <p>"Loading..."</p> }>
            {move || post.get().map(|result| match result {
                Ok(post) => view! {
                    <article>
                        <h1>{post.title}</h1>
                        <p class="meta">"By "{post.author}" on "{post.created_at}</p>
                        <div class="content">{post.content}</div>
                    </article>
                }.into_any(),
                Err(e) => view! { <p>"Error: "{e.to_string()}</p> }.into_any(),
            })}
        </Suspense>
    }
}

#[component]
fn CreatePostPage() -> impl IntoView {
    let (title, set_title) = create_signal(String::new());
    let (content, set_content) = create_signal(String::new());

    let on_submit = move |ev: leptos::ev::SubmitEvent| {
        ev.prevent_default();

        let req = CreatePostRequest {
            title: title.get(),
            content: content.get(),
        };

        spawn_local(async move {
            match create_post(req).await {
                Ok(_) => {
                    let navigate = use_navigate();
                    navigate("/posts", NavigateOptions::default());
                }
                Err(e) => {
                    leptos::logging::error!("Failed to create post: {}", e);
                }
            }
        });
    };

    view! {
        <h1>"Create New Post"</h1>
        <form on:submit=on_submit>
            <div>
                <label>"Title"</label>
                <input
                    type="text"
                    prop:value=title
                    on:input=move |e| set_title.set(event_target_value(&e))
                    required
                />
            </div>
            <div>
                <label>"Content"</label>
                <textarea
                    prop:value=content
                    on:input=move |e| set_content.set(event_target_value(&e))
                    rows="10"
                    required
                ></textarea>
            </div>
            <button type="submit">"Create Post"</button>
        </form>
    }
}

#[component]
fn AboutPage() -> impl IntoView {
    view! {
        <h1>"About"</h1>
        <p>"This blog is built with Leptos, a full-stack Rust framework."</p>
        <p>"Features:"</p>
        <ul>
            <li>"Server-side rendering (SSR)"</li>
            <li>"Client-side hydration"</li>
            <li>"Reactive signals"</li>
            <li>"Type-safe routing"</li>
        </ul>
    }
}

#[component]
fn NotFound() -> impl IntoView {
    view! {
        <h1>"404 - Not Found"</h1>
        <p>"The page you're looking for doesn't exist."</p>
        <A href="/">"Go Home"</A>
    }
}

fn main() {
    mount_to_body(App);
}
```

---

## API 设计与实现

### REST API 最佳实践

```rust
//! REST API 设计与 OpenAPI 集成

use axum::{
    routing::{get, post, put, delete},
    Router, Json, extract::{Path, Query, State},
    response::IntoResponse,
    http::StatusCode,
};
use utoipa::{OpenApi, ToSchema};
use utoipa_swagger_ui::SwaggerUi;
use serde::{Deserialize, Serialize};
use validator::{Validate, ValidationError};
use chrono::{DateTime, Utc};
use uuid::Uuid;
use std::sync::Arc;

// ==================== OpenAPI Schema ====================

#[derive(OpenApi)]
#[openapi(
    paths(
        api_create_user,
        api_get_user,
        api_list_users,
        api_update_user,
        api_delete_user,
    ),
    components(
        schemas(User, CreateUserRequest, UpdateUserRequest, ApiError, PaginationParams)
    ),
    tags(
        (name = "users", description = "User management API")
    )
)]
pub struct ApiDoc;

// ==================== 数据模型 ====================

#[derive(Debug, Clone, Serialize, Deserialize, ToSchema, Validate)]
pub struct User {
    #[schema(example = "550e8400-e29b-41d4-a716-446655440000")]
    pub id: String,

    #[schema(example = "johndoe")]
    #[validate(length(min = 3, max = 50))]
    pub username: String,

    #[schema(example = "john@example.com")]
    #[validate(email)]
    pub email: String,

    #[schema(example = "2024-01-01T00:00:00Z")]
    pub created_at: DateTime<Utc>,

    #[schema(example = "2024-01-01T00:00:00Z")]
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Deserialize, ToSchema, Validate)]
pub struct CreateUserRequest {
    #[schema(example = "johndoe")]
    #[validate(length(min = 3, max = 50, message = "Username must be 3-50 characters"))]
    pub username: String,

    #[schema(example = "john@example.com")]
    #[validate(email(message = "Invalid email format"))]
    pub email: String,

    #[schema(example = "SecurePassword123!")]
    #[validate(length(min = 8, message = "Password must be at least 8 characters"))]
    pub password: String,
}

#[derive(Debug, Deserialize, ToSchema, Validate)]
pub struct UpdateUserRequest {
    #[schema(example = "johndoe")]
    #[validate(length(min = 3, max = 50))]
    pub username: Option<String>,

    #[schema(example = "john@example.com")]
    #[validate(email)]
    pub email: Option<String>,
}

#[derive(Debug, Deserialize, ToSchema)]
pub struct PaginationParams {
    #[schema(default = 1, example = 1)]
    pub page: Option<usize>,

    #[schema(default = 10, example = 10, maximum = 100)]
    pub per_page: Option<usize>,

    #[schema(example = "john")]
    pub search: Option<String>,
}

#[derive(Debug, Serialize, ToSchema)]
pub struct ApiError {
    pub code: String,
    pub message: String,
    pub details: Option<serde_json::Value>,
    pub timestamp: DateTime<Utc>,
}

#[derive(Debug, Serialize, ToSchema)]
pub struct PaginatedResponse<T> {
    pub data: Vec<T>,
    pub pagination: PaginationInfo,
}

#[derive(Debug, Serialize, ToSchema)]
pub struct PaginationInfo {
    pub page: usize,
    pub per_page: usize,
    pub total: usize,
    pub total_pages: usize,
}

// ==================== 服务层 ====================

pub struct UserService;

impl UserService {
    pub async fn create(req: CreateUserRequest) -> Result<User, ApiError> {
        req.validate().map_err(|e| ApiError {
            code: "VALIDATION_ERROR".to_string(),
            message: "Invalid request data".to_string(),
            details: Some(serde_json::json!({ "errors": e.to_string() })),
            timestamp: Utc::now(),
        })?;

        Ok(User {
            id: Uuid::new_v4().to_string(),
            username: req.username,
            email: req.email,
            created_at: Utc::now(),
            updated_at: Utc::now(),
        })
    }

    pub async fn get(id: &str) -> Result<User, ApiError> {
        // 模拟数据库查询
        Ok(User {
            id: id.to_string(),
            username: "johndoe".to_string(),
            email: "john@example.com".to_string(),
            created_at: Utc::now(),
            updated_at: Utc::now(),
        })
    }

    pub async fn list(params: PaginationParams) -> Result<PaginatedResponse<User>, ApiError> {
        let page = params.page.unwrap_or(1).max(1);
        let per_page = params.per_page.unwrap_or(10).clamp(1, 100);

        Ok(PaginatedResponse {
            data: vec![],
            pagination: PaginationInfo {
                page,
                per_page,
                total: 0,
                total_pages: 0,
            },
        })
    }
}

// ==================== API 处理器 ====================

/// Create a new user
#[utoipa::path(
    post,
    path = "/api/v1/users",
    request_body = CreateUserRequest,
    responses(
        (status = 201, description = "User created successfully", body = User),
        (status = 400, description = "Invalid request data", body = ApiError),
        (status = 409, description = "User already exists", body = ApiError),
    ),
    tag = "users"
)]
async fn api_create_user(
    Json(req): Json<CreateUserRequest>,
) -> Result<(StatusCode, Json<User>), (StatusCode, Json<ApiError>)> {
    match UserService::create(req).await {
        Ok(user) => Ok((StatusCode::CREATED, Json(user))),
        Err(e) => Err((StatusCode::BAD_REQUEST, Json(e))),
    }
}

/// Get a user by ID
#[utoipa::path(
    get,
    path = "/api/v1/users/{id}",
    params(
        ("id" = String, Path, description = "User ID")
    ),
    responses(
        (status = 200, description = "User found", body = User),
        (status = 404, description = "User not found", body = ApiError),
    ),
    tag = "users"
)]
async fn api_get_user(
    Path(id): Path<String>,
) -> Result<Json<User>, (StatusCode, Json<ApiError>)> {
    match UserService::get(&id).await {
        Ok(user) => Ok(Json(user)),
        Err(e) => Err((StatusCode::NOT_FOUND, Json(e))),
    }
}

/// List users with pagination
#[utoipa::path(
    get,
    path = "/api/v1/users",
    params(PaginationParams),
    responses(
        (status = 200, description = "List of users", body = PaginatedResponse<User>),
    ),
    tag = "users"
)]
async fn api_list_users(
    Query(params): Query<PaginationParams>,
) -> Json<PaginatedResponse<User>> {
    let result = UserService::list(params).await.unwrap();
    Json(result)
}

/// Update a user
#[utoipa::path(
    put,
    path = "/api/v1/users/{id}",
    params(
        ("id" = String, Path, description = "User ID")
    ),
    request_body = UpdateUserRequest,
    responses(
        (status = 200, description = "User updated", body = User),
        (status = 404, description = "User not found", body = ApiError),
        (status = 400, description = "Invalid request data", body = ApiError),
    ),
    tag = "users"
)]
async fn api_update_user(
    Path(id): Path<String>,
    Json(req): Json<UpdateUserRequest>,
) -> Result<Json<User>, (StatusCode, Json<ApiError>)> {
    // 实现更新逻辑
    let user = UserService::get(&id).await.map_err(|e| (StatusCode::NOT_FOUND, Json(e)))?;
    Ok(Json(user))
}

/// Delete a user
#[utoipa::path(
    delete,
    path = "/api/v1/users/{id}",
    params(
        ("id" = String, Path, description = "User ID")
    ),
    responses(
        (status = 204, description = "User deleted"),
        (status = 404, description = "User not found", body = ApiError),
    ),
    tag = "users"
)]
async fn api_delete_user(Path(id): Path<String>) -> StatusCode {
    // 实现删除逻辑
    StatusCode::NO_CONTENT
}

// ==================== 应用构建 ====================

pub fn create_api_router() -> Router {
    Router::new()
        .route("/api/v1/users", post(api_create_user).get(api_list_users))
        .route("/api/v1/users/:id", get(api_get_user).put(api_update_user).delete(api_delete_user))
        .merge(SwaggerUi::new("/swagger-ui").url("/api-docs/openapi.json", ApiDoc::openapi()))
}

#[tokio::main]
async fn main() {
    let app = create_api_router();

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

---

## 数据库集成

### SQLx 异步数据库

```rust
//! SQLx 数据库集成

use sqlx::{PgPool, Row, QueryBuilder, Postgres};
use sqlx::postgres::PgPoolOptions;
use serde::{Serialize, Deserialize};
use chrono::{DateTime, Utc};

// ==================== 数据库模型 ====================

#[derive(Debug, Clone, Serialize, Deserialize, sqlx::FromRow)]
pub struct User {
    pub id: i64,
    pub username: String,
    pub email: String,
    pub password_hash: String,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize, sqlx::FromRow)]
pub struct Post {
    pub id: i64,
    pub title: String,
    pub content: String,
    pub author_id: i64,
    pub published: bool,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

// ==================== 数据库连接管理 ====================

pub struct Database {
    pool: PgPool,
}

impl Database {
    pub async fn connect(database_url: &str) -> Result<Self, sqlx::Error> {
        let pool = PgPoolOptions::new()
            .max_connections(20)
            .min_connections(5)
            .acquire_timeout(std::time::Duration::from_secs(30))
            .idle_timeout(std::time::Duration::from_secs(600))
            .connect(database_url)
            .await?;

        Ok(Self { pool })
    }

    pub fn pool(&self) -> &PgPool {
        &self.pool
    }

    pub async fn migrate(&self) -> Result<(), sqlx::migrate::MigrateError> {
        sqlx::migrate!("./migrations").run(&self.pool).await
    }
}

// ==================== 用户 Repository ====================

pub struct UserRepository<'a> {
    db: &'a Database,
}

impl<'a> UserRepository<'a> {
    pub fn new(db: &'a Database) -> Self {
        Self { db }
    }

    pub async fn create(&self, username: &str, email: &str, password_hash: &str) -> Result<User, sqlx::Error> {
        sqlx::query_as::<_, User>(
            r#"
            INSERT INTO users (username, email, password_hash)
            VALUES ($1, $2, $3)
            RETURNING *
            "#
        )
        .bind(username)
        .bind(email)
        .bind(password_hash)
        .fetch_one(self.db.pool())
        .await
    }

    pub async fn find_by_id(&self, id: i64) -> Result<Option<User>, sqlx::Error> {
        sqlx::query_as::<_, User>("SELECT * FROM users WHERE id = $1")
            .bind(id)
            .fetch_optional(self.db.pool())
            .await
    }

    pub async fn find_by_username(&self, username: &str) -> Result<Option<User>, sqlx::Error> {
        sqlx::query_as::<_, User>("SELECT * FROM users WHERE username = $1")
            .bind(username)
            .fetch_optional(self.db.pool())
            .await
    }

    pub async fn list(&self, limit: i64, offset: i64) -> Result<Vec<User>, sqlx::Error> {
        sqlx::query_as::<_, User>("SELECT * FROM users ORDER BY created_at DESC LIMIT $1 OFFSET $2")
            .bind(limit)
            .bind(offset)
            .fetch_all(self.db.pool())
            .await
    }

    pub async fn update(&self, id: i64, username: Option<&str>, email: Option<&str>) -> Result<User, sqlx::Error> {
        sqlx::query_as::<_, User>(
            r#"
            UPDATE users
            SET username = COALESCE($1, username),
                email = COALESCE($2, email),
                updated_at = NOW()
            WHERE id = $3
            RETURNING *
            "#
        )
        .bind(username)
        .bind(email)
        .bind(id)
        .fetch_one(self.db.pool())
        .await
    }

    pub async fn delete(&self, id: i64) -> Result<bool, sqlx::Error> {
        let result = sqlx::query("DELETE FROM users WHERE id = $1")
            .bind(id)
            .execute(self.db.pool())
            .await?;

        Ok(result.rows_affected() > 0)
    }

    pub async fn search(&self, query: &str, limit: i64) -> Result<Vec<User>, sqlx::Error> {
        let pattern = format!("%{}%", query);

        sqlx::query_as::<_, User>(
            "SELECT * FROM users WHERE username ILIKE $1 OR email ILIKE $1 LIMIT $2"
        )
        .bind(pattern)
        .bind(limit)
        .fetch_all(self.db.pool())
        .await
    }
}

// ==================== 批量操作 ====================

pub struct BatchInserter<'a> {
    db: &'a Database,
}

impl<'a> BatchInserter<'a> {
    pub fn new(db: &'a Database) -> Self {
        Self { db }
    }

    pub async fn insert_users(&self, users: Vec<(String, String, String)>) -> Result<u64, sqlx::Error> {
        let mut builder = QueryBuilder::<Postgres>::new(
            "INSERT INTO users (username, email, password_hash) "
        );

        builder.push_values(users, |mut b, user| {
            b.push_bind(user.0)
             .push_bind(user.1)
             .push_bind(user.2);
        });

        let query = builder.build();
        let result = query.execute(self.db.pool()).await?;

        Ok(result.rows_affected())
    }
}

// ==================== 事务管理 ====================

pub struct Transaction<'a> {
    tx: sqlx::Transaction<'a, Postgres>,
}

impl<'a> Transaction<'a> {
    pub async fn begin(db: &'a Database) -> Result<Self, sqlx::Error> {
        let tx = db.pool().begin().await?;
        Ok(Self { tx })
    }

    pub async fn create_user(&mut self, username: &str, email: &str, password_hash: &str) -> Result<User, sqlx::Error> {
        sqlx::query_as::<_, User>(
            "INSERT INTO users (username, email, password_hash) VALUES ($1, $2, $3) RETURNING *"
        )
        .bind(username)
        .bind(email)
        .bind(password_hash)
        .fetch_one(&mut *self.tx)
        .await
    }

    pub async fn create_post(&mut self, title: &str, content: &str, author_id: i64) -> Result<Post, sqlx::Error> {
        sqlx::query_as::<_, Post>(
            "INSERT INTO posts (title, content, author_id) VALUES ($1, $2, $3) RETURNING *"
        )
        .bind(title)
        .bind(content)
        .bind(author_id)
        .fetch_one(&mut *self.tx)
        .await
    }

    pub async fn commit(self) -> Result<(), sqlx::Error> {
        self.tx.commit().await
    }

    pub async fn rollback(self) -> Result<(), sqlx::Error> {
        self.tx.rollback().await
    }
}
```

---

## 认证与授权

### JWT 认证

```rust
//! JWT 认证与授权

use jsonwebtoken::{encode, decode, Header, Validation, EncodingKey, DecodingKey, TokenData};
use serde::{Serialize, Deserialize};
use chrono::{DateTime, Utc, Duration};
use bcrypt::{hash, verify, DEFAULT_COST};
use std::sync::Arc;

// ==================== JWT 声明 ====================

#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: String,           // 用户ID
    pub username: String,      // 用户名
    pub email: String,         // 邮箱
    pub roles: Vec<String>,    // 角色
    pub iat: i64,              // 签发时间
    pub exp: i64,              // 过期时间
}

#[derive(Debug, Serialize, Deserialize)]
pub struct RefreshClaims {
    pub sub: String,
    pub token_version: i32,
    pub exp: i64,
}

// ==================== 认证服务 ====================

pub struct AuthService {
    jwt_secret: Arc<String>,
    refresh_secret: Arc<String>,
    access_token_expiry: Duration,
    refresh_token_expiry: Duration,
}

impl AuthService {
    pub fn new(jwt_secret: String, refresh_secret: String) -> Self {
        Self {
            jwt_secret: Arc::new(jwt_secret),
            refresh_secret: Arc::new(refresh_secret),
            access_token_expiry: Duration::hours(1),
            refresh_token_expiry: Duration::days(7),
        }
    }

    pub fn generate_tokens(&self, user_id: &str, username: &str, email: &str, roles: Vec<String>) -> Result<TokenPair, AuthError> {
        let now = Utc::now();

        // 生成访问令牌
        let access_claims = Claims {
            sub: user_id.to_string(),
            username: username.to_string(),
            email: email.to_string(),
            roles: roles.clone(),
            iat: now.timestamp(),
            exp: (now + self.access_token_expiry).timestamp(),
        };

        let access_token = encode(
            &Header::default(),
            &access_claims,
            &EncodingKey::from_secret(self.jwt_secret.as_bytes())
        ).map_err(|e| AuthError::TokenGeneration(e.to_string()))?;

        // 生成刷新令牌
        let refresh_claims = RefreshClaims {
            sub: user_id.to_string(),
            token_version: 1,
            exp: (now + self.refresh_token_expiry).timestamp(),
        };

        let refresh_token = encode(
            &Header::default(),
            &refresh_claims,
            &EncodingKey::from_secret(self.refresh_secret.as_bytes())
        ).map_err(|e| AuthError::TokenGeneration(e.to_string()))?;

        Ok(TokenPair {
            access_token,
            refresh_token,
            expires_in: self.access_token_expiry.num_seconds() as i64,
        })
    }

    pub fn validate_access_token(&self, token: &str) -> Result<Claims, AuthError> {
        let token_data = decode::<Claims>(
            token,
            &DecodingKey::from_secret(self.jwt_secret.as_bytes()),
            &Validation::default()
        ).map_err(|e| AuthError::InvalidToken(e.to_string()))?;

        // 检查令牌是否过期
        if token_data.claims.exp < Utc::now().timestamp() {
            return Err(AuthError::TokenExpired);
        }

        Ok(token_data.claims)
    }

    pub fn validate_refresh_token(&self, token: &str) -> Result<RefreshClaims, AuthError> {
        let token_data = decode::<RefreshClaims>(
            token,
            &DecodingKey::from_secret(self.refresh_secret.as_bytes()),
            &Validation::default()
        ).map_err(|e| AuthError::InvalidToken(e.to_string()))?;

        if token_data.claims.exp < Utc::now().timestamp() {
            return Err(AuthError::TokenExpired);
        }

        Ok(token_data.claims)
    }

    pub fn hash_password(&self, password: &str) -> Result<String, AuthError> {
        hash(password, DEFAULT_COST)
            .map_err(|e| AuthError::PasswordHashing(e.to_string()))
    }

    pub fn verify_password(&self, password: &str, hash: &str) -> Result<bool, AuthError> {
        verify(password, hash)
            .map_err(|e| AuthError::PasswordVerification(e.to_string()))
    }
}

#[derive(Debug)]
pub struct TokenPair {
    pub access_token: String,
    pub refresh_token: String,
    pub expires_in: i64,
}

#[derive(Debug)]
pub enum AuthError {
    TokenGeneration(String),
    InvalidToken(String),
    TokenExpired,
    PasswordHashing(String),
    PasswordVerification(String),
    Unauthorized,
}

// ==================== 权限检查 ====================

pub struct PermissionChecker;

impl PermissionChecker {
    pub fn has_role(claims: &Claims, required_role: &str) -> bool {
        claims.roles.contains(&required_role.to_string())
    }

    pub fn has_any_role(claims: &Claims, required_roles: &[String]) -> bool {
        required_roles.iter().any(|r| claims.roles.contains(r))
    }

    pub fn has_all_roles(claims: &Claims, required_roles: &[String]) -> bool {
        required_roles.iter().all(|r| claims.roles.contains(r))
    }
}
```

---

## 实时通信

### WebSocket 实现

```rust
//! WebSocket 实时通信

use axum::{
    extract::ws::{WebSocketUpgrade, WebSocket, Message, CloseFrame},
    extract::State,
    response::Response,
};
use serde::{Serialize, Deserialize};
use tokio::sync::{broadcast, RwLock};
use std::sync::Arc;
use std::collections::HashMap;
use futures::{sink::SinkExt, stream::StreamExt};

// ==================== 消息协议 ====================

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum WsMessage {
    #[serde(rename = "join")]
    Join { room: String },

    #[serde(rename = "leave")]
    Leave { room: String },

    #[serde(rename = "chat")]
    Chat { room: String, content: String },

    #[serde(rename = "typing")]
    Typing { room: String, user: String },

    #[serde(rename = "presence")]
    Presence { room: String, users: Vec<String> },

    #[serde(rename = "system")]
    System { message: String },

    #[serde(rename = "error")]
    Error { code: String, message: String },
}

// ==================== 连接管理 ====================

pub struct ConnectionManager {
    rooms: RwLock<HashMap<String, Room>>,
    user_connections: RwLock<HashMap<String, String>>, // user_id -> room
}

struct Room {
    tx: broadcast::Sender<WsMessage>,
    users: HashMap<String, String>, // user_id -> username
}

impl ConnectionManager {
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            rooms: RwLock::new(HashMap::new()),
            user_connections: RwLock::new(HashMap::new()),
        })
    }

    pub async fn join_room(&self, room_id: &str, user_id: &str, username: &str) -> broadcast::Receiver<WsMessage> {
        let mut rooms = self.rooms.write().await;

        let room = rooms.entry(room_id.to_string()).or_insert_with(|| {
            let (tx, _) = broadcast::channel(1000);
            Room { tx, users: HashMap::new() }
        });

        room.users.insert(user_id.to_string(), username.to_string());
        let rx = room.tx.subscribe();

        // 广播用户加入消息
        let join_msg = WsMessage::System {
            message: format!("{} joined the room", username)
        };
        let _ = room.tx.send(join_msg);

        // 更新用户连接
        self.user_connections.write().await.insert(user_id.to_string(), room_id.to_string());

        // 广播在线用户列表
        self.broadcast_presence(room_id).await;

        rx
    }

    pub async fn leave_room(&self, room_id: &str, user_id: &str) {
        let mut rooms = self.rooms.write().await;

        if let Some(room) = rooms.get_mut(room_id) {
            if let Some(username) = room.users.remove(user_id) {
                let leave_msg = WsMessage::System {
                    message: format!("{} left the room", username)
                };
                let _ = room.tx.send(leave_msg);

                // 如果房间为空，删除房间
                if room.users.is_empty() {
                    rooms.remove(room_id);
                } else {
                    self.broadcast_presence(room_id).await;
                }
            }
        }

        self.user_connections.write().await.remove(user_id);
    }

    pub async fn broadcast(&self, room_id: &str, message: WsMessage) {
        if let Some(room) = self.rooms.read().await.get(room_id) {
            let _ = room.tx.send(message);
        }
    }

    async fn broadcast_presence(&self, room_id: &str) {
        if let Some(room) = self.rooms.read().await.get(room_id) {
            let users: Vec<String> = room.users.values().cloned().collect();
            let presence = WsMessage::Presence {
                room: room_id.to_string(),
                users,
            };
            let _ = room.tx.send(presence);
        }
    }
}

// ==================== WebSocket 处理器 ====================

pub async fn ws_handler(
    ws: WebSocketUpgrade,
    State(manager): State<Arc<ConnectionManager>>,
) -> Response {
    ws.on_upgrade(move |socket| handle_socket(socket, manager))
}

async fn handle_socket(socket: WebSocket, manager: Arc<ConnectionManager>) {
    let (mut sender, mut receiver) = socket.split();
    let mut current_room: Option<String> = None;
    let mut current_user: Option<String> = None;
    let mut rx: Option<broadcast::Receiver<WsMessage>> = None;

    // 处理接收到的消息
    while let Some(Ok(msg)) = receiver.next().await {
        match msg {
            Message::Text(text) => {
                match serde_json::from_str::<WsMessage>(&text) {
                    Ok(ws_msg) => {
                        match ws_msg {
                            WsMessage::Join { room } => {
                                // 生成用户ID（实际应从认证信息获取）
                                let user_id = format!("user_{}", rand::random::<u32>());
                                let username = format!("User{}", rand::random::<u32>());

                                if let Some(old_room) = &current_room {
                                    manager.leave_room(old_room, &user_id).await;
                                }

                                rx = Some(manager.join_room(&room, &user_id, &username).await);
                                current_room = Some(room);
                                current_user = Some(user_id);
                            }

                            WsMessage::Chat { room, content } => {
                                if current_room.as_ref() == Some(&room) {
                                    let chat_msg = WsMessage::Chat { room, content };
                                    manager.broadcast(&room, chat_msg).await;
                                }
                            }

                            WsMessage::Typing { room, user } => {
                                if current_room.as_ref() == Some(&room) {
                                    let typing_msg = WsMessage::Typing { room, user };
                                    manager.broadcast(&room, typing_msg).await;
                                }
                            }

                            _ => {}
                        }
                    }
                    Err(e) => {
                        let error_msg = WsMessage::Error {
                            code: "INVALID_MESSAGE".to_string(),
                            message: e.to_string(),
                        };
                        let _ = sender.send(Message::Text(serde_json::to_string(&error_msg).unwrap())).await;
                    }
                }
            }

            Message::Close(_) => break,
            _ => {}
        }
    }

    // 清理
    if let (Some(room), Some(user)) = (&current_room, &current_user) {
        manager.leave_room(room, user).await;
    }
}
```

---

## 部署与运维

### Docker 部署

```dockerfile
# Dockerfile
FROM rust:1.75-slim as builder

WORKDIR /app
COPY Cargo.toml Cargo.lock ./
COPY src ./src

RUN cargo build --release

FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y ca-certificates && rm -rf /var/lib/apt/lists/*

WORKDIR /app
COPY --from=builder /app/target/release/myapp /app/

EXPOSE 3000

CMD ["./myapp"]
```

### Kubernetes 配置

```yaml
# deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: rust-web-app
spec:
  replicas: 3
  selector:
    matchLabels:
      app: rust-web-app
  template:
    metadata:
      labels:
        app: rust-web-app
    spec:
      containers:
      - name: app
        image: myregistry/rust-web-app:latest
        ports:
        - containerPort: 3000
        env:
        - name: DATABASE_URL
          valueFrom:
            secretKeyRef:
              name: db-credentials
              key: url
        - name: RUST_LOG
          value: info
        resources:
          requests:
            memory: "64Mi"
            cpu: "100m"
          limits:
            memory: "256Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 3000
          initialDelaySeconds: 10
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 3000
          initialDelaySeconds: 5
          periodSeconds: 5
```

---

## 最佳实践

### 1. 错误处理

```rust
//! 统一的错误处理

use axum::{
    response::{IntoResponse, Response},
    http::StatusCode,
    Json,
};
use serde_json::json;

pub struct AppError {
    code: StatusCode,
    message: String,
}

impl AppError {
    pub fn not_found(msg: impl Into<String>) -> Self {
        Self { code: StatusCode::NOT_FOUND, message: msg.into() }
    }

    pub fn bad_request(msg: impl Into<String>) -> Self {
        Self { code: StatusCode::BAD_REQUEST, message: msg.into() }
    }

    pub fn internal(msg: impl Into<String>) -> Self {
        Self { code: StatusCode::INTERNAL_SERVER_ERROR, message: msg.into() }
    }
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let body = Json(json!({
            "error": self.message,
            "status": self.code.as_u16()
        }));

        (self.code, body).into_response()
    }
}
```

### 2. 配置管理

```rust
//! 配置管理

use serde::Deserialize;
use config::{Config, ConfigError, Environment, File};

#[derive(Debug, Deserialize)]
pub struct Settings {
    pub server: ServerConfig,
    pub database: DatabaseConfig,
    pub jwt: JwtConfig,
    pub redis: RedisConfig,
}

#[derive(Debug, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
}

#[derive(Debug, Deserialize)]
pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
}

#[derive(Debug, Deserialize)]
pub struct JwtConfig {
    pub secret: String,
    pub expires_in: i64,
}

#[derive(Debug, Deserialize)]
pub struct RedisConfig {
    pub url: String,
}

impl Settings {
    pub fn new() -> Result<Self, ConfigError> {
        let s = Config::builder()
            .add_source(File::with_name("config/default"))
            .add_source(File::with_name("config/local").required(false))
            .add_source(Environment::with_prefix("APP"))
            .build()?;

        s.try_deserialize()
    }
}
```

---

## 总结

Rust 在 Web 开发领域提供了：

1. **极致性能**: 接近 C/C++ 的性能，远超解释型语言
2. **内存安全**: 编译时消除常见的 Web 安全漏洞
3. **并发优势**:  fearless concurrency，轻松处理高并发
4. **生态成熟**: 丰富的 Web 框架和工具
5. **全栈能力**: 从后端到 WebAssembly 前端的完整支持

通过本文档介绍的技术和最佳实践，开发者可以构建高性能、高可靠性的 Web 应用。
