# HTTP服务器模式

> 基于Axum和Actix-web的生产级模式

---

## 1. 架构模式对比

### 1.1 Axum - 函数式风格

```rust
use axum::{
    routing::{get, post},
    Router, Json, extract::{State, Path},
    http::StatusCode,
    response::IntoResponse,
};
use std::sync::Arc;
use tokio::sync::RwLock;

// 状态管理
#[derive(Clone)]
struct AppState {
    db: Database,
    cache: Arc<RwLock<Cache>>,
}

// 处理器函数
async fn get_user(
    State(state): State<AppState>,
    Path(id): Path<u64>,
) -> Result<Json<User>, StatusCode> {
    // 尝试缓存
    if let Some(user) = state.cache.read().await.get(&id) {
        return Ok(Json(user.clone()));
    }

    // 查询数据库
    let user = state.db
        .fetch_user(id)
        .await
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?
        .ok_or(StatusCode::NOT_FOUND)?;

    // 更新缓存
    state.cache.write().await.insert(id, user.clone());

    Ok(Json(user))
}

// 路由配置
fn app(state: AppState) -> Router {
    Router::new()
        .route("/users/:id", get(get_user).put(update_user))
        .route("/users", post(create_user))
        .layer(TraceLayer::new_for_http())
        .layer(CompressionLayer::new())
        .with_state(state)
}

#[tokio::main]
async fn main() {
    let state = AppState {
        db: Database::connect().await,
        cache: Arc::new(RwLock::new(Cache::new())),
    };

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app(state)).await.unwrap();
}
```

### 1.2 Actix-web - Actor风格

```rust
use actix_web::{web, App, HttpServer, HttpResponse, Result};
use actix::prelude::*;

// Actor定义
struct DbActor {
    connection: Database,
}

impl Actor for DbActor {
    type Context = Context<Self>;
}

// 消息定义
struct GetUser { id: u64 }
impl Message for GetUser {
    type Result = Result<User, Error>;
}

// 消息处理
impl Handler<GetUser> for DbActor {
    type Result = ResponseFuture<Result<User, Error>>;

    fn handle(&mut self, msg: GetUser, _ctx: &mut Self::Context) -> Self::Result {
        let conn = self.connection.clone();
        Box::pin(async move {
            conn.fetch_user(msg.id).await
        })
    }
}

// 处理器
async fn get_user(
    db: web::Data<Addr<DbActor>>,
    path: web::Path<u64>,
) -> Result<HttpResponse> {
    let user = db.send(GetUser { id: *path }).await??;
    Ok(HttpResponse::Ok().json(user))
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    let db_addr = DbActor::new().start();

    HttpServer::new(move || {
        App::new()
            .app_data(web::Data::new(db_addr.clone()))
            .route("/users/{id}", web::get().to(get_user))
    })
    .bind("0.0.0.0:8080")?
    .run()
    .await
}
```

---

## 2. 中间件链模式

### 2.1 认证中间件

```rust
use axum::{
    middleware::{self, Next},
    response::Response,
    extract::Request,
    http::{header, StatusCode},
};

// Tower Service实现
async fn auth_middleware(
    State(state): State<AppState>,
    req: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 提取token
    let token = req
        .headers()
        .get(header::AUTHORIZATION)
        .and_then(|h| h.to_str().ok())
        .and_then(|h| h.strip_prefix("Bearer "))
        .ok_or(StatusCode::UNAUTHORIZED)?;

    // 验证token
    let claims = state.auth.verify(token)
        .await
        .map_err(|_| StatusCode::UNAUTHORIZED)?;

    // 注入用户信息到请求扩展
    let mut req = req;
    req.extensions_mut().insert(claims);

    Ok(next.run(req).await)
}

// 使用
let app = Router::new()
    .route("/api/*path", get(api_handler))
    .layer(middleware::from_fn_with_state(state.clone(), auth_middleware));
```

### 2.2 限流中间件

```rust
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;
use std::time::{Duration, Instant};

#[derive(Clone)]
struct RateLimiter {
    requests: Arc<RwLock<HashMap<String, Vec<Instant>>>>,
    max_requests: usize,
    window: Duration,
}

impl RateLimiter {
    async fn check(&self, key: &str) -> bool {
        let now = Instant::now();
        let mut requests = self.requests.write().await;

        let timestamps = requests.entry(key.to_string()).or_default();

        // 清理过期请求
        timestamps.retain(|t| now.duration_since(*t) < self.window);

        if timestamps.len() >= self.max_requests {
            return false;
        }

        timestamps.push(now);
        true
    }
}

// 中间件实现
async fn rate_limit_middleware<B>(
    State(limiter): State<RateLimiter>,
    req: Request<B>,
    next: Next<B>,
) -> Result<Response, StatusCode> {
    let key = req.headers()
        .get("x-forwarded-for")
        .and_then(|h| h.to_str().ok())
        .unwrap_or("unknown")
        .to_string();

    if !limiter.check(&key).await {
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    Ok(next.run(req).await)
}
```

---

## 3. 错误处理模式

### 3.1 统一错误响应

```rust
use axum::{
    response::{IntoResponse, Response},
    Json,
};
use serde_json::json;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("database error: {0}")]
    Database(#[from] sqlx::Error),

    #[error("not found")]
    NotFound,

    #[error("validation error: {0}")]
    Validation(String),

    #[error("unauthorized")]
    Unauthorized,

    #[error("rate limited")]
    RateLimited,
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let (status, message) = match &self {
            AppError::Database(_) => (
                StatusCode::INTERNAL_SERVER_ERROR,
                "Internal server error".to_string(),
            ),
            AppError::NotFound => (
                StatusCode::NOT_FOUND,
                "Resource not found".to_string(),
            ),
            AppError::Validation(msg) => (
                StatusCode::BAD_REQUEST,
                msg.clone(),
            ),
            AppError::Unauthorized => (
                StatusCode::UNAUTHORIZED,
                "Unauthorized".to_string(),
            ),
            AppError::RateLimited => (
                StatusCode::TOO_MANY_REQUESTS,
                "Rate limited".to_string(),
            ),
        };

        let body = Json(json!({
            "error": message,
            "code": status.as_u16(),
        }));

        (status, body).into_response()
    }
}

// 使用
async fn handler() -> Result<Json<Data>, AppError> {
    let data = fetch_data().await?; // sqlx::Error自动转换
    Ok(Json(data))
}
```

### 3.2 请求验证

```rust
use validator::{Validate, ValidationError};
use serde::Deserialize;

#[derive(Deserialize, Validate)]
pub struct CreateUserRequest {
    #[validate(length(min = 3, max = 20))]
    pub username: String,

    #[validate(email)]
    pub email: String,

    #[validate(length(min = 8))]
    pub password: String,
}

async fn create_user(
    Json(req): Json<CreateUserRequest>,
) -> Result<Json<User>, AppError> {
    req.validate()
        .map_err(|e| AppError::Validation(e.to_string()))?;

    // 处理请求...
}
```

---

## 4. 流式响应

### 4.1 SSE (Server-Sent Events)

```rust
use axum::{
    response::sse::{Event, Sse},
    Router,
};
use futures::stream::{self, Stream};
use std::{convert::Infallible, time::Duration};
use tokio_stream::StreamExt;

async fn sse_handler() -> Sse<impl Stream<Item = Result<Event, Infallible>>> {
    let stream = stream::repeat_with(|| {
        Event::default()
            .data(format!("time: {}", chrono::Local::now()))
    })
    .throttle(Duration::from_secs(1))
    .map(Ok);

    Sse::new(stream).keep_alive(
        axum::response::sse::KeepAlive::new()
            .interval(Duration::from_secs(15))
            .text("keep-alive"),
    )
}

// 使用
let app = Router::new()
    .route("/events", get(sse_handler));
```

### 4.2 文件流式下载

```rust
use axum::{
    body::Body,
    response::Response,
    http::header,
};
use tokio::fs::File;
use tokio_util::io::ReaderStream;

async fn download_file(
    Path(filename): Path<String>,
) -> Result<Response, StatusCode> {
    let file = File::open(&filename)
        .await
        .map_err(|_| StatusCode::NOT_FOUND)?;

    let stream = ReaderStream::new(file);
    let body = Body::from_stream(stream);

    let headers = [
        (header::CONTENT_TYPE, "application/octet-stream"),
        (header::CONTENT_DISPOSITION, &format!("attachment; filename=\"{}\"", filename)),
    ];

    Ok(Response::builder()
        .header(header::CONTENT_TYPE, "application/octet-stream")
        .header(header::CONTENT_DISPOSITION, format!("attachment; filename=\"{}\"", filename))
        .body(body)
        .unwrap())
}
```

---

## 5. 优雅关闭

```rust
use tokio::signal;

#[tokio::main]
async fn main() {
    let app = create_app();

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();

    axum::serve(listener, app)
        .with_graceful_shutdown(shutdown_signal())
        .await
        .unwrap();
}

async fn shutdown_signal() {
    let ctrl_c = async {
        signal::ctrl_c()
            .await
            .expect("failed to install Ctrl+C handler");
    };

    #[cfg(unix)]
    let terminate = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("failed to install signal handler")
            .recv()
            .await;
    };

    #[cfg(not(unix))]
    let terminate = std::future::pending::<()>();

    tokio::select! {
        _ = ctrl_c => {},
        _ = terminate => {},
    }

    println!("signal received, starting graceful shutdown");
}
```

---

**维护者**: Rust Async Specialty Team
**更新日期**: 2026-03-05
