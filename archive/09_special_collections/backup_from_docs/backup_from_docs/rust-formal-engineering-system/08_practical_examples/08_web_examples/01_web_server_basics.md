# Web 服务器基础（Web Server Basics）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [Web 服务器基础](#web-服务器基础web-server-basics)
  - [概述](#概述)
  - [使用 Axum](#使用-axum)
  - [使用 Actix-web](#使用-actix-web)
  - [路由处理](#路由处理)
  - [中间件](#中间件)
  - [实践示例](#实践示例)
  - [最佳实践](#最佳实践)
  - [参考资料](#参考资料)

---

## 概述

Rust 提供了多个高性能的 Web 框架，包括 Axum、Actix-web、Rocket 等。本示例展示如何使用这些框架构建 Web 服务器。

## 使用 Axum

### 基本服务器

```rust
use axum::{
    routing::get,
    Router,
    response::Json,
};
use serde_json::{Value, json};

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(root))
        .route("/api/hello", get(hello));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();

    println!("服务器运行在 http://0.0.0.0:3000");
    axum::serve(listener, app).await.unwrap();
}

async fn root() -> &'static str {
    "Hello, World!"
}

async fn hello() -> Json<Value> {
    Json(json!({
        "message": "Hello from Axum!",
        "status": "ok"
    }))
}
```

### 路由参数

```rust
use axum::{
    extract::Path,
    routing::get,
    Router,
};

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/users/:id", get(get_user))
        .route("/posts/:id/comments/:comment_id", get(get_comment));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();

    axum::serve(listener, app).await.unwrap();
}

async fn get_user(Path(id): Path<u32>) -> String {
    format!("用户 ID: {}", id)
}

async fn get_comment(
    Path((post_id, comment_id)): Path<(u32, u32)>
) -> String {
    format!("文章 {} 的评论 {}", post_id, comment_id)
}
```

### 请求体处理

```rust
use axum::{
    extract::Json,
    routing::post,
    Router,
};
use serde::{Deserialize, Serialize};

#[derive(Debug, Deserialize, Serialize)]
struct CreateUser {
    name: String,
    email: String,
}

#[derive(Debug, Serialize)]
struct User {
    id: u32,
    name: String,
    email: String,
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/users", post(create_user));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();

    axum::serve(listener, app).await.unwrap();
}

async fn create_user(Json(payload): Json<CreateUser>) -> Json<User> {
    let user = User {
        id: 1,
        name: payload.name,
        email: payload.email,
    };
    Json(user)
}
```

## 使用 Actix-web

### 基本服务器

```rust
use actix_web::{web, App, HttpServer, Responder};

async fn index() -> impl Responder {
    "Hello, World!"
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .route("/", web::get().to(index))
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
```

### 路由处理

```rust
use actix_web::{web, App, HttpServer, HttpResponse, Result};
use serde::{Deserialize, Serialize};

#[derive(Serialize)]
struct Message {
    message: String,
}

async fn hello() -> Result<HttpResponse> {
    Ok(HttpResponse::Ok().json(Message {
        message: "Hello from Actix-web!".to_string(),
    }))
}

async fn get_user(path: web::Path<u32>) -> Result<HttpResponse> {
    let user_id = path.into_inner();
    Ok(HttpResponse::Ok().json(Message {
        message: format!("用户 ID: {}", user_id),
    }))
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .route("/hello", web::get().to(hello))
            .route("/users/{id}", web::get().to(get_user))
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
```

## 路由处理

### RESTful API

```rust
use axum::{
    extract::{Path, Query},
    routing::{get, post, put, delete},
    Router,
    Json,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize, Clone)]
struct Todo {
    id: u32,
    title: String,
    completed: bool,
}

#[derive(Debug, Deserialize)]
struct CreateTodo {
    title: String,
}

#[derive(Debug, Deserialize)]
struct UpdateTodo {
    title: Option<String>,
    completed: Option<bool>,
}

#[derive(Debug, Deserialize)]
struct TodoQuery {
    completed: Option<bool>,
}

// 简单的内存存储（实际应用中应使用数据库）
type TodoStore = std::sync::Arc<tokio::sync::RwLock<HashMap<u32, Todo>>>;

#[tokio::main]
async fn main() {
    let store: TodoStore = std::sync::Arc::new(tokio::sync::RwLock::new(HashMap::new()));

    let app = Router::new()
        .route("/todos", get(list_todos).post(create_todo))
        .route("/todos/:id", get(get_todo).put(update_todo).delete(delete_todo))
        .with_state(store);

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();

    axum::serve(listener, app).await.unwrap();
}

async fn list_todos(
    Query(query): Query<TodoQuery>,
    axum::extract::State(store): axum::extract::State<TodoStore>,
) -> Json<Vec<Todo>> {
    let todos = store.read().await;
    let mut result: Vec<Todo> = todos.values().cloned().collect();

    if let Some(completed) = query.completed {
        result.retain(|todo| todo.completed == completed);
    }

    Json(result)
}

async fn get_todo(
    Path(id): Path<u32>,
    axum::extract::State(store): axum::extract::State<TodoStore>,
) -> Result<Json<Todo>, axum::http::StatusCode> {
    let todos = store.read().await;
    todos.get(&id)
        .cloned()
        .map(Json)
        .ok_or(axum::http::StatusCode::NOT_FOUND)
}

async fn create_todo(
    axum::extract::State(store): axum::extract::State<TodoStore>,
    Json(payload): Json<CreateTodo>,
) -> Json<Todo> {
    let mut todos = store.write().await;
    let id = todos.len() as u32 + 1;
    let todo = Todo {
        id,
        title: payload.title,
        completed: false,
    };
    todos.insert(id, todo.clone());
    Json(todo)
}

async fn update_todo(
    Path(id): Path<u32>,
    axum::extract::State(store): axum::extract::State<TodoStore>,
    Json(payload): Json<UpdateTodo>,
) -> Result<Json<Todo>, axum::http::StatusCode> {
    let mut todos = store.write().await;
    let todo = todos.get_mut(&id)
        .ok_or(axum::http::StatusCode::NOT_FOUND)?;

    if let Some(title) = payload.title {
        todo.title = title;
    }
    if let Some(completed) = payload.completed {
        todo.completed = completed;
    }

    Ok(Json(todo.clone()))
}

async fn delete_todo(
    Path(id): Path<u32>,
    axum::extract::State(store): axum::extract::State<TodoStore>,
) -> Result<axum::http::StatusCode, axum::http::StatusCode> {
    let mut todos = store.write().await;
    todos.remove(&id)
        .map(|_| axum::http::StatusCode::NO_CONTENT)
        .ok_or(axum::http::StatusCode::NOT_FOUND)
}
```

## 中间件

### 使用 Tower 中间件

```rust
use axum::{
    middleware,
    routing::get,
    Router,
};
use tower::ServiceBuilder;
use tower_http::{
    trace::TraceLayer,
    cors::CorsLayer,
    compression::CompressionLayer,
};

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(|| async { "Hello, World!" }))
        .layer(
            ServiceBuilder::new()
                .layer(TraceLayer::new_for_http())
                .layer(CorsLayer::permissive())
                .layer(CompressionLayer::new())
        );

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();

    axum::serve(listener, app).await.unwrap();
}
```

### 自定义中间件

```rust
use axum::{
    extract::Request,
    middleware::Next,
    response::Response,
    http::HeaderValue,
};

async fn add_custom_header(
    mut request: Request,
    next: Next,
) -> Response {
    // 在请求中添加自定义头
    request.headers_mut().insert(
        "X-Custom-Header",
        HeaderValue::from_static("custom-value"),
    );

    let response = next.run(request).await;
    response
}

// 使用自定义中间件
let app = Router::new()
    .route("/", get(|| async { "Hello, World!" }))
    .layer(middleware::from_fn(add_custom_header));
```

## 实践示例

### 示例 1：文件上传

```rust
use axum::{
    extract::Multipart,
    routing::post,
    Router,
    response::Json,
};
use serde_json::json;

async fn upload_file(mut multipart: Multipart) -> Json<serde_json::Value> {
    while let Some(field) = multipart.next_field().await.unwrap() {
        let name = field.name().unwrap().to_string();
        let data = field.bytes().await.unwrap();

        // 处理文件数据
        println!("字段名: {}, 大小: {} 字节", name, data.len());
    }

    Json(json!({
        "status": "success",
        "message": "文件上传成功"
    }))
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/upload", post(upload_file));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();

    axum::serve(listener, app).await.unwrap();
}
```

### 示例 2：WebSocket 支持

```rust
use axum::{
    extract::ws::{WebSocket, Message},
    routing::get,
    Router,
    response::Response,
};
use futures_util::{SinkExt, StreamExt};

async fn websocket_handler(ws: WebSocket) -> Response {
    // WebSocket 处理逻辑
    // 实际实现需要使用 axum 的 WebSocket 支持
    Response::new("WebSocket endpoint".into())
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/ws", get(websocket_handler));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000")
        .await
        .unwrap();

    axum::serve(listener, app).await.unwrap();
}
```

## 最佳实践

### 1. 错误处理

```rust
use axum::{
    response::IntoResponse,
    http::StatusCode,
};

#[derive(Debug)]
enum AppError {
    NotFound,
    InternalError,
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let (status, message) = match self {
            AppError::NotFound => (StatusCode::NOT_FOUND, "资源未找到"),
            AppError::InternalError => (StatusCode::INTERNAL_SERVER_ERROR, "内部服务器错误"),
        };
        (status, message).into_response()
    }
}
```

### 2. 状态管理

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

#[derive(Clone)]
struct AppState {
    db: Arc<RwLock<Database>>,
    config: Config,
}

// 在路由中使用状态
let app = Router::new()
    .route("/", get(handler))
    .with_state(app_state);
```

### 3. 日志记录

```rust
use tower_http::trace::TraceLayer;
use tracing_subscriber;

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();

    let app = Router::new()
        .route("/", get(|| async { "Hello, World!" }))
        .layer(TraceLayer::new_for_http());

    // ...
}
```

## 参考资料

- [Web 示例索引](./00_index.md)
- [实践示例索引](../00_index.md)
- [Axum 文档](https://docs.rs/axum/)
- [Actix-web 文档](https://docs.rs/actix-web/)

---

**导航**:
- 返回索引: [`00_index.md`](./00_index.md)
- 返回实践示例: [`../00_index.md`](../00_index.md)
