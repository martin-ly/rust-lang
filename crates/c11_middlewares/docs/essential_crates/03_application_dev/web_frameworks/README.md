# Web 框架

> **核心库**: axum, actix-web, rocket, warp, poem  
> **适用场景**: RESTful API、微服务、全栈Web应用

---

## 📋 框架对比

| 框架 | 性能 | 易用性 | 生态 | 异步 | 推荐度 |
|------|------|--------|------|------|--------|
| **axum** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | Tokio | ⭐⭐⭐⭐⭐ |
| **actix-web** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | actix | ⭐⭐⭐⭐⭐ |
| **rocket** | ⭐⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐⭐⭐⭐ | Tokio | ⭐⭐⭐⭐ |
| **warp** | ⭐⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐⭐⭐ | Tokio | ⭐⭐⭐⭐ |

---

## 🚀 axum - 现代化首选

### 核心特性

- ✅ 基于 tokio 和 hyper
- ✅ 类型安全的提取器
- ✅ 中间件系统强大
- ✅ 与 tower 生态集成

### 快速开始

```rust
use axum::{
    routing::{get, post},
    Router, Json, extract::{Path, Query},
    response::IntoResponse,
    http::StatusCode,
};
use serde::{Deserialize, Serialize};
use std::net::SocketAddr;

#[derive(Serialize)]
struct User {
    id: u64,
    name: String,
}

#[derive(Deserialize)]
struct CreateUser {
    name: String,
}

#[derive(Deserialize)]
struct Pagination {
    page: Option<u32>,
    per_page: Option<u32>,
}

// 路由处理器
async fn hello() -> &'static str {
    "Hello, World!"
}

async fn get_user(Path(id): Path<u64>) -> Json<User> {
    Json(User {
        id,
        name: format!("User {}", id),
    })
}

async fn list_users(Query(pagination): Query<Pagination>) -> Json<Vec<User>> {
    let page = pagination.page.unwrap_or(1);
    let per_page = pagination.per_page.unwrap_or(10);
    
    Json(vec![
        User { id: 1, name: "Alice".to_string() },
        User { id: 2, name: "Bob".to_string() },
    ])
}

async fn create_user(Json(payload): Json<CreateUser>) -> (StatusCode, Json<User>) {
    (
        StatusCode::CREATED,
        Json(User {
            id: 1,
            name: payload.name,
        }),
    )
}

#[tokio::main]
async fn main() {
    // 构建应用
    let app = Router::new()
        .route("/", get(hello))
        .route("/users", get(list_users).post(create_user))
        .route("/users/:id", get(get_user));
    
    // 启动服务器
    let addr = SocketAddr::from(([127, 0, 0, 1], 3000));
    println!("Listening on {}", addr);
    
    axum::Server::bind(&addr)
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

### 状态共享

```rust
use axum::{Router, extract::State, routing::get};
use std::sync::Arc;
use tokio::sync::Mutex;

#[derive(Clone)]
struct AppState {
    counter: Arc<Mutex<u64>>,
}

async fn increment(State(state): State<AppState>) -> String {
    let mut counter = state.counter.lock().await;
    *counter += 1;
    format!("Counter: {}", counter)
}

#[tokio::main]
async fn main() {
    let state = AppState {
        counter: Arc::new(Mutex::new(0)),
    };
    
    let app = Router::new()
        .route("/increment", get(increment))
        .with_state(state);
    
    // ... 启动服务器
}
```

### 中间件

```rust
use axum::{
    Router, routing::get,
    middleware::{self, Next},
    http::{Request, StatusCode},
    response::Response,
};

async fn auth_middleware<B>(
    req: Request<B>,
    next: Next<B>,
) -> Result<Response, StatusCode> {
    // 验证逻辑
    let auth_header = req.headers()
        .get("authorization")
        .and_then(|v| v.to_str().ok());
    
    if auth_header != Some("Bearer valid_token") {
        return Err(StatusCode::UNAUTHORIZED);
    }
    
    Ok(next.run(req).await)
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/protected", get(|| async { "Protected!" }))
        .layer(middleware::from_fn(auth_middleware));
}
```

---

## ⚡ actix-web - 高性能

### 快速开始1

```rust
use actix_web::{web, App, HttpServer, Responder, HttpResponse};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct User {
    id: u32,
    name: String,
}

async fn hello() -> impl Responder {
    HttpResponse::Ok().body("Hello world!")
}

async fn get_user(path: web::Path<u32>) -> impl Responder {
    let user = User {
        id: path.into_inner(),
        name: "Alice".to_string(),
    };
    web::Json(user)
}

async fn create_user(user: web::Json<User>) -> impl Responder {
    HttpResponse::Created().json(user.into_inner())
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .route("/", web::get().to(hello))
            .route("/users/{id}", web::get().to(get_user))
            .route("/users", web::post().to(create_user))
    })
    .bind(("127.0.0.1", 8080))?
    .run()
    .await
}
```

---

## 🚀 rocket - 易用性极佳

### 快速开始2

```rust
#[macro_use] extern crate rocket;
use rocket::serde::{Serialize, Deserialize, json::Json};

#[derive(Serialize, Deserialize)]
#[serde(crate = "rocket::serde")]
struct User {
    id: u64,
    name: String,
}

#[get("/")]
fn index() -> &'static str {
    "Hello, world!"
}

#[get("/users/<id>")]
fn get_user(id: u64) -> Json<User> {
    Json(User {
        id,
        name: format!("User {}", id),
    })
}

#[post("/users", data = "<user>")]
fn create_user(user: Json<User>) -> Json<User> {
    user
}

#[launch]
fn rocket() -> _ {
    rocket::build()
        .mount("/", routes![index, get_user, create_user])
}
```

---

## 💡 最佳实践

### 选择框架

```rust
// ✅ 推荐 axum (2024+)
// - 现代化设计
// - 类型安全
// - Tower 生态
// - 活跃维护

// ✅ actix-web (成熟稳定)
// - 最高性能
// - 功能完整
// - 大规模验证

// ✅ rocket (快速原型)
// - 最易上手
// - 宏驱动
// - 开发体验好
```

### 错误处理

```rust
use axum::{
    response::{IntoResponse, Response},
    http::StatusCode,
    Json,
};
use serde::Serialize;

#[derive(Serialize)]
struct ErrorResponse {
    error: String,
}

enum AppError {
    NotFound,
    InternalError,
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let (status, message) = match self {
            AppError::NotFound => (StatusCode::NOT_FOUND, "Not found"),
            AppError::InternalError => (StatusCode::INTERNAL_SERVER_ERROR, "Internal error"),
        };
        
        (status, Json(ErrorResponse {
            error: message.to_string(),
        })).into_response()
    }
}
```

---

## 🔧 常见场景

### RESTful API

```rust
use axum::{Router, routing::{get, post, put, delete}};

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/api/users", get(list_users).post(create_user))
        .route("/api/users/:id", get(get_user).put(update_user).delete(delete_user));
}
```

### WebSocket

```rust
use axum::{
    extract::ws::{WebSocket, WebSocketUpgrade},
    response::Response,
    routing::get,
    Router,
};

async fn ws_handler(ws: WebSocketUpgrade) -> Response {
    ws.on_upgrade(handle_socket)
}

async fn handle_socket(mut socket: WebSocket) {
    while let Some(msg) = socket.recv().await {
        if let Ok(msg) = msg {
            if socket.send(msg).await.is_err() {
                break;
            }
        }
    }
}

#[tokio::main]
async fn main() {
    let app = Router::new().route("/ws", get(ws_handler));
}
```

---

**文档版本**: 1.0.0  
**最后更新**: 2025-10-20
