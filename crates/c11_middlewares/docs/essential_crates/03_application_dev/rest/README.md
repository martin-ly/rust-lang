# REST API - RESTful接口开发

## 📋 目录

- [概述](#概述)
- [Axum REST](#axum-rest)
- [Actix-web REST](#actix-web-rest)
- [最佳实践](#最佳实践)

---

## 概述

REST (Representational State Transfer) 是一种设计风格，用于构建可扩展的 Web 服务。

### 核心依赖

```toml
[dependencies]
# Axum
axum = { version = "0.7", features = ["macros"] }
tokio = { version = "1", features = ["full"] }
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# Actix-web
actix-web = "4"
```

---

## Axum REST

### 基础 CRUD

```rust
use axum::{
    Router,
    routing::{get, post, put, delete},
    extract::{Path, Json},
    http::StatusCode,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::Mutex;
use std::collections::HashMap;

#[derive(Debug, Serialize, Deserialize, Clone)]
struct User {
    id: u32,
    name: String,
    email: String,
}

type DB = Arc<Mutex<HashMap<u32, User>>>;

// GET /users - 获取所有用户
async fn list_users(db: axum::extract::State<DB>) -> Json<Vec<User>> {
    let users = db.lock().await.values().cloned().collect();
    Json(users)
}

// GET /users/:id - 获取单个用户
async fn get_user(
    Path(id): Path<u32>,
    db: axum::extract::State<DB>,
) -> Result<Json<User>, StatusCode> {
    db.lock()
        .await
        .get(&id)
        .cloned()
        .map(Json)
        .ok_or(StatusCode::NOT_FOUND)
}

// POST /users - 创建用户
async fn create_user(
    db: axum::extract::State<DB>,
    Json(user): Json<User>,
) -> (StatusCode, Json<User>) {
    db.lock().await.insert(user.id, user.clone());
    (StatusCode::CREATED, Json(user))
}

// PUT /users/:id - 更新用户
async fn update_user(
    Path(id): Path<u32>,
    db: axum::extract::State<DB>,
    Json(user): Json<User>,
) -> Result<Json<User>, StatusCode> {
    let mut db = db.lock().await;
    
    if db.contains_key(&id) {
        db.insert(id, user.clone());
        Ok(Json(user))
    } else {
        Err(StatusCode::NOT_FOUND)
    }
}

// DELETE /users/:id - 删除用户
async fn delete_user(
    Path(id): Path<u32>,
    db: axum::extract::State<DB>,
) -> StatusCode {
    if db.lock().await.remove(&id).is_some() {
        StatusCode::NO_CONTENT
    } else {
        StatusCode::NOT_FOUND
    }
}

#[tokio::main]
async fn main() {
    let db: DB = Arc::new(Mutex::new(HashMap::new()));
    
    let app = Router::new()
        .route("/users", get(list_users).post(create_user))
        .route("/users/:id", get(get_user).put(update_user).delete(delete_user))
        .with_state(db);
    
    println!("服务器运行在 http://127.0.0.1:3000");
    axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

### 查询参数

```rust
use axum::extract::Query;
use serde::Deserialize;

#[derive(Deserialize)]
struct Pagination {
    page: Option<u32>,
    per_page: Option<u32>,
}

async fn list_items(Query(pagination): Query<Pagination>) -> String {
    let page = pagination.page.unwrap_or(1);
    let per_page = pagination.per_page.unwrap_or(10);
    
    format!("第{}页，每页{}条", page, per_page)
}

// 使用: GET /items?page=2&per_page=20
```

### 请求验证

```rust
use axum::{Json, http::StatusCode};
use serde::{Deserialize, Serialize};
use validator::Validate;

#[derive(Debug, Deserialize, Validate)]
struct CreateUserRequest {
    #[validate(length(min = 1, max = 50))]
    name: String,
    
    #[validate(email)]
    email: String,
}

async fn create_user_validated(
    Json(payload): Json<CreateUserRequest>,
) -> Result<StatusCode, (StatusCode, String)> {
    payload.validate()
        .map_err(|e| (StatusCode::BAD_REQUEST, e.to_string()))?;
    
    Ok(StatusCode::CREATED)
}
```

---

## Actix-web REST

### 基础示例

```rust
use actix_web::{web, App, HttpServer, HttpResponse, Result};
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct Info {
    name: String,
}

async fn index() -> Result<HttpResponse> {
    Ok(HttpResponse::Ok().json(Info {
        name: "Actix REST API".to_string(),
    }))
}

async fn create(info: web::Json<Info>) -> Result<HttpResponse> {
    Ok(HttpResponse::Created().json(info.into_inner()))
}

#[actix_web::main]
async fn main() -> std::io::Result<()> {
    HttpServer::new(|| {
        App::new()
            .route("/", web::get().to(index))
            .route("/create", web::post().to(create))
    })
    .bind(("127.0.0.1", 8080))?
    .run()
    .await
}
```

---

## 最佳实践

### 1. 标准化响应格式

```rust
use serde::Serialize;

#[derive(Serialize)]
struct ApiResponse<T> {
    success: bool,
    data: Option<T>,
    error: Option<String>,
}

impl<T> ApiResponse<T> {
    fn success(data: T) -> Self {
        Self {
            success: true,
            data: Some(data),
            error: None,
        }
    }
    
    fn error(msg: String) -> Self {
        Self {
            success: false,
            data: None,
            error: Some(msg),
        }
    }
}
```

### 2. 版本控制

```rust
async fn v1_users() -> &'static str { "API v1" }
async fn v2_users() -> &'static str { "API v2" }

let app = Router::new()
    .route("/v1/users", get(v1_users))
    .route("/v2/users", get(v2_users));
```

### 3. 错误处理

```rust
use axum::{
    response::{IntoResponse, Response},
    http::StatusCode,
};

struct AppError(anyhow::Error);

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        (
            StatusCode::INTERNAL_SERVER_ERROR,
            format!("错误: {}", self.0)
        ).into_response()
    }
}

impl<E> From<E> for AppError
where
    E: Into<anyhow::Error>,
{
    fn from(err: E) -> Self {
        Self(err.into())
    }
}
```

### 4. API 文档（OpenAPI）

```rust
use utoipa::{OpenApi, ToSchema};

#[derive(ToSchema)]
struct User {
    id: u32,
    name: String,
}

#[utoipa::path(
    get,
    path = "/users",
    responses(
        (status = 200, description = "获取用户列表", body = [User])
    )
)]
async fn get_users() -> Json<Vec<User>> {
    Json(vec![])
}
```

---

## 参考资源

- [Axum 文档](https://docs.rs/axum/)
- [Actix-web 官网](https://actix.rs/)
- [REST API 设计指南](https://restfulapi.net/)

