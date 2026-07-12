# Axum 深度解析

**EN**: Axum Deep Dive
**Summary**: A practical deep dive into the Axum web framework: routing, extractors, middleware, state management, error handling, testing, and production patterns.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 通用 Rust 概念（async/await、Trait、并发、生命周期）请见 [`concept/`](../../../concept/)；Rust Web 框架选型与对比请见 [`concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md`](../../../concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md)。

---

## 目录

- [Axum 深度解析](#axum-深度解析)
  - [目录](#目录)
  - [一、定位与核心设计](#一定位与核心设计)
  - [二、路由系统](#二路由系统)
    - [2.1 基本路由](#21-基本路由)
    - [2.2 路由嵌套与路径参数](#22-路由嵌套与路径参数)
    - [2.3 Fallback](#23-fallback)
  - [三、Handler 与 Extractor](#三handler-与-extractor)
    - [3.1 Extractor 顺序的重要性](#31-extractor-顺序的重要性)
  - [四、响应与 IntoResponse](#四响应与-intoresponse)
  - [五、中间件与 Tower 集成](#五中间件与-tower-集成)
    - [5.1 自定义中间件](#51-自定义中间件)
  - [六、状态管理](#六状态管理)
  - [七、错误处理](#七错误处理)
    - [7.1 使用 Result](#71-使用-result)
    - [7.2 全局错误响应](#72-全局错误响应)
  - [八、测试](#八测试)
  - [九、生产实践](#九生产实践)
    - [9.1 Graceful Shutdown](#91-graceful-shutdown)
    - [9.2 请求体大小限制](#92-请求体大小限制)
    - [9.3 超时与限流](#93-超时与限流)
  - [十、常见陷阱](#十常见陷阱)
  - [十一、延伸阅读](#十一延伸阅读)

---

## 一、定位与核心设计

Axum 是 Tokio 生态的原生 Web 框架，其设计目标不是重新发明运行时或中间件抽象，而是把 Rust 已有的基础设施组合成类型安全的 HTTP 接口：

- **无自有运行时**：直接依赖 [`tokio`](https://tokio.rs/)，运行时选择由应用决定（multi-thread / current-thread）。
- **Tower / Service 作为中间件基础**：所有中间件都实现 `tower::Service`，这意味着 Axum 的中间件可以与任何基于 Tower 的库复用。
- **Handler 即 async fn**：一个 handler 可以是任何满足签名约束的 async 函数，参数通过 `FromRequest` extractor 自动解析，返回值通过 `IntoResponse` 自动序列化。
- **零成本抽象与类型安全**：路由、extractor、中间件组合在编译期确定，运行时无动态反射。

> **权威来源**: Tokio / Axum 设计哲学与运行时模型详见 [`02_tokio_deep_dive.md`](./02_tokio_deep_dive.md) 与 [`concept/03_advanced/01_async/01_async.md`](../../../concept/03_advanced/01_async/01_async.md)。

---

## 二、路由系统

### 2.1 基本路由

```rust
use axum::{
    routing::{get, post},
    Router,
};

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(root))
        .route("/users", post(create_user));

    let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}

async fn root() -> &'static str { "Hello, Axum!" }
async fn create_user() -> &'static str { "user created" }
```

### 2.2 路由嵌套与路径参数

```rust
use axum::{extract::Path, routing::get, Router};

let user_routes = Router::new()
    .route("/:id", get(show_user))
    .route("/:id/profile", get(show_profile));

let app = Router::new().nest("/users", user_routes);

async fn show_user(Path(id): Path<u64>) -> String {
    format!("user {}", id)
}
```

### 2.3 Fallback

```rust
let app = Router::new()
    .route("/api/health", get(health))
    .fallback(handler_404);

async fn handler_404() -> (StatusCode, &'static str) {
    (StatusCode::NOT_FOUND, "not found")
}
```

---

## 三、Handler 与 Extractor

Extractor 是 Axum 的核心抽象：它把 HTTP 请求的一部分转换为 Rust 类型。常见 extractor：

| Extractor | 来源 | 说明 |
|---|---|---|
| `Path<T>` | URL 路径参数 | 需要 `T: Deserialize` |
| `Query<T>` | URL 查询参数 | 需要 `T: Deserialize` |
| `Json<T>` | 请求体 | 需要 `T: Deserialize` |
| `Form<T>` | 表单 | 需要 `T: Deserialize` |
| `TypedHeader<T>` | 请求头 | 需要 `T: TypedHeader` |
| `State<S>` | 应用共享状态 | `S: Clone + Send + Sync + 'static` |
| `Extension<E>` | 请求扩展 | 通常用于依赖注入 |

```rust
use axum::{
    extract::{Path, Query, State},
    Json,
};
use serde::Deserialize;

#[derive(Deserialize)]
struct Pagination { page: usize, per_page: usize }

async fn list_users(
    State(db): State<Db>,
    Query(pagination): Query<Pagination>,
) -> Json<Vec<User>> {
    Json(db.fetch_users(pagination.page, pagination.per_page).await)
}
```

### 3.1 Extractor 顺序的重要性

请求体只能被消费一次。若 `Json` 前面有另一个会消费 body 的 extractor，则 `Json` 会失败。

```rust
// ✅ 正确：先取不消费 body 的 extractor，再取 Json
async fn handler(
    Path(id): Path<u64>,
    Json(payload): Json<Payload>,
) { }

// ❌ 错误：Json 在前，Path 在后不会导致问题；但两个 body extractor 同时存在会冲突
```

---

## 四、响应与 IntoResponse

Axum 自动为常见类型实现 `IntoResponse`：`&'static str`、`String`、`Json<T>`、`Html<T>`、`StatusCode`、`(StatusCode, T)` 等。

```rust
use axum::{response::Html, http::StatusCode};

async fn page() -> Html<&'static str> {
    Html("<h1>Hello</h1>")
}

async fn maybe_user(id: u64) -> Result<Json<User>, StatusCode> {
    if id == 0 {
        Err(StatusCode::BAD_REQUEST)
    } else {
        Ok(Json(User { id }))
    }
}
```

自定义响应类型：

```rust
use axum::{response::IntoResponse, body::Body};

struct CustomResponse(Vec<u8>);

impl IntoResponse for CustomResponse {
    fn into_response(self) -> axum::response::Response {
        ([("content-type", "application/octet-stream")], self.0).into_response()
    }
}
```

---

## 五、中间件与 Tower 集成

Axum 使用 `tower::ServiceBuilder` 组合中间件。

```rust
use axum::{Router, middleware};
use tower::ServiceBuilder;
use tower_http::{cors::CorsLayer, trace::TraceLayer, timeout::TimeoutLayer};
use std::time::Duration;

let middleware = ServiceBuilder::new()
    .layer(TraceLayer::new_for_http())
    .layer(CorsLayer::permissive())
    .layer(TimeoutLayer::new(Duration::from_secs(30)));

let app = Router::new()
    .route("/api/*", get(api_handler))
    .layer(middleware);
```

### 5.1 自定义中间件

```rust
use axum::{middleware::Next, response::Response, extract::Request};

async fn add_request_id(req: Request, next: Next) -> Response {
    let id = uuid::Uuid::new_v4().to_string();
    let (mut parts, body) = req.into_parts();
    parts.headers.insert("x-request-id", id.parse().unwrap());
    let req = Request::from_parts(parts, body);
    next.run(req).await
}

let app = Router::new().layer(middleware::from_fn(add_request_id));
```

---

## 六、状态管理

推荐通过 `State` extractor 共享只读或原子状态；可变状态使用 `Arc<RwLock<T>>` 或外部服务。

```rust
use std::sync::Arc;
use axum::extract::State;

#[derive(Clone)]
struct AppState {
    db: Arc<Db>,
    config: Arc<Config>,
}

let state = AppState {
    db: Arc::new(Db::new()),
    config: Arc::new(Config::load()),
};

let app = Router::new()
    .route("/items", get(list_items))
    .with_state(state);

async fn list_items(State(state): State<AppState>) -> Json<Vec<Item>> {
    Json(state.db.all_items().await)
}
```

> **权威来源**: `Arc`、`RwLock`、`Send/Sync` 语义详见 [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md)。

---

## 七、错误处理

### 7.1 使用 Result

```rust
use axum::{response::IntoResponse, http::StatusCode};
use thiserror::Error;

#[derive(Error, Debug)]
enum AppError {
    #[error("database error")]
    Database(#[from] sqlx::Error),
    #[error("not found")]
    NotFound,
}

impl IntoResponse for AppError {
    fn into_response(self) -> axum::response::Response {
        let (status, body) = match self {
            AppError::Database(_) => (StatusCode::INTERNAL_SERVER_ERROR, self.to_string()),
            AppError::NotFound => (StatusCode::NOT_FOUND, self.to_string()),
        };
        (status, body).into_response()
    }
}

async fn get_user(id: u64) -> Result<Json<User>, AppError> {
    if id == 0 { Err(AppError::NotFound) } else { Ok(Json(User { id })) }
}
```

### 7.2 全局错误响应

通过 `Result<T, AppError>` 与 `IntoResponse` 的组合，错误会自动转换为 HTTP 响应，无需在每个 handler 中手动处理。

---

## 八、测试

Axum 应用实现了 `tower::Service<Request>`，因此可以使用 Tower 的测试工具。

```rust
use axum::{body::Body, http::{Request, StatusCode}};
use tower::ServiceExt;

#[tokio::test]
async fn test_hello() {
    let app = app();
    let response = app
        .oneshot(Request::builder().uri("/").body(Body::empty()).unwrap())
        .await
        .unwrap();
    assert_eq!(response.status(), StatusCode::OK);
}
```

对于需要真实 HTTP 客户端的场景，可使用 [`axum-test`](https://docs.rs/axum-test) 或 `reqwest` + `tokio::spawn`。

---

## 九、生产实践

### 9.1 Graceful Shutdown

```rust
use tokio::signal;

let listener = tokio::net::TcpListener::bind("0.0.0.0:3000").await.unwrap();
axum::serve(listener, app)
    .with_graceful_shutdown(shutdown_signal())
    .await
    .unwrap();

async fn shutdown_signal() {
    signal::ctrl_c().await.expect("install ctrl+c handler");
}
```

### 9.2 请求体大小限制

```rust
use axum::extract::DefaultBodyLimit;

let app = Router::new()
    .route("/upload", post(upload))
    .layer(DefaultBodyLimit::max(1024 * 1024 * 10)); // 10 MB
```

### 9.3 超时与限流

使用 `tower_http::timeout::TimeoutLayer` 与 `tower::limit::RateLimitLayer` 组合。

---

## 十、常见陷阱

1. **在 handler 中执行阻塞操作**：应使用 `tokio::task::spawn_blocking`。
2. **忘记为共享状态实现 `Clone`**：`State<S>` 要求 `S: Clone`，通常用 `Arc` 包装。
3. **两个 body extractor 同时存在**：例如 `Json` 和 `String` 同时作为参数。
4. **错误类型未实现 `IntoResponse`**：会导致编译错误，提示返回值不匹配。
5. **运行时选择错误**：CPU 密集型服务不应在 current-thread runtime 上运行大量并发任务。

> **权威来源**: 异步运行时陷阱与阻塞任务处理详见 [`02_tokio_deep_dive.md`](./02_tokio_deep_dive.md)。

---

## 十一、延伸阅读

- [Axum 官方文档](https://docs.rs/axum/latest/axum/)
- [Tower 官方文档](https://docs.rs/tower/latest/tower/)
- [tokio-rs/axum examples](https://github.com/tokio-rs/axum/tree/main/examples)
- 框架对比与选型：[`concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md`](../../../concept/06_ecosystem/04_web_and_networking/03_web_frameworks.md)
- Async/await 与 Future：[`concept/03_advanced/01_async/01_async.md`](../../../concept/03_advanced/01_async/01_async.md)
