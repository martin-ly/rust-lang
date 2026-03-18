# Axum Web框架形式化分析

> **主题**: 现代异步Web框架
> **形式化框架**: 类型安全路由 + Tower服务抽象 + 提取器
> **参考**: Axum Documentation (<https://docs.rs/axum>)

---

## 目录

- [Axum Web框架形式化分析](#axum-web框架形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. 类型安全路由](#2-类型安全路由)
    - [定义 ROUTE-1 ( 路由类型 )](#定义-route-1--路由类型-)
    - [定义 ROUTE-2 ( 路径参数 )](#定义-route-2--路径参数-)
    - [定理 ROUTE-T1 ( 类型安全 )](#定理-route-t1--类型安全-)
  - [3. 提取器模式](#3-提取器模式)
    - [定义 EXTRACTOR-1 ( FromRequest trait )](#定义-extractor-1--fromrequest-trait-)
    - [定义 EXTRACTOR-2 ( 提取器组合 )](#定义-extractor-2--提取器组合-)
    - [定理 EXTRACTOR-T1 ( 独立性 )](#定理-extractor-t1--独立性-)
  - [4. Tower服务集成](#4-tower服务集成)
    - [定义 TOWER-1 ( Service trait )](#定义-tower-1--service-trait-)
    - [定义 TOWER-2 ( 中间件链 )](#定义-tower-2--中间件链-)
    - [定理 TOWER-T1 ( 组合性 )](#定理-tower-t1--组合性-)
  - [5. 状态管理](#5-状态管理)
    - [定义 STATE-1 ( 共享状态 )](#定义-state-1--共享状态-)
    - [定义 STATE-2 ( 状态注入 )](#定义-state-2--状态注入-)
    - [定理 STATE-T1 ( 线程安全 )](#定理-state-t1--线程安全-)
  - [6. 定理与证明](#6-定理与证明)
    - [定理 AXUM-T1 ( 编译时路由验证 )](#定理-axum-t1--编译时路由验证-)
    - [定理 AXUM-T2 ( 零成本抽象 )](#定理-axum-t2--零成本抽象-)
  - [7. 代码示例](#7-代码示例)
    - [示例1: CRUD API](#示例1-crud-api)
    - [示例2: 自定义提取器](#示例2-自定义提取器)
    - [示例3: 中间件](#示例3-中间件)
    - [示例4: 错误处理](#示例4-错误处理)

---

## 1. 引言

Axum是Tokio生态的现代Web框架：

- 类型安全路由
- 异步处理器
- Tower中间件兼容
- 宏-free设计（可选）
- 编译时路由验证

---

## 2. 类型安全路由

### 定义 ROUTE-1 ( 路由类型 )

```rust
Router::new()
    .route("/", get(root))
    .route("/users", post(create_user))
    .route("/users/:id", get(get_user).put(update_user))
```

**形式化**:

$$
\text{Route} = (\text{path} : \text{PathPattern}, \text{methods} : \text{Set}<\text{Method}>, \text{handler} : \text{Handler})
$$

### 定义 ROUTE-2 ( 路径参数 )

```rust
async fn get_user(Path(id): Path<u64>) -> impl IntoResponse
```

$$
\text{PathParam} : \text{str} \to T \text{ where } T : \text{FromStr}
$$

### 定理 ROUTE-T1 ( 类型安全 )

路径参数在编译时验证可转换性。

$$
\forall p : \text{Path}<T>.\ T : \text{FromStr} \lor \text{compile\_error}
$$

**证明**: 提取器约束确保类型可实现FromStr。$\square$

---

## 3. 提取器模式

### 定义 EXTRACTOR-1 ( FromRequest trait )

```rust
trait FromRequest<S>: Sized {
    type Rejection: IntoResponse;
    async fn from_request(req: Request, state: &S) -> Result<Self, Self::Rejection>;
}
```

**形式化**:

$$
\text{Extractor} : \text{Request} \times \text{State} \to \text{Result}<T, \text{Response}>
$$

### 定义 EXTRACTOR-2 ( 提取器组合 )

```rust
async fn handler(
    Path(id): Path<u64>,
    Query(params): Query<SearchParams>,
    Json(body): Json<CreateUser>,
    headers: HeaderMap,
) -> Result<impl IntoResponse, StatusCode>
```

$$
\text{CombinedExtractor} = \text{Path}<T_1> \times \text{Query}<T_2> \times \text{Json}<T_3> \times \ldots
$$

### 定理 EXTRACTOR-T1 ( 独立性 )

提取器之间相互独立，可任意组合。

$$
\forall e_1, e_2 : \text{Extractor}.\ e_1 \text{ and } e_2 \text{ commute}
$$

---

## 4. Tower服务集成

### 定义 TOWER-1 ( Service trait )

```rust
trait Service<Request> {
    type Response;
    type Error;
    type Future: Future<Output = Result<Self::Response, Self::Error>>;

    fn call(&mut self, req: Request) -> Self::Future;
}
```

### 定义 TOWER-2 ( 中间件链 )

$$
\text{MiddlewareStack} = m_n \circ m_{n-1} \circ \ldots \circ m_1 \circ \text{handler}
$$

### 定理 TOWER-T1 ( 组合性 )

Tower服务可任意组合而不改变类型安全。

$$
\forall s_1, s_2 : \text{Service}.\ s_1 \text{ and } s_2 \text{ composable}
$$

---

## 5. 状态管理

### 定义 STATE-1 ( 共享状态 )

```rust
#[derive(Clone)]
struct AppState {
    db: Database,
    cache: Cache,
}

let app = Router::new()
    .route("/", get(handler))
    .with_state(state);
```

$$
\text{State} = \{ s : S \mid s : \text{Clone} + \text{Send} + \text{Sync} + 'static \}
$$

### 定义 STATE-2 ( 状态注入 )

$$
\text{Extension}(s) : \text{Request} \to \text{Request} \text{ with } s \text{ attached}
$$

### 定理 STATE-T1 ( 线程安全 )

共享状态自动满足线程安全约束。

$$
\text{with\_state}(s) \text{ requires } s : \text{Send} + \text{Sync}
$$

---

## 6. 定理与证明

### 定理 AXUM-T1 ( 编译时路由验证 )

无效路由在编译时检测。

$$
\text{invalid\_route} \to \text{compile\_error}
$$

**证明**: 路由构建器使用类型系统确保handler与路径匹配。$\square$

### 定理 AXUM-T2 ( 零成本抽象 )

路由分发无运行时开销。

$$
\text{dispatch\_time} = O(1)
$$

**证明**: 路由匹配使用哈希表，单次查找确定handler。$\square$

---

## 7. 代码示例

### 示例1: CRUD API

```rust
use axum::{
    routing::{get, post, put, delete},
    Router, Json, extract::Path,
    http::StatusCode,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;
use tokio::sync::RwLock;

#[derive(Clone, Serialize, Deserialize)]
struct User {
    id: u64,
    name: String,
    email: String,
}

#[derive(Deserialize)]
struct CreateUser {
    name: String,
    email: String,
}

type Db = Arc<RwLock<Vec<User>>>;

async fn list_users(State(db): State<Db>) -> Json<Vec<User>> {
    let users = db.read().await.clone();
    Json(users)
}

async fn get_user(
    State(db): State<Db>,
    Path(id): Path<u64>,
) -> Result<Json<User>, StatusCode> {
    let users = db.read().await;
    users
        .iter()
        .find(|u| u.id == id)
        .cloned()
        .map(Json)
        .ok_or(StatusCode::NOT_FOUND)
}

async fn create_user(
    State(db): State<Db>,
    Json(input): Json<CreateUser>,
) -> (StatusCode, Json<User>) {
    let mut users = db.write().await;
    let user = User {
        id: users.len() as u64 + 1,
        name: input.name,
        email: input.email,
    };
    users.push(user.clone());
    (StatusCode::CREATED, Json(user))
}

async fn delete_user(
    State(db): State<Db>,
    Path(id): Path<u64>,
) -> StatusCode {
    let mut users = db.write().await;
    if let Some(pos) = users.iter().position(|u| u.id == id) {
        users.remove(pos);
        StatusCode::NO_CONTENT
    } else {
        StatusCode::NOT_FOUND
    }
}

fn app() -> Router {
    let db: Db = Arc::new(RwLock::new(Vec::new()));

    Router::new()
        .route("/users", get(list_users).post(create_user))
        .route("/users/:id", get(get_user).delete(delete_user))
        .with_state(db)
}
```

### 示例2: 自定义提取器

```rust
use axum::{
    async_trait,
    extract::FromRequestParts,
    http::{request::Parts, StatusCode},
};
use headers::{authorization::Bearer, Authorization, HeaderMapExt};

struct AuthenticatedUser {
    user_id: u64,
    permissions: Vec<String>,
}

#[async_trait]
impl<S> FromRequestParts<S> for AuthenticatedUser
where
    S: Send + Sync,
{
    type Rejection = StatusCode;

    async fn from_request_parts(parts: &mut Parts, state: &S) -> Result<Self, Self::Rejection> {
        // 从header提取token
        let auth_header = parts
            .headers
            .typed_get::<Authorization<Bearer>>()
            .ok_or(StatusCode::UNAUTHORIZED)?;

        // 验证token
        let token = auth_header.token();
        validate_token(token).await
            .map_err(|_| StatusCode::UNAUTHORIZED)
    }
}

async fn protected_handler(
    user: AuthenticatedUser,
) -> Result<String, StatusCode> {
    Ok(format!("Hello user {}", user.user_id))
}
```

### 示例3: 中间件

```rust
use axum::{
    middleware::{self, Next},
    response::Response,
    http::Request,
};
use tower::ServiceBuilder;
use tower_http::{
    trace::TraceLayer,
    compression::CompressionLayer,
    cors::CorsLayer,
};

async fn auth_middleware<B>(
    req: Request<B>,
    next: Next<B>,
) -> Result<Response, StatusCode> {
    // 验证请求
    if !is_valid(&req) {
        return Err(StatusCode::UNAUTHORIZED);
    }

    Ok(next.run(req).await)
}

fn app_with_middleware() -> Router {
    Router::new()
        .route("/api/*path", get(api_handler))
        .layer(
            ServiceBuilder::new()
                .layer(TraceLayer::new_for_http())
                .layer(CompressionLayer::new())
                .layer(CorsLayer::permissive())
                .layer(middleware::from_fn(auth_middleware))
        )
}
```

### 示例4: 错误处理

```rust
use axum::{
    response::{IntoResponse, Response},
    Json,
};
use serde_json::json;
use thiserror::Error;

#[derive(Error, Debug)]
enum AppError {
    #[error("database error")]
    Database(#[from] sqlx::Error),
    #[error("not found")]
    NotFound,
    #[error("validation error: {0}")]
    Validation(String),
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let (status, message) = match self {
            AppError::Database(_) => (
                StatusCode::INTERNAL_SERVER_ERROR,
                "Internal server error".to_string(),
            ),
            AppError::NotFound => (StatusCode::NOT_FOUND, "Not found".to_string()),
            AppError::Validation(msg) => (StatusCode::BAD_REQUEST, msg),
        };

        let body = Json(json!({
            "error": message,
        }));

        (status, body).into_response()
    }
}

type Result<T> = std::result::Result<T, AppError>;

async fn may_fail() -> Result<Json<User>> {
    let user = fetch_user().await?;  // ?自动转换错误
    Ok(Json(user))
}
```

---

**维护者**: Rust Web Framework Formal Methods Team
**创建日期**: 2026-03-05
**Axum版本**: 0.7+
**状态**: ✅ 已对齐
