# Middleware - Web中间件

## 📋 目录

- [Middleware - Web中间件](#middleware---web中间件)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [核心依赖](#核心依赖)
  - [Tower](#tower)
    - [Service Trait](#service-trait)
    - [Layer](#layer)
  - [Axum 中间件](#axum-中间件)
    - [函数式中间件](#函数式中间件)
    - [认证中间件](#认证中间件)
  - [实战示例](#实战示例)
    - [CORS 中间件](#cors-中间件)
    - [压缩中间件](#压缩中间件)
    - [限流中间件](#限流中间件)
    - [超时中间件](#超时中间件)
  - [参考资源](#参考资源)

---

## 概述

中间件是 Web 应用中处理请求和响应的可复用组件，提供认证、日志、压缩等功能。

### 核心依赖

```toml
[dependencies]
# Tower - 通用中间件框架
tower = { version = "0.4", features = ["full"] }
tower-http = { version = "0.5", features = ["full"] }

# Axum
axum = "0.7"
```

---

## Tower

### Service Trait

```rust
use tower::Service;
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// Tower 的核心抽象
trait Service<Request> {
    type Response;
    type Error;
    type Future: Future<Output = Result<Self::Response, Self::Error>>;
    
    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>>;
    fn call(&mut self, req: Request) -> Self::Future;
}
```

### Layer

```rust
use tower::{Service, ServiceBuilder, ServiceExt};
use tower::layer::Layer;

// Layer 用于构建中间件
struct LogLayer;

impl<S> Layer<S> for LogLayer {
    type Service = LogService<S>;
    
    fn layer(&self, service: S) -> Self::Service {
        LogService { inner: service }
    }
}

struct LogService<S> {
    inner: S,
}

impl<S, Request> Service<Request> for LogService<S>
where
    S: Service<Request>,
{
    type Response = S::Response;
    type Error = S::Error;
    type Future = S::Future;
    
    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>> {
        self.inner.poll_ready(cx)
    }
    
    fn call(&mut self, req: Request) -> Self::Future {
        println!("处理请求");
        self.inner.call(req)
    }
}
```

---

## Axum 中间件

### 函数式中间件

```rust
use axum::{
    Router,
    routing::get,
    middleware::{self, Next},
    http::Request,
    response::Response,
};

async fn logging_middleware<B>(
    req: Request<B>,
    next: Next<B>,
) -> Response {
    println!("请求: {} {}", req.method(), req.uri());
    
    let response = next.run(req).await;
    
    println!("响应状态: {}", response.status());
    response
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(|| async { "Hello" }))
        .layer(middleware::from_fn(logging_middleware));
    
    println!("服务器运行中...");
}
```

### 认证中间件

```rust
use axum::{
    Router,
    middleware::{self, Next},
    http::{Request, StatusCode},
    response::{Response, IntoResponse},
};

async fn auth_middleware<B>(
    req: Request<B>,
    next: Next<B>,
) -> Result<Response, StatusCode> {
    let auth_header = req
        .headers()
        .get("authorization")
        .and_then(|v| v.to_str().ok());
    
    match auth_header {
        Some(token) if token.starts_with("Bearer ") => {
            Ok(next.run(req).await)
        }
        _ => Err(StatusCode::UNAUTHORIZED),
    }
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/protected", get(|| async { "Protected" }))
        .layer(middleware::from_fn(auth_middleware));
}
```

---

## 实战示例

### CORS 中间件

```rust
use tower_http::cors::{CorsLayer, Any};

fn cors_layer() -> CorsLayer {
    CorsLayer::new()
        .allow_origin(Any)
        .allow_methods(Any)
        .allow_headers(Any)
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(|| async { "Hello" }))
        .layer(cors_layer());
}
```

### 压缩中间件

```rust
use tower_http::compression::CompressionLayer;

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(|| async { "Hello, World!".repeat(100) }))
        .layer(CompressionLayer::new());
}
```

### 限流中间件

```rust
use tower::limit::RateLimitLayer;
use std::time::Duration;

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(|| async { "Hello" }))
        .layer(RateLimitLayer::new(100, Duration::from_secs(60))); // 每分钟100次
}
```

### 超时中间件

```rust
use tower_http::timeout::TimeoutLayer;
use std::time::Duration;

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/", get(|| async {
            tokio::time::sleep(Duration::from_secs(5)).await;
            "Slow response"
        }))
        .layer(TimeoutLayer::new(Duration::from_secs(3))); // 3秒超时
}
```

---

## 参考资源

- [Tower 文档](https://docs.rs/tower/)
- [tower-http GitHub](https://github.com/tower-rs/tower-http)
