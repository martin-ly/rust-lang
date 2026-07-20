// API网关基本示例（Philosophical & Rigorous Example for API Gateway）
// 本示例展示如何用axum实现异步API路由与认证中间件
// This example demonstrates how to use axum for async API routing and authentication middleware
use axum::{Router, routing::get, middleware::from_fn, response::IntoResponse};
use std::net::SocketAddr;

async fn hello() -> impl IntoResponse {
    "Hello, API Gateway! 哲科严谨"
}

async fn auth_middleware<B>(req: axum::http::Request<B>, next: axum::middleware::Next<B>) -> impl IntoResponse {
    // 哲学：边界控制，科学：类型安全
    // Philosophy: boundary control, Science: type safety
    if req.headers().get("Authorization").is_some() {
        next.run(req).await
    } else {
        (axum::http::StatusCode::UNAUTHORIZED, "未授权/Unauthorized")
    }
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/hello", get(hello))
        .layer(from_fn(auth_middleware));
    let addr = SocketAddr::from(([127, 0, 0, 1], 3000));
    println!("Listening on {} 哲科严谨", addr);
    axum::Server::bind(&addr).serve(app.into_make_service()).await.unwrap();
} 