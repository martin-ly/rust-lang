//! API中间件
//! 
//! 提供认证、日志、限流等中间件

use axum::{
    extract::Request,
    http::{HeaderMap, StatusCode},
    middleware::Next,
    response::Response,
};
use std::time::Instant;

/// 请求日志中间件
pub async fn logging_middleware(
    headers: HeaderMap,
    request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    let start = Instant::now();
    let method = request.method().clone();
    let uri = request.uri().clone();
    
    let response = next.run(request).await;
    let duration = start.elapsed();
    
    println!(
        "{} {} - {}ms - {}",
        method,
        uri,
        duration.as_millis(),
        response.status()
    );
    
    Ok(response)
}

/// 认证中间件
pub async fn auth_middleware(
    headers: HeaderMap,
    mut request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // TODO: 实现JWT认证逻辑
    if let Some(auth_header) = headers.get("Authorization") {
        if let Ok(auth_str) = auth_header.to_str() {
            if auth_str.starts_with("Bearer ") {
                // 验证token
                return Ok(next.run(request).await);
            }
        }
    }
    
    // 对于需要认证的端点，返回401
    Ok(Response::builder()
        .status(StatusCode::UNAUTHORIZED)
        .body("Unauthorized".into())
        .unwrap())
}