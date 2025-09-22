//! API中间件模块
//! 
//! 提供认证、日志记录、速率限制等中间件

use axum::{
    extract::{Request, State},
    http::{HeaderMap, StatusCode},
    middleware::Next,
    response::Response,
};
use std::sync::Arc;
use std::time::{Duration, Instant};
use std::collections::HashMap;
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};

/// 速率限制器
#[derive(Debug, Clone)]
pub struct RateLimiter {
    requests: Arc<RwLock<HashMap<String, Vec<Instant>>>>,
    max_requests: u32,
    window_duration: Duration,
}

impl RateLimiter {
    pub fn new(max_requests: u32, window_duration: Duration) -> Self {
        Self {
            requests: Arc::new(RwLock::new(HashMap::new())),
            max_requests,
            window_duration,
        }
    }

    pub async fn is_allowed(&self, key: &str) -> bool {
        let mut requests = self.requests.write().await;
        let now = Instant::now();
        let window_start = now - self.window_duration;

        // 清理过期的请求记录
        if let Some(timestamps) = requests.get_mut(key) {
            timestamps.retain(|&timestamp| timestamp > window_start);
        }

        // 检查是否超过限制
        let current_requests = requests
            .get(key)
            .map(|timestamps| timestamps.len())
            .unwrap_or(0);

        if current_requests < self.max_requests as usize {
            requests
                .entry(key.to_string())
                .or_insert_with(Vec::new)
                .push(now);
            true
        } else {
            false
        }
    }
}

/// 认证中间件
pub async fn auth_middleware(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
    request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 从请求头中提取令牌
    let token = headers
        .get("Authorization")
        .and_then(|header| header.to_str().ok())
        .and_then(|header| header.strip_prefix("Bearer "));

    if let Some(token) = token {
        // 验证令牌
        if state.auth.validate_token(token).await {
            return Ok(next.run(request).await);
        }
    }

    Err(StatusCode::UNAUTHORIZED)
}

/// 速率限制中间件
pub async fn rate_limit_middleware(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
    request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 从请求头中提取客户端标识
    let client_id = headers
        .get("X-Client-ID")
        .and_then(|header| header.to_str().ok())
        .unwrap_or("anonymous");

    // 检查速率限制
    if state.rate_limiter.is_allowed(client_id).await {
        Ok(next.run(request).await)
    } else {
        Err(StatusCode::TOO_MANY_REQUESTS)
    }
}

/// 日志记录中间件
pub async fn logging_middleware(
    State(state): State<Arc<AppState>>,
    request: Request,
    next: Next,
) -> Response {
    let start = Instant::now();
    let method = request.method().clone();
    let uri = request.uri().clone();

    // 处理请求
    let response = next.run(request).await;

    // 记录请求日志
    let duration = start.elapsed();
    let status = response.status();
    
    tracing::info!(
        "{} {} - {} - {:?}",
        method,
        uri,
        status,
        duration
    );

    response
}

/// CORS中间件
pub async fn cors_middleware(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
    request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 检查Origin头
    if let Some(origin) = headers.get("Origin") {
        if let Ok(origin_str) = origin.to_str() {
            if state.cors.is_allowed_origin(origin_str) {
                return Ok(next.run(request).await);
            }
        }
    }

    Err(StatusCode::FORBIDDEN)
}

/// 压缩中间件
pub async fn compression_middleware(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
    request: Request,
    next: Next,
) -> Response {
    // 检查是否支持压缩
    let supports_compression = headers
        .get("Accept-Encoding")
        .and_then(|header| header.to_str().ok())
        .map(|header| header.contains("gzip") || header.contains("deflate"))
        .unwrap_or(false);

    if supports_compression {
        // 应用压缩
        // 这里需要根据具体的压缩库来实现
        // 例如使用 flate2 或 async-compression
    }

    next.run(request).await
}

/// 超时中间件
pub async fn timeout_middleware(
    State(state): State<Arc<AppState>>,
    request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 设置请求超时
    let timeout_duration = state.config.request_timeout;
    
    // 使用 tokio::time::timeout 来限制请求处理时间
    match tokio::time::timeout(timeout_duration, next.run(request)).await {
        Ok(response) => Ok(response),
        Err(_) => Err(StatusCode::REQUEST_TIMEOUT),
    }
}

/// 请求ID中间件
pub async fn request_id_middleware(
    State(state): State<Arc<AppState>>,
    mut request: Request,
    next: Next,
) -> Response {
    // 生成请求ID
    let request_id = uuid::Uuid::new_v4().to_string();
    
    // 将请求ID添加到请求扩展中
    request.extensions_mut().insert(request_id.clone());
    
    // 处理请求
    let mut response = next.run(request).await;
    
    // 将请求ID添加到响应头中
    response.headers_mut().insert(
        "X-Request-ID",
        request_id.parse().unwrap(),
    );
    
    response
}

/// 健康检查中间件
pub async fn health_check_middleware(
    State(state): State<Arc<AppState>>,
    request: Request,
    next: Next,
) -> Response {
    // 检查系统健康状态
    if !state.health_checker.is_healthy().await {
        return Response::builder()
            .status(StatusCode::SERVICE_UNAVAILABLE)
            .body("Service Unavailable".into())
            .unwrap();
    }

    next.run(request).await
}

/// 指标收集中间件
pub async fn metrics_middleware(
    State(state): State<Arc<AppState>>,
    request: Request,
    next: Next,
) -> Response {
    let start = Instant::now();
    let method = request.method().clone();
    let uri = request.uri().clone();

    // 处理请求
    let response = next.run(request).await;

    // 收集指标
    let duration = start.elapsed();
    let status = response.status();
    
    state.metrics.record_request(
        method.as_str(),
        uri.path(),
        status.as_u16(),
        duration,
    ).await;

    response
}

/// 错误处理中间件
pub async fn error_handling_middleware(
    State(state): State<Arc<AppState>>,
    request: Request,
    next: Next,
) -> Response {
    match next.run(request).await.into_parts() {
        (parts, body) => {
            // 检查响应状态
            if parts.status.is_client_error() || parts.status.is_server_error() {
                // 记录错误
                state.error_tracker.record_error(
                    parts.status.as_u16(),
                    uri.path(),
                    method.as_str(),
                ).await;
            }

            Response::from_parts(parts, body)
        }
    }
}

/// 安全头中间件
pub async fn security_headers_middleware(
    State(state): State<Arc<AppState>>,
    request: Request,
    next: Next,
) -> Response {
    let mut response = next.run(request).await;
    
    // 添加安全头
    response.headers_mut().insert(
        "X-Content-Type-Options",
        "nosniff".parse().unwrap(),
    );
    response.headers_mut().insert(
        "X-Frame-Options",
        "DENY".parse().unwrap(),
    );
    response.headers_mut().insert(
        "X-XSS-Protection",
        "1; mode=block".parse().unwrap(),
    );
    response.headers_mut().insert(
        "Strict-Transport-Security",
        "max-age=31536000; includeSubDomains".parse().unwrap(),
    );
    
    response
}

/// 缓存控制中间件
pub async fn cache_control_middleware(
    State(state): State<Arc<AppState>>,
    request: Request,
    next: Next,
) -> Response {
    let mut response = next.run(request).await;
    
    // 根据请求类型设置缓存头
    if request.uri().path().starts_with("/static/") {
        response.headers_mut().insert(
            "Cache-Control",
            "public, max-age=31536000".parse().unwrap(),
        );
    } else if request.uri().path().starts_with("/api/") {
        response.headers_mut().insert(
            "Cache-Control",
            "no-cache, no-store, must-revalidate".parse().unwrap(),
        );
    }
    
    response
}

/// 请求验证中间件
pub async fn request_validation_middleware(
    State(state): State<Arc<AppState>>,
    request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 验证请求大小
    if let Some(content_length) = request.headers().get("Content-Length") {
        if let Ok(length_str) = content_length.to_str() {
            if let Ok(length) = length_str.parse::<u64>() {
                if length > state.config.max_request_size {
                    return Err(StatusCode::PAYLOAD_TOO_LARGE);
                }
            }
        }
    }

    // 验证内容类型
    if let Some(content_type) = request.headers().get("Content-Type") {
        if let Ok(content_type_str) = content_type.to_str() {
            if !state.config.allowed_content_types.contains(content_type_str) {
                return Err(StatusCode::UNSUPPORTED_MEDIA_TYPE);
            }
        }
    }

    Ok(next.run(request).await)
}

/// 中间件配置
#[derive(Debug, Clone)]
pub struct MiddlewareConfig {
    pub enable_auth: bool,
    pub enable_rate_limit: bool,
    pub enable_logging: bool,
    pub enable_cors: bool,
    pub enable_compression: bool,
    pub enable_timeout: bool,
    pub enable_request_id: bool,
    pub enable_health_check: bool,
    pub enable_metrics: bool,
    pub enable_error_handling: bool,
    pub enable_security_headers: bool,
    pub enable_cache_control: bool,
    pub enable_request_validation: bool,
}

impl Default for MiddlewareConfig {
    fn default() -> Self {
        Self {
            enable_auth: true,
            enable_rate_limit: true,
            enable_logging: true,
            enable_cors: true,
            enable_compression: true,
            enable_timeout: true,
            enable_request_id: true,
            enable_health_check: true,
            enable_metrics: true,
            enable_error_handling: true,
            enable_security_headers: true,
            enable_cache_control: true,
            enable_request_validation: true,
        }
    }
}

/// 中间件管理器
#[derive(Debug)]
pub struct MiddlewareManager {
    config: MiddlewareConfig,
    rate_limiter: RateLimiter,
}

impl MiddlewareManager {
    pub fn new(config: MiddlewareConfig) -> Self {
        Self {
            rate_limiter: RateLimiter::new(100, Duration::from_secs(60)),
            config,
        }
    }

    pub fn get_rate_limiter(&self) -> &RateLimiter {
        &self.rate_limiter
    }

    pub fn get_config(&self) -> &MiddlewareConfig {
        &self.config
    }
}
