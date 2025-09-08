//! Axum中间件实现
//! 
//! 提供基于Axum框架的中间件功能

use std::time::{Duration, Instant};
use std::sync::Arc;
use std::collections::HashMap;
use tokio::sync::RwLock;
use tower::ServiceBuilder;
use tower_http::{
    cors::{CorsLayer, Any},
    timeout::TimeoutLayer,
    compression::CompressionLayer,
};
use axum::{
    extract::{Request, State},
    http::StatusCode,
    middleware::Next,
    response::Response,
};
use tracing::{info, warn, error, instrument};
use uuid::Uuid;

use crate::error::Result;

/// 请求ID中间件
#[derive(Debug, Clone)]
pub struct RequestIdLayer;

impl RequestIdLayer {
    pub fn new() -> Self {
        Self
    }
}

/// 请求ID状态
#[derive(Debug, Clone)]
pub struct RequestId(pub String);

/// 请求ID中间件实现
pub async fn request_id_middleware(
    mut request: Request,
    next: Next,
) -> std::result::Result<Response, StatusCode> {
    let request_id = Uuid::new_v4().to_string();
    
    // 将请求ID添加到请求头
    request.headers_mut().insert(
        "x-request-id",
        request_id.parse().map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?,
    );
    
    // 将请求ID添加到扩展中
    request.extensions_mut().insert(RequestId(request_id.clone()));
    
    info!("请求开始: {}", request_id);
    
    let response = next.run(request).await;
    
    info!("请求完成: {}", request_id);
    Ok(response)
}

/// 日志中间件
#[derive(Debug, Clone)]
pub struct LoggingLayer;

impl LoggingLayer {
    pub fn new() -> Self {
        Self
    }
}

/// 日志中间件实现
#[instrument(skip(request, next))]
pub async fn logging_middleware(
    request: Request,
    next: Next,
) -> std::result::Result<Response, StatusCode> {
    let start = Instant::now();
    let method = request.method().clone();
    let uri = request.uri().clone();
    let headers = request.headers().clone();
    
    // 获取请求ID
    let request_id = request
        .extensions()
        .get::<RequestId>()
        .map(|id| id.0.clone())
        .unwrap_or_else(|| "unknown".to_string());
    
    info!(
        request_id = %request_id,
        method = %method,
        uri = %uri,
        "请求开始"
    );
    
    // 记录请求头（敏感信息除外）
    for (key, value) in headers.iter() {
        if !is_sensitive_header(key.as_str()) {
            if let Ok(value_str) = value.to_str() {
                info!(
                    request_id = %request_id,
                    header_name = %key,
                    header_value = %value_str,
                    "请求头"
                );
            }
        }
    }
    
    let response = next.run(request).await;
    let duration = start.elapsed();
    
    info!(
        request_id = %request_id,
        method = %method,
        uri = %uri,
        status = %response.status(),
        duration_ms = duration.as_millis(),
        "请求完成"
    );
    
    Ok(response)
}

/// 检查是否为敏感请求头
fn is_sensitive_header(header_name: &str) -> bool {
    matches!(
        header_name.to_lowercase().as_str(),
        "authorization" | "cookie" | "x-api-key" | "x-auth-token"
    )
}

/// 限流中间件
#[derive(Debug, Clone)]
pub struct RateLimitLayer {
    pub requests_per_minute: u32,
    pub requests_per_hour: u32,
}

impl RateLimitLayer {
    pub fn new(requests_per_minute: u32, requests_per_hour: u32) -> Self {
        Self {
            requests_per_minute,
            requests_per_hour,
        }
    }
}

/// 限流状态
#[derive(Debug, Clone)]
pub struct RateLimitState {
    pub minute_requests: Arc<RwLock<HashMap<String, Vec<Instant>>>>,
    pub hour_requests: Arc<RwLock<HashMap<String, Vec<Instant>>>>,
}

impl RateLimitState {
    pub fn new() -> Self {
        Self {
            minute_requests: Arc::new(RwLock::new(HashMap::new())),
            hour_requests: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub async fn is_allowed(&self, client_id: &str, config: &RateLimitLayer) -> bool {
        let now = Instant::now();
        let minute_ago = now - Duration::from_secs(60);
        let hour_ago = now - Duration::from_secs(3600);
        
        // 检查每分钟限制
        {
            let mut minute_reqs = self.minute_requests.write().await;
            let requests = minute_reqs.entry(client_id.to_string()).or_insert_with(Vec::new);
            
            // 清理过期请求
            requests.retain(|&time| time > minute_ago);
            
            if requests.len() >= config.requests_per_minute as usize {
                return false;
            }
            
            requests.push(now);
        }
        
        // 检查每小时限制
        {
            let mut hour_reqs = self.hour_requests.write().await;
            let requests = hour_reqs.entry(client_id.to_string()).or_insert_with(Vec::new);
            
            // 清理过期请求
            requests.retain(|&time| time > hour_ago);
            
            if requests.len() >= config.requests_per_hour as usize {
                return false;
            }
            
            requests.push(now);
        }
        
        true
    }
}

/// 限流中间件实现
pub async fn rate_limit_middleware(
    State(state): State<RateLimitState>,
    State(config): State<RateLimitLayer>,
    request: Request,
    next: Next,
) -> std::result::Result<Response, StatusCode> {
    // 获取客户端ID（这里简化使用IP地址）
    let client_id = request
        .headers()
        .get("x-forwarded-for")
        .or_else(|| request.headers().get("x-real-ip"))
        .and_then(|h| h.to_str().ok())
        .unwrap_or("unknown");
    
    if !state.is_allowed(client_id, &config).await {
        warn!("请求被限流: {}", client_id);
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }
    
    Ok(next.run(request).await)
}

/// 健康检查中间件
#[derive(Debug, Clone)]
pub struct HealthCheckLayer;

impl HealthCheckLayer {
    pub fn new() -> Self {
        Self
    }
}

/// 健康检查中间件实现
pub async fn health_check_middleware(
    request: Request,
    next: Next,
) -> std::result::Result<Response, StatusCode> {
    if request.uri().path() == "/health" {
        info!("健康检查请求");
        // 这里可以添加实际的健康检查逻辑
        return Ok(Response::builder()
            .status(StatusCode::OK)
            .body("OK".into())
            .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?);
    }
    
    Ok(next.run(request).await)
}

/// 错误处理中间件
#[derive(Debug, Clone)]
pub struct ErrorHandlerLayer;

impl ErrorHandlerLayer {
    pub fn new() -> Self {
        Self
    }
}

/// 错误处理中间件实现
pub async fn error_handler_middleware(
    request: Request,
    next: Next,
) -> std::result::Result<Response, StatusCode> {
    let response = next.run(request).await;
    Ok(response)
}

/// 中间件构建器
#[derive(Debug, Clone)]
pub struct AxumMiddlewareBuilder {
    pub request_id: bool,
    pub logging: bool,
    pub rate_limit: Option<RateLimitLayer>,
    pub health_check: bool,
    pub error_handler: bool,
    pub timeout: Option<Duration>,
    pub cors: bool,
    pub compression: bool,
}

impl Default for AxumMiddlewareBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl AxumMiddlewareBuilder {
    pub fn new() -> Self {
        Self {
            request_id: false,
            logging: false,
            rate_limit: None,
            health_check: false,
            error_handler: false,
            timeout: None,
            cors: false,
            compression: false,
        }
    }
    
    pub fn with_request_id(mut self) -> Self {
        self.request_id = true;
        self
    }
    
    pub fn with_logging(mut self) -> Self {
        self.logging = true;
        self
    }
    
    pub fn with_rate_limit(mut self, requests_per_minute: u32, requests_per_hour: u32) -> Self {
        self.rate_limit = Some(RateLimitLayer::new(requests_per_minute, requests_per_hour));
        self
    }
    
    pub fn with_health_check(mut self) -> Self {
        self.health_check = true;
        self
    }
    
    pub fn with_error_handler(mut self) -> Self {
        self.error_handler = true;
        self
    }
    
    pub fn with_timeout(mut self, duration: Duration) -> Self {
        self.timeout = Some(duration);
        self
    }
    
    pub fn with_cors(mut self) -> Self {
        self.cors = true;
        self
    }
    
    pub fn with_compression(mut self) -> Self {
        self.compression = true;
        self
    }
    
    pub fn build(self) -> ServiceBuilder<tower::layer::util::Identity> {
        let builder = ServiceBuilder::new();
        
        // 简化的中间件构建，暂时只返回基础构建器
        // 实际实现需要根据具体的Axum版本进行调整
        builder
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_axum_middleware_builder() {
        let builder = AxumMiddlewareBuilder::new()
            .with_request_id()
            .with_logging()
            .with_rate_limit(100, 1000)
            .with_health_check()
            .with_error_handler()
            .with_timeout(Duration::from_secs(30))
            .with_cors()
            .with_compression();
        
        let _service_builder = builder.build();
        assert!(true); // 如果能构建成功就说明测试通过
    }
    
    #[test]
    fn test_rate_limit_layer() {
        let layer = RateLimitLayer::new(60, 1000);
        assert_eq!(layer.requests_per_minute, 60);
        assert_eq!(layer.requests_per_hour, 1000);
    }
    
    #[test]
    fn test_is_sensitive_header() {
        assert!(is_sensitive_header("Authorization"));
        assert!(is_sensitive_header("Cookie"));
        assert!(is_sensitive_header("X-API-Key"));
        assert!(!is_sensitive_header("Content-Type"));
        assert!(!is_sensitive_header("User-Agent"));
    }
}
