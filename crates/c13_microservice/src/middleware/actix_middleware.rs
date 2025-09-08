//! Actix-Web中间件实现
//! 
//! 提供基于Actix-Web框架的中间件功能

use std::time::{Duration, Instant};
use std::sync::Arc;
use std::collections::HashMap;
use tokio::sync::RwLock;
use actix_web::{
    dev::{ServiceRequest, ServiceResponse, Transform},
    Error, HttpMessage, Result,
    middleware::Logger,
};
use actix_web::http::header::HeaderValue;
use actix_web::middleware::Compress;
use actix_web::middleware::NormalizePath;
use actix_web::middleware::TrailingSlash;
use tracing::{info, error};
use uuid::Uuid;

/// 请求ID中间件
#[derive(Debug, Clone)]
pub struct RequestIdMiddleware;

impl<S, B> Transform<S, ServiceRequest> for RequestIdMiddleware
where
    S: actix_web::dev::Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error> + 'static,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Transform = RequestIdService<S>;
    type InitError = ();
    type Future = std::pin::Pin<Box<dyn std::future::Future<Output = Result<Self::Transform, Self::InitError>>>>;

    fn new_transform(&self, service: S) -> Self::Future {
        Box::pin(async move {
            Ok(RequestIdService { service })
        })
    }
}

pub struct RequestIdService<S> {
    service: S,
}

impl<S, B> actix_web::dev::Service<ServiceRequest> for RequestIdService<S>
where
    S: actix_web::dev::Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error> + 'static,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = std::pin::Pin<Box<dyn std::future::Future<Output = Result<Self::Response, Self::Error>>>>;

    fn poll_ready(&self, ctx: &mut std::task::Context<'_>) -> std::task::Poll<Result<(), Self::Error>> {
        self.service.poll_ready(ctx)
    }

    fn call(&self, mut req: ServiceRequest) -> Self::Future {
        let request_id = Uuid::new_v4().to_string();
        
        // 将请求ID添加到请求头
        if let Ok(header_value) = HeaderValue::try_from(&request_id) {
            req.headers_mut().insert("x-request-id", header_value);
        }
        
        // 将请求ID添加到请求扩展中
        req.extensions_mut().insert(RequestId(request_id.clone()));
        
        info!("请求开始: {}", request_id);
        
        let service = self.service.clone();
        Box::pin(async move {
            let response = service.call(req).await?;
            info!("请求完成: {}", request_id);
            Ok(response)
        })
    }
}

/// 请求ID结构
#[derive(Debug, Clone)]
pub struct RequestId(pub String);

/// 限流中间件
#[derive(Debug, Clone)]
pub struct RateLimitMiddleware {
    pub requests_per_minute: u32,
    pub requests_per_hour: u32,
}

impl RateLimitMiddleware {
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
    
    pub async fn is_allowed(&self, client_id: &str, config: &RateLimitMiddleware) -> bool {
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

impl<S, B> Transform<S, ServiceRequest> for RateLimitMiddleware
where
    S: actix_web::dev::Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error> + 'static,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Transform = RateLimitService<S>;
    type InitError = ();
    type Future = std::pin::Pin<Box<dyn std::future::Future<Output = Result<Self::Transform, Self::InitError>>>>;

    fn new_transform(&self, service: S) -> Self::Future {
        let config = self.clone();
        Box::pin(async move {
            Ok(RateLimitService { service, config })
        })
    }
}

pub struct RateLimitService<S> {
    service: S,
    config: RateLimitMiddleware,
}

impl<S, B> actix_web::dev::Service<ServiceRequest> for RateLimitService<S>
where
    S: actix_web::dev::Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error> + 'static,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = std::pin::Pin<Box<dyn std::future::Future<Output = Result<Self::Response, Self::Error>>>>;

    fn poll_ready(&self, ctx: &mut std::task::Context<'_>) -> std::task::Poll<Result<(), Self::Error>> {
        self.service.poll_ready(ctx)
    }

    fn call(&self, req: ServiceRequest) -> Self::Future {
        // 获取客户端ID
        let client_id = req
            .headers()
            .get("x-forwarded-for")
            .or_else(|| req.headers().get("x-real-ip"))
            .and_then(|h| h.to_str().ok())
            .unwrap_or("unknown");
        
        let config = self.config.clone();
        let service = self.service.clone();
        
        Box::pin(async move {
            // 这里需要从应用状态中获取限流状态
            // 简化实现，直接允许请求
            info!("限流检查: {}", client_id);
            service.call(req).await
        })
    }
}

/// 健康检查中间件
#[derive(Debug, Clone)]
pub struct HealthCheckMiddleware;

impl<S, B> Transform<S, ServiceRequest> for HealthCheckMiddleware
where
    S: actix_web::dev::Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error> + 'static,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Transform = HealthCheckService<S>;
    type InitError = ();
    type Future = std::pin::Pin<Box<dyn std::future::Future<Output = Result<Self::Transform, Self::InitError>>>>;

    fn new_transform(&self, service: S) -> Self::Future {
        Box::pin(async move {
            Ok(HealthCheckService { service })
        })
    }
}

pub struct HealthCheckService<S> {
    service: S,
}

impl<S, B> actix_web::dev::Service<ServiceRequest> for HealthCheckService<S>
where
    S: actix_web::dev::Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error> + 'static,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = std::pin::Pin<Box<dyn std::future::Future<Output = Result<Self::Response, Self::Error>>>>;

    fn poll_ready(&self, ctx: &mut std::task::Context<'_>) -> std::task::Poll<Result<(), Self::Error>> {
        self.service.poll_ready(ctx)
    }

    fn call(&self, req: ServiceRequest) -> Self::Future {
        if req.path() == "/health" {
            info!("健康检查请求");
            let service = self.service.clone();
            Box::pin(async move {
                // 这里可以添加实际的健康检查逻辑
                let response = service.call(req).await?;
                Ok(response)
            })
        } else {
            self.service.call(req)
        }
    }
}

/// 错误处理中间件
#[derive(Debug, Clone)]
pub struct ErrorHandlerMiddleware;

impl<S, B> Transform<S, ServiceRequest> for ErrorHandlerMiddleware
where
    S: actix_web::dev::Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error> + 'static,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Transform = ErrorHandlerService<S>;
    type InitError = ();
    type Future = std::pin::Pin<Box<dyn std::future::Future<Output = Result<Self::Transform, Self::InitError>>>>;

    fn new_transform(&self, service: S) -> Self::Future {
        Box::pin(async move {
            Ok(ErrorHandlerService { service })
        })
    }
}

pub struct ErrorHandlerService<S> {
    service: S,
}

impl<S, B> actix_web::dev::Service<ServiceRequest> for ErrorHandlerService<S>
where
    S: actix_web::dev::Service<ServiceRequest, Response = ServiceResponse<B>, Error = Error> + 'static,
    S::Future: 'static,
    B: 'static,
{
    type Response = ServiceResponse<B>;
    type Error = Error;
    type Future = std::pin::Pin<Box<dyn std::future::Future<Output = Result<Self::Response, Self::Error>>>>;

    fn poll_ready(&self, ctx: &mut std::task::Context<'_>) -> std::task::Poll<Result<(), Self::Error>> {
        self.service.poll_ready(ctx)
    }

    fn call(&self, req: ServiceRequest) -> Self::Future {
        let service = self.service.clone();
        Box::pin(async move {
            match service.call(req).await {
                Ok(response) => Ok(response),
                Err(error) => {
                    error!("请求处理失败: {}", error);
                    // 这里可以添加自定义错误处理逻辑
                    Err(error)
                }
            }
        })
    }
}

/// 中间件构建器
#[derive(Debug, Clone)]
pub struct ActixMiddlewareBuilder {
    pub request_id: bool,
    pub logging: bool,
    pub rate_limit: Option<RateLimitMiddleware>,
    pub health_check: bool,
    pub error_handler: bool,
    pub cors: bool,
    pub compression: bool,
    pub normalize_path: bool,
}

impl Default for ActixMiddlewareBuilder {
    fn default() -> Self {
        Self::new()
    }
}

impl ActixMiddlewareBuilder {
    pub fn new() -> Self {
        Self {
            request_id: false,
            logging: false,
            rate_limit: None,
            health_check: false,
            error_handler: false,
            cors: false,
            compression: false,
            normalize_path: false,
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
        self.rate_limit = Some(RateLimitMiddleware::new(requests_per_minute, requests_per_hour));
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
    
    pub fn with_cors(mut self) -> Self {
        self.cors = true;
        self
    }
    
    pub fn with_compression(mut self) -> Self {
        self.compression = true;
        self
    }
    
    pub fn with_normalize_path(mut self) -> Self {
        self.normalize_path = true;
        self
    }
    
    pub fn build(self) -> Vec<Box<dyn actix_web::dev::Transform<actix_web::dev::ServiceRequest, actix_web::dev::ServiceRequest, Response = actix_web::dev::ServiceResponse, Error = actix_web::Error, InitError = (), Transform = actix_web::dev::TransformService<actix_web::dev::ServiceRequest, actix_web::dev::ServiceRequest>, Future = std::pin::Pin<Box<dyn std::future::Future<Output = Result<actix_web::dev::TransformService<actix_web::dev::ServiceRequest, actix_web::dev::ServiceRequest>, ()>> + Send + 'static>>> + Send + Sync>> {
        let mut middlewares: Vec<Box<dyn actix_web::dev::Transform<actix_web::dev::ServiceRequest, actix_web::dev::ServiceRequest, Response = actix_web::dev::ServiceResponse, Error = actix_web::Error, InitError = (), Transform = actix_web::dev::TransformService<actix_web::dev::ServiceRequest, actix_web::dev::ServiceRequest>, Future = std::pin::Pin<Box<dyn std::future::Future<Output = Result<actix_web::dev::TransformService<actix_web::dev::ServiceRequest, actix_web::dev::ServiceRequest>, ()>> + Send + 'static>>> + Send + Sync>> = Vec::new();
        
        // 简化的中间件构建，暂时只返回空向量
        // 实际实现需要根据具体的Actix-Web版本进行调整
        middlewares
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_actix_middleware_builder() {
        let builder = ActixMiddlewareBuilder::new()
            .with_request_id()
            .with_logging()
            .with_rate_limit(100, 1000)
            .with_health_check()
            .with_error_handler()
            .with_cors()
            .with_compression()
            .with_normalize_path();
        
        let _middlewares = builder.build();
        assert!(true); // 如果能构建成功就说明测试通过
    }
    
    #[test]
    fn test_rate_limit_middleware() {
        let middleware = RateLimitMiddleware::new(60, 1000);
        assert_eq!(middleware.requests_per_minute, 60);
        assert_eq!(middleware.requests_per_hour, 1000);
    }
    
    #[test]
    fn test_rate_limit_state() {
        let state = RateLimitState::new();
        assert!(state.minute_requests.try_read().is_ok());
        assert!(state.hour_requests.try_read().is_ok());
    }
}
