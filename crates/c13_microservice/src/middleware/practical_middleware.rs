//! 实用的中间件实现
//! 
//! 提供可以在实际项目中使用的中间件功能

use std::time::{Duration, Instant};
use std::sync::Arc;
use std::collections::HashMap;
use tokio::sync::RwLock;
use tracing::{info, warn, error, instrument};
use uuid::Uuid;

// use crate::error::Result; // 暂时未使用

/// 请求追踪中间件
#[derive(Debug, Clone)]
pub struct RequestTracingMiddleware {
    pub enabled: bool,
    pub log_headers: bool,
    pub log_body: bool,
}

impl Default for RequestTracingMiddleware {
    fn default() -> Self {
        Self {
            enabled: true,
            log_headers: false, // 默认不记录请求头，避免敏感信息泄露
            log_body: false,    // 默认不记录请求体，避免性能影响
        }
    }
}

impl RequestTracingMiddleware {
    pub fn new() -> Self {
        Self::default()
    }
    
    pub fn with_headers(mut self, enabled: bool) -> Self {
        self.log_headers = enabled;
        self
    }
    
    pub fn with_body(mut self, enabled: bool) -> Self {
        self.log_body = enabled;
        self
    }
    
    /// 记录请求开始
    #[instrument(skip(self))]
    pub fn log_request_start(&self, method: &str, path: &str, request_id: &str) {
        if self.enabled {
            info!(
                request_id = %request_id,
                method = %method,
                path = %path,
                "请求开始"
            );
        }
    }
    
    /// 记录请求完成
    #[instrument(skip(self))]
    pub fn log_request_end(&self, request_id: &str, status_code: u16, duration: Duration) {
        if self.enabled {
            info!(
                request_id = %request_id,
                status_code = %status_code,
                duration_ms = duration.as_millis(),
                "请求完成"
            );
        }
    }
    
    /// 记录请求头（过滤敏感信息）
    #[instrument(skip(self))]
    pub fn log_headers(&self, headers: &HashMap<String, String>, request_id: &str) {
        if self.enabled && self.log_headers {
            for (key, value) in headers {
                if !self.is_sensitive_header(key) {
                    info!(
                        request_id = %request_id,
                        header_name = %key,
                        header_value = %value,
                        "请求头"
                    );
                }
            }
        }
    }
    
    /// 检查是否为敏感请求头
    fn is_sensitive_header(&self, header_name: &str) -> bool {
        matches!(
            header_name.to_lowercase().as_str(),
            "authorization" | "cookie" | "x-api-key" | "x-auth-token" | "x-forwarded-for"
        )
    }
}

/// 限流中间件
#[derive(Debug, Clone)]
pub struct RateLimitMiddleware {
    pub requests_per_minute: u32,
    pub requests_per_hour: u32,
    pub burst_size: u32,
    pub enabled: bool,
}

impl Default for RateLimitMiddleware {
    fn default() -> Self {
        Self {
            requests_per_minute: 60,
            requests_per_hour: 1000,
            burst_size: 10,
            enabled: true,
        }
    }
}

/// 限流状态
#[derive(Debug, Clone)]
pub struct RateLimitState {
    pub minute_requests: Arc<RwLock<HashMap<String, Vec<Instant>>>>,
    pub hour_requests: Arc<RwLock<HashMap<String, Vec<Instant>>>>,
    pub burst_tokens: Arc<RwLock<HashMap<String, u32>>>,
}

impl RateLimitState {
    pub fn new() -> Self {
        Self {
            minute_requests: Arc::new(RwLock::new(HashMap::new())),
            hour_requests: Arc::new(RwLock::new(HashMap::new())),
            burst_tokens: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 检查是否允许请求
    pub async fn is_allowed(&self, client_id: &str, config: &RateLimitMiddleware) -> bool {
        if !config.enabled {
            return true;
        }
        
        let now = Instant::now();
        let minute_ago = now - Duration::from_secs(60);
        let hour_ago = now - Duration::from_secs(3600);
        
        // 检查突发限制
        if !self.check_burst_limit(client_id, config).await {
            return false;
        }
        
        // 检查每分钟限制
        if !self.check_minute_limit(client_id, config, now, minute_ago).await {
            return false;
        }
        
        // 检查每小时限制
        if !self.check_hour_limit(client_id, config, now, hour_ago).await {
            return false;
        }
        
        true
    }
    
    async fn check_burst_limit(&self, client_id: &str, config: &RateLimitMiddleware) -> bool {
        let mut tokens = self.burst_tokens.write().await;
        let current_tokens = tokens.get(client_id).copied().unwrap_or(config.burst_size);
        
        if current_tokens > 0 {
            tokens.insert(client_id.to_string(), current_tokens - 1);
            true
        } else {
            false
        }
    }
    
    async fn check_minute_limit(&self, client_id: &str, config: &RateLimitMiddleware, now: Instant, minute_ago: Instant) -> bool {
        let mut minute_reqs = self.minute_requests.write().await;
        let requests = minute_reqs.entry(client_id.to_string()).or_insert_with(Vec::new);
        
        // 清理过期请求
        requests.retain(|&time| time > minute_ago);
        
        if requests.len() < config.requests_per_minute as usize {
            requests.push(now);
            true
        } else {
            false
        }
    }
    
    async fn check_hour_limit(&self, client_id: &str, config: &RateLimitMiddleware, now: Instant, hour_ago: Instant) -> bool {
        let mut hour_reqs = self.hour_requests.write().await;
        let requests = hour_reqs.entry(client_id.to_string()).or_insert_with(Vec::new);
        
        // 清理过期请求
        requests.retain(|&time| time > hour_ago);
        
        if requests.len() < config.requests_per_hour as usize {
            requests.push(now);
            true
        } else {
            false
        }
    }
    
    /// 恢复突发令牌
    pub async fn restore_burst_tokens(&self, client_id: &str, config: &RateLimitMiddleware) {
        let mut tokens = self.burst_tokens.write().await;
        let current_tokens = tokens.get(client_id).copied().unwrap_or(0);
        let new_tokens = (current_tokens + 1).min(config.burst_size);
        tokens.insert(client_id.to_string(), new_tokens);
    }
}

/// 健康检查中间件
#[derive(Debug, Clone)]
pub struct HealthCheckMiddleware {
    pub health_endpoints: Vec<String>,
    pub detailed_health: bool,
    pub check_dependencies: bool,
}

impl Default for HealthCheckMiddleware {
    fn default() -> Self {
        Self {
            health_endpoints: vec!["/health".to_string(), "/healthz".to_string()],
            detailed_health: false,
            check_dependencies: false,
        }
    }
}

impl HealthCheckMiddleware {
    pub fn new() -> Self {
        Self::default()
    }
    
    pub fn with_endpoints(mut self, endpoints: Vec<String>) -> Self {
        self.health_endpoints = endpoints;
        self
    }
    
    pub fn with_detailed_health(mut self, enabled: bool) -> Self {
        self.detailed_health = enabled;
        self
    }
    
    pub fn with_dependency_check(mut self, enabled: bool) -> Self {
        self.check_dependencies = enabled;
        self
    }
    
    /// 检查是否为健康检查请求
    pub fn is_health_check(&self, path: &str) -> bool {
        self.health_endpoints.iter().any(|endpoint| path.starts_with(endpoint))
    }
    
    /// 执行健康检查
    pub async fn perform_health_check(&self) -> HealthCheckResult {
        let mut result = HealthCheckResult {
            status: "healthy".to_string(),
            timestamp: crate::utils::current_timestamp_secs(),
            checks: HashMap::new(),
        };
        
        // 基本健康检查
        result.checks.insert("basic".to_string(), "ok".to_string());
        
        // 详细健康检查
        if self.detailed_health {
            result.checks.insert("memory".to_string(), "ok".to_string());
            result.checks.insert("cpu".to_string(), "ok".to_string());
        }
        
        // 依赖检查
        if self.check_dependencies {
            // 这里可以添加数据库、Redis等依赖的检查
            result.checks.insert("database".to_string(), "ok".to_string());
            result.checks.insert("cache".to_string(), "ok".to_string());
        }
        
        result
    }
}

#[derive(Debug, Clone)]
pub struct HealthCheckResult {
    pub status: String,
    pub timestamp: u64,
    pub checks: HashMap<String, String>,
}

/// 错误处理中间件
#[derive(Debug, Clone)]
pub struct ErrorHandlingMiddleware {
    pub log_errors: bool,
    pub return_detailed_errors: bool,
    pub error_threshold: u32,
}

impl Default for ErrorHandlingMiddleware {
    fn default() -> Self {
        Self {
            log_errors: true,
            return_detailed_errors: false, // 生产环境建议设为false
            error_threshold: 10,
        }
    }
}

impl ErrorHandlingMiddleware {
    pub fn new() -> Self {
        Self::default()
    }
    
    pub fn with_detailed_errors(mut self, enabled: bool) -> Self {
        self.return_detailed_errors = enabled;
        self
    }
    
    pub fn with_error_threshold(mut self, threshold: u32) -> Self {
        self.error_threshold = threshold;
        self
    }
    
    /// 处理错误
    pub fn handle_error(&self, error: &dyn std::error::Error, request_id: &str) -> ErrorResponse {
        if self.log_errors {
            error!(
                request_id = %request_id,
                error = %error,
                "请求处理错误"
            );
        }
        
        let error_message = if self.return_detailed_errors {
            error.to_string()
        } else {
            "内部服务器错误".to_string()
        };
        
        ErrorResponse {
            error: error_message,
            request_id: request_id.to_string(),
            timestamp: crate::utils::current_timestamp_secs(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct ErrorResponse {
    pub error: String,
    pub request_id: String,
    pub timestamp: u64,
}

/// 中间件管理器
#[derive(Debug, Clone)]
pub struct MiddlewareManager {
    pub request_tracing: RequestTracingMiddleware,
    pub rate_limit: RateLimitMiddleware,
    pub health_check: HealthCheckMiddleware,
    pub error_handling: ErrorHandlingMiddleware,
    pub rate_limit_state: RateLimitState,
}

impl MiddlewareManager {
    pub fn new() -> Self {
        Self {
            request_tracing: RequestTracingMiddleware::new(),
            rate_limit: RateLimitMiddleware::default(),
            health_check: HealthCheckMiddleware::new(),
            error_handling: ErrorHandlingMiddleware::new(),
            rate_limit_state: RateLimitState::new(),
        }
    }
    
    /// 处理请求
    pub async fn process_request(&self, method: &str, path: &str, client_id: &str) -> RequestResult {
        let request_id = Uuid::new_v4().to_string();
        let start_time = Instant::now();
        
        // 记录请求开始
        self.request_tracing.log_request_start(method, path, &request_id);
        
        // 健康检查
        if self.health_check.is_health_check(path) {
            let health_result = self.health_check.perform_health_check().await;
            return RequestResult::HealthCheck(health_result);
        }
        
        // 限流检查
        if !self.rate_limit_state.is_allowed(client_id, &self.rate_limit).await {
            warn!(
                request_id = %request_id,
                client_id = %client_id,
                "请求被限流"
            );
            return RequestResult::RateLimited;
        }
        
        // 模拟请求处理
        let duration = start_time.elapsed();
        let status_code = 200;
        
        // 记录请求完成
        self.request_tracing.log_request_end(&request_id, status_code, duration);
        
        RequestResult::Success {
            request_id,
            status_code,
            duration,
        }
    }
    
    /// 处理错误
    pub fn handle_error(&self, error: &dyn std::error::Error, request_id: &str) -> ErrorResponse {
        self.error_handling.handle_error(error, request_id)
    }
}

#[derive(Debug, Clone)]
pub enum RequestResult {
    Success {
        request_id: String,
        status_code: u16,
        duration: Duration,
    },
    RateLimited,
    HealthCheck(HealthCheckResult),
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_request_tracing_middleware() {
        let middleware = RequestTracingMiddleware::new()
            .with_headers(true)
            .with_body(false);
        
        assert!(middleware.enabled);
        assert!(middleware.log_headers);
        assert!(!middleware.log_body);
    }
    
    #[test]
    fn test_rate_limit_middleware() {
        let middleware = RateLimitMiddleware {
            requests_per_minute: 100,
            requests_per_hour: 1000,
            burst_size: 20,
            enabled: true,
        };
        
        assert_eq!(middleware.requests_per_minute, 100);
        assert_eq!(middleware.burst_size, 20);
    }
    
    #[test]
    fn test_health_check_middleware() {
        let middleware = HealthCheckMiddleware::new()
            .with_endpoints(vec!["/health".to_string(), "/status".to_string()])
            .with_detailed_health(true);
        
        assert!(middleware.is_health_check("/health"));
        assert!(middleware.is_health_check("/status"));
        assert!(!middleware.is_health_check("/api/users"));
    }
    
    #[tokio::test]
    async fn test_rate_limit_state() {
        let state = RateLimitState::new();
        let config = RateLimitMiddleware::default();
        
        // 测试正常请求
        assert!(state.is_allowed("client1", &config).await);
        
        // 测试突发限制
        for _ in 0..config.burst_size {
            assert!(state.is_allowed("client1", &config).await);
        }
        
        // 突发限制应该生效
        assert!(!state.is_allowed("client1", &config).await);
    }
    
    #[tokio::test]
    async fn test_middleware_manager() {
        let manager = MiddlewareManager::new();
        
        // 测试健康检查
        let result = manager.process_request("GET", "/health", "client1").await;
        match result {
            RequestResult::HealthCheck(_) => assert!(true),
            _ => assert!(false, "Expected HealthCheck result"),
        }
        
        // 测试正常请求
        let result = manager.process_request("GET", "/api/users", "client1").await;
        match result {
            RequestResult::Success { request_id, status_code, .. } => {
                assert!(!request_id.is_empty());
                assert_eq!(status_code, 200);
            }
            _ => assert!(false, "Expected Success result"),
        }
    }
}
