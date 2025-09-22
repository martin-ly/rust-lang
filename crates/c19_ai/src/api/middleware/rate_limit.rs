//! 速率限制中间件
//! 
//! 提供API请求速率限制功能

use axum::{
    extract::Request,
    middleware::Next,
    response::Response,
    http::{StatusCode, HeaderMap},
};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use tracing::{info, warn};

/// 速率限制器
#[derive(Debug, Clone)]
struct RateLimiter {
    requests: Arc<RwLock<HashMap<String, Vec<Instant>>>>,
    max_requests: u32,
    window_duration: Duration,
}

impl RateLimiter {
    fn new(max_requests: u32, window_duration: Duration) -> Self {
        Self {
            requests: Arc::new(RwLock::new(HashMap::new())),
            max_requests,
            window_duration,
        }
    }

    async fn is_allowed(&self, key: &str) -> bool {
        let now = Instant::now();
        let cutoff = now - self.window_duration;

        let mut requests = self.requests.write().await;
        let entry = requests.entry(key.to_string()).or_insert_with(Vec::new);

        // 清理过期的请求记录
        entry.retain(|&time| time > cutoff);

        // 检查是否超过限制
        if entry.len() >= self.max_requests as usize {
            false
        } else {
            entry.push(now);
            true
        }
    }
}

/// 全局速率限制器
static RATE_LIMITER: std::sync::OnceLock<RateLimiter> = std::sync::OnceLock::new();

/// 获取速率限制器
fn get_rate_limiter() -> &'static RateLimiter {
    RATE_LIMITER.get_or_init(|| {
        RateLimiter::new(
            100, // 每分钟100个请求
            Duration::from_secs(60),
        )
    })
}

/// 速率限制中间件
pub async fn rate_limit_middleware(
    request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 获取客户端IP
    let client_ip = get_client_ip(&request);
    
    // 检查速率限制
    let rate_limiter = get_rate_limiter();
    if !rate_limiter.is_allowed(&client_ip).await {
        warn!(
            client_ip = %client_ip,
            "Rate limit exceeded"
        );
        return Err(StatusCode::TOO_MANY_REQUESTS);
    }

    Ok(next.run(request).await)
}

/// 获取客户端IP地址
fn get_client_ip(request: &Request) -> String {
    let headers = request.headers();
    
    // 检查X-Forwarded-For头
    if let Some(forwarded) = headers.get("X-Forwarded-For") {
        if let Ok(forwarded_str) = forwarded.to_str() {
            if let Some(ip) = forwarded_str.split(',').next() {
                return ip.trim().to_string();
            }
        }
    }
    
    // 检查X-Real-IP头
    if let Some(real_ip) = headers.get("X-Real-IP") {
        if let Ok(real_ip_str) = real_ip.to_str() {
            return real_ip_str.to_string();
        }
    }
    
    // 默认返回本地IP
    "127.0.0.1".to_string()
}
