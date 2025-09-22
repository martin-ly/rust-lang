//! 速率限制模块
//!
//! 提供请求速率限制和DDoS保护功能

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// 速率限制配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimitConfig {
    pub enabled: bool,
    pub default_limit: RateLimit,
    pub endpoint_limits: HashMap<String, RateLimit>,
    pub client_limits: HashMap<String, RateLimit>,
    pub window_size: Duration,
    pub cleanup_interval: Duration,
    pub max_entries: usize,
}

impl Default for RateLimitConfig {
    fn default() -> Self {
        Self {
            enabled: true,
            default_limit: RateLimit {
                requests_per_window: 100,
                window_size: Duration::from_secs(60), // 1分钟
                burst_size: 10,
            },
            endpoint_limits: HashMap::new(),
            client_limits: HashMap::new(),
            window_size: Duration::from_secs(60),
            cleanup_interval: Duration::from_secs(300), // 5分钟
            max_entries: 10000,
        }
    }
}

/// 速率限制规则
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RateLimit {
    pub requests_per_window: u32,
    pub window_size: Duration,
    pub burst_size: u32,
}

/// 速率限制器
#[derive(Debug)]
pub struct RateLimiter {
    config: RateLimitConfig,
    counters: Arc<RwLock<HashMap<String, ClientCounter>>>,
    last_cleanup: Arc<RwLock<Instant>>,
    blocked_count: Arc<RwLock<usize>>,
}

/// 客户端计数器
#[derive(Debug, Clone)]
struct ClientCounter {
    requests: Vec<Instant>,
    blocked_requests: u32,
    last_reset: Instant,
}

impl ClientCounter {
    fn new() -> Self {
        Self {
            requests: Vec::new(),
            blocked_requests: 0,
            last_reset: Instant::now(),
        }
    }

    fn cleanup_old_requests(&mut self, window_size: Duration) {
        let cutoff = Instant::now() - window_size;
        self.requests.retain(|&time| time > cutoff);
    }

    fn add_request(&mut self) {
        self.requests.push(Instant::now());
    }

    fn get_request_count(&self, window_size: Duration) -> u32 {
        let cutoff = Instant::now() - window_size;
        self.requests.iter().filter(|&&time| time > cutoff).count() as u32
    }
}

impl RateLimiter {
    /// 创建新的速率限制器
    pub fn new(config: RateLimitConfig) -> Self {
        Self {
            config,
            counters: Arc::new(RwLock::new(HashMap::new())),
            last_cleanup: Arc::new(RwLock::new(Instant::now())),
            blocked_count: Arc::new(RwLock::new(0)),
        }
    }

    /// 检查速率限制
    pub async fn check_limit(
        &self,
        client_id: &str,
        endpoint: &str,
    ) -> Result<RateLimitResult, RateLimitError> {
        if !self.config.enabled {
            return Ok(RateLimitResult::allowed());
        }

        let key = format!("{}:{}", client_id, endpoint);
        let limit = self.get_limit_for_endpoint(endpoint);

        let mut counters = self.counters.write().await;
        
        // 获取或创建客户端计数器
        let counter = counters.entry(key.clone()).or_insert_with(ClientCounter::new);
        
        // 清理过期的请求记录
        counter.cleanup_old_requests(limit.window_size);
        
        // 检查是否超过限制
        let current_requests = counter.get_request_count(limit.window_size);
        
        if current_requests >= limit.requests_per_window {
            counter.blocked_requests += 1;
            *self.blocked_count.write().await += 1;
            
            return Ok(RateLimitResult {
                allowed: false,
                exceeded: true,
                limit: limit.requests_per_window,
                remaining: 0,
                reset_time: counter.last_reset + limit.window_size,
                retry_after: Some(limit.window_size.as_secs()),
                client_id: client_id.to_string(),
                endpoint: endpoint.to_string(),
            });
        }

        // 检查突发限制
        let recent_requests = counter.requests
            .iter()
            .filter(|&&time| time > Instant::now() - Duration::from_secs(1))
            .count() as u32;

        if recent_requests >= limit.burst_size {
            counter.blocked_requests += 1;
            *self.blocked_count.write().await += 1;
            
            return Ok(RateLimitResult {
                allowed: false,
                exceeded: true,
                limit: limit.requests_per_window,
                remaining: limit.requests_per_window.saturating_sub(current_requests),
                reset_time: counter.last_reset + limit.window_size,
                retry_after: Some(1), // 1秒后重试
                client_id: client_id.to_string(),
                endpoint: endpoint.to_string(),
            });
        }

        // 添加请求记录
        counter.add_request();

        Ok(RateLimitResult {
            allowed: true,
            exceeded: false,
            limit: limit.requests_per_window,
            remaining: limit.requests_per_window.saturating_sub(current_requests + 1),
            reset_time: counter.last_reset + limit.window_size,
            retry_after: None,
            client_id: client_id.to_string(),
            endpoint: endpoint.to_string(),
        })
    }

    /// 获取端点的速率限制
    fn get_limit_for_endpoint(&self, endpoint: &str) -> RateLimit {
        // 首先检查端点特定的限制
        if let Some(limit) = self.config.endpoint_limits.get(endpoint) {
            return limit.clone();
        }

        // 然后检查通配符匹配
        for (pattern, limit) in &self.config.endpoint_limits {
            if self.matches_pattern(endpoint, pattern) {
                return limit.clone();
            }
        }

        // 最后使用默认限制
        self.config.default_limit.clone()
    }

    /// 检查端点是否匹配模式
    fn matches_pattern(&self, endpoint: &str, pattern: &str) -> bool {
        if pattern.contains('*') {
            let parts: Vec<&str> = pattern.split('*').collect();
            if parts.len() == 2 {
                let prefix = parts[0];
                let suffix = parts[1];
                endpoint.starts_with(prefix) && endpoint.ends_with(suffix)
            } else {
                false
            }
        } else {
            endpoint == pattern
        }
    }

    /// 清理过期的计数器
    pub async fn cleanup_expired_counters(&self) -> Result<usize, RateLimitError> {
        let mut counters = self.counters.write().await;
        let mut last_cleanup = self.last_cleanup.write().await;

        // 检查是否需要清理
        if last_cleanup.elapsed() < self.config.cleanup_interval {
            return Ok(0);
        }

        let mut removed_count = 0;
        let cutoff = Instant::now() - self.config.window_size * 2; // 保留2个窗口的数据

        counters.retain(|_, counter| {
            if counter.last_reset < cutoff {
                removed_count += 1;
                false
            } else {
                true
            }
        });

        *last_cleanup = Instant::now();
        Ok(removed_count)
    }

    /// 获取客户端统计信息
    pub async fn get_client_stats(&self, client_id: &str) -> Option<ClientStats> {
        let counters = self.counters.read().await;
        
        let mut total_requests = 0;
        let mut blocked_requests = 0;
        let mut endpoints: Vec<String> = Vec::new();

        for (key, counter) in counters.iter() {
            if key.starts_with(&format!("{}:", client_id)) {
                total_requests += counter.requests.len();
                blocked_requests += counter.blocked_requests;
                
                if let Some(endpoint) = key.split(':').nth(1) {
                    endpoints.push(endpoint.to_string());
                }
            }
        }

        if total_requests > 0 || blocked_requests > 0 {
            Some(ClientStats {
                client_id: client_id.to_string(),
                total_requests,
                blocked_requests,
                endpoints,
                last_seen: Instant::now(),
            })
        } else {
            None
        }
    }

    /// 获取被阻止的请求数量
    pub async fn get_blocked_count(&self) -> usize {
        *self.blocked_count.read().await
    }

    /// 重置客户端计数器
    pub async fn reset_client(&self, client_id: &str) -> Result<usize, RateLimitError> {
        let mut counters = self.counters.write().await;
        let mut removed_count = 0;

        let keys_to_remove: Vec<String> = counters
            .keys()
            .filter(|key| key.starts_with(&format!("{}:", client_id)))
            .cloned()
            .collect();

        for key in keys_to_remove {
            if counters.remove(&key).is_some() {
                removed_count += 1;
            }
        }

        Ok(removed_count)
    }

    /// 添加端点限制
    pub fn add_endpoint_limit(&mut self, endpoint: String, limit: RateLimit) {
        self.config.endpoint_limits.insert(endpoint, limit);
    }

    /// 添加客户端限制
    pub fn add_client_limit(&mut self, client_id: String, limit: RateLimit) {
        self.config.client_limits.insert(client_id, limit);
    }

    /// 获取速率限制配置
    pub fn get_config(&self) -> &RateLimitConfig {
        &self.config
    }

    /// 获取统计信息
    pub async fn get_stats(&self) -> RateLimiterStats {
        let counters = self.counters.read().await;
        let blocked_count = *self.blocked_count.read().await;

        let mut total_clients = 0;
        let mut total_requests = 0;
        let mut total_blocked = 0;

        for counter in counters.values() {
            total_clients += 1;
            total_requests += counter.requests.len();
            total_blocked += counter.blocked_requests;
        }

        RateLimiterStats {
            enabled: self.config.enabled,
            total_clients,
            total_requests,
            total_blocked: total_blocked as usize,
            blocked_count,
            max_entries: self.config.max_entries,
            window_size: self.config.window_size,
        }
    }
}

/// 速率限制结果
#[derive(Debug, Clone)]
pub struct RateLimitResult {
    pub allowed: bool,
    pub exceeded: bool,
    pub limit: u32,
    pub remaining: u32,
    pub reset_time: Instant,
    pub retry_after: Option<u64>,
    pub client_id: String,
    pub endpoint: String,
}

impl RateLimitResult {
    /// 创建允许的结果
    pub fn allowed() -> Self {
        Self {
            allowed: true,
            exceeded: false,
            limit: 0,
            remaining: 0,
            reset_time: Instant::now(),
            retry_after: None,
            client_id: String::new(),
            endpoint: String::new(),
        }
    }

    /// 获取重试等待时间（秒）
    pub fn get_retry_after_seconds(&self) -> Option<u64> {
        self.retry_after
    }

    /// 检查是否应该重试
    pub fn should_retry(&self) -> bool {
        self.reset_time <= Instant::now()
    }
}

/// 客户端统计信息
#[derive(Debug, Clone)]
pub struct ClientStats {
    pub client_id: String,
    pub total_requests: usize,
    pub blocked_requests: u32,
    pub endpoints: Vec<String>,
    pub last_seen: Instant,
}

/// 速率限制器统计信息
#[derive(Debug, Clone)]
pub struct RateLimiterStats {
    pub enabled: bool,
    pub total_clients: usize,
    pub total_requests: usize,
    pub total_blocked: usize,
    pub blocked_count: usize,
    pub max_entries: usize,
    pub window_size: Duration,
}

/// 速率限制错误
#[derive(Error, Debug, Clone)]
pub enum RateLimitError {
    #[error("速率限制配置错误: {0}")]
    ConfigurationError(String),
    #[error("客户端ID无效: {0}")]
    InvalidClientId(String),
    #[error("端点无效: {0}")]
    InvalidEndpoint(String),
    #[error("存储错误: {0}")]
    StorageError(String),
    #[error("清理错误: {0}")]
    CleanupError(String),
}

/// 速率限制结果类型别名
pub type RateLimitResultType<T> = Result<T, RateLimitError>;
