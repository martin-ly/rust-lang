//! 缓存中间件
//!
//! 提供HTTP响应缓存、内存缓存和分布式缓存功能

use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use tokio::sync::RwLock;
use tracing::{debug, info, warn, instrument};
use serde::{Deserialize, Serialize};

/// 缓存配置
#[derive(Debug, Clone)]
pub struct CacheConfig {
    pub default_ttl: Duration,
    pub max_size: usize,
    pub enable_memory_cache: bool,
    pub enable_redis_cache: bool,
    pub cache_key_prefix: String,
    pub compress_responses: bool,
    pub cache_control_headers: bool,
}

impl Default for CacheConfig {
    fn default() -> Self {
        Self {
            default_ttl: Duration::from_secs(300), // 5分钟
            max_size: 1000,
            enable_memory_cache: true,
            enable_redis_cache: false,
            cache_key_prefix: "cache:".to_string(),
            compress_responses: false,
            cache_control_headers: true,
        }
    }
}

impl CacheConfig {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_ttl(mut self, ttl: Duration) -> Self {
        self.default_ttl = ttl;
        self
    }

    pub fn with_max_size(mut self, size: usize) -> Self {
        self.max_size = size;
        self
    }

    pub fn with_redis(mut self, enabled: bool) -> Self {
        self.enable_redis_cache = enabled;
        self
    }

    pub fn with_compression(mut self, enabled: bool) -> Self {
        self.compress_responses = enabled;
        self
    }
}

/// 缓存项
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheItem {
    pub key: String,
    pub value: Vec<u8>,
    pub created_at: u64,
    pub expires_at: u64,
    pub access_count: u64,
    pub last_accessed: u64,
    pub headers: HashMap<String, String>,
    pub compressed: bool,
}

impl CacheItem {
    pub fn new(key: String, value: Vec<u8>, ttl: Duration) -> Self {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        Self {
            key,
            value,
            created_at: now,
            expires_at: now + ttl.as_secs(),
            access_count: 0,
            last_accessed: now,
            headers: HashMap::new(),
            compressed: false,
        }
    }

    pub fn is_expired(&self) -> bool {
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        self.expires_at < now
    }

    pub fn access(&mut self) {
        self.access_count += 1;
        self.last_accessed = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
    }

    pub fn with_headers(mut self, headers: HashMap<String, String>) -> Self {
        self.headers = headers;
        self
    }

    pub fn with_compression(mut self, compressed: bool) -> Self {
        self.compressed = compressed;
        self
    }
}

/// 内存缓存
#[derive(Debug)]
pub struct MemoryCache {
    items: Arc<RwLock<HashMap<String, CacheItem>>>,
    config: CacheConfig,
    stats: Arc<RwLock<CacheStats>>,
}

impl MemoryCache {
    pub fn new(config: CacheConfig) -> Self {
        Self {
            items: Arc::new(RwLock::new(HashMap::new())),
            config,
            stats: Arc::new(RwLock::new(CacheStats::new())),
        }
    }

    /// 获取缓存项
    #[instrument(skip(self))]
    pub async fn get(&self, key: &str) -> Option<CacheItem> {
        let mut items = self.items.write().await;
        let mut stats = self.stats.write().await;

        if let Some(mut item) = items.get(key).cloned() {
            // 检查是否过期
            if item.is_expired() {
                items.remove(key);
                stats.misses += 1;
                stats.expired_removals += 1;
                debug!("缓存项已过期: {}", key);
                return None;
            }

            // 更新访问统计
            item.access();
            stats.hits += 1;
            debug!("缓存命中: {}", key);
            Some(item)
        } else {
            stats.misses += 1;
            debug!("缓存未命中: {}", key);
            None
        }
    }

    /// 设置缓存项
    #[instrument(skip(self, value))]
    pub async fn set(&self, key: String, value: Vec<u8>, ttl: Option<Duration>) -> Result<(), CacheError> {
        let ttl = ttl.unwrap_or(self.config.default_ttl);
        let mut item = CacheItem::new(key.clone(), value, ttl);

        // 压缩响应
        if self.config.compress_responses && item.value.len() > 1024 {
            item = self.compress_item(item).await?;
        }

        let mut items = self.items.write().await;
        let mut stats = self.stats.write().await;

        // 检查缓存大小限制
        if items.len() >= self.config.max_size && !items.contains_key(&key) {
            self.evict_oldest(&mut items).await;
        }

        items.insert(key.clone(), item);
        stats.sets += 1;
        
        debug!("缓存项已设置: {}", key);
        Ok(())
    }

    /// 删除缓存项
    #[instrument(skip(self))]
    pub async fn delete(&self, key: &str) -> bool {
        let mut items = self.items.write().await;
        let mut stats = self.stats.write().await;

        if items.remove(key).is_some() {
            stats.deletes += 1;
            debug!("缓存项已删除: {}", key);
            true
        } else {
            false
        }
    }

    /// 清空缓存
    #[instrument(skip(self))]
    pub async fn clear(&self) {
        let mut items = self.items.write().await;
        let mut stats = self.stats.write().await;

        let count = items.len();
        items.clear();
        stats.clears += 1;
        
        info!("缓存已清空，删除了 {} 个项", count);
    }

    /// 获取缓存统计
    pub async fn get_stats(&self) -> CacheStats {
        self.stats.read().await.clone()
    }

    /// 压缩缓存项
    async fn compress_item(&self, mut item: CacheItem) -> Result<CacheItem, CacheError> {
        use flate2::write::GzEncoder;
        use flate2::Compression;
        use std::io::Write;

        let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
        encoder.write_all(&item.value)
            .map_err(|e| CacheError::CompressionError(e.to_string()))?;
        
        let compressed_data = encoder.finish()
            .map_err(|e| CacheError::CompressionError(e.to_string()))?;

        item.value = compressed_data;
        item.compressed = true;
        item.headers.insert("Content-Encoding".to_string(), "gzip".to_string());

        Ok(item)
    }

    /// 驱逐最旧的项
    async fn evict_oldest(&self, items: &mut HashMap<String, CacheItem>) {
        let mut oldest_key = None;
        let mut oldest_time = u64::MAX;

        for (key, item) in items.iter() {
            if item.last_accessed < oldest_time {
                oldest_time = item.last_accessed;
                oldest_key = Some(key.clone());
            }
        }

        if let Some(key) = oldest_key {
            items.remove(&key);
            debug!("驱逐最旧的缓存项: {}", key);
        }
    }
}

/// 缓存统计
#[derive(Debug, Clone, Default)]
pub struct CacheStats {
    pub hits: u64,
    pub misses: u64,
    pub sets: u64,
    pub deletes: u64,
    pub clears: u64,
    pub expired_removals: u64,
}

impl CacheStats {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn hit_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 {
            0.0
        } else {
            self.hits as f64 / total as f64
        }
    }

    pub fn total_requests(&self) -> u64 {
        self.hits + self.misses
    }
}

/// HTTP缓存中间件
#[derive(Debug, Clone)]
pub struct HttpCacheMiddleware {
    pub config: CacheConfig,
    pub cache_by_path: bool,
    pub cache_by_query: bool,
    pub cache_by_headers: Vec<String>,
    pub cache_control: CacheControl,
}

impl Default for HttpCacheMiddleware {
    fn default() -> Self {
        Self::new(CacheConfig::default())
    }
}

impl HttpCacheMiddleware {
    pub fn new(config: CacheConfig) -> Self {
        Self {
            config,
            cache_by_path: true,
            cache_by_query: false,
            cache_by_headers: vec!["Authorization".to_string()],
            cache_control: CacheControl::Public,
        }
    }

    pub fn with_cache_control(mut self, control: CacheControl) -> Self {
        self.cache_control = control;
        self
    }

    pub fn with_query_caching(mut self, enabled: bool) -> Self {
        self.cache_by_query = enabled;
        self
    }

    /// 生成缓存键
    pub fn generate_cache_key(&self, request: &HttpCacheRequest) -> String {
        let mut key_parts = vec![self.config.cache_key_prefix.clone()];

        // 添加路径
        if self.cache_by_path {
            key_parts.push(request.path.clone());
        }

        // 添加查询参数
        if self.cache_by_query && !request.query_params.is_empty() {
            let mut query_keys: Vec<String> = request.query_params.keys().cloned().collect();
            query_keys.sort();
            let query_string = query_keys.into_iter()
                .map(|k| format!("{}={}", k, request.query_params[&k]))
                .collect::<Vec<_>>()
                .join("&");
            key_parts.push(query_string);
        }

        // 添加相关请求头
        for header_name in &self.cache_by_headers {
            if let Some(header_value) = request.headers.get(header_name) {
                key_parts.push(format!("{}:{}", header_name, header_value));
            }
        }

        // 生成哈希键
        let key_string = key_parts.join(":");
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        key_string.hash(&mut hasher);
        format!("{:x}", hasher.finish())
    }

    /// 检查是否应该缓存响应
    pub fn should_cache_response(&self, response: &HttpCacheResponse) -> bool {
        // 检查状态码 (200-299 表示成功)
        if response.status_code < 200 || response.status_code >= 300 {
            return false;
        }

        // 检查缓存控制头
        if let Some(ref cache_control) = response.headers.get("Cache-Control") {
            if cache_control.contains("no-cache") || cache_control.contains("no-store") {
                return false;
            }
        }

        // 检查内容类型
        if let Some(ref content_type) = response.headers.get("Content-Type") {
            if content_type.starts_with("application/json") || 
               content_type.starts_with("text/") ||
               content_type.starts_with("image/") {
                return true;
            }
        }

        false
    }

    /// 计算缓存TTL
    pub fn calculate_ttl(&self, response: &HttpCacheResponse) -> Duration {
        // 检查Cache-Control头中的max-age
        if let Some(ref cache_control) = response.headers.get("Cache-Control") {
            if let Some(max_age) = self.extract_max_age(cache_control) {
                return Duration::from_secs(max_age);
            }
        }

        // 检查Expires头
        if let Some(ref expires) = response.headers.get("Expires") {
            if let Ok(expires_time) = self.parse_expires_header(expires) {
                let now = SystemTime::now()
                    .duration_since(UNIX_EPOCH)
                    .unwrap()
                    .as_secs();
                if expires_time > now {
                    return Duration::from_secs(expires_time - now);
                }
            }
        }

        self.config.default_ttl
    }

    /// 提取max-age值
    fn extract_max_age(&self, cache_control: &str) -> Option<u64> {
        for part in cache_control.split(',') {
            let part = part.trim();
            if part.starts_with("max-age=") {
                if let Ok(age) = part[8..].parse::<u64>() {
                    return Some(age);
                }
            }
        }
        None
    }

    /// 解析Expires头
    #[allow(unused)]
    fn parse_expires_header(&self, expires: &str) -> Result<u64, Box<dyn std::error::Error>> {
        // 简化的日期解析，实际项目中应该使用更robust的日期解析库
        // 这里返回当前时间+默认TTL作为示例
        let now = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        Ok(now + self.config.default_ttl.as_secs())
    }
}

/// 缓存控制
#[derive(Debug, Clone)]
pub enum CacheControl {
    Public,
    Private,
    NoCache,
    NoStore,
    MustRevalidate,
}

impl CacheControl {
    pub fn to_header_value(&self) -> String {
        match self {
            CacheControl::Public => "public".to_string(),
            CacheControl::Private => "private".to_string(),
            CacheControl::NoCache => "no-cache".to_string(),
            CacheControl::NoStore => "no-store".to_string(),
            CacheControl::MustRevalidate => "must-revalidate".to_string(),
        }
    }
}

/// HTTP缓存请求
#[derive(Debug, Clone)]
pub struct HttpCacheRequest {
    pub method: String,
    pub path: String,
    pub query_params: HashMap<String, String>,
    pub headers: HashMap<String, String>,
}

/// HTTP缓存响应
#[derive(Debug, Clone)]
pub struct HttpCacheResponse {
    pub status_code: u16,
    pub headers: HashMap<String, String>,
    pub body: Vec<u8>,
    pub created_at: Instant,
}

impl HttpCacheResponse {
    pub fn new(status_code: u16, body: Vec<u8>) -> Self {
        Self {
            status_code,
            headers: HashMap::new(),
            body,
            created_at: Instant::now(),
        }
    }

    pub fn with_headers(mut self, headers: HashMap<String, String>) -> Self {
        self.headers = headers;
        self
    }

    pub fn age(&self) -> Duration {
        self.created_at.elapsed()
    }
}

/// 缓存管理器
#[derive(Debug)]
pub struct CacheManager {
    pub memory_cache: Option<MemoryCache>,
    pub http_cache: HttpCacheMiddleware,
    pub stats: Arc<RwLock<CacheStats>>,
}

impl CacheManager {
    pub fn new(config: CacheConfig) -> Self {
        let memory_cache = if config.enable_memory_cache {
            Some(MemoryCache::new(config.clone()))
        } else {
            None
        };

        Self {
            memory_cache,
            http_cache: HttpCacheMiddleware::new(config),
            stats: Arc::new(RwLock::new(CacheStats::new())),
        }
    }

    /// 获取缓存项
    pub async fn get(&self, key: &str) -> Option<CacheItem> {
        if let Some(ref cache) = self.memory_cache {
            cache.get(key).await
        } else {
            None
        }
    }

    /// 设置缓存项
    pub async fn set(&self, key: String, value: Vec<u8>, ttl: Option<Duration>) -> Result<(), CacheError> {
        if let Some(ref cache) = self.memory_cache {
            cache.set(key, value, ttl).await
        } else {
            Ok(())
        }
    }

    /// 处理HTTP缓存请求
    pub async fn handle_http_request(&self, request: HttpCacheRequest) -> Option<HttpCacheResponse> {
        let cache_key = self.http_cache.generate_cache_key(&request);
        
        if let Some(cache_item) = self.get(&cache_key).await {
            debug!("HTTP缓存命中: {}", cache_key);
            
            return Some(HttpCacheResponse {
                status_code: 200,
                headers: cache_item.headers.clone(),
                body: cache_item.value,
                created_at: Instant::now(),
            });
        }

        debug!("HTTP缓存未命中: {}", cache_key);
        None
    }

    /// 缓存HTTP响应
    pub async fn cache_http_response(&self, request: HttpCacheRequest, response: HttpCacheResponse) {
        if self.http_cache.should_cache_response(&response) {
            let cache_key = self.http_cache.generate_cache_key(&request);
            let ttl = self.http_cache.calculate_ttl(&response);
            
            let mut headers = response.headers.clone();
            headers.insert("X-Cache".to_string(), "MISS".to_string());
            
            let cache_item = CacheItem::new(cache_key.clone(), response.body, ttl)
                .with_headers(headers);

            if let Err(e) = self.set(cache_key.clone(), cache_item.value, Some(ttl)).await {
                warn!("缓存HTTP响应失败: {} - {}", cache_key, e);
            } else {
                debug!("HTTP响应已缓存: {}", cache_key);
            }
        }
    }

    /// 获取缓存统计
    pub async fn get_stats(&self) -> CacheStats {
        if let Some(ref cache) = self.memory_cache {
            cache.get_stats().await
        } else {
            CacheStats::new()
        }
    }

    /// 清空缓存
    pub async fn clear(&self) {
        if let Some(ref cache) = self.memory_cache {
            cache.clear().await;
        }
    }
}

/// 缓存错误
#[derive(Debug, thiserror::Error)]
pub enum CacheError {
    #[error("缓存压缩失败: {0}")]
    CompressionError(String),
    
    #[error("缓存序列化失败: {0}")]
    SerializationError(String),
    
    #[error("缓存反序列化失败: {0}")]
    DeserializationError(String),
    
    #[error("缓存大小超限")]
    SizeLimitExceeded,
    
    #[error("缓存键无效: {0}")]
    InvalidKey(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache_config() {
        let config = CacheConfig::new()
            .with_ttl(Duration::from_secs(600))
            .with_max_size(2000)
            .with_compression(true);

        assert_eq!(config.default_ttl.as_secs(), 600);
        assert_eq!(config.max_size, 2000);
        assert!(config.compress_responses);
    }

    #[test]
    fn test_cache_item() {
        let item = CacheItem::new("test-key".to_string(), b"test-value".to_vec(), Duration::from_secs(60));
        
        assert_eq!(item.key, "test-key");
        assert_eq!(item.value, b"test-value");
        assert!(!item.is_expired());
        assert_eq!(item.access_count, 0);
    }

    #[tokio::test]
    async fn test_memory_cache() {
        let config = CacheConfig::new().with_max_size(10);
        let cache = MemoryCache::new(config);

        // 测试设置和获取
        let key = "test-key".to_string();
        let value = b"test-value".to_vec();
        
        cache.set(key.clone(), value.clone(), None).await.unwrap();
        let retrieved = cache.get(&key).await;
        
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().value, value);

        // 测试删除
        assert!(cache.delete(&key).await);
        assert!(cache.get(&key).await.is_none());
    }

    #[test]
    fn test_http_cache_middleware() {
        let config = CacheConfig::new();
        let middleware = HttpCacheMiddleware::new(config);

        let request = HttpCacheRequest {
            method: "GET".to_string(),
            path: "/api/users".to_string(),
            query_params: HashMap::new(),
            headers: HashMap::new(),
        };

        let cache_key = middleware.generate_cache_key(&request);
        assert!(!cache_key.is_empty());
    }

    #[tokio::test]
    async fn test_cache_manager() {
        let config = CacheConfig::new();
        let manager = CacheManager::new(config);

        let key = "test-key".to_string();
        let value = b"test-value".to_vec();
        
        manager.set(key.clone(), value.clone(), None).await.unwrap();
        let retrieved = manager.get(&key).await;
        
        assert!(retrieved.is_some());
        assert_eq!(retrieved.unwrap().value, value);
    }
}
