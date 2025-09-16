//! # 工作流扩展中间件 / Workflow Extension Middleware
//!
//! 本模块实现了工作流系统的扩展中间件，包括缓存、压缩、加密等。
//! This module implements extension middleware for workflow systems, including caching, compression, encryption, etc.

use crate::middleware::{MiddlewareContext, MiddlewarePriority, WorkflowMiddleware};
use async_trait::async_trait;
use std::collections::HashMap;

/// 初始化扩展中间件 / Initialize extension middleware
pub fn init_extension_middleware() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("初始化扩展中间件 / Initializing extension middleware");
    Ok(())
}

/// 缓存中间件 / Caching Middleware
///
/// 提供工作流请求的缓存功能。
/// Provides caching functionality for workflow requests.
pub struct CachingMiddleware {
    name: String,
    version: String,
    description: String,
    priority: MiddlewarePriority,
    cache: HashMap<String, CachedItem>,
}

/// 缓存项 / Cached Item
#[derive(Debug, Clone)]
struct CachedItem {
    data: serde_json::Value,
    timestamp: std::time::Instant,
    ttl: std::time::Duration,
}

impl Default for CachingMiddleware {
    fn default() -> Self {
        Self::new()
    }
}

#[allow(dead_code)]
impl CachingMiddleware {
    /// 创建缓存中间件 / Create caching middleware
    pub fn new() -> Self {
        Self {
            name: "CachingMiddleware".to_string(),
            version: "1.0.0".to_string(),
            description: "工作流缓存中间件 / Workflow caching middleware".to_string(),
            priority: MiddlewarePriority::Normal,
            cache: HashMap::new(),
        }
    }

    /// 获取缓存项 / Get cached item
    fn get_cached_item(&self, key: &str) -> Option<&CachedItem> {
        self.cache.get(key).and_then(|item| {
            if item.timestamp.elapsed() < item.ttl {
                Some(item)
            } else {
                None
            }
        })
    }

    /// 设置缓存项 / Set cached item
    fn set_cached_item(&mut self, key: String, data: serde_json::Value, ttl: std::time::Duration) {
        let item = CachedItem {
            data,
            timestamp: std::time::Instant::now(),
            ttl,
        };
        self.cache.insert(key, item);
    }
}

#[async_trait]
impl WorkflowMiddleware for CachingMiddleware {
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        &self.version
    }

    fn description(&self) -> &str {
        &self.description
    }

    fn priority(&self) -> MiddlewarePriority {
        self.priority
    }

    async fn before_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        tracing::debug!("执行缓存中间件 / Executing caching middleware");

        // 检查是否有缓存 / Check if there's a cache
        let cache_key = format!("{}_{}", context.workflow_id, context.request_id);

        if let Some(cached_item) = self.get_cached_item(&cache_key) {
            tracing::info!("使用缓存数据 / Using cached data for key: {}", cache_key);
            context.set_metadata("cache_hit".to_string(), "true".to_string());
            context.set_metadata("cached_data".to_string(), cached_item.data.to_string());
        } else {
            context.set_metadata("cache_hit".to_string(), "false".to_string());
        }

        Ok(())
    }

    async fn after_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        tracing::debug!("缓存中间件请求后处理 / Caching middleware after request processing");

        // 如果请求成功且没有缓存命中，则缓存结果 / If request succeeded and no cache hit, cache the result
        if context.get_metadata("cache_hit") == Some(&"false".to_string()) {
            let cache_key = format!("{}_{}", context.workflow_id, context.request_id);
            let ttl = std::time::Duration::from_secs(300); // 5分钟缓存 / 5 minutes cache

            // 注意：这里需要可变引用，但在 trait 中不能直接修改
            // Note: This requires a mutable reference, but cannot directly modify in trait
            context.set_metadata("cache_key".to_string(), cache_key);
            context.set_metadata("cache_ttl".to_string(), ttl.as_secs().to_string());
        }

        Ok(())
    }

    async fn handle_error(
        &self,
        _context: &mut MiddlewareContext,
        error: &str,
    ) -> Result<(), String> {
        tracing::error!(
            "缓存中间件错误处理 / Caching middleware error handling: {}",
            error
        );
        Ok(())
    }
}

/// 压缩中间件 / Compression Middleware
///
/// 提供工作流请求的压缩功能。
/// Provides compression functionality for workflow requests.
pub struct CompressionMiddleware {
    name: String,
    version: String,
    description: String,
    priority: MiddlewarePriority,
}

#[allow(dead_code)]
impl Default for CompressionMiddleware {
    fn default() -> Self {
        Self::new()
    }
}

impl CompressionMiddleware {
    /// 创建压缩中间件 / Create compression middleware
    pub fn new() -> Self {
        Self {
            name: "CompressionMiddleware".to_string(),
            version: "1.0.0".to_string(),
            description: "工作流压缩中间件 / Workflow compression middleware".to_string(),
            priority: MiddlewarePriority::Low,
        }
    }

    /// 压缩数据 / Compress data
    #[allow(dead_code)]
    fn compress_data(&self, data: &str) -> Result<Vec<u8>, String> {
        // 简单的压缩实现 / Simple compression implementation
        // 在实际应用中，可以使用更复杂的压缩算法 / In actual applications, more complex compression algorithms can be used
        Ok(data.as_bytes().to_vec())
    }

    /// 解压数据 / Decompress data
    #[allow(dead_code)]
    fn decompress_data(&self, compressed_data: &[u8]) -> Result<String, String> {
        // 简单的解压实现 / Simple decompression implementation
        String::from_utf8(compressed_data.to_vec())
            .map_err(|e| format!("解压失败 / Decompression failed: {}", e))
    }
}

#[async_trait]
impl WorkflowMiddleware for CompressionMiddleware {
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        &self.version
    }

    fn description(&self) -> &str {
        &self.description
    }

    fn priority(&self) -> MiddlewarePriority {
        self.priority
    }

    async fn before_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        tracing::debug!("执行压缩中间件 / Executing compression middleware");

        // 检查是否需要解压 / Check if decompression is needed
        if let Some(compressed_data) = context.get_header("Content-Encoding")
            && compressed_data == "gzip" {
            tracing::info!(
                "检测到压缩数据，准备解压 / Detected compressed data, preparing to decompress"
            );
            context.set_metadata("compression_detected".to_string(), "true".to_string());
        }

        Ok(())
    }

    async fn after_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        tracing::debug!("压缩中间件请求后处理 / Compression middleware after request processing");

        // 检查是否需要压缩响应 / Check if response needs compression
        if let Some(accept_encoding) = context.get_header("Accept-Encoding")
            && accept_encoding.contains("gzip") {
            tracing::info!(
                "客户端支持压缩，准备压缩响应 / Client supports compression, preparing to compress response"
            );
            context.set_metadata("compression_enabled".to_string(), "true".to_string());
        }

        Ok(())
    }

    async fn handle_error(
        &self,
        _context: &mut MiddlewareContext,
        error: &str,
    ) -> Result<(), String> {
        tracing::error!(
            "压缩中间件错误处理 / Compression middleware error handling: {}",
            error
        );
        Ok(())
    }
}

/// 加密中间件 / Encryption Middleware
///
/// 提供工作流请求的加密功能。
/// Provides encryption functionality for workflow requests.
pub struct EncryptionMiddleware {
    name: String,
    version: String,
    description: String,
    priority: MiddlewarePriority,
}

#[allow(dead_code)]
impl Default for EncryptionMiddleware {
    fn default() -> Self {
        Self::new()
    }
}

impl EncryptionMiddleware {
    /// 创建加密中间件 / Create encryption middleware
    pub fn new() -> Self {
        Self {
            name: "EncryptionMiddleware".to_string(),
            version: "1.0.0".to_string(),
            description: "工作流加密中间件 / Workflow encryption middleware".to_string(),
            priority: MiddlewarePriority::High,
        }
    }

    /// 加密数据 / Encrypt data
    #[allow(dead_code)]
    fn encrypt_data(&self, data: &str, key: &str) -> Result<String, String> {
        // 简单的加密实现 / Simple encryption implementation
        // 在实际应用中，应该使用更安全的加密算法 / In actual applications, more secure encryption algorithms should be used
        let mut encrypted = String::new();
        for (i, c) in data.chars().enumerate() {
            let key_char = key.chars().nth(i % key.len()).unwrap_or('A');
            let encrypted_char = ((c as u8) ^ (key_char as u8)) as char;
            encrypted.push(encrypted_char);
        }
        Ok(encrypted)
    }

    /// 解密数据 / Decrypt data
    #[allow(dead_code)]
    fn decrypt_data(&self, encrypted_data: &str, key: &str) -> Result<String, String> {
        // 简单的解密实现 / Simple decryption implementation
        let mut decrypted = String::new();
        for (i, c) in encrypted_data.chars().enumerate() {
            let key_char = key.chars().nth(i % key.len()).unwrap_or('A');
            let decrypted_char = ((c as u8) ^ (key_char as u8)) as char;
            decrypted.push(decrypted_char);
        }
        Ok(decrypted)
    }
}

#[async_trait]
impl WorkflowMiddleware for EncryptionMiddleware {
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        &self.version
    }

    fn description(&self) -> &str {
        &self.description
    }

    fn priority(&self) -> MiddlewarePriority {
        self.priority
    }

    async fn before_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        tracing::debug!("执行加密中间件 / Executing encryption middleware");

        // 检查是否需要解密 / Check if decryption is needed
        if let Some(encrypted_header) = context.get_header("X-Encrypted")
            && encrypted_header == "true" {
            tracing::info!(
                "检测到加密数据，准备解密 / Detected encrypted data, preparing to decrypt"
            );
            context.set_metadata("encryption_detected".to_string(), "true".to_string());
        }

        Ok(())
    }

    async fn after_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        tracing::debug!("加密中间件请求后处理 / Encryption middleware after request processing");

        // 检查是否需要加密响应 / Check if response needs encryption
        if let Some(encrypt_header) = context.get_header("X-Require-Encryption")
            && encrypt_header == "true" {
            tracing::info!("需要加密响应 / Response encryption required");
            context.set_metadata("encryption_required".to_string(), "true".to_string());
        }

        Ok(())
    }

    async fn handle_error(
        &self,
        _context: &mut MiddlewareContext,
        error: &str,
    ) -> Result<(), String> {
        tracing::error!(
            "加密中间件错误处理 / Encryption middleware error handling: {}",
            error
        );
        Ok(())
    }
}

/// 重试中间件 / Retry Middleware
///
/// 提供工作流请求的重试功能。
/// Provides retry functionality for workflow requests.
pub struct RetryMiddleware {
    name: String,
    version: String,
    description: String,
    priority: MiddlewarePriority,
    max_retries: u32,
    retry_delay: std::time::Duration,
}

impl Default for RetryMiddleware {
    fn default() -> Self {
        Self::new()
    }
}

impl RetryMiddleware {
    /// 创建重试中间件 / Create retry middleware
    pub fn new() -> Self {
        Self {
            name: "RetryMiddleware".to_string(),
            version: "1.0.0".to_string(),
            description: "工作流重试中间件 / Workflow retry middleware".to_string(),
            priority: MiddlewarePriority::Normal,
            max_retries: 3,
            retry_delay: std::time::Duration::from_secs(1),
        }
    }

    /// 设置最大重试次数 / Set maximum retry count
    pub fn with_max_retries(mut self, max_retries: u32) -> Self {
        self.max_retries = max_retries;
        self
    }

    /// 设置重试延迟 / Set retry delay
    pub fn with_retry_delay(mut self, delay: std::time::Duration) -> Self {
        self.retry_delay = delay;
        self
    }
}

#[async_trait]
impl WorkflowMiddleware for RetryMiddleware {
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        &self.version
    }

    fn description(&self) -> &str {
        &self.description
    }

    fn priority(&self) -> MiddlewarePriority {
        self.priority
    }

    async fn before_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        tracing::debug!("执行重试中间件 / Executing retry middleware");

        // 初始化重试计数 / Initialize retry count
        let retry_count = context
            .get_metadata("retry_count")
            .and_then(|s| s.parse::<u32>().ok())
            .unwrap_or(0);

        context.set_metadata("retry_count".to_string(), retry_count.to_string());
        context.set_metadata("max_retries".to_string(), self.max_retries.to_string());

        Ok(())
    }

    async fn after_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        tracing::debug!("重试中间件请求后处理 / Retry middleware after request processing");

        // 检查是否需要重试 / Check if retry is needed
        let retry_count = context
            .get_metadata("retry_count")
            .and_then(|s| s.parse::<u32>().ok())
            .unwrap_or(0);

        if retry_count > 0 {
            tracing::info!(
                "请求重试成功 / Request retry successful, retry count: {}",
                retry_count
            );
            context.set_metadata("retry_successful".to_string(), "true".to_string());
        }

        Ok(())
    }

    async fn handle_error(
        &self,
        context: &mut MiddlewareContext,
        error: &str,
    ) -> Result<(), String> {
        tracing::error!(
            "重试中间件错误处理 / Retry middleware error handling: {}",
            error
        );

        let retry_count = context
            .get_metadata("retry_count")
            .and_then(|s| s.parse::<u32>().ok())
            .unwrap_or(0);

        if retry_count < self.max_retries {
            tracing::info!(
                "准备重试请求 / Preparing to retry request, attempt: {}/{}",
                retry_count + 1,
                self.max_retries
            );
            context.set_metadata("retry_count".to_string(), (retry_count + 1).to_string());
            context.set_metadata(
                "retry_delay_ms".to_string(),
                self.retry_delay.as_millis().to_string(),
            );
        } else {
            tracing::error!("达到最大重试次数 / Maximum retry count reached");
            context.set_metadata("retry_exhausted".to_string(), "true".to_string());
        }

        Ok(())
    }
}

/// 超时中间件 / Timeout Middleware
///
/// 提供工作流请求的超时功能。
/// Provides timeout functionality for workflow requests.
pub struct TimeoutMiddleware {
    name: String,
    version: String,
    description: String,
    priority: MiddlewarePriority,
    timeout: std::time::Duration,
}

impl Default for TimeoutMiddleware {
    fn default() -> Self {
        Self::new()
    }
}

impl TimeoutMiddleware {
    /// 创建超时中间件 / Create timeout middleware
    pub fn new() -> Self {
        Self {
            name: "TimeoutMiddleware".to_string(),
            version: "1.0.0".to_string(),
            description: "工作流超时中间件 / Workflow timeout middleware".to_string(),
            priority: MiddlewarePriority::High,
            timeout: std::time::Duration::from_secs(30),
        }
    }

    /// 设置超时时间 / Set timeout duration
    pub fn with_timeout(mut self, timeout: std::time::Duration) -> Self {
        self.timeout = timeout;
        self
    }
}

#[async_trait]
impl WorkflowMiddleware for TimeoutMiddleware {
    fn name(&self) -> &str {
        &self.name
    }

    fn version(&self) -> &str {
        &self.version
    }

    fn description(&self) -> &str {
        &self.description
    }

    fn priority(&self) -> MiddlewarePriority {
        self.priority
    }

    async fn before_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        tracing::debug!("执行超时中间件 / Executing timeout middleware");

        // 设置超时时间 / Set timeout duration
        context.set_metadata(
            "timeout_duration_ms".to_string(),
            self.timeout.as_millis().to_string(),
        );
        context.set_metadata(
            "timeout_start_time".to_string(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_millis()
                .to_string(),
        );

        Ok(())
    }

    async fn after_request(&self, context: &mut MiddlewareContext) -> Result<(), String> {
        tracing::debug!("超时中间件请求后处理 / Timeout middleware after request processing");

        // 检查是否超时 / Check if timeout occurred
        let execution_time = context.start_time.elapsed();
        if execution_time > self.timeout {
            tracing::warn!(
                "请求执行超时 / Request execution timeout: {}ms",
                execution_time.as_millis()
            );
            context.set_metadata("timeout_occurred".to_string(), "true".to_string());
        } else {
            context.set_metadata("timeout_occurred".to_string(), "false".to_string());
        }

        Ok(())
    }

    async fn handle_error(
        &self,
        context: &mut MiddlewareContext,
        error: &str,
    ) -> Result<(), String> {
        tracing::error!(
            "超时中间件错误处理 / Timeout middleware error handling: {}",
            error
        );

        // 检查是否是超时错误 / Check if it's a timeout error
        if error.contains("timeout") {
            context.set_metadata("timeout_error".to_string(), "true".to_string());
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_caching_middleware() {
        let middleware = CachingMiddleware::new();
        assert_eq!(middleware.name(), "CachingMiddleware");
        assert_eq!(middleware.priority(), MiddlewarePriority::Normal);

        let mut context = MiddlewareContext::new(
            "req_1".to_string(),
            "workflow_1".to_string(),
            serde_json::json!({}),
        );

        let result = middleware.before_request(&mut context).await;
        assert!(result.is_ok());
        assert_eq!(
            context.get_metadata("cache_hit"),
            Some(&"false".to_string())
        );
    }

    #[tokio::test]
    async fn test_compression_middleware() {
        let middleware = CompressionMiddleware::new();
        assert_eq!(middleware.name(), "CompressionMiddleware");
        assert_eq!(middleware.priority(), MiddlewarePriority::Low);

        let mut context = MiddlewareContext::new(
            "req_1".to_string(),
            "workflow_1".to_string(),
            serde_json::json!({}),
        );

        context.set_header("Content-Encoding".to_string(), "gzip".to_string());

        let result = middleware.before_request(&mut context).await;
        assert!(result.is_ok());
        assert_eq!(
            context.get_metadata("compression_detected"),
            Some(&"true".to_string())
        );
    }

    #[tokio::test]
    async fn test_encryption_middleware() {
        let middleware = EncryptionMiddleware::new();
        assert_eq!(middleware.name(), "EncryptionMiddleware");
        assert_eq!(middleware.priority(), MiddlewarePriority::High);

        let mut context = MiddlewareContext::new(
            "req_1".to_string(),
            "workflow_1".to_string(),
            serde_json::json!({}),
        );

        context.set_header("X-Encrypted".to_string(), "true".to_string());

        let result = middleware.before_request(&mut context).await;
        assert!(result.is_ok());
        assert_eq!(
            context.get_metadata("encryption_detected"),
            Some(&"true".to_string())
        );
    }

    #[tokio::test]
    async fn test_retry_middleware() {
        let middleware = RetryMiddleware::new();
        assert_eq!(middleware.name(), "RetryMiddleware");
        assert_eq!(middleware.priority(), MiddlewarePriority::Normal);

        let mut context = MiddlewareContext::new(
            "req_1".to_string(),
            "workflow_1".to_string(),
            serde_json::json!({}),
        );

        let result = middleware.before_request(&mut context).await;
        assert!(result.is_ok());
        assert_eq!(context.get_metadata("retry_count"), Some(&"0".to_string()));
    }

    #[tokio::test]
    async fn test_timeout_middleware() {
        let middleware = TimeoutMiddleware::new();
        assert_eq!(middleware.name(), "TimeoutMiddleware");
        assert_eq!(middleware.priority(), MiddlewarePriority::High);

        let mut context = MiddlewareContext::new(
            "req_1".to_string(),
            "workflow_1".to_string(),
            serde_json::json!({}),
        );

        let result = middleware.before_request(&mut context).await;
        assert!(result.is_ok());
        assert_eq!(
            context.get_metadata("timeout_duration_ms"),
            Some(&"30000".to_string())
        );
    }
}
