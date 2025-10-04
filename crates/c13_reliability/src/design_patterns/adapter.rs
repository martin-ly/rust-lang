/// 适配器模式 (Adapter Pattern)
///
/// 将一个类的接口转换成客户期望的另一个接口，使原本接口不兼容的类可以一起工作
///
/// # 应用场景
///
/// - 接口兼容性转换
/// - 第三方库集成
/// - 遗留系统集成
/// - 协议转换

use crate::prelude::*;
//use crate::error_handling::{ErrorContext, ErrorSeverity};
use std::sync::Arc;
//use std::collections::HashMap;
use serde::{Serialize, Deserialize};

// Helper function to create validation errors
fn validation_error(msg: impl Into<String>) -> anyhow::Error {
    anyhow::anyhow!(msg.into())
}

/// 适配器 trait
#[async_trait::async_trait]
pub trait Adapter<Source, Target>: Send + Sync {
    /// 适配转换
    async fn adapt(&self, source: Source) -> Result<Target>;
    
    /// 适配器名称
    fn name(&self) -> &str;
}

// ============================================================================
// 日志适配器 - 统一不同日志库的接口
// ============================================================================

/// 统一日志接口
#[async_trait::async_trait]
pub trait Logger: Send + Sync {
    async fn log(&self, level: LogLevel, message: &str) -> Result<()>;
}

/// 日志级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
}

/// Tracing库适配器
pub struct TracingAdapter;

#[async_trait::async_trait]
impl Logger for TracingAdapter {
    async fn log(&self, level: LogLevel, message: &str) -> Result<()> {
        match level {
            LogLevel::Trace => tracing::trace!("{}", message),
            LogLevel::Debug => tracing::debug!("{}", message),
            LogLevel::Info => tracing::info!("{}", message),
            LogLevel::Warn => tracing::warn!("{}", message),
            LogLevel::Error => tracing::error!("{}", message),
        }
        Ok(())
    }
}

/// Stdout适配器（简化版）
pub struct StdoutAdapter;

#[async_trait::async_trait]
impl Logger for StdoutAdapter {
    async fn log(&self, level: LogLevel, message: &str) -> Result<()> {
        println!("[{:?}] {}", level, message);
        Ok(())
    }
}

// ============================================================================
// 指标适配器 - 统一不同指标系统的接口
// ============================================================================

/// 统一指标接口
#[async_trait::async_trait]
pub trait MetricsCollector: Send + Sync {
    async fn increment_counter(&self, name: &str, value: u64) -> Result<()>;
    async fn record_gauge(&self, name: &str, value: f64) -> Result<()>;
    async fn record_histogram(&self, name: &str, value: f64) -> Result<()>;
}

/// 内存指标收集器（简化实现）
pub struct InMemoryMetricsCollector {
    counters: Arc<tokio::sync::RwLock<std::collections::HashMap<String, u64>>>,
    gauges: Arc<tokio::sync::RwLock<std::collections::HashMap<String, f64>>>,
    histograms: Arc<tokio::sync::RwLock<std::collections::HashMap<String, Vec<f64>>>>,
}

impl InMemoryMetricsCollector {
    pub fn new() -> Self {
        Self {
            counters: Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new())),
            gauges: Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new())),
            histograms: Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new())),
        }
    }
    
    pub async fn get_counter(&self, name: &str) -> Option<u64> {
        self.counters.read().await.get(name).copied()
    }
    
    pub async fn get_gauge(&self, name: &str) -> Option<f64> {
        self.gauges.read().await.get(name).copied()
    }
}

impl Default for InMemoryMetricsCollector {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait::async_trait]
impl MetricsCollector for InMemoryMetricsCollector {
    async fn increment_counter(&self, name: &str, value: u64) -> Result<()> {
        let mut counters = self.counters.write().await;
        *counters.entry(name.to_string()).or_insert(0) += value;
        Ok(())
    }
    
    async fn record_gauge(&self, name: &str, value: f64) -> Result<()> {
        let mut gauges = self.gauges.write().await;
        gauges.insert(name.to_string(), value);
        Ok(())
    }
    
    async fn record_histogram(&self, name: &str, value: f64) -> Result<()> {
        let mut histograms = self.histograms.write().await;
        histograms.entry(name.to_string())
            .or_insert_with(Vec::new)
            .push(value);
        Ok(())
    }
}

// ============================================================================
// 缓存适配器 - 统一不同缓存系统的接口
// ============================================================================

/// 统一缓存接口
#[async_trait::async_trait]
pub trait Cache<K, V>: Send + Sync {
    async fn get(&self, key: &K) -> Result<Option<V>>;
    async fn set(&self, key: K, value: V) -> Result<()>;
    async fn delete(&self, key: &K) -> Result<()>;
    async fn exists(&self, key: &K) -> Result<bool>;
}

/// 内存缓存适配器
pub struct MemoryCacheAdapter<K, V>
where
    K: std::hash::Hash + Eq + Clone + Send + Sync,
    V: Clone + Send + Sync,
{
    cache: Arc<tokio::sync::RwLock<std::collections::HashMap<K, V>>>,
}

impl<K, V> MemoryCacheAdapter<K, V>
where
    K: std::hash::Hash + Eq + Clone + Send + Sync,
    V: Clone + Send + Sync,
{
    pub fn new() -> Self {
        Self {
            cache: Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new())),
        }
    }
}

impl<K, V> Default for MemoryCacheAdapter<K, V>
where
    K: std::hash::Hash + Eq + Clone + Send + Sync,
    V: Clone + Send + Sync,
{
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait::async_trait]
impl<K, V> Cache<K, V> for MemoryCacheAdapter<K, V>
where
    K: std::hash::Hash + Eq + Clone + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    async fn get(&self, key: &K) -> Result<Option<V>> {
        Ok(self.cache.read().await.get(key).cloned())
    }
    
    async fn set(&self, key: K, value: V) -> Result<()> {
        self.cache.write().await.insert(key, value);
        Ok(())
    }
    
    async fn delete(&self, key: &K) -> Result<()> {
        self.cache.write().await.remove(key);
        Ok(())
    }
    
    async fn exists(&self, key: &K) -> Result<bool> {
        Ok(self.cache.read().await.contains_key(key))
    }
}

// ============================================================================
// 协议适配器 - HTTP到gRPC
// ============================================================================

/// HTTP请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HttpRequest {
    pub method: String,
    pub path: String,
    pub headers: std::collections::HashMap<String, String>,
    pub body: Vec<u8>,
}

/// gRPC请求（简化版）
#[derive(Debug, Clone)]
pub struct GrpcRequest {
    pub service: String,
    pub method: String,
    pub metadata: std::collections::HashMap<String, String>,
    pub payload: Vec<u8>,
}

/// HTTP到gRPC适配器
pub struct HttpToGrpcAdapter {
    service_mapping: std::collections::HashMap<String, String>,
}

impl HttpToGrpcAdapter {
    pub fn new() -> Self {
        Self {
            service_mapping: std::collections::HashMap::new(),
        }
    }
    
    pub fn with_mapping(mut self, http_path: impl Into<String>, grpc_service: impl Into<String>) -> Self {
        self.service_mapping.insert(http_path.into(), grpc_service.into());
        self
    }
}

impl Default for HttpToGrpcAdapter {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait::async_trait]
impl Adapter<HttpRequest, GrpcRequest> for HttpToGrpcAdapter {
    async fn adapt(&self, source: HttpRequest) -> Result<GrpcRequest> {
        // 从路径解析服务和方法
        let parts: Vec<&str> = source.path.trim_start_matches('/').split('/').collect();
        if parts.len() < 2 {
            return Err(validation_error("Invalid HTTP path for gRPC conversion"));
        }
        
        let service = self.service_mapping
            .get(&source.path)
            .cloned()
            .unwrap_or_else(|| parts[0].to_string());
        
        let method = parts.get(1)
            .map(|s| s.to_string())
            .unwrap_or_default();
        
        // 转换headers到metadata
        let mut metadata = std::collections::HashMap::new();
        for (k, v) in source.headers {
            if k.starts_with("x-") || k.starts_with("grpc-") {
                metadata.insert(k, v);
            }
        }
        
        Ok(GrpcRequest {
            service,
            method,
            metadata,
            payload: source.body,
        })
    }
    
    fn name(&self) -> &str {
        "http_to_grpc"
    }
}

// ============================================================================
// 数据格式适配器
// ============================================================================

// NOTE: MessagePack适配器需要添加rmp-serde依赖，这里暂时注释掉
// /// JSON到MessagePack适配器
// pub struct JsonToMessagePackAdapter;
//
// #[async_trait::async_trait]
// impl Adapter<serde_json::Value, Vec<u8>> for JsonToMessagePackAdapter {
//     async fn adapt(&self, source: serde_json::Value) -> Result<Vec<u8>> {
//         rmp_serde::to_vec(&source)
//             .map_err(|e| validation_error(e.to_string()))
//     }
//     
//     fn name(&self) -> &str {
//         "json_to_messagepack"
//     }
// }
//
// /// MessagePack到JSON适配器
// pub struct MessagePackToJsonAdapter;
//
// #[async_trait::async_trait]
// impl Adapter<Vec<u8>, serde_json::Value> for MessagePackToJsonAdapter {
//     async fn adapt(&self, source: Vec<u8>) -> Result<serde_json::Value> {
//         rmp_serde::from_slice(&source)
//             .map_err(|e| validation_error(e.to_string()))
//     }
//     
//     fn name(&self) -> &str {
//         "messagepack_to_json"
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_logger_adapter() {
        let logger = StdoutAdapter;
        logger.log(LogLevel::Info, "Test message").await.unwrap();
    }
    
    #[tokio::test]
    async fn test_metrics_collector() {
        let metrics = InMemoryMetricsCollector::new();
        
        metrics.increment_counter("requests", 1).await.unwrap();
        metrics.increment_counter("requests", 2).await.unwrap();
        
        assert_eq!(metrics.get_counter("requests").await, Some(3));
        
        metrics.record_gauge("cpu_usage", 0.75).await.unwrap();
        assert_eq!(metrics.get_gauge("cpu_usage").await, Some(0.75));
    }
    
    #[tokio::test]
    async fn test_cache_adapter() {
        let cache: MemoryCacheAdapter<String, String> = MemoryCacheAdapter::new();
        
        cache.set("key1".to_string(), "value1".to_string()).await.unwrap();
        
        let value = cache.get(&"key1".to_string()).await.unwrap();
        assert_eq!(value, Some("value1".to_string()));
        
        assert!(cache.exists(&"key1".to_string()).await.unwrap());
        
        cache.delete(&"key1".to_string()).await.unwrap();
        assert!(!cache.exists(&"key1".to_string()).await.unwrap());
    }
    
    #[tokio::test]
    async fn test_http_to_grpc_adapter() {
        let adapter = HttpToGrpcAdapter::new()
            .with_mapping("/api/user/get", "UserService");
        
        let http_req = HttpRequest {
            method: "POST".to_string(),
            path: "/api/user/get".to_string(),
            headers: [("x-request-id".to_string(), "123".to_string())]
                .iter()
                .cloned()
                .collect(),
            body: vec![1, 2, 3],
        };
        
        let grpc_req = adapter.adapt(http_req).await.unwrap();
        assert_eq!(grpc_req.service, "UserService");
        assert_eq!(grpc_req.metadata.get("x-request-id"), Some(&"123".to_string()));
    }
    
    // #[tokio::test]
    // async fn test_json_to_messagepack() {
    //     let adapter = JsonToMessagePackAdapter;
    //     let json = serde_json::json!({"name": "test", "value": 42});
    //     
    //     let msgpack = adapter.adapt(json.clone()).await.unwrap();
    //     assert!(!msgpack.is_empty());
    //     
    //     let back_adapter = MessagePackToJsonAdapter;
    //     let back_json = back_adapter.adapt(msgpack).await.unwrap();
    //     assert_eq!(json, back_json);
    // }
}

