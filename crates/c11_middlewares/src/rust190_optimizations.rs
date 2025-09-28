//! Rust 1.90 特性优化模块
//! 
//! 本模块展示了如何利用 Rust 1.90 的新特性来优化中间件实现：
//! - 常量泛型推断
//! - 生命周期语法一致性
//! - 改进的异步编程模式
//! - 类型安全的比较机制

use crate::error::Result;
use async_trait::async_trait;
use std::sync::Arc;

/// Rust 1.90 特性 1: 使用常量泛型优化连接池配置
/// 
/// 通过常量泛型参数提供编译时配置验证和内存优化
#[derive(Debug)]
pub struct OptimizedConnectionPool<const MAX_CONNECTIONS: usize = 10, const TIMEOUT_MS: u64 = 5000> {
    max_connections: usize,
    #[allow(dead_code)]
    timeout_ms: u64,
    current_connections: std::sync::atomic::AtomicUsize,
}

impl<const MAX_CONNECTIONS: usize, const TIMEOUT_MS: u64> OptimizedConnectionPool<MAX_CONNECTIONS, TIMEOUT_MS> {
    /// 创建新的连接池
    pub fn new() -> Self {
        Self {
            max_connections: MAX_CONNECTIONS,
            timeout_ms: TIMEOUT_MS,
            current_connections: std::sync::atomic::AtomicUsize::new(0),
        }
    }
    
    /// 使用常量推断创建指定大小的连接池
    pub fn with_capacity<const NEW_CAPACITY: usize>(_capacity: usize) -> OptimizedConnectionPool<NEW_CAPACITY, TIMEOUT_MS> {
        OptimizedConnectionPool::new()
    }
    
    /// 使用常量推断创建指定超时的连接池
    pub fn with_timeout<const NEW_TIMEOUT: u64>(_timeout: u64) -> OptimizedConnectionPool<MAX_CONNECTIONS, NEW_TIMEOUT> {
        OptimizedConnectionPool::new()
    }
    
    /// 获取连接
    pub async fn acquire(&self) -> Result<ConnectionHandle> {
        // 检查连接数限制
        let current = self.current_connections.load(std::sync::atomic::Ordering::Relaxed);
        if current >= self.max_connections {
            return Err(crate::error::Error::Other("连接池已满".to_string()));
        }
        
        // 增加连接计数
        self.current_connections.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        
        Ok(ConnectionHandle {
            pool: Arc::new(OptimizedConnectionPool::<10, 5000>::new()),
            created_at: std::time::Instant::now(),
        })
    }
    
    /// 释放连接
    pub fn release(&self) {
        self.current_connections.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
    }
    
    /// 获取当前连接数
    pub fn current_connections(&self) -> usize {
        self.current_connections.load(std::sync::atomic::Ordering::Relaxed)
    }
    
    /// 检查是否已满
    pub fn is_full(&self) -> bool {
        self.current_connections.load(std::sync::atomic::Ordering::Relaxed) >= self.max_connections
    }
}

/// 连接句柄，利用 Rust 1.90 的生命周期语法一致性
pub struct ConnectionHandle {
    pool: Arc<OptimizedConnectionPool<10, 5000>>, // 默认配置
    created_at: std::time::Instant,
}

impl ConnectionHandle {
    /// 生命周期语法一致的方法
    pub async fn execute_query<'a, 'b>(&'a self, query: &'b str) -> Result<String> 
    where 
        'b: 'a, // 确保 query 的生命周期不短于 self
    {
        // 模拟查询执行
        #[cfg(feature = "tokio")]
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        #[cfg(not(feature = "tokio"))]
        std::thread::sleep(std::time::Duration::from_millis(10));
        Ok(format!("执行查询: {} (连接创建于: {:?})", query, self.created_at))
    }
    
    /// 获取连接信息
    pub fn get_info(&self) -> String {
        format!("连接创建于: {:?}, 当前连接数: {}", 
                self.created_at, 
                self.pool.current_connections())
    }
}

impl Drop for ConnectionHandle {
    fn drop(&mut self) {
        self.pool.release();
    }
}

/// Rust 1.90 特性 2: 类型安全的中间件类型系统
/// 
/// 使用枚举和模式匹配替代函数指针比较，避免不确定行为
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum MiddlewareType {
    Redis,
    Postgres,
    Mysql,
    Sqlite,
    Nats,
    Kafka,
    Mqtt,
}

impl MiddlewareType {
    /// 使用模式匹配进行类型安全的比较
    pub fn is_database(&self) -> bool {
        matches!(self, MiddlewareType::Postgres | MiddlewareType::Mysql | MiddlewareType::Sqlite)
    }
    
    pub fn is_cache(&self) -> bool {
        matches!(self, MiddlewareType::Redis)
    }
    
    pub fn is_message_queue(&self) -> bool {
        matches!(self, MiddlewareType::Nats | MiddlewareType::Kafka | MiddlewareType::Mqtt)
    }
    
    /// 类型安全的比较
    pub fn is_same_category(&self, other: &Self) -> bool {
        (self.is_database() && other.is_database()) ||
        (self.is_cache() && other.is_cache()) ||
        (self.is_message_queue() && other.is_message_queue())
    }
    
    /// 获取默认端口
    pub fn default_port(&self) -> u16 {
        match self {
            MiddlewareType::Redis => 6379,
            MiddlewareType::Postgres => 5432,
            MiddlewareType::Mysql => 3306,
            MiddlewareType::Sqlite => 0, // 文件数据库
            MiddlewareType::Nats => 4222,
            MiddlewareType::Kafka => 9092,
            MiddlewareType::Mqtt => 1883,
        }
    }
    
    /// 获取协议前缀
    pub fn protocol_prefix(&self) -> &'static str {
        match self {
            MiddlewareType::Redis => "redis://",
            MiddlewareType::Postgres => "postgres://",
            MiddlewareType::Mysql => "mysql://",
            MiddlewareType::Sqlite => "sqlite://",
            MiddlewareType::Nats => "nats://",
            MiddlewareType::Kafka => "kafka://",
            MiddlewareType::Mqtt => "mqtt://",
        }
    }
}

/// Rust 1.90 特性 3: 改进的异步中间件接口
/// 
/// 利用 async fn in trait 和 GAT (Generic Associated Types)
#[async_trait]
pub trait OptimizedMiddleware {
    /// 使用 GAT 定义连接类型
    type Connection<'a>: Send + Sync + 'a where Self: 'a;
    type Error: std::error::Error + Send + Sync + 'static;
    
    /// 异步连接方法
    async fn connect(&self) -> std::result::Result<Self::Connection<'_>, Self::Error>;
    
    /// 异步执行方法
    async fn execute(&self, operation: &[u8]) -> std::result::Result<Vec<u8>, Self::Error>;
    
    /// 批量异步执行方法
    async fn batch_execute(&self, operations: Vec<&[u8]>) -> std::result::Result<Vec<Vec<u8>>, Self::Error>;
    
    /// 获取中间件类型
    fn middleware_type(&self) -> MiddlewareType;
    
    /// 获取配置信息
    fn get_config(&self) -> MiddlewareConfig;
}

/// 中间件配置，利用常量泛型优化
#[derive(Debug, Clone)]
pub struct MiddlewareConfig<const POOL_SIZE: usize = 10, const TIMEOUT_MS: u64 = 5000> {
    pub middleware_type: MiddlewareType,
    pub url: String,
    pub pool_size: usize,
    pub timeout_ms: u64,
    pub retry_count: u32,
}

impl<const POOL_SIZE: usize, const TIMEOUT_MS: u64> MiddlewareConfig<POOL_SIZE, TIMEOUT_MS> {
    pub fn new(middleware_type: MiddlewareType, url: String) -> Self {
        Self {
            middleware_type,
            url,
            pool_size: POOL_SIZE,
            timeout_ms: TIMEOUT_MS,
            retry_count: 3,
        }
    }
    
    /// 使用常量推断创建配置
    pub fn with_pool_size<const NEW_POOL_SIZE: usize>(_pool_size: usize) -> MiddlewareConfig<NEW_POOL_SIZE, TIMEOUT_MS> {
        MiddlewareConfig::new(MiddlewareType::Redis, "".to_string())
    }
    
    /// 验证配置
    pub fn validate(&self) -> Result<()> {
        if self.url.is_empty() {
            return Err(crate::error::Error::Other("URL 不能为空".to_string()));
        }
        
        if !self.url.starts_with(self.middleware_type.protocol_prefix()) {
            return Err(crate::error::Error::Other(
                format!("URL 必须以 {} 开头", self.middleware_type.protocol_prefix())
            ));
        }
        
        if self.pool_size == 0 {
            return Err(crate::error::Error::Other("连接池大小必须大于 0".to_string()));
        }
        
        if self.timeout_ms == 0 {
            return Err(crate::error::Error::Other("超时时间必须大于 0".to_string()));
        }
        
        Ok(())
    }
}

/// Rust 1.90 特性 4: 高级错误处理优化
/// 
/// 利用 Result::flatten 和新的错误处理机制
pub struct OptimizedErrorHandler;

impl OptimizedErrorHandler {
    /// 使用 Result::flatten 简化嵌套错误处理
    pub async fn batch_operations_with_flatten(
        operations: Vec<std::result::Result<Vec<u8>, String>>
    ) -> std::result::Result<Vec<Vec<u8>>, String> {
        let results: Vec<std::result::Result<Vec<u8>, String>> = operations
            .into_iter()
            .map(|op| op.map_err(|e| format!("操作失败: {}", e)))
            .collect();
        
        // 使用 Rust 1.90 的错误处理改进
        let mut success_results = Vec::new();
        let mut errors = Vec::new();
        
        for result in results {
            match result {
                Ok(data) => success_results.push(data),
                Err(e) => errors.push(e),
            }
        }
        
        if !errors.is_empty() {
            Err(format!("批量操作失败: {}", errors.join(", ")))
        } else {
            Ok(success_results)
        }
    }
    
    /// 错误恢复机制
    pub async fn execute_with_retry<F, Fut>(
        operation: F,
        max_retries: u32,
        backoff_ms: u64
    ) -> std::result::Result<Vec<u8>, String> 
    where
        F: Fn() -> Fut,
        Fut: std::future::Future<Output = std::result::Result<Vec<u8>, String>>,
    {
        let mut attempt = 0;
        let mut delay = backoff_ms;
        
        loop {
            match operation().await {
                Ok(result) => return Ok(result),
                Err(e) if attempt < max_retries => {
                    attempt += 1;
                    #[cfg(feature = "tokio")]
                    tokio::time::sleep(std::time::Duration::from_millis(delay)).await;
                    #[cfg(not(feature = "tokio"))]
                    std::thread::sleep(std::time::Duration::from_millis(delay));
                    delay = (delay * 2).min(5000); // 最大 5 秒
                    eprintln!("重试第 {} 次，延迟 {}ms，错误: {}", attempt, delay, e);
                }
                Err(e) => return Err(format!("操作失败，已重试 {} 次: {}", max_retries, e)),
            }
        }
    }
}

/// Rust 1.90 特性 5: 内存优化的缓冲区系统
/// 
/// 使用常量泛型优化内存使用模式
#[derive(Debug)]
pub struct OptimizedBuffer<const CAPACITY: usize> {
    data: [u8; CAPACITY],
    len: usize,
    created_at: std::time::Instant,
}

impl<const CAPACITY: usize> OptimizedBuffer<CAPACITY> {
    pub fn new() -> Self {
        Self {
            data: [0u8; CAPACITY],
            len: 0,
            created_at: std::time::Instant::now(),
        }
    }
    
    /// 使用常量推断创建指定大小的缓冲区
    pub fn with_capacity<const SIZE: usize>(_size: usize) -> OptimizedBuffer<SIZE> {
        OptimizedBuffer::new()
    }
    
    pub fn write(&mut self, data: &[u8]) -> Result<()> {
        if data.len() > CAPACITY - self.len {
            return Err(crate::error::Error::Other("缓冲区空间不足".to_string()));
        }
        
        self.data[self.len..self.len + data.len()].copy_from_slice(data);
        self.len += data.len();
        Ok(())
    }
    
    pub fn read(&self) -> &[u8] {
        &self.data[..self.len]
    }
    
    pub fn clear(&mut self) {
        self.len = 0;
    }
    
    pub fn is_full(&self) -> bool {
        self.len >= CAPACITY
    }
    
    pub fn remaining_capacity(&self) -> usize {
        CAPACITY - self.len
    }
    
    /// 获取缓冲区统计信息
    pub fn get_stats(&self) -> BufferStats {
        BufferStats {
            capacity: CAPACITY,
            used: self.len,
            remaining: self.remaining_capacity(),
            usage_percentage: (self.len as f64 / CAPACITY as f64) * 100.0,
            age: self.created_at.elapsed(),
        }
    }
}

/// 缓冲区统计信息
#[derive(Debug)]
pub struct BufferStats {
    pub capacity: usize,
    pub used: usize,
    pub remaining: usize,
    pub usage_percentage: f64,
    pub age: std::time::Duration,
}

/// Rust 1.90 特性 6: 性能监控和指标收集
/// 
/// 利用常量泛型优化监控数据结构
#[derive(Debug)]
pub struct PerformanceMonitor<const METRIC_COUNT: usize = 100> {
    metrics: [f64; METRIC_COUNT],
    current_index: usize,
    total_samples: usize,
}

impl<const METRIC_COUNT: usize> PerformanceMonitor<METRIC_COUNT> {
    pub fn new() -> Self {
        Self {
            metrics: [0.0; METRIC_COUNT],
            current_index: 0,
            total_samples: 0,
        }
    }
    
    /// 使用常量推断创建指定大小的监控器
    pub fn with_capacity<const CAPACITY: usize>(_capacity: usize) -> PerformanceMonitor<CAPACITY> {
        PerformanceMonitor::new()
    }
    
    pub fn record_metric(&mut self, value: f64) {
        self.metrics[self.current_index] = value;
        self.current_index = (self.current_index + 1) % METRIC_COUNT;
        self.total_samples += 1;
    }
    
    pub fn get_average(&self) -> f64 {
        if self.total_samples == 0 {
            return 0.0;
        }
        
        let sum: f64 = self.metrics.iter().sum();
        sum / METRIC_COUNT.min(self.total_samples) as f64
    }
    
    pub fn get_min(&self) -> f64 {
        if self.total_samples == 0 {
            return 0.0;
        }
        
        let count = METRIC_COUNT.min(self.total_samples);
        self.metrics[..count].iter().fold(f64::INFINITY, |a, &b| a.min(b))
    }
    
    pub fn get_max(&self) -> f64 {
        if self.total_samples == 0 {
            return 0.0;
        }
        
        let count = METRIC_COUNT.min(self.total_samples);
        self.metrics[..count].iter().fold(f64::NEG_INFINITY, |a, &b| a.max(b))
    }
    
    pub fn get_stats(&self) -> PerformanceStats {
        PerformanceStats {
            average: self.get_average(),
            min: self.get_min(),
            max: self.get_max(),
            total_samples: self.total_samples,
            capacity: METRIC_COUNT,
        }
    }
}

/// 性能统计信息
#[derive(Debug)]
pub struct PerformanceStats {
    pub average: f64,
    pub min: f64,
    pub max: f64,
    pub total_samples: usize,
    pub capacity: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_optimized_connection_pool() {
        let pool: OptimizedConnectionPool<20, 10000> = OptimizedConnectionPool::new();
        assert_eq!(pool.current_connections(), 0);
        assert!(!pool.is_full());
    }
    
    #[test]
    fn test_middleware_type() {
        let redis = MiddlewareType::Redis;
        let postgres = MiddlewareType::Postgres;
        
        assert!(redis.is_cache());
        assert!(!redis.is_database());
        assert!(postgres.is_database());
        assert!(!postgres.is_cache());
        assert!(!redis.is_same_category(&postgres));
        
        assert_eq!(redis.default_port(), 6379);
        assert_eq!(postgres.default_port(), 5432);
        assert_eq!(redis.protocol_prefix(), "redis://");
    }
    
    #[test]
    fn test_middleware_config() {
        let config: MiddlewareConfig<10, 5000> = MiddlewareConfig::new(
            MiddlewareType::Redis,
            "redis://localhost:6379".to_string()
        );
        
        assert!(config.validate().is_ok());
        assert_eq!(config.pool_size, 10);
        assert_eq!(config.timeout_ms, 5000);
    }
    
    #[test]
    fn test_optimized_buffer() {
        let mut buffer: OptimizedBuffer<1024> = OptimizedBuffer::new();
        
        let data = b"Hello, World!";
        assert!(buffer.write(data).is_ok());
        assert_eq!(buffer.read(), data);
        assert!(!buffer.is_full());
        assert_eq!(buffer.remaining_capacity(), 1024 - data.len());
        
        let stats = buffer.get_stats();
        assert_eq!(stats.capacity, 1024);
        assert_eq!(stats.used, data.len());
    }
    
    #[test]
    fn test_performance_monitor() {
        let mut monitor: PerformanceMonitor<10> = PerformanceMonitor::new();
        
        monitor.record_metric(1.0);
        monitor.record_metric(2.0);
        monitor.record_metric(3.0);
        
        let stats = monitor.get_stats();
        assert_eq!(stats.average, 2.0);
        assert_eq!(stats.min, 1.0);
        assert_eq!(stats.max, 3.0);
        assert_eq!(stats.total_samples, 3);
    }
    
    #[cfg(feature = "tokio")]
    #[tokio::test]
    async fn test_error_handler() {
        let operations = vec![
            Ok(b"success1".to_vec()),
            Ok(b"success2".to_vec()),
            Err("error1".to_string()),
        ];
        
        let result = OptimizedErrorHandler::batch_operations_with_flatten(operations).await;
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("操作失败"));
    }
    
    #[cfg(feature = "tokio")]
    #[tokio::test]
    async fn test_connection_handle() {
        let pool = OptimizedConnectionPool::<5, 1000>::new();
        let handle = pool.acquire().await.unwrap();
        
        let result = handle.execute_query("SELECT * FROM users").await.unwrap();
        assert!(result.contains("执行查询"));
        assert!(result.contains("SELECT * FROM users"));
    }
}
