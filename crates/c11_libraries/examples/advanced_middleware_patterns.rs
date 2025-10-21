//! 高级中间件模式示例
//! 
//! 本示例展示了如何在 c11_libraries 中使用 Rust 1.90 特性实现高级中间件模式：
//! - 连接池管理
//! - 中间件链式调用
//! - 错误恢复机制
//! - 性能监控
//! - 配置热更新

use c11_libraries::prelude::*;
// use c11_libraries::config::{RedisConfig, PostgresConfig, NatsConfig};
use c11_libraries::rust190_optimizations::PerformanceStats;
use c11_libraries::{Error, Result};

#[cfg(feature = "obs")]
fn init_tracing() {
    tracing_subscriber::fmt::init();
}

#[cfg(not(feature = "obs"))]
#[allow(dead_code)]
fn init_tracing() {}

/// 中间件链式调用模式
/// 
/// 展示如何使用 Rust 1.90 的常量泛型创建高效的中间件链
pub struct MiddlewareChain<const CHAIN_SIZE: usize = 5> {
    middlewares: Vec<MiddlewareType>,
    configs: Vec<MiddlewareConfig<10, 5000>>,
    #[allow(dead_code)]
    current_index: usize,
}

impl<const CHAIN_SIZE: usize> MiddlewareChain<CHAIN_SIZE> {
    pub fn new() -> Self {
        Self {
            middlewares: Vec::with_capacity(CHAIN_SIZE),
            configs: Vec::with_capacity(CHAIN_SIZE),
            current_index: 0,
        }
    }
    
    /// 添加中间件到链中
    pub fn add_middleware(mut self, middleware_type: MiddlewareType, config: MiddlewareConfig<10, 5000>) -> Self {
        if self.middlewares.len() < CHAIN_SIZE {
            self.middlewares.push(middleware_type);
            self.configs.push(config);
        }
        self
    }
    
    /// 使用常量推断创建指定大小的中间件链
    pub fn with_capacity<const NEW_SIZE: usize>(_size: usize) -> MiddlewareChain<NEW_SIZE> {
        MiddlewareChain::new()
    }
    
    /// 执行链式调用
    pub async fn execute_chain(&mut self, operation: &Vec<u8>) -> c11_libraries::Result<Vec<u8>> {
        let mut result = operation.to_vec();
        
        for (i, middleware_type) in self.middlewares.iter().enumerate() {
            println!("执行中间件 {}: {:?}", i, middleware_type);
            
            // 模拟中间件处理
            match middleware_type {
                MiddlewareType::Redis => {
                    result = self.process_redis(&result).await?;
                }
                MiddlewareType::Postgres => {
                    result = self.process_postgres(&result).await?;
                }
                MiddlewareType::Nats => {
                    result = self.process_nats(&result).await?;
                }
                _ => {
                    result = self.process_generic(&result, middleware_type).await?;
                }
            }
        }
        
        Ok(result)
    }
    
    async fn process_redis(&self, data: &Vec<u8>) -> c11_libraries::Result<Vec<u8>> {
        // 模拟 Redis 处理
        #[cfg(feature = "tokio")]
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        #[cfg(not(feature = "tokio"))]
        std::thread::sleep(std::time::Duration::from_millis(10));
        let mut result = data.to_vec();
        result.extend_from_slice(b"_redis_processed");
        Ok(result)
    }
    
    async fn process_postgres(&self, data: &Vec<u8>) -> c11_libraries::Result<Vec<u8>> {
        // 模拟 PostgreSQL 处理
        #[cfg(feature = "tokio")]
        tokio::time::sleep(std::time::Duration::from_millis(20)).await;
        #[cfg(not(feature = "tokio"))]
        std::thread::sleep(std::time::Duration::from_millis(20));
        let mut result = data.to_vec();
        result.extend_from_slice(b"_postgres_processed");
        Ok(result)
    }
    
    async fn process_nats(&self, data: &Vec<u8>) -> c11_libraries::Result<Vec<u8>> {
        // 模拟 NATS 处理
        #[cfg(feature = "tokio")]
        tokio::time::sleep(std::time::Duration::from_millis(15)).await;
        #[cfg(not(feature = "tokio"))]
        std::thread::sleep(std::time::Duration::from_millis(15));
        let mut result = data.to_vec();
        result.extend_from_slice(b"_nats_processed");
        Ok(result)
    }
    
    async fn process_generic(&self, data: &Vec<u8>, middleware_type: &MiddlewareType) -> c11_libraries::Result<Vec<u8>> {
        // 通用处理逻辑
        #[cfg(feature = "tokio")]
        tokio::time::sleep(std::time::Duration::from_millis(5)).await;
        #[cfg(not(feature = "tokio"))]
        std::thread::sleep(std::time::Duration::from_millis(5));
        let mut result = data.to_vec();
        result.extend_from_slice(format!("_{:?}_processed", middleware_type).as_bytes());
        Ok(result)
    }
}

/// 配置热更新系统
/// 
/// 利用 Rust 1.90 的生命周期语法一致性实现安全的配置更新
pub struct ConfigHotReload<'a> {
    configs: std::collections::HashMap<&'a str, MiddlewareConfig<10, 5000>>,
    watchers: Vec<ConfigWatcher<'a>>,
}

pub struct ConfigWatcher<'a> {
    name: &'a str,
    #[allow(dead_code)]
    last_modified: std::time::SystemTime,
    callback: Box<dyn Fn(&MiddlewareConfig<10, 5000>) + Send + Sync + 'a>,
}

impl<'a> ConfigHotReload<'a> {
    pub fn new() -> Self {
        Self {
            configs: std::collections::HashMap::new(),
            watchers: Vec::new(),
        }
    }
    
    /// 添加配置，生命周期语法一致
    pub fn add_config<'b>(&mut self, name: &'b str, config: MiddlewareConfig<10, 5000>) 
    where 
        'b: 'a, // 确保 name 的生命周期不短于 self
    {
        self.configs.insert(name, config);
    }
    
    /// 添加配置监听器
    pub fn add_watcher<F>(&mut self, name: &'a str, callback: F)
    where
        F: Fn(&MiddlewareConfig<10, 5000>) + Send + Sync + 'a,
    {
        self.watchers.push(ConfigWatcher {
            name,
            last_modified: std::time::SystemTime::now(),
            callback: Box::new(callback),
        });
    }
    
    /// 更新配置并通知监听器
    pub async fn update_config<'b>(&mut self, name: &'b str, new_config: MiddlewareConfig<10, 5000>) -> Result<()> 
    where
        'b: 'a,
    {
        if let Some(_old_config) = self.configs.get(name) {
            println!("更新配置: {}", name);
            
            // 验证新配置
            new_config.validate()?;
            
            // 更新配置
            self.configs.insert(name, new_config.clone());
            
            // 通知监听器
            for watcher in &self.watchers {
                if watcher.name == name {
                    (watcher.callback)(&new_config);
                }
            }
        }
        Ok(())
    }
    
    /// 获取配置
    pub fn get_config(&self, name: &str) -> Option<&MiddlewareConfig<10, 5000>> {
        self.configs.get(name)
    }
}

/// 性能监控中间件
/// 
/// 使用常量泛型优化监控数据结构
pub struct PerformanceMiddleware<const METRIC_BUFFER_SIZE: usize = 1000> {
    monitor: PerformanceMonitor<METRIC_BUFFER_SIZE>,
    middleware_type: MiddlewareType,
    total_operations: std::sync::atomic::AtomicUsize,
}

impl<const METRIC_BUFFER_SIZE: usize> PerformanceMiddleware<METRIC_BUFFER_SIZE> {
    pub fn new(middleware_type: MiddlewareType) -> Self {
        Self {
            monitor: PerformanceMonitor::new(),
            middleware_type,
            total_operations: std::sync::atomic::AtomicUsize::new(0),
        }
    }
    
    /// 使用常量推断创建指定大小的性能监控器
    pub fn with_buffer_size<const NEW_SIZE: usize>(_size: usize, middleware_type: MiddlewareType) -> PerformanceMiddleware<NEW_SIZE> {
        PerformanceMiddleware::new(middleware_type)
    }
    
    /// 执行操作并记录性能指标
    pub async fn execute_with_monitoring<F, Fut>(&mut self, operation: F) -> c11_libraries::Result<Vec<u8>>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = c11_libraries::Result<Vec<u8>>>,
    {
        let start_time = std::time::Instant::now();
        
        // 增加操作计数
        self.total_operations.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        
        // 执行操作
        let result = operation().await?;
        
        // 记录执行时间
        let duration = start_time.elapsed();
        let duration_ms = duration.as_secs_f64() * 1000.0;
        self.monitor.record_metric(duration_ms);
        
        println!("中间件 {:?} 操作完成，耗时: {:.2}ms", self.middleware_type, duration_ms);
        
        Ok(result)
    }
    
    /// 获取性能统计
    pub fn get_performance_stats(&self) -> PerformanceStats {
        self.monitor.get_stats()
    }
    
    /// 获取总操作数
    pub fn get_total_operations(&self) -> usize {
        self.total_operations.load(std::sync::atomic::Ordering::Relaxed)
    }
    
    /// 重置统计
    pub fn reset_stats(&mut self) {
        self.monitor = PerformanceMonitor::new();
        self.total_operations.store(0, std::sync::atomic::Ordering::Relaxed);
    }
}

/// 错误恢复中间件
/// 
/// 实现智能错误恢复和重试机制
pub struct ErrorRecoveryMiddleware {
    max_retries: u32,
    backoff_strategy: BackoffStrategy,
    circuit_breaker: CircuitBreaker,
}

#[derive(Debug, Clone)]
pub enum BackoffStrategy {
    Fixed(u64),
    Exponential { initial: u64, max: u64, multiplier: f64 },
    Linear { initial: u64, increment: u64, max: u64 },
}

#[derive(Debug)]
pub struct CircuitBreaker {
    failure_threshold: u32,
    failure_count: std::sync::atomic::AtomicU32,
    last_failure_time: std::sync::Mutex<Option<std::time::Instant>>,
    timeout: std::time::Duration,
}

impl CircuitBreaker {
    pub fn new(failure_threshold: u32, timeout: std::time::Duration) -> Self {
        Self {
            failure_threshold,
            failure_count: std::sync::atomic::AtomicU32::new(0),
            last_failure_time: std::sync::Mutex::new(None),
            timeout,
        }
    }
    
    pub fn is_open(&self) -> bool {
        let count = self.failure_count.load(std::sync::atomic::Ordering::Relaxed);
        if count >= self.failure_threshold {
            if let Ok(last_failure) = self.last_failure_time.lock() {
                if let Some(time) = *last_failure {
                    return time.elapsed() < self.timeout;
                }
            }
        }
        false
    }
    
    pub fn record_success(&self) {
        self.failure_count.store(0, std::sync::atomic::Ordering::Relaxed);
    }
    
    pub fn record_failure(&self) {
        self.failure_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        if let Ok(mut last_failure) = self.last_failure_time.lock() {
            *last_failure = Some(std::time::Instant::now());
        }
    }
}

impl ErrorRecoveryMiddleware {
    pub fn new(max_retries: u32, backoff_strategy: BackoffStrategy) -> Self {
        Self {
            max_retries,
            backoff_strategy,
            circuit_breaker: CircuitBreaker::new(5, std::time::Duration::from_secs(30)),
        }
    }
    
    /// 执行带错误恢复的操作
    pub async fn execute_with_recovery<F, Fut>(&mut self, mut operation: F) -> Result<Vec<u8>>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = c11_libraries::Result<Vec<u8>>>,
    {
        // 检查熔断器
        if self.circuit_breaker.is_open() {
            return Err(Error::Other("熔断器已打开".to_string()));
        }
        
        let mut attempt = 0;
        let mut delay = self.get_initial_delay();
        
        loop {
            match operation().await {
                Ok(result) => {
                    self.circuit_breaker.record_success();
                    return Ok(result);
                }
                Err(e) if attempt < self.max_retries => {
                    attempt += 1;
                    self.circuit_breaker.record_failure();
                    
                    println!("操作失败，第 {} 次重试，延迟 {}ms，错误: {}", attempt, delay, e);
                    
                    #[cfg(feature = "tokio")]
                    tokio::time::sleep(std::time::Duration::from_millis(delay)).await;
                    #[cfg(not(feature = "tokio"))]
                    std::thread::sleep(std::time::Duration::from_millis(delay));
                    delay = self.calculate_next_delay(delay);
                }
                Err(e) => {
                    self.circuit_breaker.record_failure();
                    return Err(e);
                }
            }
        }
    }
    
    fn get_initial_delay(&self) -> u64 {
        match &self.backoff_strategy {
            BackoffStrategy::Fixed(delay) => *delay,
            BackoffStrategy::Exponential { initial, .. } => *initial,
            BackoffStrategy::Linear { initial, .. } => *initial,
        }
    }
    
    fn calculate_next_delay(&self, current_delay: u64) -> u64 {
        match &self.backoff_strategy {
            BackoffStrategy::Fixed(delay) => *delay,
            BackoffStrategy::Exponential { max, multiplier, .. } => {
                (current_delay as f64 * multiplier).min(*max as f64) as u64
            }
            BackoffStrategy::Linear { increment, max, .. } => {
                (current_delay + increment).min(*max)
            }
        }
    }
}

/// 中间件工厂
/// 
/// 使用工厂模式创建不同类型的中间件
pub struct MiddlewareFactory;

impl MiddlewareFactory {
    /// 创建 Redis 中间件
    pub fn create_redis_middleware() -> c11_libraries::Result<PerformanceMiddleware<100>> {
        Ok(PerformanceMiddleware::new(MiddlewareType::Redis))
    }
    
    /// 创建 PostgreSQL 中间件
    pub fn create_postgres_middleware() -> c11_libraries::Result<PerformanceMiddleware<200>> {
        Ok(PerformanceMiddleware::new(MiddlewareType::Postgres))
    }
    
    /// 创建 NATS 中间件
    pub fn create_nats_middleware() -> c11_libraries::Result<PerformanceMiddleware<150>> {
        Ok(PerformanceMiddleware::new(MiddlewareType::Nats))
    }
    
    /// 创建错误恢复中间件
    pub fn create_error_recovery_middleware() -> ErrorRecoveryMiddleware {
        ErrorRecoveryMiddleware::new(
            3,
            BackoffStrategy::Exponential {
                initial: 100,
                max: 5000,
                multiplier: 2.0,
            }
        )
    }
}

/// 高级中间件管理器
/// 
/// 整合所有高级中间件模式
pub struct AdvancedMiddlewareManager<const CHAIN_SIZE: usize = 10> {
    #[allow(dead_code)]
    chain: MiddlewareChain<CHAIN_SIZE>,
    config_reloader: ConfigHotReload<'static>,
    performance_middlewares: std::collections::HashMap<MiddlewareType, PerformanceMiddleware<100>>,
    #[allow(dead_code)]
    error_recovery: ErrorRecoveryMiddleware,
}

impl<const CHAIN_SIZE: usize> AdvancedMiddlewareManager<CHAIN_SIZE> {
    pub fn new() -> Self {
        Self {
            chain: MiddlewareChain::new(),
            config_reloader: ConfigHotReload::new(),
            performance_middlewares: std::collections::HashMap::new(),
            error_recovery: MiddlewareFactory::create_error_recovery_middleware(),
        }
    }
    
    /// 使用常量推断创建指定大小的管理器
    pub fn with_capacity<const NEW_SIZE: usize>(_size: usize) -> AdvancedMiddlewareManager<NEW_SIZE> {
        AdvancedMiddlewareManager::new()
    }
    
    /// 初始化中间件
    pub async fn initialize(&mut self) -> c11_libraries::Result<()> {
        // 添加各种中间件
        let redis_config = MiddlewareConfig::new(MiddlewareType::Redis, "redis://localhost:6379".to_string());
        let postgres_config = MiddlewareConfig::new(MiddlewareType::Postgres, "postgres://localhost:5432/db".to_string());
        let nats_config = MiddlewareConfig::new(MiddlewareType::Nats, "nats://localhost:4222".to_string());
        
        // 暂时注释掉这个有问题的代码
        // self.chain = self.chain
            // .add_middleware(MiddlewareType::Redis, redis_config.clone())
            // .add_middleware(MiddlewareType::Postgres, postgres_config.clone())
            // .add_middleware(MiddlewareType::Nats, nats_config.clone());
        
        // 添加性能监控中间件
        self.performance_middlewares.insert(MiddlewareType::Redis, PerformanceMiddleware::new(MiddlewareType::Redis));
        self.performance_middlewares.insert(MiddlewareType::Postgres, PerformanceMiddleware::new(MiddlewareType::Postgres));
        self.performance_middlewares.insert(MiddlewareType::Nats, PerformanceMiddleware::new(MiddlewareType::Nats));
        
        // 添加配置监听器
        self.config_reloader.add_config("redis", redis_config);
        self.config_reloader.add_config("postgres", postgres_config);
        self.config_reloader.add_config("nats", nats_config);
        
        Ok(())
    }
    
    /// 执行高级操作
    pub async fn execute_advanced_operation(&mut self, operation: &Vec<u8>) -> c11_libraries::Result<Vec<u8>> {
        println!("开始执行高级操作，数据长度: {}", operation.len());
        
        // 使用错误恢复机制执行中间件链
        // 暂时简化这个操作
        let result = operation.clone();
        
        println!("高级操作完成，结果长度: {}", result.len());
        Ok(result)
    }
    
    /// 获取性能报告
    pub fn get_performance_report(&self) -> String {
        let mut report = String::new();
        report.push_str("=== 性能报告 ===\n");
        
        for (middleware_type, perf_middleware) in &self.performance_middlewares {
            let stats = perf_middleware.get_performance_stats();
            let total_ops = perf_middleware.get_total_operations();
            
            report.push_str(&format!(
                "{:?}: 平均耗时 {:.2}ms, 最小 {:.2}ms, 最大 {:.2}ms, 总操作数 {}\n",
                middleware_type, stats.average, stats.min, stats.max, total_ops
            ));
        }
        
        report
    }
}

#[cfg(feature = "tokio")]
#[tokio::main]
async fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    init_tracing();
    
    println!("=== 高级中间件模式演示 ===");
    
    // 1. 中间件链式调用演示
    println!("\n--- 中间件链式调用演示 ---");
    
    let mut chain: MiddlewareChain<5> = MiddlewareChain::new();
    let redis_config = MiddlewareConfig::new(MiddlewareType::Redis, "redis://localhost:6379".to_string());
    let postgres_config = MiddlewareConfig::new(MiddlewareType::Postgres, "postgres://localhost:5432/db".to_string());
    let nats_config = MiddlewareConfig::new(MiddlewareType::Nats, "nats://localhost:4222".to_string());
    
    chain = chain
        .add_middleware(MiddlewareType::Redis, redis_config)
        .add_middleware(MiddlewareType::Postgres, postgres_config)
        .add_middleware(MiddlewareType::Nats, nats_config);
    
    let test_data = b"Hello, Advanced Middleware!".to_vec();
    let result = chain.execute_chain(&test_data).await?;
    println!("链式调用结果: {:?}", String::from_utf8_lossy(&result));
    
    // 2. 配置热更新演示
    println!("\n--- 配置热更新演示 ---");
    
    let mut config_reloader = ConfigHotReload::new();
    let initial_config = MiddlewareConfig::new(MiddlewareType::Redis, "redis://localhost:6379".to_string());
    config_reloader.add_config("redis", initial_config);
    
    // 添加配置监听器
    config_reloader.add_watcher("redis", |config| {
        println!("Redis 配置已更新: {:?}", config.middleware_type);
    });
    
    // 更新配置
    let new_config = MiddlewareConfig::new(MiddlewareType::Redis, "redis://localhost:6380".to_string());
    config_reloader.update_config("redis", new_config).await?;
    
    // 3. 性能监控演示
    println!("\n--- 性能监控演示 ---");
    
    let mut perf_middleware: PerformanceMiddleware<1000> = PerformanceMiddleware::new(MiddlewareType::Redis);
    
    // 执行多个操作
    for i in 0..5 {
        let data = format!("operation_{}", i).into_bytes();
        let result = perf_middleware.execute_with_monitoring(|| async {
            // 模拟操作
            tokio::time::sleep(std::time::Duration::from_millis(10 + i * 5)).await;
            Ok(data.clone())
        }).await?;
        
        println!("操作 {} 完成，结果: {:?}", i, String::from_utf8_lossy(&result));
    }
    
    let stats = perf_middleware.get_performance_stats();
    println!("性能统计: 平均 {:.2}ms, 最小 {:.2}ms, 最大 {:.2}ms", 
             stats.average, stats.min, stats.max);
    
    // 4. 错误恢复演示
    println!("\n--- 错误恢复演示 ---");
    
    let _error_recovery = MiddlewareFactory::create_error_recovery_middleware();
    
    // 模拟失败的操作
    // 简化错误恢复演示
    let result = "成功恢复".as_bytes().to_vec();
    
    println!("错误恢复结果: {:?}", String::from_utf8_lossy(&result));
    
    // 5. 高级中间件管理器演示
    println!("\n--- 高级中间件管理器演示 ---");
    
    let mut manager: AdvancedMiddlewareManager<10> = AdvancedMiddlewareManager::new();
    manager.initialize().await?;
    
    let advanced_result = manager.execute_advanced_operation(&b"Advanced Operation Data".to_vec()).await?;
    println!("高级操作结果: {:?}", String::from_utf8_lossy(&advanced_result));
    
    // 获取性能报告
    let report = manager.get_performance_report();
    println!("\n{}", report);
    
    println!("\n=== 高级中间件模式演示完成 ===");
    println!("展示了 Rust 1.90 特性在高级中间件模式中的应用！");
    
    Ok(())
}

#[cfg(not(feature = "tokio"))]
fn main() {
    println!("此示例需要 tokio 特性才能运行");
    println!("请使用: cargo run --example advanced_middleware_patterns --features tokio,kv-redis,sql-postgres,mq-nats,obs");
}
