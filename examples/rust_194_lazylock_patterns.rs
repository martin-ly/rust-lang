//! Rust 1.94 `LazyLock` 和 `LazyCell` 深度示例
//!
//! 本文件演示 Rust 1.94 新增的延迟初始化 API 在生产场景中的应用。

use std::cell::LazyCell;
use std::sync::LazyLock;
use std::time::Instant;

// ==================== 全局配置示例 ====================

/// 全局应用配置（延迟初始化）
static APP_CONFIG: LazyLock<AppConfig> = LazyLock::new(|| {
    println!("[INIT] 加载应用配置...");
    AppConfig::from_env()
});

pub struct AppConfig {
    pub db_url: String,
    pub max_connections: u32,
    pub log_level: String,
}

impl AppConfig {
    fn from_env() -> Self {
        Self {
            db_url: std::env::var("DATABASE_URL")
                .unwrap_or_else(|_| "postgres://localhost".to_string()),
            max_connections: std::env::var("MAX_CONNECTIONS")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(100),
            log_level: std::env::var("LOG_LEVEL")
                .unwrap_or_else(|_| "info".to_string()),
        }
    }
}

/// ✅ Rust 1.94: 使用 get() 进行热路径优化
/// 
/// 如果配置已初始化，直接返回；不会触发初始化
pub fn get_config_fast() -> Option<&'static AppConfig> {
    APP_CONFIG.get()
}

/// 标准访问方式（可能触发初始化）
pub fn get_config() -> &'static AppConfig {
    &APP_CONFIG
}

// ==================== 连接池示例 ====================

static CONNECTION_POOL: LazyLock<ConnectionPool> = LazyLock::new(|| {
    println!("[INIT] 创建连接池...");
    ConnectionPool::new(10)
});

pub struct ConnectionPool {
    connections: Vec<Connection>,
}

pub struct Connection {
    id: u64,
}

impl ConnectionPool {
    fn new(size: usize) -> Self {
        Self {
            connections: (0..size as u64)
                .map(|id| Connection { id })
                .collect(),
        }
    }
    
    pub fn get_connection(&self) -> Option<&Connection> {
        self.connections.first()
    }
    
    pub fn stats(&self) -> String {
        format!("连接池大小: {}", self.connections.len())
    }
}

/// 性能关键路径：使用 Rust 1.94 get() 优化
pub fn execute_query_optimized(query: &str) -> Result<String, String> {
    // 热路径：检查是否已初始化（无锁）
    if let Some(pool) = LazyLock::get(&CONNECTION_POOL) {
        println!("[FAST] 使用现有连接池");
        let conn = pool.get_connection()
            .ok_or("无可用连接")?;
        return Ok(format!("执行 '{}' 于连接 {:?}", query, conn.id));
    }
    
    // 冷路径：触发初始化
    println!("[SLOW] 初始化连接池");
    let pool = &*CONNECTION_POOL;
    let conn = pool.get_connection()
        .ok_or("无可用连接")?;
    Ok(format!("执行 '{}' 于连接 {:?}", query, conn.id))
}

// ==================== 单线程缓存示例 ====================

/// 单线程延迟初始化缓存
pub struct LocalCache {
    data: LazyCell<Vec<u8>>,
    access_count: usize,
}

impl LocalCache {
    pub fn new() -> Self {
        Self {
            data: LazyCell::new(|| {
                println!("[INIT] 加载 1MB 缓存数据");
                vec![0u8; 1024 * 1024]
            }),
            access_count: 0,
        }
    }
    
    /// ✅ Rust 1.94: get() - 安全读取，不触发初始化
    pub fn peek(&self) -> Option<&[u8]> {
        self.data.get().map(|v| v.as_slice())
    }
    
    /// 读取或触发初始化
    pub fn get(&self) -> &[u8] {
        &*self.data
    }
    
    /// ✅ Rust 1.94: force_mut() - 强制初始化并获取可变引用
    pub fn update(&mut self, new_data: Vec<u8>) {
        println!("[UPDATE] 替换缓存数据");
        let cache = self.data.force_mut();
        *cache = new_data;
    }
    
    pub fn record_access(&mut self) {
        self.access_count += 1;
    }
    
    pub fn is_initialized(&self) -> bool {
        self.data.get().is_some()
    }
}

// ==================== 多阶段配置示例 ====================

/// 阶段 1: 编译期配置
static COMPILE_CONFIG: LazyLock<ConfigMap> = LazyLock::new(|| {
    let mut map = ConfigMap::new();
    map.insert("app.name", "MyApplication");
    map.insert("app.version", "1.0.0");
    map
});

/// 阶段 2: 运行时配置
static RUNTIME_CONFIG: LazyLock<ConfigMap> = LazyLock::new(|| {
    let mut map = ConfigMap::new();
    
    // 从环境变量加载
    if let Ok(val) = std::env::var("API_KEY") {
        map.insert("api.key", &val);
    }
    if let Ok(val) = std::env::var("ENDPOINT") {
        map.insert("api.endpoint", &val);
    }
    
    map
});

pub struct ConfigMap {
    data: std::collections::HashMap<String, String>,
}

impl ConfigMap {
    fn new() -> Self {
        Self {
            data: std::collections::HashMap::new(),
        }
    }
    
    fn insert(&mut self, key: &str, value: &str) {
        self.data.insert(key.to_string(), value.to_string());
    }
    
    fn get(&self, key: &str) -> Option<&str> {
        self.data.get(key).map(|s| s.as_str())
    }
}

/// 高效配置查找（优先运行时，回退编译期）
pub fn lookup_config(key: &str) -> Option<&'static str> {
    // 先检查运行时配置（热路径）
    if let Some(cfg) = LazyLock::get(&RUNTIME_CONFIG)
        .and_then(|m| m.get(key)) {
        return Some(cfg);
    }
    
    // 回退到编译期配置
    LazyLock::get(&COMPILE_CONFIG)
        .and_then(|m| m.get(key))
}

// ==================== 性能基准测试 ====================

pub fn benchmark_lazy_access() {
    println!("\n=== LazyLock 性能基准测试 ===");
    
    // 预热：确保已初始化
    let _ = &*CONNECTION_POOL;
    
    // 测试 1: 标准访问 vs get() 访问
    let iterations = 1_000_000;
    
    let start = Instant::now();
    for _ in 0..iterations {
        let _ = &*CONNECTION_POOL;
    }
    let standard_duration = start.elapsed();
    
    let start = Instant::now();
    for _ in 0..iterations {
        let _ = LazyLock::get(&CONNECTION_POOL);
    }
    let get_duration = start.elapsed();
    
    println!("标准访问 ({} 次): {:?}", iterations, standard_duration);
    println!("get() 访问 ({} 次): {:?}", iterations, get_duration);
    
    if get_duration < standard_duration {
        let improvement = (standard_duration.as_nanos() as f64 
            / get_duration.as_nanos() as f64 - 1.0) * 100.0;
        println!("get() 提升: {:.1}%", improvement);
    }
}

// ==================== 主函数 ====================

fn main() {
    println!("=== Rust 1.94 LazyLock/LazyCell 深度示例 ===\n");
    
    // 1. 配置访问示例
    println!("--- 配置访问 ---");
    println!("配置是否已初始化: {}", get_config_fast().is_some());
    let config = get_config();
    println!("DB URL: {}", config.db_url);
    println!("配置已初始化: {}\n", get_config_fast().is_some());
    
    // 2. 连接池优化访问
    println!("--- 连接池访问 ---");
    let result = execute_query_optimized("SELECT * FROM users");
    println!("结果: {:?}\n", result);
    
    // 第二次访问（热路径）
    let result = execute_query_optimized("SELECT * FROM orders");
    println!("结果: {:?}\n", result);
    
    // 3. 本地缓存示例
    println!("--- 本地缓存 ---");
    let mut cache = LocalCache::new();
    println!("缓存是否已初始化: {}", cache.is_initialized());
    println!("尝试 peek (不触发初始化): {:?}", cache.peek());
    
    let _data = cache.get();  // 触发初始化
    println!("缓存是否已初始化: {}", cache.is_initialized());
    
    cache.update(vec![1, 2, 3, 4, 5]);
    println!("更新后数据: {:?}\n", cache.get());
    
    // 4. 配置查找
    println!("--- 配置查找 ---");
    println!("app.name: {:?}", lookup_config("app.name"));
    println!("api.key: {:?}", lookup_config("api.key"));
    
    // 5. 性能基准测试
    benchmark_lazy_access();
    
    println!("\n所有示例完成！");
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_lazy_config() {
        // 第一次访问触发初始化
        assert!(get_config_fast().is_none());
        let _ = get_config();
        assert!(get_config_fast().is_some());
    }
    
    #[test]
    fn test_local_cache() {
        let mut cache = LocalCache::new();
        
        // 未初始化
        assert!(cache.peek().is_none());
        
        // 读取触发初始化
        let _ = cache.get();
        assert!(cache.peek().is_some());
        
        // 更新
        cache.update(vec![1, 2, 3]);
        assert_eq!(cache.get(), &[1, 2, 3]);
    }
    
    #[test]
    fn test_config_lookup() {
        // 编译期配置总是可用
        assert!(lookup_config("app.name").is_some());
        assert_eq!(lookup_config("app.name"), Some("MyApplication"));
    }
}
