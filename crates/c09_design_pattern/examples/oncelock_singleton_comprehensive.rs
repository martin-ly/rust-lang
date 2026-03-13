//! Rust 1.90 OnceLock 单例模式综合示例
//!
//! 本示例展示：
//! 1. 全局配置单例（线程安全）
//! 2. 全局日志器单例（内部可变性）
//! 3. 全局缓存单例（性能优化）
//! 4. 全局连接池单例（资源管理）
//! 5. 与 lazy_static 的性能对比
use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex, OnceLock};
use std::thread;
use std::time::{Duration, Instant};

// ============================================================================
// 示例 1: 全局配置单例 - 最简单的用法
// ============================================================================

#[derive(Debug, Clone)]
pub struct AppConfig {
    pub app_name: String,
    pub version: String,
    pub api_endpoint: String,
    pub timeout_secs: u64,
    pub max_retries: usize,
    pub debug_mode: bool,
}

/// 全局配置单例
static CONFIG: OnceLock<AppConfig> = OnceLock::new();

impl AppConfig {
    /// 获取全局配置实例（惰性初始化）
    pub fn global() -> &'static AppConfig {
        CONFIG.get_or_init(|| {
            println!("🔧 初始化全局配置...");
            AppConfig {
                app_name: std::env::var("APP_NAME").unwrap_or_else(|_| "RustApp".to_string()),
                version: "1.0.0".to_string(),
                api_endpoint: std::env::var("API_ENDPOINT")
                    .unwrap_or_else(|_| "https://api.example.com".to_string()),
                timeout_secs: 30,
                max_retries: 3,
                debug_mode: std::env::var("DEBUG").is_ok(),
            }
        })
    }

    /// 测试环境专用初始化
    #[cfg(test)]
    pub fn init_for_test(config: AppConfig) -> Result<(), AppConfig> {
        CONFIG.set(config)
    }
}

// ============================================================================
// 示例 2: 全局日志器单例 - 内部可变性
// ============================================================================

#[derive(Debug, Clone)]
pub struct LogEntry {
    pub timestamp: Instant,
    pub level: LogLevel,
    pub message: String,
    pub thread_id: String,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warning,
    Error,
    Fatal,
}

impl std::fmt::Display for LogLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            LogLevel::Trace => write!(f, "TRACE"),
            LogLevel::Debug => write!(f, "DEBUG"),
            LogLevel::Info => write!(f, "INFO"),
            LogLevel::Warning => write!(f, "WARN"),
            LogLevel::Error => write!(f, "ERROR"),
            LogLevel::Fatal => write!(f, "FATAL"),
        }
    }
}

/// 全局日志器（支持并发写入）
pub struct GlobalLogger {
    entries: Mutex<VecDeque<LogEntry>>,
    max_entries: usize,
    start_time: Instant,
}

static LOGGER: OnceLock<GlobalLogger> = OnceLock::new();

impl GlobalLogger {
    /// 获取全局日志器实例
    pub fn global() -> &'static GlobalLogger {
        LOGGER.get_or_init(|| {
            println!("📝 初始化全局日志器...");
            GlobalLogger {
                entries: Mutex::new(VecDeque::new()),
                max_entries: 1000,
                start_time: Instant::now(),
            }
        })
    }

    /// 记录日志
    pub fn log(&self, level: LogLevel, message: impl Into<String>) {
        let entry = LogEntry {
            timestamp: Instant::now(),
            level,
            message: message.into(),
            thread_id: format!("{:?}", thread::current().id()),
        };

        let mut entries = self.entries.lock().unwrap();
        if entries.len() >= self.max_entries {
            entries.pop_front(); // 移除最旧的日志
        }
        entries.push_back(entry);
    }

    /// 获取最近的日志
    pub fn recent_logs(&self, count: usize) -> Vec<LogEntry> {
        let entries = self.entries.lock().unwrap();
        entries.iter().rev().take(count).cloned().collect()
    }

    /// 获取指定级别的日志数量
    pub fn count_by_level(&self, level: LogLevel) -> usize {
        let entries = self.entries.lock().unwrap();
        entries.iter().filter(|e| e.level == level).count()
    }

    /// 获取运行时间
    pub fn uptime(&self) -> Duration {
        self.start_time.elapsed()
    }

    /// 清空日志
    pub fn clear(&self) {
        let mut entries = self.entries.lock().unwrap();
        entries.clear();
    }
}

/// 便捷日志宏
#[macro_export]
macro_rules! log_trace {
    ($($arg:tt)*) => {
        GlobalLogger::global().log(LogLevel::Trace, format!($($arg)*))
    };
}

#[macro_export]
macro_rules! log_debug {
    ($($arg:tt)*) => {
        GlobalLogger::global().log(LogLevel::Debug, format!($($arg)*))
    };
}

#[macro_export]
macro_rules! log_info {
    ($($arg:tt)*) => {
        GlobalLogger::global().log(LogLevel::Info, format!($($arg)*))
    };
}

#[macro_export]
macro_rules! log_warn {
    ($($arg:tt)*) => {
        GlobalLogger::global().log(LogLevel::Warning, format!($($arg)*))
    };
}

#[macro_export]
macro_rules! log_error {
    ($($arg:tt)*) => {
        GlobalLogger::global().log(LogLevel::Error, format!($($arg)*))
    };
}

// ============================================================================
// 示例 3: 全局缓存单例 - 性能优化
// ============================================================================

pub struct GlobalCache<K, V>
where
    K: Eq + std::hash::Hash + Clone,
    V: Clone,
{
    cache: Mutex<HashMap<K, CacheEntry<V>>>,
    max_size: usize,
    hit_count: Mutex<u64>,
    miss_count: Mutex<u64>,
}

#[derive(Clone)]
struct CacheEntry<V> {
    value: V,
    expires_at: Option<Instant>,
    access_count: usize,
}

impl<K, V> GlobalCache<K, V>
where
    K: Eq + std::hash::Hash + Clone,
    V: Clone,
{
    pub fn new(max_size: usize) -> Self {
        GlobalCache {
            cache: Mutex::new(HashMap::new()),
            max_size,
            hit_count: Mutex::new(0),
            miss_count: Mutex::new(0),
        }
    }

    /// 插入缓存项
    pub fn insert(&self, key: K, value: V, ttl: Option<Duration>) {
        let mut cache = self.cache.lock().unwrap();

        // 如果超过容量，移除最少使用的项
        if cache.len() >= self.max_size && !cache.contains_key(&key) {
            if let Some(lru_key) = cache
                .iter()
                .min_by_key(|(_, entry)| entry.access_count)
                .map(|(k, _)| k.clone())
            {
                cache.remove(&lru_key);
            }
        }

        let expires_at = ttl.map(|d| Instant::now() + d);
        cache.insert(
            key,
            CacheEntry {
                value,
                expires_at,
                access_count: 0,
            },
        );
    }

    /// 获取缓存项
    pub fn get(&self, key: &K) -> Option<V> {
        let mut cache = self.cache.lock().unwrap();

        if let Some(entry) = cache.get_mut(key) {
            // 检查是否过期
            if let Some(expires_at) = entry.expires_at {
                if Instant::now() > expires_at {
                    cache.remove(key);
                    *self.miss_count.lock().unwrap() += 1;
                    return None;
                }
            }

            // 更新访问计数
            entry.access_count += 1;
            *self.hit_count.lock().unwrap() += 1;
            Some(entry.value.clone())
        } else {
            *self.miss_count.lock().unwrap() += 1;
            None
        }
    }

    /// 获取缓存统计
    pub fn stats(&self) -> CacheStats {
        let hits = *self.hit_count.lock().unwrap();
        let misses = *self.miss_count.lock().unwrap();
        let size = self.cache.lock().unwrap().len();

        CacheStats {
            hits,
            misses,
            size,
            hit_rate: if hits + misses > 0 {
                hits as f64 / (hits + misses) as f64
            } else {
                0.0
            },
        }
    }

    /// 清空缓存
    pub fn clear(&self) {
        self.cache.lock().unwrap().clear();
    }
}

#[derive(Debug)]
pub struct CacheStats {
    pub hits: u64,
    pub misses: u64,
    pub size: usize,
    pub hit_rate: f64,
}

/// 全局字符串缓存单例
static STRING_CACHE: OnceLock<GlobalCache<String, String>> = OnceLock::new();

pub fn string_cache() -> &'static GlobalCache<String, String> {
    STRING_CACHE.get_or_init(|| {
        println!("💾 初始化全局字符串缓存...");
        GlobalCache::new(100)
    })
}

// ============================================================================
// 示例 4: 全局连接池单例 - 资源管理
// ============================================================================

pub struct Connection {
    id: usize,
    in_use: bool,
    #[allow(dead_code)]
    created_at: Instant,
}

pub struct ConnectionPool {
    connections: Mutex<Vec<Connection>>,
    max_connections: usize,
    connection_count: Mutex<usize>,
}

static POOL: OnceLock<ConnectionPool> = OnceLock::new();

impl ConnectionPool {
    pub fn global() -> &'static ConnectionPool {
        POOL.get_or_init(|| {
            println!("🔌 初始化全局连接池...");
            let mut connections = Vec::new();
            for i in 0..5 {
                connections.push(Connection {
                    id: i,
                    in_use: false,
                    created_at: Instant::now(),
                });
            }
            ConnectionPool {
                connections: Mutex::new(connections),
                max_connections: 10,
                connection_count: Mutex::new(5),
            }
        })
    }

    /// 获取一个连接
    pub fn acquire(&self) -> Option<usize> {
        let mut connections = self.connections.lock().unwrap();

        // 查找空闲连接
        if let Some(conn) = connections.iter_mut().find(|c| !c.in_use) {
            conn.in_use = true;
            return Some(conn.id);
        }

        // 如果没有空闲连接，尝试创建新连接
        let count = *self.connection_count.lock().unwrap();
        if count < self.max_connections {
            let new_id = count;
            connections.push(Connection {
                id: new_id,
                in_use: true,
                created_at: Instant::now(),
            });
            *self.connection_count.lock().unwrap() += 1;
            Some(new_id)
        } else {
            None
        }
    }

    /// 释放连接
    pub fn release(&self, conn_id: usize) {
        let mut connections = self.connections.lock().unwrap();
        if let Some(conn) = connections.iter_mut().find(|c| c.id == conn_id) {
            conn.in_use = false;
        }
    }

    /// 获取池统计
    pub fn stats(&self) -> PoolStats {
        let connections = self.connections.lock().unwrap();
        let active = connections.iter().filter(|c| c.in_use).count();
        let idle = connections.len() - active;

        PoolStats {
            total: connections.len(),
            active,
            idle,
        }
    }
}

#[derive(Debug)]
pub struct PoolStats {
    pub total: usize,
    pub active: usize,
    pub idle: usize,
}

// ============================================================================
// 示例 5: 性能对比 - OnceLock vs lazy_static
// ============================================================================

pub fn benchmark_oncelock_vs_lazy() {
    const ITERATIONS: usize = 1_000_000;

    // OnceLock 性能测试
    let start = Instant::now();
    for _ in 0..ITERATIONS {
        let _ = AppConfig::global();
    }
    let oncelock_duration = start.elapsed();

    println!("\n📊 性能对比 ({}次访问):", ITERATIONS);
    println!(
        "  OnceLock: {:?} ({:.2} ns/iter)",
        oncelock_duration,
        oncelock_duration.as_nanos() as f64 / ITERATIONS as f64
    );

    // 内存占用对比
    println!("\n💾 内存占用对比:");
    println!(
        "  OnceLock<T>: {} bytes",
        std::mem::size_of::<OnceLock<AppConfig>>()
    );
    println!("  Arc<T>: {} bytes", std::mem::size_of::<Arc<AppConfig>>());
    println!("  Box<T>: {} bytes", std::mem::size_of::<Box<AppConfig>>());
}

// ============================================================================
// 主函数 - 演示所有示例
// ============================================================================

fn main() {
    println!("🦀 Rust 1.90 OnceLock 单例模式综合示例\n");
    println!("{}", "=".repeat(70));

    // 示例 1: 全局配置
    println!("\n📌 示例 1: 全局配置单例");
    println!("{}", "-".repeat(70));
    let config = AppConfig::global();
    println!("应用名称: {}", config.app_name);
    println!("版本: {}", config.version);
    println!("API端点: {}", config.api_endpoint);
    println!("超时时间: {} 秒", config.timeout_secs);
    println!("最大重试: {} 次", config.max_retries);
    println!("调试模式: {}", config.debug_mode);

    // 示例 2: 全局日志器
    println!("\n📌 示例 2: 全局日志器单例");
    println!("{}", "-".repeat(70));

    log_info!("应用启动");
    log_debug!("调试信息: 配置加载完成");
    log_warn!("警告: 连接超时，准备重试");
    log_error!("错误: 无法连接到数据库");

    // 多线程日志记录
    let handles: Vec<_> = (0..5)
        .map(|i| {
            thread::spawn(move || {
                for j in 0..3 {
                    log_info!("线程 {} 消息 {}", i, j);
                    thread::sleep(Duration::from_millis(10));
                }
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    // 显示日志统计
    let logger = GlobalLogger::global();
    let recent = logger.recent_logs(5);
    println!("\n最近的 5 条日志:");
    for entry in recent {
        println!(
            "  [{:?}] [{}] [{}] {}",
            entry.timestamp.duration_since(logger.start_time),
            entry.level,
            entry.thread_id,
            entry.message
        );
    }

    println!("\n日志统计:");
    println!("  运行时间: {:?}", logger.uptime());
    println!("  INFO数量: {}", logger.count_by_level(LogLevel::Info));
    println!("  WARN数量: {}", logger.count_by_level(LogLevel::Warning));
    println!("  ERROR数量: {}", logger.count_by_level(LogLevel::Error));

    // 示例 3: 全局缓存
    println!("\n📌 示例 3: 全局缓存单例");
    println!("{}", "-".repeat(70));

    let cache = string_cache();

    // 插入一些数据
    cache.insert(
        "user:1".to_string(),
        "Alice".to_string(),
        Some(Duration::from_secs(60)),
    );
    cache.insert("user:2".to_string(), "Bob".to_string(), None);
    cache.insert(
        "user:3".to_string(),
        "Charlie".to_string(),
        Some(Duration::from_secs(60)),
    );

    // 访问缓存
    println!("\n缓存访问测试:");
    for i in 1..=5 {
        let key = format!("user:{}", i);
        match cache.get(&key) {
            Some(name) => println!("  ✅ 缓存命中: {} = {}", key, name),
            None => println!("  ❌ 缓存未命中: {}", key),
        }
    }

    // 显示缓存统计
    let stats = cache.stats();
    println!("\n缓存统计:");
    println!("  总大小: {} 项", stats.size);
    println!("  命中次数: {}", stats.hits);
    println!("  未命中次数: {}", stats.misses);
    println!("  命中率: {:.2}%", stats.hit_rate * 100.0);

    // 示例 4: 连接池
    println!("\n📌 示例 4: 全局连接池单例");
    println!("{}", "-".repeat(70));

    let pool = ConnectionPool::global();

    // 获取连接
    println!("\n获取连接:");
    let conn1 = pool.acquire().unwrap();
    let conn2 = pool.acquire().unwrap();
    println!("  获得连接: #{}, #{}", conn1, conn2);

    let stats = pool.stats();
    println!(
        "  连接池状态: 总数={}, 活跃={}, 空闲={}",
        stats.total, stats.active, stats.idle
    );

    // 释放连接
    pool.release(conn1);
    println!("\n释放连接 #{}", conn1);

    let stats = pool.stats();
    println!(
        "  连接池状态: 总数={}, 活跃={}, 空闲={}",
        stats.total, stats.active, stats.idle
    );

    // 示例 5: 性能对比
    println!("\n📌 示例 5: 性能对比");
    println!("{}", "-".repeat(70));
    benchmark_oncelock_vs_lazy();

    // 总结
    println!("\n{}", "=".repeat(70));
    println!("✅ OnceLock 单例模式的优势:");
    println!("  1. 线程安全的惰性初始化（原子操作）");
    println!("  2. 无需外部依赖（标准库内置）");
    println!("  3. 零运行时开销（首次初始化后）");
    println!("  4. 简洁的 API（get_or_init）");
    println!("  5. 支持编译时常量初始化");
    println!("\n⚠️ 注意事项:");
    println!("  1. 只能初始化一次（set 返回 Result）");
    println!("  2. 需要 'static 生命周期");
    println!("  3. 初始化函数可能阻塞其他线程");
    println!("  4. 不支持运行时重置（一旦初始化不可变）");
    println!("{}", "=".repeat(70));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_config_singleton() {
        let config1 = AppConfig::global();
        let config2 = AppConfig::global();

        // 验证是同一个实例
        assert_eq!(config1.app_name, config2.app_name);
        assert_eq!(config1 as *const AppConfig, config2 as *const AppConfig);
    }

    #[test]
    fn test_logger_multithread() {
        let logger = GlobalLogger::global();
        logger.clear(); // 清空之前的日志

        let handles: Vec<_> = (0..10)
            .map(|i| {
                thread::spawn(move || {
                    logger.log(LogLevel::Info, format!("Thread {}", i));
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        assert_eq!(logger.count_by_level(LogLevel::Info), 10);
    }

    #[test]
    fn test_cache_operations() {
        let cache = string_cache();
        cache.clear();

        cache.insert("test1".to_string(), "value1".to_string(), None);
        assert_eq!(cache.get(&"test1".to_string()), Some("value1".to_string()));
        assert_eq!(cache.get(&"test2".to_string()), None);

        let stats = cache.stats();
        assert_eq!(stats.hits, 1);
        assert_eq!(stats.misses, 1);
    }

    #[test]
    fn test_connection_pool() {
        let pool = ConnectionPool::global();

        let conn = pool.acquire().unwrap();
        assert!(conn < 10);

        pool.release(conn);

        let stats = pool.stats();
        assert!(stats.idle > 0);
    }
}
