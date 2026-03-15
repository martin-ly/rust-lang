//! Rust 1.94 LazyCell/LazyLock 新方法完整示例
//! 
//! 运行方式: rustc --edition 2024 examples/rust_194_lazy_lock_demo.rs && ./rust_194_lazy_lock_demo

#![allow(dead_code)]

use std::cell::LazyCell;
use std::sync::{LazyLock, Mutex};
use std::time::{Duration, Instant};
use std::thread;

// =============================================================================
// 全局配置示例
// =============================================================================

/// 应用配置
#[derive(Debug)]
struct AppConfig {
    database_url: String,
    api_key: String,
    max_connections: usize,
    timeout: Duration,
}

impl AppConfig {
    fn load() -> Self {
        println!("  [Config] 正在加载配置...");
        thread::sleep(Duration::from_millis(100)); // 模拟加载延迟
        
        Self {
            database_url: std::env::var("DATABASE_URL")
                .unwrap_or_else(|_| "postgres://localhost/myapp".to_string()),
            api_key: std::env::var("API_KEY")
                .unwrap_or_else(|_| "default-api-key".to_string()),
            max_connections: std::env::var("MAX_CONNECTIONS")
                .ok()
                .and_then(|s| s.parse().ok())
                .unwrap_or(100),
            timeout: Duration::from_secs(30),
        }
    }
}

// 全局配置 - 延迟初始化
static CONFIG: LazyLock<AppConfig> = LazyLock::new(|| {
    println!("[LazyLock] 初始化全局配置");
    AppConfig::load()
});

// =============================================================================
// 热路径优化示例
// =============================================================================

/// 高性能配置访问
/// 
/// Rust 1.94 新增的 get() 方法允许无锁检查初始化状态
pub fn get_config_fast() -> Option<&'static AppConfig> {
    // 热路径优化: 使用 get() 进行无锁检查
    LazyLock::get(&CONFIG)
}

pub fn get_config() -> &'static AppConfig {
    &CONFIG
}

/// 模拟高频调用场景
fn hot_path_optimized() {
    println!("\n=== 热路径优化测试 ===");
    
    // 模拟 10000 次调用
    let iterations = 10000;
    
    // 传统方式
    let start = Instant::now();
    for _ in 0..iterations {
        let _ = get_config();
    }
    let time_traditional = start.elapsed();
    
    // 优化方式
    let start = Instant::now();
    for _ in 0..iterations {
        if let Some(config) = get_config_fast() {
            let _ = &config.api_key;
        }
    }
    let time_optimized = start.elapsed();
    
    println!("传统方式 ({} 次): {:?}", iterations, time_traditional);
    println!("优化方式 ({} 次): {:?}", iterations, time_optimized);
    println!("加速比: {:.2}x", 
        time_traditional.as_secs_f64() / time_optimized.as_secs_f64());
}

// =============================================================================
// 连接池示例
// =============================================================================

#[derive(Debug)]
struct ConnectionPool {
    connections: Mutex<Vec<Connection>>,
    max_size: usize,
}

#[derive(Debug)]
struct Connection {
    id: usize,
    created_at: Instant,
}

impl Connection {
    fn new(id: usize) -> Self {
        Self {
            id,
            created_at: Instant::now(),
        }
    }
}

impl ConnectionPool {
    fn new(max_size: usize) -> Self {
        println!("  [ConnectionPool] 创建连接池 (大小: {})", max_size);
        let mut connections = Vec::with_capacity(max_size);
        for i in 0..max_size {
            connections.push(Connection::new(i));
        }
        
        Self {
            connections: Mutex::new(connections),
            max_size,
        }
    }
    
    fn acquire(&self) -> Option<Connection> {
        self.connections.lock().unwrap().pop()
    }
    
    fn release(&self, conn: Connection) {
        self.connections.lock().unwrap().push(conn);
    }
}

// 全局连接池
static CONNECTION_POOL: LazyLock<ConnectionPool> = LazyLock::new(|| {
    println!("[LazyLock] 初始化连接池");
    ConnectionPool::new(10)
});

/// 优化的连接获取
pub fn get_connection_fast() -> Option<Connection> {
    // 先检查是否已初始化
    if LazyLock::get(&CONNECTION_POOL).is_some() {
        CONNECTION_POOL.acquire()
    } else {
        None
    }
}

pub fn get_connection() -> Option<Connection> {
    CONNECTION_POOL.acquire()
}

fn connection_pool_demo() {
    println!("\n=== 连接池示例 ===");
    
    // 获取连接
    if let Some(conn) = get_connection() {
        println!("获取连接: {:?}", conn);
        
        // 使用连接...
        
        // 释放连接
        CONNECTION_POOL.release(conn);
        println!("连接已释放");
    }
}

// =============================================================================
// LazyCell 示例 (单线程)
// =============================================================================

fn lazy_cell_demo() {
    println!("\n=== LazyCell 示例 ===");
    
    // 创建 LazyCell
    let cell: LazyCell<String> = LazyCell::new(|| {
        println!("  [LazyCell] 初始化");
        "Hello from LazyCell".to_string()
    });
    
    // 使用 get() 检查是否已初始化
    println!("初始状态: {:?}", cell.get());
    
    // 强制初始化
    let value: &String = &cell;
    println!("初始化后: {:?}", cell.get());
    println!("值: {}", value);
    
    // 可变访问 (如果未初始化，会先初始化)
    let mut_cell: LazyCell<Vec<i32>> = LazyCell::new(|| {
        println!("  [LazyCell] 初始化 Vec");
        vec![1, 2, 3]
    });
    
    if let Some(vec) = mut_cell.get_mut() {
        vec.push(4);
        println!("修改后: {:?}", vec);
    }
}

// =============================================================================
// 双重检查锁定模式
// =============================================================================

/// 使用 LazyLock 实现线程安全的单例
struct Singleton {
    data: String,
}

impl Singleton {
    fn new() -> Self {
        println!("  [Singleton] 创建实例");
        Self {
            data: "Singleton Data".to_string(),
        }
    }
}

static SINGLETON: LazyLock<Singleton> = LazyLock::new(Singleton::new);

fn singleton_demo() {
    println!("\n=== 单例模式示例 ===");
    
    // 多线程访问
    let handles: Vec<_> = (0..5)
        .map(|i| {
            thread::spawn(move || {
                let instance = &*SINGLETON;
                println!("线程 {} 访问: {:?}", i, instance.data);
            })
        })
        .collect();
    
    for h in handles {
        h.join().unwrap();
    }
}

// =============================================================================
// 缓存示例
// =============================================================================

use std::collections::HashMap;

struct Cache {
    data: Mutex<HashMap<String, String>>,
}

impl Cache {
    fn new() -> Self {
        Self {
            data: Mutex::new(HashMap::new()),
        }
    }
    
    fn get(&self, key: &str) -> Option<String> {
        self.data.lock().unwrap().get(key).cloned()
    }
    
    fn set(&self, key: String, value: String) {
        self.data.lock().unwrap().insert(key, value);
    }
}

static CACHE: LazyLock<Cache> = LazyLock::new(|| {
    println!("[LazyLock] 初始化缓存");
    Cache::new()
});

/// 带缓存的计算
fn expensive_computation(input: &str) -> String {
    // 先检查缓存
    if let Some(cached) = CACHE.get(input) {
        println!("  缓存命中: {}", input);
        return cached;
    }
    
    // 执行昂贵计算
    println!("  计算: {}", input);
    thread::sleep(Duration::from_millis(50));
    let result = format!("result_of_{}", input);
    
    // 存入缓存
    CACHE.set(input.to_string(), result.clone());
    result
}

fn cache_demo() {
    println!("\n=== 缓存示例 ===");
    
    let r1 = expensive_computation("hello");
    let r2 = expensive_computation("hello");  // 应该命中缓存
    let r3 = expensive_computation("world");
    
    println!("结果: {}, {}, {}", r1, r2, r3);
    assert_eq!(r1, r2);
}

// =============================================================================
// 数学常量示例
// =============================================================================

fn math_constants_demo() {
    println!("\n=== 数学常量示例 ===");
    
    // 欧拉-马歇罗尼常数
    println!("欧拉-马歇罗尼常数 (γ): {}", f64::consts::EULER_GAMMA);
    
    // 黄金比例
    println!("黄金比例 (φ): {}", f64::consts::GOLDEN_RATIO);
    
    // 黄金分割搜索示例
    fn golden_section_search<F>(f: F, mut a: f64, mut b: f64, eps: f64) -> f64
    where
        F: Fn(f64) -> f64,
    {
        let phi = f64::consts::GOLDEN_RATIO;
        let resphi = 2.0 - phi;
        
        let mut x1 = a + resphi * (b - a);
        let mut x2 = b - resphi * (b - a);
        let mut f1 = f(x1);
        let mut f2 = f(x2);
        
        while (b - a).abs() > eps {
            if f1 < f2 {
                b = x2;
                x2 = x1;
                f2 = f1;
                x1 = a + resphi * (b - a);
                f1 = f(x1);
            } else {
                a = x1;
                x1 = x2;
                f1 = f2;
                x2 = b - resphi * (b - a);
                f2 = f(x2);
            }
        }
        (a + b) / 2.0
    }
    
    // 测试: 寻找 x^2 的最小值 (应该在 0)
    let min = golden_section_search(|x| x * x, -10.0, 10.0, 1e-10);
    println!("x^2 的最小值点: {} (期望: 0)", min);
}

// =============================================================================
// 主函数
// =============================================================================

fn main() {
    println!("=== Rust 1.94 LazyCell/LazyLock 新方法演示 ===");
    
    // 1. 基础延迟初始化
    println!("\n1. 基础延迟初始化");
    println!("访问 CONFIG (首次，会触发初始化):");
    let _ = get_config();
    println!("再次访问 (已初始化):");
    let _ = get_config();
    
    // 2. 热路径优化
    hot_path_optimized();
    
    // 3. 连接池
    connection_pool_demo();
    
    // 4. LazyCell
    lazy_cell_demo();
    
    // 5. 单例模式
    singleton_demo();
    
    // 6. 缓存
    cache_demo();
    
    // 7. 数学常量
    math_constants_demo();
    
    println!("\n=== 演示完成 ===");
}
