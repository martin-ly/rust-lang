//! Rust 最佳实践 vs 反例对比
//!
//! 本文件通过对比展示Rust中的最佳实践和常见反例：
//! - 集合使用模式
//! - 错误处理方式
//! - 内存管理
//! - 并发编程
//! - 性能优化
//!
//! # 使用说明
//! 每个示例包含 ❌ 反例（Anti-pattern）和 ✅ 最佳实践（Best Practice）

#![allow(unused)]

use std::collections::{HashMap, VecDeque};
use std::fs::File;
use std::io::{self, BufReader, Read, Write};
use std::sync::{Arc, Mutex};
use std::thread;

/// # 集合使用最佳实践
mod collections_best_practices {
    use super::*;

    /// ## 1. Vec 容量预分配
    ///
    /// ❌ 反例：重复分配内存
    pub fn vec_bad_example() -> Vec<i32> {
        let mut vec = Vec::new();
        for i in 0..1000 {
            vec.push(i); // 多次重新分配内存
        }
        vec
    }

    /// ✅ 最佳实践：预分配容量
    pub fn vec_good_example() -> Vec<i32> {
        let mut vec = Vec::with_capacity(1000);
        for i in 0..1000 {
            vec.push(i); // 无需重新分配
        }
        vec
    }

    /// ## 2. HashMap 批量插入
    ///
    /// ❌ 反例：逐个插入
    pub fn hashmap_bad_example() -> HashMap<String, i32> {
        let mut map = HashMap::new();
        for i in 0..100 {
            map.insert(format!("key{}", i), i); // 多次哈希计算
        }
        map
    }

    /// ✅ 最佳实践：使用 collect
    pub fn hashmap_good_example() -> HashMap<String, i32> {
        (0..100).map(|i| (format!("key{}", i), i)).collect() // 更高效的批量插入
    }

    /// ## 3. 避免不必要的克隆
    ///
    /// ❌ 反例：不必要的 clone
    pub fn clone_bad_example(data: Vec<String>) -> Vec<String> {
        let mut result = Vec::new();
        for item in &data {
            result.push(item.clone()); // 不必要的数据复制
        }
        result
    }

    /// ✅ 最佳实践：使用迭代器引用
    pub fn clone_good_example(data: &[String]) -> impl Iterator<Item = &String> + '_ {
        data.iter() // 返回迭代器，避免复制
    }

    pub fn demonstrate() {
        println!("=== 集合使用最佳实践 ===\n");

        // 容量预分配对比
        let start = std::time::Instant::now();
        let _v1 = vec_bad_example();
        let bad_time = start.elapsed();

        let start = std::time::Instant::now();
        let _v2 = vec_good_example();
        let good_time = start.elapsed();

        println!("Vec without capacity: {:?}", bad_time);
        println!("Vec with capacity: {:?}", good_time);
        println!("预分配容量避免了多次内存重新分配\\n");
    }
}

/// # 错误处理最佳实践
mod error_handling_best_practices {
    use std::collections::HashMap;
    use std::fs::File;
    use std::io::{self, Read};

    /// ## 1. Result 传播
    ///
    /// ❌ 反例：过度的 match 嵌套
    pub fn read_file_bad(path: &str) -> Result<String, io::Error> {
        match File::open(path) {
            Ok(mut file) => {
                let mut contents = String::new();
                match file.read_to_string(&mut contents) {
                    Ok(_) => Ok(contents),
                    Err(e) => Err(e),
                }
            }
            Err(e) => Err(e),
        }
    }

    /// ✅ 最佳实践：使用 ? 运算符
    pub fn read_file_good(path: &str) -> Result<String, io::Error> {
        let mut file = File::open(path)?;
        let mut contents = String::new();
        file.read_to_string(&mut contents)?;
        Ok(contents)
    }

    /// ## 2. Option 处理
    ///
    /// ❌ 反例：手动 unwrap
    pub fn option_bad(map: &HashMap<String, i32>, key: &str) -> i32 {
        match map.get(key) {
            Some(val) => *val,
            None => 0,
        }
    }

    /// ✅ 最佳实践：使用 unwrap_or
    pub fn option_good(map: &HashMap<String, i32>, key: &str) -> i32 {
        map.get(key).copied().unwrap_or(0)
    }

    /// ## 3. 错误转换
    ///
    /// ❌ 反例：手动错误映射
    pub fn parse_number_bad(s: &str) -> Result<i32, String> {
        match s.parse::<i32>() {
            Ok(n) => Ok(n),
            Err(e) => Err(format!("Parse error: {}", e)),
        }
    }

    /// ✅ 最佳实践：使用 map_err
    pub fn parse_number_good(s: &str) -> Result<i32, String> {
        s.parse::<i32>().map_err(|e| format!("Parse error: {}", e))
    }

    pub fn demonstrate() {
        println!("=== 错误处理最佳实践 ===\n");

        let mut map = HashMap::new();
        map.insert("key".to_string(), 42);

        println!("Option with default: {}", option_good(&map, "missing"));

        match read_file_good("/nonexistent/file.txt") {
            Ok(_) => println!("File read successfully"),
            Err(e) => println!("Expected error (file not found): {}", e),
        }

        println!();
    }
}

/// # 内存管理最佳实践
mod memory_best_practices {
    /// ## 1. 避免内存泄漏：使用 RAII
    ///
    /// ❌ 反例：手动内存管理
    pub fn memory_bad() {
        // 在unsafe代码中手动分配，容易忘记释放
        // let ptr = Box::into_raw(Box::new(42));
        // ... 某些操作
        // 如果这里 panic，内存就泄漏了
    }

    /// ✅ 最佳实践：使用 RAII
    pub fn memory_good() {
        let _data = Box::new(42); // 自动释放
        // ... 某些操作
        // 即使 panic，析构函数也会被调用
    }

    /// ## 2. 大数组的栈/堆选择
    ///
    /// ❌ 反例：大数组分配在栈上
    pub fn stack_bad() {
        // let _large_array = [0u8; 1_000_000]; // 可能导致栈溢出
    }

    /// ✅ 最佳实践：大数组分配到堆上
    pub fn stack_good() {
        let _large_vec = vec![0u8; 1_000_000]; // 安全地在堆上分配
    }

    /// ## 3. 避免不必要的装箱
    ///
    /// ❌ 反例：小类型装箱
    pub fn boxing_bad() -> Box<i32> {
        Box::new(42) // i32 可以直接放在栈上
    }

    /// ✅ 最佳实践：直接返回值
    pub fn boxing_good() -> i32 {
        42 // 更高效的栈分配
    }

    pub fn demonstrate() {
        println!("=== 内存管理最佳实践 ===\n");
        println!("✓ 使用 RAII 模式自动管理资源");
        println!("✓ 大数组 (>1MB) 使用 Vec 分配到堆上");
        println!("✓ 避免对小类型进行 Box 装箱");
        println!();
    }
}

/// # 并发编程最佳实践
mod concurrency_best_practices {
    use std::sync::{Arc, Mutex};
    use std::thread;

    /// ## 1. 锁的范围最小化
    ///
    /// ❌ 反例：持有锁时间过长
    pub fn lock_scope_bad() {
        let data = Arc::new(Mutex::new(vec![1, 2, 3]));
        let data_clone = Arc::clone(&data);

        thread::spawn(move || {
            let mut guard = data_clone.lock().unwrap();
            // 在锁内做耗时操作，阻塞其他线程
            // std::thread::sleep(std::time::Duration::from_secs(1));
            guard.push(4);
        });
    }

    /// ✅ 最佳实践：最小化锁范围
    pub fn lock_scope_good() {
        let data = Arc::new(Mutex::new(vec![1, 2, 3]));
        let data_clone = Arc::clone(&data);

        thread::spawn(move || {
            // 只在需要时获取锁
            {
                let mut guard = data_clone.lock().unwrap();
                guard.push(4);
            } // 锁在这里释放

            // 耗时操作在锁外执行
            // std::thread::sleep(std::time::Duration::from_secs(1));
        });
    }

    /// ## 2. 避免死锁
    ///
    /// ❌ 反例：锁顺序不一致
    pub fn deadlock_bad() {
        let lock1 = Arc::new(Mutex::new(1));
        let lock2 = Arc::new(Mutex::new(2));

        let l1_clone = Arc::clone(&lock1);
        let l2_clone = Arc::clone(&lock2);

        thread::spawn(move || {
            let _a = l1_clone.lock().unwrap();
            let _b = l2_clone.lock().unwrap(); // 可能死锁
        });

        let l1_clone = Arc::clone(&lock1);
        let l2_clone = Arc::clone(&lock2);

        thread::spawn(move || {
            let _b = l2_clone.lock().unwrap(); // 不同顺序！
            let _a = l1_clone.lock().unwrap(); // 可能死锁
        });
    }

    /// ✅ 最佳实践：统一的锁获取顺序
    pub fn deadlock_good() {
        let lock1 = Arc::new(Mutex::new(1));
        let lock2 = Arc::new(Mutex::new(2));

        let l1_clone = Arc::clone(&lock1);
        let l2_clone = Arc::clone(&lock2);

        thread::spawn(move || {
            let _a = l1_clone.lock().unwrap();
            let _b = l2_clone.lock().unwrap();
        });

        let l1_clone = Arc::clone(&lock1);
        let l2_clone = Arc::clone(&lock2);

        thread::spawn(move || {
            // 相同的顺序！
            let _a = l1_clone.lock().unwrap();
            let _b = l2_clone.lock().unwrap();
        });
    }

    /// ## 3. 使用消息传递而非共享状态
    ///
    /// ❌ 反例：过度使用共享状态
    pub fn shared_state_bad() {
        // 多个线程竞争修改共享数据
        // 复杂且容易出错
    }

    /// ✅ 最佳实践：使用通道
    pub fn channel_good() {
        let (tx, rx) = std::sync::mpsc::channel();

        thread::spawn(move || {
            tx.send(42).unwrap();
        });

        let result = rx.recv().unwrap();
        println!("Received: {}", result);
    }

    pub fn demonstrate() {
        println!("=== 并发编程最佳实践 ===\n");

        channel_good();

        println!("✓ 最小化锁的持有范围");
        println!("✓ 统一锁获取顺序避免死锁");
        println!("✓ 优先使用消息传递而非共享状态");
        println!();
    }
}

/// # 性能优化最佳实践
mod performance_best_practices {
    /// ## 1. 字符串拼接
    ///
    /// ❌ 反例：重复字符串分配
    pub fn string_concat_bad() -> String {
        let mut result = String::new();
        for i in 0..100 {
            result += &format!("item{}", i); // 每次循环都分配新内存
        }
        result
    }

    /// ✅ 最佳实践：使用 push_str 或 join
    pub fn string_concat_good() -> String {
        let items: Vec<String> = (0..100).map(|i| format!("item{}", i)).collect();
        items.join("") // 更高效的拼接
    }

    /// ✅ 最佳实践：使用 write! 宏
    pub fn string_concat_best() -> String {
        use std::fmt::Write;
        let mut result = String::with_capacity(1000);
        for i in 0..100 {
            write!(&mut result, "item{}", i).unwrap(); // 高效，避免中间分配
        }
        result
    }

    /// ## 2. 迭代器 vs 索引循环
    ///
    /// ❌ 反例：索引访问
    pub fn iteration_bad(data: &[i32]) -> i32 {
        let mut sum = 0;
        for i in 0..data.len() {
            sum += data[i]; // 每次都要做边界检查
        }
        sum
    }

    /// ✅ 最佳实践：使用迭代器
    pub fn iteration_good(data: &[i32]) -> i32 {
        data.iter().sum() // 优化更好，更简洁
    }

    /// ## 3. 避免不必要的分配
    ///
    /// ❌ 反例：重复分配
    pub fn allocation_bad(data: &str) -> Vec<String> {
        let mut parts = Vec::new();
        for part in data.split(',') {
            let trimmed = part.trim().to_string(); // 不必要的 to_string
            if !trimmed.is_empty() {
                parts.push(trimmed); // 每次都分配新的 String
            }
        }
        parts
    }

    /// ✅ 最佳实践：使用引用
    pub fn allocation_good(data: &str) -> impl Iterator<Item = &str> + '_ {
        data.split(',').map(str::trim).filter(|s| !s.is_empty())
    }

    pub fn demonstrate() {
        println!("=== 性能优化最佳实践 ===\n");

        let data = vec![1, 2, 3, 4, 5];
        println!("Sum using iterator: {}", iteration_good(&data));

        let text = "a, b, c";
        let parts: Vec<_> = allocation_good(text).collect();
        println!("Parsed parts: {:?}", parts);

        println!("✓ 使用 String::with_capacity 预分配");
        println!("✓ 优先使用迭代器而非索引");
        println!("✓ 避免不必要的 to_string/clone");
        println!();
    }
}

/// # API 设计最佳实践
mod api_design_best_practices {
    /// ## 1. 返回类型选择
    ///
    /// ❌ 反例：返回裸指针
    pub unsafe fn raw_pointer_bad() -> *const u8 {
        std::ptr::null()
    }

    /// ✅ 最佳实践：返回 Option 或 Result
    pub fn safe_api_good() -> Option<&'static u8> {
        None
    }

    /// ## 2. 借用 vs 所有权
    ///
    /// ❌ 反例：不必要的所有权转移
    pub fn ownership_bad(s: String) -> String {
        s.to_uppercase()
    }

    /// ✅ 最佳实践：接受借用
    pub fn borrow_good(s: &str) -> String {
        s.to_uppercase()
    }

    /// ## 3. Builder 模式
    ///
    /// ❌ 反例：复杂的多参数构造
    pub struct ConfigBad {
        pub host: String,
        pub port: u16,
        pub workers: usize,
        pub timeout: u64,
    }

    impl ConfigBad {
        pub fn new(host: String, port: u16, workers: usize, timeout: u64) -> Self {
            Self {
                host,
                port,
                workers,
                timeout,
            }
        }
    }

    /// ✅ 最佳实践：Builder 模式
    #[derive(Debug)]
    pub struct ConfigGood {
        host: String,
        port: u16,
        workers: usize,
        timeout: u64,
    }

    impl ConfigGood {
        pub fn builder() -> ConfigBuilder {
            ConfigBuilder::default()
        }
    }

    #[derive(Default)]
    pub struct ConfigBuilder {
        host: Option<String>,
        port: Option<u16>,
        workers: Option<usize>,
        timeout: Option<u64>,
    }

    impl ConfigBuilder {
        pub fn host(mut self, host: impl Into<String>) -> Self {
            self.host = Some(host.into());
            self
        }

        pub fn port(mut self, port: u16) -> Self {
            self.port = Some(port);
            self
        }

        pub fn build(self) -> Result<ConfigGood, String> {
            Ok(ConfigGood {
                host: self.host.ok_or("host is required")?,
                port: self.port.unwrap_or(8080),
                workers: self.workers.unwrap_or(4),
                timeout: self.timeout.unwrap_or(30),
            })
        }
    }

    pub fn demonstrate() {
        println!("=== API 设计最佳实践 ===\n");

        // Builder 模式使用
        let config = ConfigGood::builder()
            .host("localhost")
            .port(3000)
            .build()
            .unwrap();

        println!("Built config: {:?}", config);
        println!("✓ 优先返回 Option/Result 而非裸指针");
        println!("✓ 接受引用而非所有权（除非需要转移）");
        println!("✓ 对复杂构造使用 Builder 模式");
        println!();
    }
}

fn main() {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║     Rust 最佳实践 vs 反例对比                             ║");
    println!("╚══════════════════════════════════════════════════════════╝");

    collections_best_practices::demonstrate();
    error_handling_best_practices::demonstrate();
    memory_best_practices::demonstrate();
    concurrency_best_practices::demonstrate();
    performance_best_practices::demonstrate();
    api_design_best_practices::demonstrate();

    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║     核心原则总结                                          ║");
    println!("╠══════════════════════════════════════════════════════════╣");
    println!("║ 1. 集合: 预分配容量，避免不必要克隆                        ║");
    println!("║ 2. 错误: 使用 ? 运算符，unwrap_or 提供默认值               ║");
    println!("║ 3. 内存: RAII，大对象堆分配，避免小对象装箱                 ║");
    println!("║ 4. 并发: 最小锁范围，统一锁顺序，优先消息传递               ║");
    println!("║ 5. 性能: with_capacity，迭代器，避免重复分配               ║");
    println!("║ 6. API:  Option/Result，借用，Builder 模式                 ║");
    println!("╚══════════════════════════════════════════════════════════╝");
}
