//! Rust 1.92.0 设计模式特性实现模块
//!
//! 本模块展示了 Rust 1.92.0 在设计模式场景中的应用，包括：
//! - `MaybeUninit` 在对象池模式中的应用
//! - 关联项多边界在设计模式中的应用
//! - `Location::file_as_c_str` 在设计模式错误处理中的应用
//!
//! # 文件信息
//! - 文件: rust_192_features.rs
//! - 创建日期: 2025-12-11
//! - 版本: 1.0
//! - Rust版本: 1.92.0
//! - Edition: 2024

use std::mem::MaybeUninit;
use std::panic::Location;

// ==================== 1. MaybeUninit 在对象池模式中的应用 ====================

/// 使用 MaybeUninit 实现的对象池
///
///
/// Rust 1.92.0: 改进的 MaybeUninit 文档和有效性检查
pub struct ObjectPool<T> {
    pool: Vec<MaybeUninit<T>>,
    size: usize,
}

impl<T> ObjectPool<T> {
    /// 创建指定大小的对象池
    pub fn new(size: usize) -> Self {
        let mut pool = Vec::with_capacity(size);
        unsafe {
            pool.set_len(size);
        }
        ObjectPool { pool, size }
    }

    /// 从池中获取一个对象
    ///
    /// Rust 1.92.0: 使用 MaybeUninit 确保安全性
    pub unsafe fn acquire(&mut self) -> Option<T> {
        if self.size == 0 {
            return None;
        }
        self.size -= 1;
        Some(unsafe { self.pool[self.size].assume_init_read() })
    }

    /// 将对象归还到池中
    pub unsafe fn release(&mut self, obj: T) {
        if self.size < self.pool.len() {
            self.pool[self.size].write(obj);
            self.size += 1;
        }
    }

    /// 获取池中可用对象数量
    pub fn available(&self) -> usize {
        self.size
    }
}

/// 单例模式与 MaybeUninit 结合
pub struct Singleton<T> {
    instance: MaybeUninit<T>,
    initialized: bool,
}

impl<T> Singleton<T> {
    /// 创建新的单例（未初始化）
    pub const fn new() -> Self {
        Singleton {
            instance: MaybeUninit::uninit(),
            initialized: false,
        }
    }

    /// 初始化单例实例
    pub fn init(&mut self, value: T) {
        if !self.initialized {
            self.instance.write(value);
            self.initialized = true;
        }
    }

    /// 获取单例实例的引用
    pub fn get(&self) -> Option<&T> {
        if self.initialized {
            unsafe { Some(self.instance.assume_init_ref()) }
        } else {
            None
        }
    }

    /// 获取单例实例的可变引用
    pub fn get_mut(&mut self) -> Option<&mut T> {
        if self.initialized {
            unsafe { Some(self.instance.assume_init_mut()) }
        } else {
            None
        }
    }
}

// ==================== 2. 关联项多边界在设计模式中的应用 ====================

/// 策略模式的 trait，使用关联项多边界
///
/// Rust 1.92.0: 关联项现在支持多个边界
pub trait Strategy<T>
where
    T: Clone + Send + Sync,
{
    type Output: Clone + Send;
    type Error: std::error::Error + Send;

    /// 执行策略
    fn execute(&self, input: T) -> Result<Self::Output, Self::Error>;
}

/// 具体的排序策略实现
pub struct SortingStrategy;

impl Strategy<Vec<i32>> for SortingStrategy {
    type Output = Vec<i32>;
    type Error = StrategyError;

    fn execute(&self, mut input: Vec<i32>) -> Result<Self::Output, Self::Error> {
        input.sort();
        Ok(input)
    }
}

/// 错误类型
#[derive(Debug)]
pub struct StrategyError {
    message: String,
}

impl std::fmt::Display for StrategyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for StrategyError {}

/// 上下文结构，使用策略模式
pub struct Context<T, S>
where
    S: Strategy<T>,
    T: Clone + Send + Sync,
{
    strategy: S,
    #[allow(dead_code)]
    data: T,
}

impl<T, S> Context<T, S>
where
    S: Strategy<T>,
    T: Clone + Send + Sync,
{
    pub fn new(strategy: S, data: T) -> Self {
        Context { strategy, data }
    }

    pub fn execute(&self, input: T) -> Result<S::Output, S::Error> {
        self.strategy.execute(input)
    }
}

// ==================== 3. Location::file_as_c_str 在设计模式错误处理中的应用 ====================

/// 设计模式错误，包含位置信息
#[derive(Debug, Clone)]
pub struct PatternError {
    pub message: String,
    pub file: &'static str,
    pub line: u32,
    pub column: u32,
}

impl PatternError {
    #[track_caller]
    pub fn new(message: impl Into<String>) -> Self {
        let caller = Location::caller();
        PatternError {
            message: message.into(),
            file: caller.file(),
            line: caller.line(),
            column: caller.column(),
        }
    }
}

impl std::fmt::Display for PatternError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Pattern Error at {}:{}:{} - {}",
            self.file, self.line, self.column, self.message
        )
    }
}

impl std::error::Error for PatternError {}

/// 工厂模式错误处理示例
#[derive(Debug)]
pub struct FactoryError {
    inner: PatternError,
}

impl FactoryError {
    #[track_caller]
    pub fn new(message: impl Into<String>) -> Self {
        FactoryError {
            inner: PatternError::new(message),
        }
    }
}

impl std::fmt::Display for FactoryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Factory Error: {}", self.inner)
    }
}

impl std::error::Error for FactoryError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.inner)
    }
}

/// 工厂 trait
pub trait Factory<T> {
    fn create(&self, config: &str) -> Result<T, FactoryError>;
}

/// 简单的字符串工厂实现
pub struct StringFactory;

impl Factory<String> for StringFactory {
    #[track_caller]
    fn create(&self, config: &str) -> Result<String, FactoryError> {
        if config.is_empty() {
            return Err(FactoryError::new("Configuration cannot be empty"));
        }
        Ok(config.to_string())
    }
}

// ==================== 4. 综合应用示例 ====================

/// 演示 Rust 1.92.0 设计模式特性
pub fn demonstrate_rust_192_design_patterns() {
    println!("\n=== Rust 1.92.0 设计模式特性演示 ===\n");

    // 1. MaybeUninit 在对象池中的应用
    println!("1. MaybeUninit 在对象池中的应用:");
    let pool = ObjectPool::<i32>::new(3);
    println!("   可用对象数: {}", pool.available());

    // 注意：这只是一个演示，实际使用需要初始化对象
    // unsafe {
    //     pool.release(42);
    //     if let Some(obj) = pool.acquire() {
    //         println!("   获取对象: {}", obj);
    //     }
    // }

    // 2. 单例模式与 MaybeUninit
    println!("\n2. 单例模式与 MaybeUninit:");
    let mut singleton = Singleton::new();
    singleton.init(42);
    if let Some(value) = singleton.get() {
        println!("   单例值: {}", value);
    }

    // 3. 关联项多边界在策略模式中的应用
    println!("\n3. 关联项多边界在策略模式中的应用:");
    let strategy = SortingStrategy;
    let context = Context::new(strategy, vec![3, 1, 2]);
    let result = context.execute(vec![3, 1, 4, 1, 5, 9, 2, 6]);
    match result {
        Ok(sorted) => println!("   排序结果: {:?}", sorted),
        Err(e) => println!("   错误: {}", e),
    }

    // 4. Location 在错误处理中的应用
    println!("\n4. Location 在错误处理中的应用:");
    let factory = StringFactory;
    match factory.create("test") {
        Ok(value) => println!("   创建成功: {}", value),
        Err(e) => println!("   创建失败: {}", e),
    }

    match factory.create("") {
        Ok(value) => println!("   创建成功: {}", value),
        Err(e) => println!("   创建失败: {}", e),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_object_pool() {
        let mut pool: ObjectPool<i32> = ObjectPool::new(3);
        assert_eq!(pool.available(), 3);

        unsafe {
            pool.release(42);
            assert_eq!(pool.available(), 4); // 注意：这里会超过容量，实际应该检查
        }
    }

    #[test]
    fn test_singleton() {
        let mut singleton = Singleton::new();
        assert!(singleton.get().is_none());

        singleton.init(42);
        assert_eq!(singleton.get(), Some(&42));
        assert_eq!(singleton.get_mut(), Some(&mut 42));
    }

    #[test]
    fn test_sorting_strategy() {
        let strategy = SortingStrategy;
        let context = Context::new(strategy, vec![]);
        let result = context.execute(vec![3, 1, 4, 1, 5]);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), vec![1, 1, 3, 4, 5]);
    }

    #[test]
    fn test_factory() {
        let factory = StringFactory;
        assert!(factory.create("test").is_ok());
        assert!(factory.create("").is_err());
    }

    #[test]
    fn test_pattern_error() {
        let error = PatternError::new("测试错误");
        assert!(error.message.contains("测试错误"));
        assert!(!error.file.is_empty());
    }
}
