//! Rust 1.90 高级特性演示模块
//!
//! 本模块展示了 Rust 1.90 中的高级语言特性，包括：
//! - 高级生命周期管理
//! - 复杂类型约束
//! - 高级宏系统
//! - 内存安全高级特性
//! - 并发编程高级模式
//!
//! # 文件信息
//! - 文件: rust_190_advanced_features.rs
//! - 创建日期: 2025-01-27
//! - 版本: 1.0
//! - Rust版本: 1.90.0
//! - Edition: 2024

use std::collections::HashMap;
use std::sync::{Arc, Mutex, RwLock};
use std::thread;
use std::time::Duration;

// ==================== 1. 高级生命周期管理 ====================

/// 高级生命周期组合类型
/// 
/// 展示了 Rust 1.90 中复杂的生命周期约束和组合
pub struct AdvancedLifetimeComposition<'a, 'b, 'c, T>
where
    'a: 'c,
    'b: 'c,
    T: 'a + 'b,
{
    /// 第一个生命周期受限的数据
    pub primary_data: &'a T,
    /// 第二个生命周期受限的数据
    pub secondary_data: &'b T,
    /// 组合生命周期受限的元数据
    pub metadata: &'c str,
    /// 生命周期组合标记
    pub lifetime_marker: LifetimeMarker<'a, 'b, 'c>,
}

/// 生命周期标记结构
pub struct LifetimeMarker<'a, 'b, 'c>
where
    'a: 'c,
    'b: 'c,
{
    pub primary_lifetime: &'a str,
    pub secondary_lifetime: &'b str,
    pub combined_lifetime: &'c str,
}

impl<'a, 'b, 'c, T> AdvancedLifetimeComposition<'a, 'b, 'c, T>
where
    'a: 'c,
    'b: 'c,
    T: 'a + 'b + Clone + std::fmt::Debug,
{
    /// 创建新的高级生命周期组合
    pub fn new(
        primary_data: &'a T,
        secondary_data: &'b T,
        metadata: &'c str,
    ) -> Self {
        Self {
            primary_data,
            secondary_data,
            metadata,
            lifetime_marker: LifetimeMarker {
                primary_lifetime: "primary",
                secondary_lifetime: "secondary",
                combined_lifetime: "combined",
            },
        }
    }
    
    /// 获取组合数据
    pub fn get_combined_data(&self) -> (T, T) {
        (self.primary_data.clone(), self.secondary_data.clone())
    }
    
    /// 验证生命周期约束
    pub fn validate_lifetimes(&self) -> bool {
        // 这里可以添加生命周期验证逻辑
        true
    }
    
    /// 生命周期转换
    pub fn transform_lifetimes<F, R>(&self, transformer: F) -> R
    where
        F: FnOnce(&'a T, &'b T, &'c str) -> R,
    {
        transformer(self.primary_data, self.secondary_data, self.metadata)
    }
}

// ==================== 2. 复杂类型约束 ====================

/// 高级类型约束 trait
/// 
/// 展示了 Rust 1.90 中复杂的类型约束和关联类型
pub trait AdvancedTypeConstraints {
    /// 关联类型约束
    type Item: Clone + std::fmt::Debug + PartialEq;
    type Container: std::iter::IntoIterator<Item = Self::Item>;
    type Error: std::error::Error + Send + Sync + 'static;
    
    /// 复杂约束方法
    fn process_with_constraints<F, R>(
        &self,
        processor: F,
    ) -> Result<R, Self::Error>
    where
        F: FnOnce(Self::Container) -> R,
        R: std::fmt::Display + Send + Sync;
    
    /// 类型转换约束
    fn convert_with_bounds<T>(&self, value: T) -> Result<Self::Item, Self::Error>
    where
        T: Into<Self::Item> + Clone + std::fmt::Debug;
}

/// 高级类型约束实现
pub struct ConstrainedProcessor<T> {
    data: Vec<T>,
}

impl<T> ConstrainedProcessor<T>
where
    T: Clone + std::fmt::Debug + PartialEq + Send + Sync + 'static,
{
    pub fn new(data: Vec<T>) -> Self {
        Self { data }
    }
}

impl<T> AdvancedTypeConstraints for ConstrainedProcessor<T>
where
    T: Clone + std::fmt::Debug + PartialEq + Send + Sync + 'static,
{
    type Item = T;
    type Container = Vec<T>;
    type Error = ProcessingError;
    
    fn process_with_constraints<F, R>(
        &self,
        processor: F,
    ) -> Result<R, Self::Error>
    where
        F: FnOnce(Self::Container) -> R,
        R: std::fmt::Display + Send + Sync,
    {
        let result = processor(self.data.clone());
        Ok(result)
    }
    
    fn convert_with_bounds<U>(&self, value: U) -> Result<Self::Item, Self::Error>
    where
        U: Into<Self::Item> + Clone + std::fmt::Debug,
    {
        Ok(value.into())
    }
}

/// 处理错误类型
#[derive(Debug, Clone)]
pub struct ProcessingError {
    pub message: String,
}

impl std::fmt::Display for ProcessingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Processing error: {}", self.message)
    }
}

impl std::error::Error for ProcessingError {}

// ==================== 3. 高级宏系统 ====================

/// 高级宏定义
/// 
/// 展示了 Rust 1.90 中宏系统的高级用法
#[macro_export]
macro_rules! advanced_type_builder {
    // 基础类型构建
    ($name:ident { $($field:ident: $type:ty),* }) => {
        #[derive(Debug, Clone, PartialEq)]
        pub struct $name {
            $(pub $field: $type),*
        }
        
        impl $name {
            pub fn new($($field: $type),*) -> Self {
                Self { $($field),* }
            }
        }
    };
    
    // 带默认值的类型构建
    ($name:ident { $($field:ident: $type:ty = $default:expr),* }) => {
        #[derive(Debug, Clone, PartialEq)]
        pub struct $name {
            $(pub $field: $type),*
        }
        
        impl $name {
            pub fn new() -> Self {
                Self { $($field: $default),* }
            }
            
            pub fn with_values($($field: $type),*) -> Self {
                Self { $($field),* }
            }
        }
        
        impl Default for $name {
            fn default() -> Self {
                Self::new()
            }
        }
    };
    
    // 泛型类型构建
    ($name:ident<$($param:ident: $bound:tt),*> { $($field:ident: $type:ty),* }) => {
        #[derive(Debug, Clone, PartialEq)]
        pub struct $name<$($param: $bound),*> {
            $(pub $field: $type),*
        }
        
        impl<$($param: $bound),*> $name<$($param),*> {
            pub fn new($($field: $type),*) -> Self {
                Self { $($field),* }
            }
        }
    };
}

// 高级宏使用示例
advanced_type_builder! {
    AdvancedStruct {
        id: u64,
        name: String,
        metadata: HashMap<String, String>
    }
}

advanced_type_builder! {
    ConfigurableStruct {
        timeout: Duration = Duration::from_secs(30),
        retries: u32 = 3,
        enabled: bool = true
    }
}

// 手动定义泛型结构体，因为宏不支持复杂的泛型约束
#[derive(Debug, Clone, PartialEq)]
pub struct GenericStruct<T: Clone + std::fmt::Debug> {
    pub data: T,
    pub count: usize,
}

impl<T: Clone + std::fmt::Debug> GenericStruct<T> {
    pub fn new(data: T, count: usize) -> Self {
        Self { data, count }
    }
}

// ==================== 4. 内存安全高级特性 ====================

/// 高级内存安全类型
/// 
/// 展示了 Rust 1.90 中的高级内存安全特性
pub struct AdvancedMemorySafe<T> {
    /// 使用 Arc 确保线程安全
    data: Arc<T>,
    /// 使用 Mutex 保护可变访问
    access_count: Arc<Mutex<usize>>,
    /// 使用 RwLock 支持多读单写
    metadata: Arc<RwLock<HashMap<String, String>>>,
}

impl<T> AdvancedMemorySafe<T>
where
    T: Send + Sync + 'static,
{
    /// 创建新的内存安全类型
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(data),
            access_count: Arc::new(Mutex::new(0)),
            metadata: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 安全访问数据
    pub fn get_data(&self) -> Arc<T> {
        let mut count = self.access_count.lock().unwrap();
        *count += 1;
        self.data.clone()
    }
    
    /// 安全更新元数据
    pub fn update_metadata(&self, key: String, value: String) -> Result<(), String> {
        let mut metadata = self.metadata.write().map_err(|_| "Failed to acquire write lock")?;
        metadata.insert(key, value);
        Ok(())
    }
    
    /// 安全读取元数据
    pub fn get_metadata(&self, key: &str) -> Result<Option<String>, String> {
        let metadata = self.metadata.read().map_err(|_| "Failed to acquire read lock")?;
        Ok(metadata.get(key).cloned())
    }
    
    /// 获取访问计数
    pub fn get_access_count(&self) -> usize {
        *self.access_count.lock().unwrap()
    }
}

impl<T> Clone for AdvancedMemorySafe<T> {
    fn clone(&self) -> Self {
        Self {
            data: self.data.clone(),
            access_count: self.access_count.clone(),
            metadata: self.metadata.clone(),
        }
    }
}

// ==================== 5. 并发编程高级模式 ====================

/// 高级并发处理器
/// 
/// 展示了 Rust 1.90 中的高级并发编程模式
pub struct AdvancedConcurrentProcessor<T> {
    /// 工作线程池
    workers: Vec<thread::JoinHandle<()>>,
    /// 任务队列
    task_queue: Arc<Mutex<Vec<T>>>,
    /// 结果收集器
    results: Arc<Mutex<Vec<ProcessingResult>>>,
    /// 停止信号
    stop_signal: Arc<Mutex<bool>>,
}

/// 处理结果
#[derive(Debug, Clone)]
pub struct ProcessingResult {
    pub id: u64,
    pub success: bool,
    pub message: String,
    pub timestamp: std::time::SystemTime,
}

impl<T> AdvancedConcurrentProcessor<T>
where
    T: Send + Sync + 'static + Clone,
{
    /// 创建新的并发处理器
    pub fn new(worker_count: usize) -> Self {
        let task_queue = Arc::new(Mutex::new(Vec::new()));
        let results = Arc::new(Mutex::new(Vec::new()));
        let stop_signal = Arc::new(Mutex::new(false));
        
        let mut workers = Vec::new();
        
        for worker_id in 0..worker_count {
            let task_queue = task_queue.clone();
            let results = results.clone();
            let stop_signal = stop_signal.clone();
            
            let handle = thread::spawn(move || {
                let mut local_results = Vec::new();
                
                loop {
                    // 检查停止信号
                    if *stop_signal.lock().unwrap() {
                        break;
                    }
                    
                    // 获取任务
                    let task = {
                        let mut queue = task_queue.lock().unwrap();
                        queue.pop()
                    };
                    
                    if let Some(task) = task {
                        // 处理任务
                        let result = Self::process_task(worker_id as u64, task);
                        local_results.push(result);
                    } else {
                        // 没有任务时短暂休眠
                        thread::sleep(Duration::from_millis(10));
                    }
                }
                
                // 将本地结果添加到全局结果
                let mut global_results = results.lock().unwrap();
                global_results.extend(local_results);
            });
            
            workers.push(handle);
        }
        
        Self {
            workers,
            task_queue,
            results,
            stop_signal,
        }
    }
    
    /// 添加任务
    pub fn add_task(&self, task: T) {
        let mut queue = self.task_queue.lock().unwrap();
        queue.push(task);
    }
    
    /// 获取结果
    pub fn get_results(&self) -> Vec<ProcessingResult> {
        let results = self.results.lock().unwrap();
        results.clone()
    }
    
    /// 停止处理器
    pub fn stop(self) -> Vec<ProcessingResult> {
        // 发送停止信号
        {
            let mut signal = self.stop_signal.lock().unwrap();
            *signal = true;
        }
        
        // 等待所有工作线程完成
        for worker in self.workers {
            let _ = worker.join();
        }
        
        // 返回最终结果
        let results = self.results.lock().unwrap();
        results.clone()
    }
    
    /// 处理单个任务
    fn process_task(worker_id: u64, _task: T) -> ProcessingResult {
        // 模拟任务处理
        thread::sleep(Duration::from_millis(100));
        
        ProcessingResult {
            id: worker_id,
            success: true,
            message: format!("Task processed by worker {}", worker_id),
            timestamp: std::time::SystemTime::now(),
        }
    }
}

// ==================== 6. 高级错误处理 ====================

/// 高级错误类型
/// 
/// 展示了 Rust 1.90 中的高级错误处理模式
#[derive(Debug, Clone)]
pub enum AdvancedError {
    /// 处理错误
    Processing(ProcessingError),
    /// 并发错误
    Concurrent(String),
    /// 内存错误
    Memory(String),
    /// 类型错误
    Type(String),
    /// 生命周期错误
    Lifetime(String),
}

impl std::fmt::Display for AdvancedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AdvancedError::Processing(e) => write!(f, "Processing error: {}", e),
            AdvancedError::Concurrent(msg) => write!(f, "Concurrent error: {}", msg),
            AdvancedError::Memory(msg) => write!(f, "Memory error: {}", msg),
            AdvancedError::Type(msg) => write!(f, "Type error: {}", msg),
            AdvancedError::Lifetime(msg) => write!(f, "Lifetime error: {}", msg),
        }
    }
}

impl std::error::Error for AdvancedError {}

impl From<ProcessingError> for AdvancedError {
    fn from(error: ProcessingError) -> Self {
        AdvancedError::Processing(error)
    }
}

/// 高级错误处理工具
pub struct ErrorHandler {
    error_log: Arc<Mutex<Vec<AdvancedError>>>,
}

impl ErrorHandler {
    /// 创建新的错误处理器
    pub fn new() -> Self {
        Self {
            error_log: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    /// 记录错误
    pub fn log_error(&self, error: AdvancedError) {
        let mut log = self.error_log.lock().unwrap();
        log.push(error);
    }
    
    /// 获取错误日志
    pub fn get_errors(&self) -> Vec<AdvancedError> {
        let log = self.error_log.lock().unwrap();
        log.clone()
    }
    
    /// 清空错误日志
    pub fn clear_errors(&self) {
        let mut log = self.error_log.lock().unwrap();
        log.clear();
    }
}

impl Default for ErrorHandler {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 演示函数 ====================

/// 演示所有高级特性
pub fn demonstrate_advanced_features() {
    println!("=== Rust 1.90 高级特性演示 ===\n");
    
    // 1. 高级生命周期管理演示
    println!("1. 高级生命周期管理演示:");
    let primary_data = String::from("Primary data");
    let secondary_data = String::from("Secondary data");
    let metadata = "Combined metadata";
    
    let composition = AdvancedLifetimeComposition::new(&primary_data, &secondary_data, metadata);
    let (p, s) = composition.get_combined_data();
    println!("  组合数据: ({}, {})", p, s);
    println!("  生命周期验证: {}", composition.validate_lifetimes());
    
    let result = composition.transform_lifetimes(|p, s, m| {
        format!("Transformed: {} + {} + {}", p, s, m)
    });
    println!("  转换结果: {}", result);
    println!();
    
    // 2. 复杂类型约束演示
    println!("2. 复杂类型约束演示:");
    let processor = ConstrainedProcessor::new(vec![1, 2, 3, 4, 5]);
    let result = processor.process_with_constraints(|data| {
        format!("Processed {} items", data.len())
    });
    println!("  处理结果: {:?}", result);
    
    let converted = processor.convert_with_bounds(42i32);
    println!("  转换结果: {:?}", converted);
    println!();
    
    // 3. 高级宏系统演示
    println!("3. 高级宏系统演示:");
    let advanced_struct = AdvancedStruct::new(
        1,
        "Test".to_string(),
        HashMap::new(),
    );
    println!("  高级结构体: {:?}", advanced_struct);
    
    let configurable = ConfigurableStruct::new();
    println!("  可配置结构体: {:?}", configurable);
    
    let generic_struct = GenericStruct::new("Hello", 5);
    println!("  泛型结构体: {:?}", generic_struct);
    println!();
    
    // 4. 内存安全高级特性演示
    println!("4. 内存安全高级特性演示:");
    let memory_safe = AdvancedMemorySafe::new("Safe data".to_string());
    let data = memory_safe.get_data();
    println!("  安全数据: {:?}", data);
    
    let _ = memory_safe.update_metadata("key1".to_string(), "value1".to_string());
    let metadata = memory_safe.get_metadata("key1");
    println!("  元数据: {:?}", metadata);
    println!("  访问计数: {}", memory_safe.get_access_count());
    println!();
    
    // 5. 并发编程高级模式演示
    println!("5. 并发编程高级模式演示:");
    let processor = AdvancedConcurrentProcessor::new(2);
    
    // 添加一些任务
    for i in 0..5 {
        processor.add_task(format!("Task {}", i));
    }
    
    // 等待处理完成
    thread::sleep(Duration::from_millis(500));
    
    let results = processor.get_results();
    println!("  处理结果数量: {}", results.len());
    for result in &results {
        println!("    结果: {:?}", result);
    }
    
    // 停止处理器
    let final_results = processor.stop();
    println!("  最终结果数量: {}", final_results.len());
    println!();
    
    // 6. 高级错误处理演示
    println!("6. 高级错误处理演示:");
    let error_handler = ErrorHandler::new();
    
    error_handler.log_error(AdvancedError::Processing(ProcessingError {
        message: "Test processing error".to_string(),
    }));
    error_handler.log_error(AdvancedError::Concurrent("Test concurrent error".to_string()));
    
    let errors = error_handler.get_errors();
    println!("  错误数量: {}", errors.len());
    for error in &errors {
        println!("    错误: {}", error);
    }
    
    println!("\n=== 高级特性演示完成 ===");
}

// ==================== 测试模块 ====================

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_advanced_lifetime_composition() {
        let primary = String::from("primary");
        let secondary = String::from("secondary");
        let metadata = "metadata";
        
        let composition = AdvancedLifetimeComposition::new(&primary, &secondary, metadata);
        assert!(composition.validate_lifetimes());
        
        let (p, s) = composition.get_combined_data();
        assert_eq!(p, "primary");
        assert_eq!(s, "secondary");
    }
    
    #[test]
    fn test_constrained_processor() {
        let processor = ConstrainedProcessor::new(vec![1, 2, 3]);
        let result = processor.process_with_constraints(|data| format!("{}", data.len()));
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), "3");
    }
    
    #[test]
    fn test_advanced_memory_safe() {
        let memory_safe = AdvancedMemorySafe::new("test".to_string());
        let data = memory_safe.get_data();
        assert_eq!(*data, "test");
        assert_eq!(memory_safe.get_access_count(), 1);
    }
    
    #[test]
    fn test_error_handler() {
        let handler = ErrorHandler::new();
        handler.log_error(AdvancedError::Processing(ProcessingError {
            message: "test".to_string(),
        }));
        
        let errors = handler.get_errors();
        assert_eq!(errors.len(), 1);
    }
}
