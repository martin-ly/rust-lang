//! # Rust 1.90 全面特性示例 / Rust 1.90 Comprehensive Features Examples
//!
//! 本示例全面展示 Rust 1.90 版本的所有语言特性，包括：
//! This example comprehensively demonstrates all language features in Rust 1.90, including:
//!
//! - 改进的借用检查器 / Improved borrow checker
//! - 增强的生命周期推断 / Enhanced lifetime inference
//! - 新的智能指针特性 / New smart pointer features
//! - 优化的作用域管理 / Optimized scope management
//! - 增强的并发安全 / Enhanced concurrency safety
//! - 智能内存管理 / Smart memory management
//! - 改进的错误处理 / Improved error handling
//! - 性能优化特性 / Performance optimization features

use std::collections::HashMap;
use std::rc::Rc;
use std::sync::{Arc, Mutex, RwLock};
use std::cell::RefCell;
use std::thread;
use std::sync::atomic::{AtomicUsize, Ordering};

/// # 1. 改进的借用检查器特性 / Improved Borrow Checker Features

/// 演示 Rust 1.90 中改进的借用检查器
/// Demonstrates improved borrow checker in Rust 1.90
pub mod improved_borrow_checker {
    use super::*;

    /// 复杂借用模式示例 / Complex Borrowing Pattern Example
    pub fn complex_borrowing_patterns() {
        println!("=== 复杂借用模式 / Complex Borrowing Patterns ===");
        
        let mut data = vec![vec![1, 2, 3], vec![4, 5, 6], vec![7, 8, 9]];
        
        // Rust 1.90 支持更复杂的借用模式
        // Rust 1.90 supports more complex borrowing patterns
        for (i, row) in data.iter_mut().enumerate() {
            for (j, element) in row.iter_mut().enumerate() {
                *element = (i + 1) * 10 + (j + 1);
            }
        }
        
        println!("Modified matrix: {:?}", data);
        
        // 同时借用向量的不同部分
        // Borrow different parts of vector simultaneously
        let mut numbers = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let (first_half, second_half) = numbers.split_at_mut(5);
        
        // 可以同时修改不同部分
        // Can modify different parts simultaneously
        for element in first_half.iter_mut() {
            *element *= 2;
        }
        
        for element in second_half.iter_mut() {
            *element *= 3;
        }
        
        println!("Modified numbers: {:?}", numbers);
    }

    /// 智能借用分析示例 / Smart Borrow Analysis Example
    pub fn smart_borrow_analysis() {
        println!("=== 智能借用分析 / Smart Borrow Analysis ===");
        
        let mut complex_data = HashMap::new();
        complex_data.insert("key1".to_string(), vec![1, 2, 3]);
        complex_data.insert("key2".to_string(), vec![4, 5, 6]);
        
        // Rust 1.90 可以更智能地分析借用
        // Rust 1.90 can more intelligently analyze borrows
        // 分别借用不同的键
        // Borrow different keys separately
        if let Some(vec1) = complex_data.get_mut("key1") {
            vec1.push(7);
        }
        if let Some(vec2) = complex_data.get_mut("key2") {
            vec2.push(8);
        }
        
        println!("Complex data: {:?}", complex_data);
    }
}

/// # 2. 增强的生命周期推断特性 / Enhanced Lifetime Inference Features

/// 演示 Rust 1.90 中增强的生命周期推断
/// Demonstrates enhanced lifetime inference in Rust 1.90
pub mod enhanced_lifetime_inference {

    /// 自动生命周期推断示例 / Automatic Lifetime Inference Example
    pub fn automatic_lifetime_inference() {
        println!("=== 自动生命周期推断 / Automatic Lifetime Inference ===");
        
        let string1 = String::from("long string is long");
        let string2 = String::from("xyz");
        
        // Rust 1.90 可以更好地推断生命周期
        // Rust 1.90 can better infer lifetimes
        let result = longest_string(&string1, &string2);
        println!("Longest string: {}", result);
        
        // 复杂生命周期推断
        // Complex lifetime inference
        let complex_result = complex_lifetime_function(&string1, &string2, "static");
        println!("Complex result: {}", complex_result);
    }

    /// 最长字符串函数 / Longest string function
    fn longest_string<'a>(x: &'a str, y: &'a str) -> &'a str {
        if x.len() > y.len() { x } else { y }
    }

    /// 复杂生命周期函数 / Complex lifetime function
    fn complex_lifetime_function<'a, 'b>(x: &'a str, y: &'b str, z: &'static str) -> &'a str 
    where
        'b: 'a,
    {
        if x.len() > y.len() { x } else { z }
    }

    /// 结构体生命周期推断示例 / Struct Lifetime Inference Example
    pub fn struct_lifetime_inference() {
        println!("=== 结构体生命周期推断 / Struct Lifetime Inference ===");
        
        let text = String::from("This is a sample text for analysis.");
        let excerpt = create_excerpt(&text);
        println!("Excerpt: {}", excerpt.part);
    }

    /// 包含引用的结构体 / Struct containing reference
    struct TextExcerpt<'a> {
        part: &'a str,
    }

    /// 创建摘录 / Create excerpt
    fn create_excerpt<'a>(text: &'a str) -> TextExcerpt<'a> {
        let first_sentence = text.split('.').next().expect("Could not find a '.'");
        TextExcerpt { part: first_sentence }
    }
}

/// # 3. 新的智能指针特性 / New Smart Pointer Features

/// 演示 Rust 1.90 中新的智能指针特性
/// Demonstrates new smart pointer features in Rust 1.90
pub mod new_smart_pointer_features {
    use super::*;

    /// 高级智能指针模式示例 / Advanced Smart Pointer Pattern Example
    pub fn advanced_smart_pointer_patterns() {
        println!("=== 高级智能指针模式 / Advanced Smart Pointer Patterns ===");
        
        // 使用 Rc<RefCell<T>> 实现内部可变性
        // Use Rc<RefCell<T>> for interior mutability
        let shared_data = Rc::new(RefCell::new(vec![1, 2, 3]));
        let data_clone1 = Rc::clone(&shared_data);
        let data_clone2 = Rc::clone(&shared_data);
        
        // 可以同时修改共享数据
        // Can modify shared data simultaneously
        data_clone1.borrow_mut().push(4);
        data_clone2.borrow_mut().push(5);
        
        println!("Shared data: {:?}", shared_data.borrow());
        println!("Reference count: {}", Rc::strong_count(&shared_data));
        
        // 演示弱引用
        // Demonstrate weak references
        let strong = Rc::new(42);
        let weak = Rc::downgrade(&strong);
        
        println!("Strong count: {}, Weak count: {}", 
                Rc::strong_count(&strong), Rc::weak_count(&strong));
        
        drop(strong);
        
        match weak.upgrade() {
            Some(value) => println!("Weak reference still valid: {}", value),
            None => println!("Weak reference is no longer valid"),
        }
    }

    /// 智能指针优化示例 / Smart Pointer Optimization Example
    pub fn smart_pointer_optimization() {
        println!("=== 智能指针优化 / Smart Pointer Optimization ===");
        
        // 使用 Box 进行堆分配优化
        // Use Box for heap allocation optimization
        let heap_data = Box::new(vec![1, 2, 3, 4, 5]);
        let processed_data: Vec<i32> = heap_data.iter()
            .map(|x| x * x)
            .filter(|&x| x % 2 == 0)
            .collect();
        
        println!("Processed data: {:?}", processed_data);
        
        // 使用 Arc 进行线程间共享
        // Use Arc for inter-thread sharing
        let shared_counter = Arc::new(AtomicUsize::new(0));
        let mut handles = vec![];
        
        for i in 0..5 {
            let counter_clone = Arc::clone(&shared_counter);
            let handle = thread::spawn(move || {
                for _ in 0..1000 {
                    counter_clone.fetch_add(1, Ordering::SeqCst);
                }
                println!("Thread {} finished", i);
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        println!("Final counter value: {}", shared_counter.load(Ordering::SeqCst));
    }
}

/// # 4. 优化的作用域管理特性 / Optimized Scope Management Features

/// 演示 Rust 1.90 中优化的作用域管理
/// Demonstrates optimized scope management in Rust 1.90
pub mod optimized_scope_management {

    /// 精确作用域控制示例 / Precise Scope Control Example
    pub fn precise_scope_control() {
        println!("=== 精确作用域控制 / Precise Scope Control ===");
        
        let outer_data = String::from("outer");
        
        {
            let inner_data = String::from("inner");
            
            // Rust 1.90 提供更精确的作用域分析
            // Rust 1.90 provides more precise scope analysis
            println!("Outer: {}, Inner: {}", outer_data, inner_data);
            
            {
                let nested_data = String::from("nested");
                println!("Nested scope: {}", nested_data);
                
                // 可以访问所有外层作用域的变量
                // Can access variables from all outer scopes
                let combined = format!("{} + {} + {}", outer_data, inner_data, nested_data);
                println!("Combined: {}", combined);
            } // nested_data 离开作用域 / nested_data goes out of scope
            
        } // inner_data 离开作用域 / inner_data goes out of scope
        
        // outer_data 仍然有效 / outer_data is still valid
        println!("Outer data still valid: {}", outer_data);
    }

    /// 作用域优化示例 / Scope Optimization Example
    pub fn scope_optimization() {
        println!("=== 作用域优化 / Scope Optimization ===");
        
        // 早期释放不需要的变量
        // Early release of unnecessary variables
        let expensive_data = String::from("expensive data");
        let result = process_data(&expensive_data);
        
        // 在不需要 expensive_data 后立即释放
        // Release expensive_data immediately when no longer needed
        drop(expensive_data);
        
        println!("Processed result: {}", result);
        
        // 使用块作用域进行精确控制
        // Use block scope for precise control
        let final_result = {
            let temp_data = String::from("temporary");
            let processed = process_data(&temp_data);
            // temp_data 在这里自动释放
            // temp_data is automatically released here
            processed
        };
        
        println!("Final result: {}", final_result);
    }

    /// 处理数据 / Process data
    fn process_data(data: &str) -> String {
        format!("Processed: {}", data)
    }
}

/// # 5. 增强的并发安全特性 / Enhanced Concurrency Safety Features

/// 演示 Rust 1.90 中增强的并发安全特性
/// Demonstrates enhanced concurrency safety features in Rust 1.90
pub mod enhanced_concurrency_safety {
    use super::*;

    /// 高级并发模式示例 / Advanced Concurrency Pattern Example
    pub fn advanced_concurrency_patterns() {
        println!("=== 高级并发模式 / Advanced Concurrency Patterns ===");
        
        // 使用读写锁进行并发控制
        // Use read-write lock for concurrency control
        let rw_data = Arc::new(RwLock::new(vec![1, 2, 3, 4, 5]));
        
        // 创建多个读线程
        // Create multiple reader threads
        let mut reader_handles = vec![];
        for i in 0..3 {
            let data_clone = Arc::clone(&rw_data);
            let handle = thread::spawn(move || {
                let data = data_clone.read().unwrap();
                println!("Reader {} read: {:?}", i, *data);
            });
            reader_handles.push(handle);
        }
        
        // 创建写线程
        // Create writer thread
        let writer_data = Arc::clone(&rw_data);
        let writer_handle = thread::spawn(move || {
            let mut data = writer_data.write().unwrap();
            data.push(6);
            println!("Writer added 6");
        });
        
        // 等待所有线程完成
        // Wait for all threads to complete
        for handle in reader_handles {
            handle.join().unwrap();
        }
        writer_handle.join().unwrap();
        
        // 使用原子操作
        // Use atomic operations
        let counter = Arc::new(AtomicUsize::new(0));
        let mut atomic_handles = vec![];
        
        for i in 0..5 {
            let counter_clone = Arc::clone(&counter);
            let handle = thread::spawn(move || {
                for _ in 0..1000 {
                    counter_clone.fetch_add(1, Ordering::SeqCst);
                }
                println!("Atomic thread {} finished", i);
            });
            atomic_handles.push(handle);
        }
        
        for handle in atomic_handles {
            handle.join().unwrap();
        }
        
        println!("Final atomic counter value: {}", counter.load(Ordering::SeqCst));
    }

    /// 数据竞争检测示例 / Data Race Detection Example
    pub fn data_race_detection() {
        println!("=== 数据竞争检测 / Data Race Detection ===");
        
        let shared_data = Arc::new(Mutex::new(vec![1, 2, 3]));
        let mut handles = vec![];
        
        for i in 0..3 {
            let data_clone = Arc::clone(&shared_data);
            let handle = thread::spawn(move || {
                let mut data = data_clone.lock().unwrap();
                data.push(i);
                println!("Thread {} added {}", i, i);
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        println!("Final data: {:?}", *shared_data.lock().unwrap());
    }
}

/// # 6. 智能内存管理特性 / Smart Memory Management Features

/// 演示 Rust 1.90 中智能内存管理特性
/// Demonstrates smart memory management features in Rust 1.90
pub mod smart_memory_management {

    /// 智能内存分配示例 / Smart Memory Allocation Example
    pub fn smart_memory_allocation() {
        println!("=== 智能内存分配 / Smart Memory Allocation ===");
        
        // 使用 Box 进行堆分配
        // Use Box for heap allocation
        let heap_data = Box::new([1, 2, 3, 4, 5]);
        println!("Heap allocated data: {:?}", heap_data);
        
        // 使用 Vec 进行动态分配
        // Use Vec for dynamic allocation
        let mut dynamic_data = Vec::with_capacity(10);
        for i in 1..=10 {
            dynamic_data.push(i * i);
        }
        println!("Dynamic data: {:?}", dynamic_data);
        
        // 内存预分配
        // Memory pre-allocation
        let mut preallocated = Vec::with_capacity(1000);
        for i in 0..1000 {
            preallocated.push(i);
        }
        println!("Preallocated data length: {}", preallocated.len());
        
        // 内存重用
        // Memory reuse
        preallocated.clear();
        preallocated.shrink_to_fit();
        println!("After clear and shrink: capacity = {}", preallocated.capacity());
    }

    /// 内存对齐优化示例 / Memory Alignment Optimization Example
    pub fn memory_alignment_optimization() {
        println!("=== 内存对齐优化 / Memory Alignment Optimization ===");
        
        // 内存对齐
        // Memory alignment
        #[repr(align(64))]
        struct AlignedData {
            value: i32,
        }
        
        let aligned = AlignedData { value: 42 };
        println!("Aligned data value: {}", aligned.value);
        
        // 零成本抽象
        // Zero-cost abstractions
        let zero_cost_data = (0..1000)
            .map(|x| x * x)
            .filter(|&x| x % 2 == 0)
            .collect::<Vec<_>>();
        println!("Zero-cost processed data length: {}", zero_cost_data.len());
    }
}

/// # 7. 改进的错误处理特性 / Improved Error Handling Features

/// 演示 Rust 1.90 中改进的错误处理特性
/// Demonstrates improved error handling features in Rust 1.90
pub mod improved_error_handling {

    /// 高级错误处理示例 / Advanced Error Handling Example
    pub fn advanced_error_handling() {
        println!("=== 高级错误处理 / Advanced Error Handling ===");
        
        // 自定义错误类型
        // Custom error types
        #[derive(Debug)]
        enum MathError {
            DivisionByZero,
            NegativeSquareRoot,
            #[allow(dead_code)]
            Overflow,
        }
        
        impl std::fmt::Display for MathError {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                match self {
                    MathError::DivisionByZero => write!(f, "Division by zero"),
                    MathError::NegativeSquareRoot => write!(f, "Negative square root"),
                    MathError::Overflow => write!(f, "Arithmetic overflow"),
                }
            }
        }
        
        impl std::error::Error for MathError {}
        
        // 使用自定义错误类型
        // Use custom error types
        fn safe_divide(a: i32, b: i32) -> Result<i32, MathError> {
            if b == 0 {
                Err(MathError::DivisionByZero)
            } else {
                Ok(a / b)
            }
        }
        
        fn safe_sqrt(x: f64) -> Result<f64, MathError> {
            if x < 0.0 {
                Err(MathError::NegativeSquareRoot)
            } else {
                Ok(x.sqrt())
            }
        }
        
        // 错误链
        // Error chaining
        fn complex_calculation(a: i32, b: i32, c: f64) -> Result<f64, MathError> {
            let division_result = safe_divide(a, b)?;
            let sqrt_result = safe_sqrt(c)?;
            Ok(division_result as f64 + sqrt_result)
        }
        
        // 测试错误处理
        // Test error handling
        match complex_calculation(10, 2, 16.0) {
            Ok(result) => println!("Complex calculation result: {}", result),
            Err(error) => println!("Complex calculation error: {}", error),
        }
        
        match complex_calculation(10, 0, 16.0) {
            Ok(result) => println!("Complex calculation result: {}", result),
            Err(error) => println!("Complex calculation error: {}", error),
        }
        
        match complex_calculation(10, 2, -16.0) {
            Ok(result) => println!("Complex calculation result: {}", result),
            Err(error) => println!("Complex calculation error: {}", error),
        }
    }

    /// 错误恢复示例 / Error Recovery Example
    pub fn error_recovery() {
        println!("=== 错误恢复 / Error Recovery ===");
        
        fn divide_with_fallback(a: i32, b: i32) -> i32 {
            if b == 0 {
                println!("Division by zero, using fallback value");
                0
            } else {
                a / b
            }
        }
        
        let result1 = divide_with_fallback(10, 2);
        let result2 = divide_with_fallback(10, 0);
        
        println!("Result 1: {}, Result 2: {}", result1, result2);
    }
}

/// # 8. 性能优化特性 / Performance Optimization Features

/// 演示 Rust 1.90 中性能优化特性
/// Demonstrates performance optimization features in Rust 1.90
pub mod performance_optimization {

    /// 内联优化示例 / Inline Optimization Example
    pub fn inline_optimization() {
        println!("=== 内联优化 / Inline Optimization ===");
        
        // 内联优化
        // Inline optimization
        #[inline(always)]
        fn fast_add(a: i32, b: i32) -> i32 {
            a + b
        }
        
        #[inline(never)]
        fn slow_complex_calculation(x: i32) -> i32 {
            // 模拟复杂计算
            // Simulate complex calculation
            let mut result = x;
            for i in 0..1000 {
                result = (result * i) % 1000;
            }
            result
        }
        
        // 使用内联函数
        // Use inline functions
        let result1 = fast_add(10, 20);
        let result2 = slow_complex_calculation(42);
        println!("Fast add result: {}, Slow calculation result: {}", result1, result2);
    }

    /// 内存访问优化示例 / Memory Access Optimization Example
    pub fn memory_access_optimization() {
        println!("=== 内存访问优化 / Memory Access Optimization ===");
        
        // 内存访问优化
        // Memory access optimization
        let mut matrix = vec![vec![0; 100]; 100];
        
        // 按行访问（缓存友好）
        // Row-wise access (cache-friendly)
        for i in 0..100 {
            for j in 0..100 {
                matrix[i][j] = i * j;
            }
        }
        
        // 按列访问（缓存不友好）
        // Column-wise access (cache-unfriendly)
        let mut sum = 0;
        for j in 0..100 {
            for i in 0..100 {
                sum += matrix[i][j];
            }
        }
        println!("Matrix sum: {}", sum);
    }

    /// 分支预测优化示例 / Branch Prediction Optimization Example
    pub fn branch_prediction_optimization() {
        println!("=== 分支预测优化 / Branch Prediction Optimization ===");
        
        // 分支预测优化
        // Branch prediction optimization
        let sorted_data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let mut count = 0;
        
        for &value in &sorted_data {
            if value > 5 { // 分支预测友好
                count += 1;
            }
        }
        println!("Count of values > 5: {}", count);
    }
}

/// 主函数 / Main Function
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Rust 1.90 全面特性示例 / Rust 1.90 Comprehensive Features Examples ===");
    
    // 1. 改进的借用检查器特性 / Improved Borrow Checker Features
    improved_borrow_checker::complex_borrowing_patterns();
    improved_borrow_checker::smart_borrow_analysis();
    
    // 2. 增强的生命周期推断特性 / Enhanced Lifetime Inference Features
    enhanced_lifetime_inference::automatic_lifetime_inference();
    enhanced_lifetime_inference::struct_lifetime_inference();
    
    // 3. 新的智能指针特性 / New Smart Pointer Features
    new_smart_pointer_features::advanced_smart_pointer_patterns();
    new_smart_pointer_features::smart_pointer_optimization();
    
    // 4. 优化的作用域管理特性 / Optimized Scope Management Features
    optimized_scope_management::precise_scope_control();
    optimized_scope_management::scope_optimization();
    
    // 5. 增强的并发安全特性 / Enhanced Concurrency Safety Features
    enhanced_concurrency_safety::advanced_concurrency_patterns();
    enhanced_concurrency_safety::data_race_detection();
    
    // 6. 智能内存管理特性 / Smart Memory Management Features
    smart_memory_management::smart_memory_allocation();
    smart_memory_management::memory_alignment_optimization();
    
    // 7. 改进的错误处理特性 / Improved Error Handling Features
    improved_error_handling::advanced_error_handling();
    improved_error_handling::error_recovery();
    
    // 8. 性能优化特性 / Performance Optimization Features
    performance_optimization::inline_optimization();
    performance_optimization::memory_access_optimization();
    performance_optimization::branch_prediction_optimization();
    
    println!("\n=== 所有 Rust 1.90 特性示例运行完成 / All Rust 1.90 Features Examples Completed ===");
    
    Ok(())
}
