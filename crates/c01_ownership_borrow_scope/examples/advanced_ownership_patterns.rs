//! # 高级所有权模式示例 / Advanced Ownership Patterns Examples
//!
//! 本示例展示了 Rust 中高级的所有权模式，包括复杂的所有权转移、借用模式和生命周期管理。
//! This example demonstrates advanced ownership patterns in Rust, including complex ownership transfers, borrowing patterns, and lifetime management.

//use c01_ownership_borrow_scope::*;
//use std::time::Duration;

/// # 1. 复杂所有权转移模式 / Complex Ownership Transfer Patterns
/// 
/// 展示复杂场景下的所有权转移和生命周期管理。
/// Demonstrates ownership transfer and lifetime management in complex scenarios.

pub mod complex_ownership_transfer {
    //use super::*;

    /// ## 1.1 所有权链式转移 / Ownership Chain Transfer
    /// 
    /// 展示所有权在多个函数间的链式转移。
    /// Demonstrates chain transfer of ownership across multiple functions.

    /// 所有权链式转移示例 / Ownership Chain Transfer Example
    pub fn ownership_chain_transfer() {
        let data = String::from("initial data");
        println!("Initial data: {}", data);
        
        // 所有权链式转移
        // Ownership chain transfer
        let processed_data = process_data_chain(data);
        println!("Processed data: {}", processed_data);
        
        // 进一步处理
        // Further processing
        let final_data = finalize_data(processed_data);
        println!("Final data: {}", final_data);
    }

    /// 数据处理函数1 / Data processing function 1
    fn process_data_chain(data: String) -> String {
        println!("Processing data: {}", data);
        let mut processed = data;
        processed.push_str(" - processed");
        processed
    }

    /// 数据处理函数2 / Data processing function 2
    fn finalize_data(data: String) -> String {
        println!("Finalizing data: {}", data);
        let mut finalized = data;
        finalized.push_str(" - finalized");
        finalized
    }

    /// ## 1.2 条件所有权转移 / Conditional Ownership Transfer
    /// 
    /// 根据条件决定是否转移所有权。
    /// Decide whether to transfer ownership based on conditions.

    /// 条件所有权转移示例 / Conditional Ownership Transfer Example
    pub fn conditional_ownership_transfer() {
        let data = String::from("test data");
        
        // 根据条件决定所有权转移
        // Decide ownership transfer based on conditions
        let result = if data.len() > 5 {
            process_large_data(data)
        } else {
            process_small_data(data)
        };
        
        println!("Result: {}", result);
    }

    /// 处理大数据 / Process large data
    fn process_large_data(data: String) -> String {
        println!("Processing large data: {}", data);
        data.to_uppercase()
    }

    /// 处理小数据 / Process small data
    fn process_small_data(data: String) -> String {
        println!("Processing small data: {}", data);
        data.to_lowercase()
    }

    /// ## 1.3 所有权回退模式 / Ownership Fallback Pattern
    /// 
    /// 在所有权转移失败时提供回退机制。
    /// Provide fallback mechanism when ownership transfer fails.

    /// 所有权回退模式示例 / Ownership Fallback Pattern Example
    pub fn ownership_fallback_pattern() {
        let data = String::from("fallback test");
        
        // 尝试所有权转移，失败时使用回退
        // Try ownership transfer, use fallback on failure
        let result = try_process_data(data).unwrap_or_else(|_| {
            String::from("fallback data")
        });
        
        println!("Result: {}", result);
    }

    /// 尝试处理数据 / Try to process data
    fn try_process_data(data: String) -> Result<String, String> {
        if data.len() > 10 {
            Ok(data.to_uppercase())
        } else {
            Err("Data too short".to_string())
        }
    }
}

/// # 2. 高级借用模式 / Advanced Borrowing Patterns
/// 
/// 展示复杂场景下的借用模式和借用检查器优化。
/// Demonstrates borrowing patterns and borrow checker optimizations in complex scenarios.

pub mod advanced_borrowing_patterns {
    //use super::*;

    /// ## 2.1 借用链模式 / Borrowing Chain Pattern
    /// 
    /// 展示多个借用之间的链式关系。
    /// Demonstrates chain relationships between multiple borrows.

    /// 借用链模式示例 / Borrowing Chain Pattern Example
    pub fn borrowing_chain_pattern() {
        let mut data = vec![1, 2, 3, 4, 5];
        
        // 创建借用链
        // Create borrowing chain
        let first_borrow = &data[0];
        let second_borrow = &data[1];
        let third_borrow = &data[2];
        
        // 使用借用链
        // Use borrowing chain
        println!("First: {}, Second: {}, Third: {}", 
                 first_borrow, second_borrow, third_borrow);
        
        // 借用链结束后可以修改数据
        // Can modify data after borrowing chain ends
        data.push(6);
        println!("After push: {:?}", data);
    }

    /// ## 2.2 借用作用域优化 / Borrowing Scope Optimization
    /// 
    /// 通过作用域优化借用模式。
    /// Optimize borrowing patterns through scopes.

    /// 借用作用域优化示例 / Borrowing Scope Optimization Example
    pub fn borrowing_scope_optimization() {
        let mut data = vec![1, 2, 3, 4, 5];
        
        // 使用作用域限制借用
        // Use scopes to limit borrows
        {
            let borrow1 = &data[0];
            let borrow2 = &data[1];
            println!("Borrows: {}, {}", borrow1, borrow2);
        } // 借用结束 / Borrows end
        
        // 现在可以修改数据
        // Now can modify data
        data.push(6);
        println!("After modification: {:?}", data);
    }

    /// ## 2.3 借用模式匹配 / Borrowing Pattern Matching
    /// 
    /// 使用模式匹配进行借用。
    /// Use pattern matching for borrowing.

    /// 借用模式匹配示例 / Borrowing Pattern Matching Example
    pub fn borrowing_pattern_matching() {
        let data = vec![Some(1), Some(2), None, Some(4)];
        
        // 使用模式匹配进行借用
        // Use pattern matching for borrowing
        for item in &data {
            match item {
                Some(value) => println!("Value: {}", value),
                None => println!("No value"),
            }
        }
    }
}

/// # 3. 复杂生命周期管理 / Complex Lifetime Management
/// 
/// 展示复杂场景下的生命周期管理和约束。
/// Demonstrates lifetime management and constraints in complex scenarios.

pub mod complex_lifetime_management {
    //use super::*;

    /// ## 3.1 多生命周期参数 / Multiple Lifetime Parameters
    /// 
    /// 使用多个生命周期参数管理复杂的关系。
    /// Use multiple lifetime parameters to manage complex relationships.

    /// 多生命周期参数示例 / Multiple Lifetime Parameters Example
    pub fn multiple_lifetime_parameters() {
        let s1 = String::from("first string");
        let s2 = String::from("second string");
        
        // 使用多生命周期参数
        // Use multiple lifetime parameters
        let result = longest_of_three(&s1, &s2, "third string");
        println!("Longest: {}", result);
    }

    /// 三个字符串中最长的 / Longest of three strings
    fn longest_of_three<'a, 'b>(x: &'a str, y: &'b str, z: &'b str) -> &'b str 
    where
        'a: 'b,
    {
        if x.len() > y.len() && x.len() > z.len() {
            x
        } else if y.len() > z.len() {
            y
        } else {
            z
        }
    }

    /// ## 3.2 生命周期约束 / Lifetime Constraints
    /// 
    /// 使用生命周期约束管理复杂的关系。
    /// Use lifetime constraints to manage complex relationships.

    /// 生命周期约束示例 / Lifetime Constraints Example
    pub fn lifetime_constraints() {
        let data = vec![1, 2, 3, 4, 5];
        let result = process_with_constraints(&data);
        println!("Result: {:?}", result);
    }

    /// 使用约束处理数据 / Process data with constraints
    fn process_with_constraints<'a>(data: &'a [i32]) -> Vec<&'a i32> {
        data.iter().filter(|&&x| x > 2).collect()
    }

    /// ## 3.3 生命周期推断优化 / Lifetime Inference Optimization
    /// 
    /// 利用编译器生命周期推断优化。
    /// Leverage compiler lifetime inference optimization.

    /// 生命周期推断优化示例 / Lifetime Inference Optimization Example
    pub fn lifetime_inference_optimization() {
        let data = vec![1, 2, 3, 4, 5];
        
        // 让编译器推断生命周期
        // Let compiler infer lifetimes
        let result = process_data_optimized(&data);
        println!("Optimized result: {:?}", result);
    }

    /// 优化的数据处理 / Optimized data processing
    fn process_data_optimized(data: &[i32]) -> Vec<&i32> {
        data.iter().filter(|&&x| x > 2).collect()
    }
}

/// # 4. 智能指针高级模式 / Smart Pointer Advanced Patterns
/// 
/// 展示智能指针的高级使用模式。
/// Demonstrates advanced usage patterns of smart pointers.

pub mod smart_pointer_advanced_patterns {
    use std::rc::Rc;
    use std::cell::RefCell;
    use std::sync::{Arc, Mutex};
    use std::thread;

    /// ## 4.1 引用计数循环 / Reference Counting Cycles
    /// 
    /// 展示引用计数循环的处理。
    /// Demonstrates handling of reference counting cycles.

    /// 引用计数循环示例 / Reference Counting Cycles Example
    pub fn reference_counting_cycles() {
        let data = Rc::new(RefCell::new(vec![1, 2, 3]));
        let data_clone1 = Rc::clone(&data);
        let data_clone2 = Rc::clone(&data);
        
        // 通过 RefCell 实现内部可变性
        // Implement interior mutability through RefCell
        data_clone1.borrow_mut().push(4);
        data_clone2.borrow_mut().push(5);
        
        println!("Data: {:?}", data.borrow());
        println!("Reference count: {}", Rc::strong_count(&data));
    }

    /// ## 4.2 智能指针组合 / Smart Pointer Composition
    /// 
    /// 展示智能指针的组合使用。
    /// Demonstrates composition of smart pointers.

    /// 智能指针组合示例 / Smart Pointer Composition Example
    pub fn smart_pointer_composition() {
        // 使用 Arc<Mutex<T>> 进行线程安全共享
        // Use Arc<Mutex<T>> for thread-safe sharing
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
        
        println!("Final data: {:?}", shared_data.lock().unwrap());
    }

    /// ## 4.3 智能指针生命周期管理 / Smart Pointer Lifetime Management
    /// 
    /// 展示智能指针的生命周期管理。
    /// Demonstrates lifetime management of smart pointers.

    /// 智能指针生命周期管理示例 / Smart Pointer Lifetime Management Example
    pub fn smart_pointer_lifetime_management() {
        let data = Rc::new(RefCell::new(String::from("initial")));
        
        // 在作用域内使用智能指针
        // Use smart pointer within scope
        {
            let data_clone = Rc::clone(&data);
            data_clone.borrow_mut().push_str(" - modified");
            println!("Modified data: {}", data_clone.borrow());
        } // data_clone 离开作用域 / data_clone goes out of scope
        
        println!("Final data: {}", data.borrow());
        println!("Reference count: {}", Rc::strong_count(&data));
    }
}

/// # 5. 并发所有权模式 / Concurrent Ownership Patterns
/// 
/// 展示并发环境下的所有权管理。
/// Demonstrates ownership management in concurrent environments.

pub mod concurrent_ownership_patterns {
    use std::sync::{Arc, Mutex};
    use std::thread;

    /// ## 5.1 线程间所有权转移 / Inter-thread Ownership Transfer
    /// 
    /// 展示线程间的所有权转移。
    /// Demonstrates ownership transfer between threads.

    /// 线程间所有权转移示例 / Inter-thread Ownership Transfer Example
    pub fn inter_thread_ownership_transfer() {
        let data = Arc::new(Mutex::new(vec![1, 2, 3]));
        let mut handles = vec![];
        
        for i in 0..3 {
            let data_clone = Arc::clone(&data);
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
        
        println!("Final data: {:?}", data.lock().unwrap());
    }

    /// ## 5.2 异步所有权管理 / Async Ownership Management
    /// 
    /// 展示异步环境下的所有权管理。
    /// Demonstrates ownership management in async environments.

    /// 异步所有权管理示例 / Async Ownership Management Example
    pub fn async_ownership_management() {
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            let data = Arc::new(Mutex::new(vec![1, 2, 3]));
            
            // 异步任务中的所有权管理
            // Ownership management in async tasks
            let data_clone = Arc::clone(&data);
            let task = tokio::spawn(async move {
                let mut data = data_clone.lock().unwrap();
                data.push(4);
                println!("Async task added 4");
            });
            
            task.await.unwrap();
            println!("Final data: {:?}", data.lock().unwrap());
        });
    }

    /// ## 5.3 锁竞争优化 / Lock Contention Optimization
    /// 
    /// 展示锁竞争的优化策略。
    /// Demonstrates lock contention optimization strategies.

    /// 锁竞争优化示例 / Lock Contention Optimization Example
    pub fn lock_contention_optimization() {
        let data = Arc::new(Mutex::new(0));
        let mut handles = vec![];
        
        for _ in 0..10 {
            let data_clone = Arc::clone(&data);
            let handle = thread::spawn(move || {
                // 使用 try_lock 避免阻塞
                // Use try_lock to avoid blocking
                if let Ok(mut num) = data_clone.try_lock() {
                    *num += 1;
                    println!("Incremented to {}", *num);
                } else {
                    println!("Failed to acquire lock");
                }
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        println!("Final value: {}", *data.lock().unwrap());
    }
}

/// # 6. 性能优化模式 / Performance Optimization Patterns
/// 
/// 展示所有权系统的性能优化模式。
/// Demonstrates performance optimization patterns of the ownership system.

pub mod performance_optimization_patterns {

    /// ## 6.1 零成本抽象优化 / Zero-cost Abstraction Optimization
    /// 
    /// 展示零成本抽象的优化。
    /// Demonstrates optimization of zero-cost abstractions.

    /// 零成本抽象优化示例 / Zero-cost Abstraction Optimization Example
    pub fn zero_cost_abstraction_optimization() {
        let numbers = vec![1, 2, 3, 4, 5];
        
        // 使用迭代器链进行零成本抽象
        // Use iterator chains for zero-cost abstractions
        let result: Vec<i32> = numbers
            .iter()
            .map(|x| x * 2)
            .filter(|&x| x > 5)
            .collect();
        
        println!("Optimized result: {:?}", result);
    }

    /// ## 6.2 内存布局优化 / Memory Layout Optimization
    /// 
    /// 展示内存布局的优化。
    /// Demonstrates memory layout optimization.

    /// 内存布局优化示例 / Memory Layout Optimization Example
    pub fn memory_layout_optimization() {
        // 使用 #[repr(C)] 优化内存布局
        // Use #[repr(C)] to optimize memory layout
        #[repr(C)]
        struct OptimizedStruct {
            a: u8,
            b: u32,
            c: u8,
            d: u16,
        }

        let _s = OptimizedStruct { a: 1, b: 2, c: 3, d: 4 };
        println!("Size: {}", std::mem::size_of::<OptimizedStruct>());
        println!("Alignment: {}", std::mem::align_of::<OptimizedStruct>());
    }

    /// ## 6.3 借用检查器优化 / Borrow Checker Optimization
    /// 
    /// 展示借用检查器的优化。
    /// Demonstrates borrow checker optimization.

    /// 借用检查器优化示例 / Borrow Checker Optimization Example
    pub fn borrow_checker_optimization() {
        let mut data = vec![1, 2, 3, 4, 5];
        
        // 使用作用域优化借用
        // Use scopes to optimize borrowing
        {
            let borrow1 = &data[0];
            let borrow2 = &data[1];
            println!("Borrows: {}, {}", borrow1, borrow2);
        } // 借用结束 / Borrows end
        
        // 现在可以修改数据
        // Now can modify data
        data.push(6);
        println!("After modification: {:?}", data);
    }
}

/// # 主要功能函数 / Main Function Functions

/// 运行所有高级所有权模式示例 / Run all advanced ownership pattern examples
pub fn run_all_advanced_ownership_examples() {
    println!("=== 高级所有权模式示例 / Advanced Ownership Patterns Examples ===");
    
    println!("\n1. 复杂所有权转移模式 / Complex Ownership Transfer Patterns");
    complex_ownership_transfer::ownership_chain_transfer();
    complex_ownership_transfer::conditional_ownership_transfer();
    complex_ownership_transfer::ownership_fallback_pattern();
    
    println!("\n2. 高级借用模式 / Advanced Borrowing Patterns");
    advanced_borrowing_patterns::borrowing_chain_pattern();
    advanced_borrowing_patterns::borrowing_scope_optimization();
    advanced_borrowing_patterns::borrowing_pattern_matching();
    
    println!("\n3. 复杂生命周期管理 / Complex Lifetime Management");
    complex_lifetime_management::multiple_lifetime_parameters();
    complex_lifetime_management::lifetime_constraints();
    complex_lifetime_management::lifetime_inference_optimization();
    
    println!("\n4. 智能指针高级模式 / Smart Pointer Advanced Patterns");
    smart_pointer_advanced_patterns::reference_counting_cycles();
    smart_pointer_advanced_patterns::smart_pointer_composition();
    smart_pointer_advanced_patterns::smart_pointer_lifetime_management();
    
    println!("\n5. 并发所有权模式 / Concurrent Ownership Patterns");
    concurrent_ownership_patterns::inter_thread_ownership_transfer();
    concurrent_ownership_patterns::async_ownership_management();
    concurrent_ownership_patterns::lock_contention_optimization();
    
    println!("\n6. 性能优化模式 / Performance Optimization Patterns");
    performance_optimization_patterns::zero_cost_abstraction_optimization();
    performance_optimization_patterns::memory_layout_optimization();
    performance_optimization_patterns::borrow_checker_optimization();
    
    println!("\n=== 所有高级所有权模式示例运行完成 / All Advanced Ownership Pattern Examples Completed ===");
}

/// 获取高级所有权模式信息 / Get Advanced Ownership Pattern Information
pub fn get_advanced_ownership_info() -> &'static str {
    "Advanced Ownership Patterns - Complex ownership transfers, advanced borrowing patterns, and sophisticated lifetime management"
}

/// 主函数 / Main Function
fn main() {
    println!("高级所有权模式示例程序 / Advanced Ownership Patterns Example Program");
    println!("================================================");
    
    // 运行所有示例
    // Run all examples
    run_all_advanced_ownership_examples();
    
    println!("\n程序执行完成 / Program execution completed");
}
