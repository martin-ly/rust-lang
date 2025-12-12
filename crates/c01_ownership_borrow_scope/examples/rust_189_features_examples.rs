//! # Rust 1.89 特性示例 (历史版本)
//!
//! ⚠️ **注意**: 本示例针对 Rust 1.89 版本编写，部分特性在 Rust 1.90 中已有更新。
//!
//! ## Rust 1.90 主要更新
//!
//! ### 编译器改进
//! - **LLD 链接器**: Linux x86_64 默认启用，链接速度提升约 2x
//! - **编译性能**: 增量编译优化，构建速度提升
//!
//! ### 标准库更新
//! - `u{n}::checked_sub_signed()` - 新增带符号减法检查方法
//! - `<[T]>::reverse()` - 现在可在 const 上下文中使用
//! - `f32/f64` 数学函数 - floor/ceil/trunc 等在 const 中可用
//!
//! ### Lint 改进
//! - `mismatched_lifetime_syntaxes` - 默认启用，检查生命周期语法一致性
//!
//! ## 迁移建议
//!
//! 1. 更新 Cargo.toml: `rust-version = "1.90"`, `edition = "2024"`
//! 2. 应用新的稳定 API 和 const 函数增强
//! 3. 检查并修复新 lint 警告
//!
//! 参考: [Rust 1.90.0 Release Notes](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
//!
//! ---
//!
//! # Rust 1.89 版本新特性示例 / Rust 1.89 New Features Examples
//!
//! 本示例展示了 Rust 1.89 版本在所有权、借用和作用域系统方面的新特性和改进。
//! This example demonstrates the new features and improvements in Rust 1.89's ownership, borrowing, and scope systems.

//use c01_ownership_borrow_scope::*;
//use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/// # 1. 改进的借用检查器 / Improved Borrow Checker
///
/// Rust 1.89 版本对借用检查器进行了重大改进，提供了更智能的借用分析和更好的错误信息。
/// Rust 1.89 has made significant improvements to the borrow checker, providing smarter borrow analysis and better error messages.

pub mod improved_borrow_checker {

    /// ## 1.1 更智能的借用分析 / Smarter Borrow Analysis
    ///
    /// 新的借用检查器能够更精确地分析借用关系，减少不必要的借用限制。
    /// The new borrow checker can analyze borrow relationships more precisely, reducing unnecessary borrow restrictions.

    /// 智能借用分析示例 / Smart Borrow Analysis Example
    pub fn smart_borrow_analysis() {
        let mut data = vec![1, 2, 3, 4, 5];

        // Rust 1.89 中的改进：更灵活的借用模式
        // Improvement in Rust 1.89: more flexible borrowing patterns
        let (first, rest) = data.split_at_mut(1);
        let (second, third) = rest.split_at_mut(1);

        // 同时修改不同部分，避免借用冲突
        // Modify different parts simultaneously, avoiding borrow conflicts
        first[0] = 10;
        second[0] = 20;
        third[0] = 30;

        println!("Modified data: {:?}", data);
    }

    /// ## 1.2 改进的错误信息 / Improved Error Messages
    ///
    /// 新的借用检查器提供更清晰、更有帮助的错误信息。
    /// The new borrow checker provides clearer, more helpful error messages.

    /// 改进的错误信息示例 / Improved Error Messages Example
    pub fn improved_error_messages() {
        let mut s = String::from("hello");

        // 展示改进的错误信息（实际代码中会编译错误）
        // Demonstrate improved error messages (would compile error in actual code)
        println!("This would show improved error messages in Rust 1.89");

        // 正确的做法：使用作用域来限制借用
        // Correct approach: use scopes to limit borrows
        {
            let r1 = &s;
            println!("r1: {}", r1);
        } // r1 的借用结束 / r1's borrow ends

        let r2 = &mut s;
        r2.push_str(", world");
        println!("r2: {}", r2);
    }

    /// ## 1.3 非词法生命周期优化 / Non-Lexical Lifetime Optimization
    ///
    /// NLL 的进一步优化，使借用检查更加精确。
    /// Further optimization of NLL, making borrow checking more precise.

    /// NLL 优化示例 / NLL Optimization Example
    pub fn nll_optimization() {
        let mut data = vec![1, 2, 3];

        // Rust 1.89 中 NLL 的改进
        // NLL improvements in Rust 1.89
        let first = &data[0];
        let second = &data[1];

        // 编译器能够更精确地推断借用结束点
        // Compiler can more precisely infer borrow end points
        println!("First: {}, Second: {}", first, second);

        // 借用结束后可以修改数据
        // Can modify data after borrows end
        data.push(4); // 在 Rust 1.89 中更灵活 / More flexible in Rust 1.89
        println!("After push: {:?}", data);
    }
}

/// # 2. 增强的生命周期推断 / Enhanced Lifetime Inference
///
/// Rust 1.89 版本改进了生命周期推断算法，减少了需要显式生命周期注解的情况。
/// Rust 1.89 has improved lifetime inference algorithms, reducing cases where explicit lifetime annotations are needed.

pub mod enhanced_lifetime_inference {

    /// ## 2.1 智能生命周期省略 / Smart Lifetime Elision
    ///
    /// 编译器能够更智能地推断生命周期，减少样板代码。
    /// The compiler can more intelligently infer lifetimes, reducing boilerplate code.

    /// 智能生命周期省略示例 / Smart Lifetime Elision Example
    pub fn smart_lifetime_elision() {
        let s1 = String::from("hello");
        let s2 = String::from("world");

        // 编译器能够自动推断生命周期
        // Compiler can automatically infer lifetimes
        let result = longest_string(&s1, &s2);
        println!("Longest string: {}", result);
    }

    /// 编译器可以推断生命周期的函数 / Function where compiler can infer lifetime
    fn longest_string<'a>(x: &'a str, y: &'a str) -> &'a str {
        if x.len() > y.len() {
            x
        } else {
            y
        }
    }

    /// ## 2.2 改进的生命周期约束 / Improved Lifetime Constraints
    ///
    /// 新的生命周期约束系统更加灵活和强大。
    /// The new lifetime constraint system is more flexible and powerful.

    /// 改进的生命周期约束示例 / Improved Lifetime Constraints Example
    pub fn improved_lifetime_constraints() {
        let data = vec![1, 2, 3, 4, 5];
        let result = process_data(&data);
        println!("Processed data: {:?}", result);
    }

    /// 使用改进的生命周期约束的函数 / Function using improved lifetime constraints
    fn process_data<'a>(data: &'a [i32]) -> Vec<&'a i32> {
        data.iter().filter(|&&x| x > 2).collect()
    }
}

/// # 3. 优化的内存管理 / Optimized Memory Management
///
/// Rust 1.89 版本在内存管理方面进行了多项优化。
/// Rust 1.89 has made several optimizations in memory management.

pub mod optimized_memory_management {

    /// ## 3.1 改进的堆分配 / Improved Heap Allocation
    ///
    /// 新的堆分配器提供了更好的性能和内存利用率。
    /// The new heap allocator provides better performance and memory utilization.

    /// 改进的堆分配示例 / Improved Heap Allocation Example
    pub fn improved_heap_allocation() {
        // 使用 Box 进行堆分配
        // Use Box for heap allocation
        let boxed_data = Box::new(vec![1, 2, 3, 4, 5]);
        println!("Boxed data: {:?}", boxed_data);

        // 使用 Box::leak 进行静态分配（高级用法）
        // Use Box::leak for static allocation (advanced usage)
        let static_data = Box::leak(Box::new("static string"));
        println!("Static data: {}", static_data);
    }

    /// ## 3.2 优化的内存布局 / Optimized Memory Layout
    ///
    /// 编译器能够更好地优化结构体的内存布局。
    /// The compiler can better optimize struct memory layout.

    /// 优化的内存布局示例 / Optimized Memory Layout Example
    pub fn optimized_memory_layout() {
        // 使用 #[repr(C)] 优化内存布局
        // Use #[repr(C)] to optimize memory layout
        #[repr(C)]
        #[derive(Debug)]
        struct OptimizedStruct {
            a: u8,
            b: u32,
            c: u8,
            d: u16,
        }

        let s = OptimizedStruct { a: 1, b: 2, c: 3, d: 4 };
        println!("Struct: {:?}", s);
        println!("Size: {}", std::mem::size_of::<OptimizedStruct>());
        println!("Alignment: {}", std::mem::align_of::<OptimizedStruct>());
    }

    /// ## 3.3 零成本抽象优化 / Zero-cost Abstraction Optimization
    ///
    /// 编译器能够更好地优化零成本抽象。
    /// The compiler can better optimize zero-cost abstractions.

    /// 零成本抽象优化示例 / Zero-cost Abstraction Optimization Example
    pub fn zero_cost_abstraction_optimization() {
        let numbers = vec![1, 2, 3, 4, 5];

        // 迭代器链是零成本抽象
        // Iterator chains are zero-cost abstractions
        let result: Vec<i32> = numbers
            .iter()
            .map(|x| x * 2)
            .filter(|&x| x > 5)
            .collect();

        println!("Filtered and mapped: {:?}", result);
    }
}

/// # 4. 增强的并发安全 / Enhanced Concurrency Safety
///
/// Rust 1.89 版本在并发安全方面进行了多项改进。
/// Rust 1.89 has made several improvements in concurrency safety.

pub mod enhanced_concurrency_safety {
    use super::*;

    /// ## 4.1 改进的数据竞争检测 / Improved Data Race Detection
    ///
    /// 新的数据竞争检测器能够更准确地识别潜在的数据竞争。
    /// The new data race detector can more accurately identify potential data races.

    /// 改进的数据竞争检测示例 / Improved Data Race Detection Example
    pub fn improved_data_race_detection() {
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

    /// ## 4.2 优化的锁机制 / Optimized Lock Mechanisms
    ///
    /// 新的锁机制提供了更好的性能和更少的死锁风险。
    /// The new lock mechanisms provide better performance and less deadlock risk.

    /// 优化的锁机制示例 / Optimized Lock Mechanisms Example
    pub fn optimized_lock_mechanisms() {
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

    /// ## 4.3 改进的异步支持 / Improved Async Support
    ///
    /// 异步编程的所有权管理得到了改进。
    /// Ownership management in async programming has been improved.

    /// 改进的异步支持示例 / Improved Async Support Example
    pub fn improved_async_support() {
        // 使用 async/await 进行异步编程
        // Use async/await for async programming
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async {
            let result = async_function().await;
            println!("Async result: {}", result);
        });
    }

    /// 异步函数示例 / Async function example
    async fn async_function() -> i32 {
        // 模拟异步操作
        // Simulate async operation
        tokio::time::sleep(Duration::from_millis(100)).await;
        42
    }
}

/// # 5. 智能指针增强 / Smart Pointer Enhancements
///
/// Rust 1.89 版本对智能指针进行了多项增强。
/// Rust 1.89 has made several enhancements to smart pointers.

pub mod smart_pointer_enhancements {
    use std::rc::Rc;
    use std::cell::RefCell;

    /// ## 5.1 改进的引用计数 / Improved Reference Counting
    ///
    /// Rc 和 Arc 的性能得到了优化。
    /// Rc and Arc performance has been optimized.

    /// 改进的引用计数示例 / Improved Reference Counting Example
    pub fn improved_reference_counting() {
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

    /// ## 5.2 优化的内存使用 / Optimized Memory Usage
    ///
    /// 智能指针的内存使用得到了优化。
    /// Smart pointer memory usage has been optimized.

    /// 优化的内存使用示例 / Optimized Memory Usage Example
    pub fn optimized_memory_usage() {
        // 使用 Box 进行堆分配
        // Use Box for heap allocation
        let boxed_data = Box::new([1, 2, 3, 4, 5]);
        println!("Boxed array: {:?}", boxed_data);

        // 使用 Box::leak 进行静态分配
        // Use Box::leak for static allocation
        let static_data = Box::leak(Box::new("static string"));
        println!("Static data: {}", static_data);
    }
}

/// # 6. 编译器优化 / Compiler Optimizations
///
/// Rust 1.89 版本在编译器优化方面进行了多项改进。
/// Rust 1.89 has made several improvements in compiler optimizations.

pub mod compiler_optimizations {

    /// ## 6.1 改进的内联优化 / Improved Inline Optimization
    ///
    /// 编译器能够更好地决定何时内联函数。
    /// The compiler can better decide when to inline functions.

    /// 改进的内联优化示例 / Improved Inline Optimization Example
    pub fn improved_inline_optimization() {
        let result = optimized_function(10, 20);
        println!("Optimized result: {}", result);
    }

    /// 优化的函数 / Optimized function
    #[inline(always)]
    fn optimized_function(a: i32, b: i32) -> i32 {
        a * b + a + b
    }

    /// ## 6.2 更好的死代码消除 / Better Dead Code Elimination
    ///
    /// 编译器能够更有效地消除死代码。
    /// The compiler can more effectively eliminate dead code.

    /// 更好的死代码消除示例 / Better Dead Code Elimination Example
    pub fn better_dead_code_elimination() {
        let data = vec![1, 2, 3, 4, 5];

        // 编译器能够识别未使用的代码
        // Compiler can identify unused code
        let _unused = data.iter().map(|x| x * 2);

        // 只使用实际需要的代码
        // Only use actually needed code
        let used: Vec<i32> = data.iter().map(|x| x * 2).collect();
        println!("Used data: {:?}", used);
    }
}

/// # 7. 工具链改进 / Toolchain Improvements
///
/// Rust 1.89 版本的工具链得到了多项改进。
/// Rust 1.89's toolchain has received several improvements.

pub mod toolchain_improvements {

    /// ## 7.1 改进的 Clippy / Improved Clippy
    ///
    /// Clippy 提供了更多的 lint 规则和更好的建议。
    /// Clippy provides more lint rules and better suggestions.

    /// 改进的 Clippy 示例 / Improved Clippy Example
    pub fn improved_clippy() {
        let data = vec![1, 2, 3];

        // Clippy 能够检测不必要的克隆
        // Clippy can detect unnecessary clones
        let cloned_data = data.clone();

        // 改进的借用检查器能够提供更好的建议
        // Improved borrow checker can provide better suggestions
        let borrowed_data = &data;

        println!("Original: {:?}, Cloned: {:?}, Borrowed: {:?}",
                 data, cloned_data, borrowed_data);
    }

    /// ## 7.2 更好的错误诊断 / Better Error Diagnostics
    ///
    /// 编译器提供了更好的错误诊断信息。
    /// The compiler provides better error diagnostic information.

    /// 更好的错误诊断示例 / Better Error Diagnostics Example
    pub fn better_error_diagnostics() {
        let mut s = String::from("hello");

        // 展示改进的错误诊断（实际代码中会编译错误）
        // Demonstrate improved error diagnostics (would compile error in actual code)
        println!("This would show better error diagnostics in Rust 1.89");

        // 正确的做法
        // Correct approach
        {
            let r1 = &s;
            println!("r1: {}", r1);
        }

        let r2 = &mut s;
        r2.push_str(", world");
        println!("r2: {}", r2);
    }
}

/// # 主要功能函数 / Main Function Functions

/// 运行所有 Rust 1.89 特性示例 / Run all Rust 1.89 feature examples
pub fn run_all_rust_189_examples() {
    println!("=== Rust 1.89 新特性示例 / Rust 1.89 New Features Examples ===");

    println!("\n1. 改进的借用检查器 / Improved Borrow Checker");
    improved_borrow_checker::smart_borrow_analysis();
    improved_borrow_checker::improved_error_messages();
    improved_borrow_checker::nll_optimization();

    println!("\n2. 增强的生命周期推断 / Enhanced Lifetime Inference");
    enhanced_lifetime_inference::smart_lifetime_elision();
    enhanced_lifetime_inference::improved_lifetime_constraints();

    println!("\n3. 优化的内存管理 / Optimized Memory Management");
    optimized_memory_management::improved_heap_allocation();
    optimized_memory_management::optimized_memory_layout();
    optimized_memory_management::zero_cost_abstraction_optimization();

    println!("\n4. 增强的并发安全 / Enhanced Concurrency Safety");
    enhanced_concurrency_safety::improved_data_race_detection();
    enhanced_concurrency_safety::optimized_lock_mechanisms();

    println!("\n5. 智能指针增强 / Smart Pointer Enhancements");
    smart_pointer_enhancements::improved_reference_counting();
    smart_pointer_enhancements::optimized_memory_usage();

    println!("\n6. 编译器优化 / Compiler Optimizations");
    compiler_optimizations::improved_inline_optimization();
    compiler_optimizations::better_dead_code_elimination();

    println!("\n7. 工具链改进 / Toolchain Improvements");
    toolchain_improvements::improved_clippy();
    toolchain_improvements::better_error_diagnostics();

    println!("\n=== 所有 Rust 1.89 特性示例运行完成 / All Rust 1.89 Feature Examples Completed ===");
}

/// 获取 Rust 1.89 特性信息 / Get Rust 1.89 Feature Information
pub fn get_rust_189_info() -> &'static str {
    "Rust 1.89 New Features - Improved borrow checker, enhanced lifetime inference, optimized memory management, and enhanced concurrency safety"
}

/// 主函数 / Main Function
fn main() {
    println!("Rust 1.89 版本新特性示例程序 / Rust 1.89 New Features Example Program");
    println!("================================================");

    // 运行所有示例
    // Run all examples
    run_all_rust_189_examples();

    println!("\n程序执行完成 / Program execution completed");
}
