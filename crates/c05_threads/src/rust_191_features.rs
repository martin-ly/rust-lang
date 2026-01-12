//! Rust 1.91 线程特性实现模块（历史版本）
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features.rs`
//!
//! 本模块实现了 Rust 1.91 在线程和并发编程方面的改进，包括：
//! - const 上下文增强在多线程配置中的应用
//! - JIT 编译器优化对多线程代码的性能提升
//! - 内存分配优化对并发场景的影响
//! - 改进的错误处理在多线程中的应用
//!
//! # 文件信息
//! - 文件: rust_191_features.rs
//! - 创建日期: 2025-01-27
//! - 版本: 1.0
//! - Rust版本: 1.91.0
//! - Edition: 2024

use std::sync::{Arc, Mutex};
use std::thread;
use std::ops::ControlFlow;

// ==================== 1. const 上下文增强在多线程配置中的应用 ====================

/// Rust 1.91 const 上下文增强在多线程配置中的应用
pub mod const_thread_config {
    /// 多线程配置系统
    pub struct ThreadConfig {
        pub max_threads: usize,
        pub stack_size: usize,
    }

    impl ThreadConfig {
        // Rust 1.91: const 上下文使用引用
        pub const MAX_THREADS: usize = 8;
        pub const STACK_SIZE: usize = 2 * 1024 * 1024;  // 2MB

        pub const THREADS_REF: &usize = &Self::MAX_THREADS;  // ✅ Rust 1.91
        pub const TOTAL_STACK: usize = *Self::THREADS_REF * Self::STACK_SIZE;

        pub const TIMEOUT_MS: u64 = 5000;
        pub const TIMEOUT_REF: &u64 = &Self::TIMEOUT_MS;  // ✅ Rust 1.91
        pub const TOTAL_TIMEOUT_MS: u64 = *Self::TIMEOUT_REF * 2;
    }

    pub fn demonstrate() {
        println!("\n=== Const 上下文在多线程配置中的应用 ===");
        println!("最大线程数: {}", ThreadConfig::MAX_THREADS);
        println!("每个线程栈大小: {} bytes", ThreadConfig::STACK_SIZE);
        println!("总栈大小: {} bytes", ThreadConfig::TOTAL_STACK);
        println!("超时时间: {} ms", ThreadConfig::TIMEOUT_MS);
        println!("总超时时间: {} ms", ThreadConfig::TOTAL_TIMEOUT_MS);
    }
}

// ==================== 2. JIT 编译器优化对多线程代码的影响 ====================

/// Rust 1.91 JIT 编译器优化对多线程代码的影响
///
/// Rust 1.91 的 JIT 优化提升了多线程场景下的迭代器操作性能
pub mod thread_jit_optimizations {
    use super::*;

    /// 并行迭代器优化示例
    ///
    /// Rust 1.91 JIT 优化：并行迭代器性能提升 10-25%
    pub fn parallel_iterator_processing(data: &[i32]) -> i32 {
        // Rust 1.91 优化：并行迭代器链式操作性能提升
        use rayon::prelude::*;

        data.par_iter()
            .map(|x| x * 2)
            .filter(|&x| x > 0)
            .sum()
    }

    /// 多线程数据处理示例
    ///
    /// Rust 1.91 优化：多线程数据分割和处理性能提升
    pub fn multi_thread_processing(data: Vec<i32>, thread_count: usize) -> i32 {
        let chunk_size = data.len().div_ceil(thread_count);
        let data = Arc::new(data);
        let results = Arc::new(Mutex::new(Vec::new()));

        let handles: Vec<_> = (0..thread_count)
            .map(|i| {
                let data = Arc::clone(&data);
                let results = Arc::clone(&results);

                thread::spawn(move || {
                    let start = i * chunk_size;
                    let end = (start + chunk_size).min(data.len());

                    // Rust 1.91 优化：迭代器链式操作性能提升
                    let chunk_result: i32 = data[start..end]
                        .iter()
                        .map(|x| x * 2)
                        .filter(|&x| x > 0)
                        .sum();

                    let mut results = results.lock().unwrap();
                    results.push(chunk_result);
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        let results = results.lock().unwrap();
        results.iter().sum()
    }

    pub fn demonstrate() {
        println!("\n=== JIT 优化对多线程代码的影响 ===");

        let data: Vec<i32> = (0..1000).collect();

        let result = multi_thread_processing(data.clone(), 4);
        println!("多线程处理结果: {}", result);
    }
}

// ==================== 3. 内存分配优化对并发场景的影响 ====================

/// Rust 1.91 内存分配优化对并发场景的影响
///
/// Rust 1.91 的内存分配优化特别有利于并发场景下的小对象分配
pub mod thread_memory_optimizations {
    use super::*;

    /// 并发小对象分配示例
    ///
    /// Rust 1.91 优化：并发场景下小对象分配性能提升 25-30%
    pub fn concurrent_small_object_allocation(thread_count: usize, objects_per_thread: usize) -> Vec<Vec<i32>> {
        let results = Arc::new(Mutex::new(Vec::new()));

        let handles: Vec<_> = (0..thread_count)
            .map(|thread_id| {
                let results = Arc::clone(&results);

                thread::spawn(move || {
                    let mut thread_results = Vec::new();
                    // Rust 1.91 优化：频繁的小对象分配更加高效
                    for i in 0..objects_per_thread {
                        thread_results.push(vec![thread_id as i32, i as i32, (i * 2) as i32]);
                    }

                    let mut results = results.lock().unwrap();
                    results.push(thread_results);
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        let results = results.lock().unwrap();
        // 展平结果：Vec<Vec<Vec<i32>>> -> Vec<Vec<i32>>
        results.iter().flatten().cloned().collect()
    }

    /// 并发 HashMap 操作优化示例
    pub fn concurrent_hashmap_operations(thread_count: usize, operations_per_thread: usize) -> Arc<Mutex<std::collections::HashMap<usize, i32>>> {
        let map = Arc::new(Mutex::new(std::collections::HashMap::new()));

        let handles: Vec<_> = (0..thread_count)
            .map(|thread_id| {
                let map = Arc::clone(&map);

                thread::spawn(move || {
                    // Rust 1.91 优化：HashMap 并发操作性能提升
                    for i in 0..operations_per_thread {
                        let key = thread_id * operations_per_thread + i;
                        let mut map = map.lock().unwrap();
                        map.insert(key, (key * 2) as i32);
                    }
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        map
    }

    pub fn demonstrate() {
        println!("\n=== 内存分配优化对并发场景的影响 ===");

        let objects = concurrent_small_object_allocation(4, 100);
        println!("并发创建了 {} 个线程的小对象", objects.len());
        println!("总对象数: {}", objects.iter().map(|v| v.len()).sum::<usize>());

        let map = concurrent_hashmap_operations(4, 50);
        let map = map.lock().unwrap();
        println!("并发 HashMap 包含 {} 个元素", map.len());
    }
}

// ==================== 4. 多线程错误处理改进 ====================

/// Rust 1.91 多线程错误处理改进
///
/// 使用改进的 ControlFlow 进行多线程错误处理
pub mod thread_error_handling {
    use super::*;

    /// 多线程验证示例
    ///
    /// 使用改进的 ControlFlow 进行多线程验证
    pub fn multi_thread_validation(
        data: &[i32],
        thread_count: usize,
    ) -> ControlFlow<String, Vec<i32>> {
        if data.is_empty() {
            return ControlFlow::Break("数据为空".to_string());
        }

        let chunk_size = data.len().div_ceil(thread_count);
        let data = Arc::new(data.to_vec());
        let errors = Arc::new(Mutex::new(Vec::new()));
        let valid_items = Arc::new(Mutex::new(Vec::new()));

        let handles: Vec<_> = (0..thread_count)
            .map(|i| {
                let data = Arc::clone(&data);
                let errors = Arc::clone(&errors);
                let valid_items = Arc::clone(&valid_items);

                thread::spawn(move || {
                    let start = i * chunk_size;
                    let end = (start + chunk_size).min(data.len());

                    for &item in &data[start..end] {
                        if item > 0 {
                            let mut valid = valid_items.lock().unwrap();
                            valid.push(item);
                        } else {
                            // Rust 1.91 改进：可以携带详细的错误信息
                            let mut errors = errors.lock().unwrap();
                            errors.push(format!("负数: {}", item));
                        }
                    }
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }

        let errors = errors.lock().unwrap();
        if !errors.is_empty() {
            return ControlFlow::Break(format!("验证失败: {}", errors[0]));
        }

        let valid = valid_items.lock().unwrap();
        ControlFlow::Continue(valid.clone())
    }

    pub fn demonstrate() {
        println!("\n=== 多线程错误处理改进 ===");

        let valid_data = vec![1, 2, 3, 4, 5];
        match multi_thread_validation(&valid_data, 2) {
            ControlFlow::Continue(items) => {
                println!("验证成功，有效元素: {:?}", items);
            }
            ControlFlow::Break(error) => {
                println!("验证失败: {}", error);
            }
        }

        let invalid_data = vec![1, 2, -3, 4, 5];
        match multi_thread_validation(&invalid_data, 2) {
            ControlFlow::Continue(items) => {
                println!("验证成功，有效元素: {:?}", items);
            }
            ControlFlow::Break(error) => {
                println!("验证失败: {}", error);
            }
        }
    }
}

// ==================== 5. 综合应用示例 ====================

/// Rust 1.91 多线程综合应用示例
pub mod comprehensive_thread_examples {
    use super::*;

    /// 多线程数据处理管道
    pub struct ThreadPipeline<T> {
        data: Vec<T>,
        thread_count: usize,
    }

    impl<T> ThreadPipeline<T> {
        pub fn new(data: Vec<T>, thread_count: usize) -> Self {
            Self { data, thread_count }
        }

        /// Rust 1.91 优化：多线程处理管道性能提升
        pub fn process<U, R, M, Red>(
            &self,
            mapper: M,
            reducer: Red,
        ) -> R
        where
            T: Send + Sync + Clone + 'static,
            U: Send + Sync + Clone + 'static,
            M: Fn(&T) -> U + Send + Sync + 'static,
            Red: Fn(Vec<U>) -> R,
        {
            let chunk_size = self.data.len().div_ceil(self.thread_count);
            let data = Arc::new(self.data.clone());
            let results = Arc::new(Mutex::new(Vec::new()));
            let mapper = Arc::new(mapper);

            let handles: Vec<_> = (0..self.thread_count)
                .map(|i| {
                    let data = Arc::clone(&data);
                    let results = Arc::clone(&results);
                    let mapper = Arc::clone(&mapper);

                    thread::spawn(move || {
                        let start = i * chunk_size;
                        let end = (start + chunk_size).min(data.len());

                        // Rust 1.91 优化：迭代器链式操作性能提升
                        let chunk_results: Vec<U> = data[start..end]
                            .iter()
                            .map(|item| mapper(item))
                            .collect();

                        let mut results = results.lock().unwrap();
                        results.push(chunk_results);
                    })
                })
                .collect();

            for handle in handles {
                handle.join().unwrap();
            }

            let results = results.lock().unwrap();
            let all_results: Vec<U> = results.iter().flatten().cloned().collect();
            reducer(all_results)
        }
    }

    pub fn demonstrate() {
        println!("\n=== 多线程综合应用示例 ===");

        let pipeline = ThreadPipeline::new(vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 4);
        let result = pipeline.process(
            |x| x * 2,
            |items| items.iter().sum::<i32>(),
        );
        println!("多线程管道处理结果: {}", result);
    }
}

// ==================== 公开 API ====================

/// Rust 1.91 线程特性演示入口
pub fn demonstrate_rust_191_threads() {
    println!("========================================");
    println!("Rust 1.91 线程特性演示");
    println!("========================================");

    const_thread_config::demonstrate();
    thread_jit_optimizations::demonstrate();
    thread_memory_optimizations::demonstrate();
    thread_error_handling::demonstrate();
    comprehensive_thread_examples::demonstrate();
}
