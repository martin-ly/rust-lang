//! # Rust 1.90 最新特性演示 / Rust 1.90 Latest Features Demo
//!
//! 本示例展示 Rust 1.90 版本的最新特性，包括：
//! This example demonstrates the latest features in Rust 1.90, including:
//!
//! - `gen` 块和生成器 / `gen` blocks and generators
//! - 异步生成器 / Async generators
//! - 改进的模式匹配 / Improved pattern matching
//! - 增强的借用检查器 / Enhanced borrow checker
//! - 新的智能指针特性 / New smart pointer features
//! - 优化的作用域管理 / Optimized scope management
//! - 增强的并发安全 / Enhanced concurrency safety
//! - 智能内存管理 / Smart memory management

use c01_ownership_borrow_scope::{
    run_all_rust_190_latest_features_examples,
    get_rust_190_latest_features_info,
    SyncGenerator,
    CustomSyncGenerator,
    create_number_generator,
    create_filtered_generator,
    create_transformed_generator,
    combine_generators,
    zip_generators,
    GeneratorMetrics,
    Rust190PerformanceAnalyzer,
    CachedGenerator,
};

use std::time::Duration;
use std::thread;
use std::sync::{Arc, Mutex};

/// 主函数 / Main Function
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("=== Rust 1.90 最新特性演示 / Rust 1.90 Latest Features Demo ===");

    // 显示模块信息 / Show module information
    println!("模块信息 / Module Info: {}", get_rust_190_latest_features_info());

    // 运行所有最新特性示例 / Run all latest features examples
    run_all_rust_190_latest_features_examples();

    // 演示自定义生成器 / Demonstrate custom generators
    demonstrate_custom_generators();

    // 演示生成器工具函数 / Demonstrate generator utility functions
    demonstrate_generator_utilities();

    // 演示生成器性能分析 / Demonstrate generator performance analysis
    demonstrate_performance_analysis();

    // 演示生成器缓存 / Demonstrate generator caching
    demonstrate_generator_caching();

    // 演示异步特性（如果可用）/ Demonstrate async features (if available)
    demonstrate_async_features();

    println!("\n=== Rust 1.90 最新特性演示完成 / Rust 1.90 Latest Features Demo Completed ===");

    Ok(())
}

/// 演示自定义生成器 / Demonstrate Custom Generators
fn demonstrate_custom_generators() {
    println!("\n=== 自定义生成器演示 / Custom Generators Demo ===");

    // 创建自定义同步生成器 / Create custom sync generator
    let mut custom_gen = CustomSyncGenerator::new(5);

    println!("自定义生成器输出 / Custom generator output:");
    while let Some(value) = custom_gen.next() {
        println!("  Generated: {}", value);
    }

    // 演示生成器特征 / Demonstrate generator traits
    let mut another_gen = CustomSyncGenerator::new(3);
    println!("\n另一个生成器 / Another generator:");
    for value in std::iter::from_fn(|| another_gen.next()) {
        println!("  Generated: {}", value);
    }
}

/// 演示生成器工具函数 / Demonstrate Generator Utility Functions
fn demonstrate_generator_utilities() {
    println!("\n=== 生成器工具函数演示 / Generator Utility Functions Demo ===");

    // 创建数字生成器 / Create number generator
    let numbers = create_number_generator(5);
    println!("数字生成器 / Number generator:");
    for num in numbers {
        println!("  Number: {}", num);
    }

    // 创建过滤生成器 / Create filtered generator
    let even_numbers = create_filtered_generator(10, |x| x % 2 == 0);
    println!("\n偶数生成器 / Even number generator:");
    for num in even_numbers {
        println!("  Even number: {}", num);
    }

    // 创建转换生成器 / Create transformed generator
    let squared_numbers = create_transformed_generator(5, |x| x * x);
    println!("\n平方数生成器 / Squared number generator:");
    for num in squared_numbers {
        println!("  Squared number: {}", num);
    }

    // 合并生成器 / Combine generators
    let gen1 = create_number_generator(3);
    let gen2 = create_number_generator(3);
    let combined = combine_generators(gen1, gen2);
    println!("\n合并生成器 / Combined generator:");
    for num in combined {
        println!("  Combined number: {}", num);
    }

    // 压缩生成器 / Zip generators
    let gen1 = create_number_generator(3);
    let gen2 = create_number_generator(3);
    let zipped = zip_generators(gen1, gen2);
    println!("\n压缩生成器 / Zipped generator:");
    for (a, b) in zipped {
        println!("  Zipped: ({}, {})", a, b);
    }
}

/// 演示性能分析 / Demonstrate Performance
#[allow(unused_variables)]
#[allow(unused_assignments)]
fn demonstrate_performance_analysis() {
    println!("\n=== 性能分析演示 / Performance Analysis Demo ===");

    // 创建性能分析生成器 / Create performance analysis generator
    let base_generator = create_number_generator(1000);
    let mut analyzer = Rust190PerformanceAnalyzer::new(base_generator);

    let start = std::time::Instant::now();

    // 消耗所有项目 / Consume all items
    let mut count = 0;
    while let Some(_value) = analyzer.next() {
        count += 1;
    }

    let duration = start.elapsed();
    analyzer.get_metrics_mut().set_time(duration);

    let metrics = analyzer.get_metrics();
    println!("性能指标 / Performance metrics:");
    println!("  生成项目数 / Items generated: {}", metrics.items_generated);
    println!("  生成时间 / Generation time: {:?}", metrics.generation_time);
    println!("  每秒项目数 / Items per second: {:.2}", metrics.items_per_second());

    // 创建生成器指标 / Create generator metrics
    let mut metrics = GeneratorMetrics::new();
    metrics.add_item();
    metrics.add_item();
    metrics.add_item();
    metrics.set_time(Duration::from_millis(100));
    metrics.set_memory(1024);

    println!("\n手动指标 / Manual metrics:");
    println!("  项目数 / Items: {}", metrics.items_generated);
    println!("  时间 / Time: {:?}", metrics.generation_time);
    println!("  内存 / Memory: {} bytes", metrics.memory_usage);
    println!("  速率 / Rate: {:.2} items/sec", metrics.items_per_second());
}

/// 演示生成器缓存 / Demonstrate Generator Caching
fn demonstrate_generator_caching() {
    println!("\n=== 生成器缓存演示 / Generator Caching Demo ===");

    // 创建缓存生成器 / Create cached generator
    let base_generator = create_number_generator(5);
    let mut cached_gen = CachedGenerator::new(base_generator);

    println!("第一次迭代 / First iteration:");
    for value in std::iter::from_fn(|| cached_gen.next()) {
        println!("  Generated: {}", value);
    }

    println!("\n缓存大小 / Cache size: {}", cached_gen.cache_size());
    println!("缓存项目 / Cached items: {:?}", cached_gen.get_cached_items());

    // 重置索引以重新迭代 / Reset index to re-iterate
    cached_gen.reset_index();

    println!("\n第二次迭代（从缓存）/ Second iteration (from cache):");
    for value in std::iter::from_fn(|| cached_gen.next()) {
        println!("  Generated from cache: {}", value);
    }
}

/// 演示异步特性 / Demonstrate Async Features
fn demonstrate_async_features() {
    println!("\n=== 异步特性演示 / Async Features Demo ===");

    // 注意：实际的异步特性需要在异步运行时中运行
    // Note: Actual async features need to run in async runtime
    println!("异步特性演示需要在异步运行时中运行 / Async features demo needs to run in async runtime");
    println!("可以使用 tokio::runtime::Runtime::new() 来运行异步代码 / Can use tokio::runtime::Runtime::new() to run async code");

    // 模拟异步操作 / Simulate async operations
    println!("\n模拟异步操作 / Simulating async operations:");

    let shared_data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let mut handles = vec![];

    for i in 0..3 {
        let data_clone = Arc::clone(&shared_data);
        let handle = thread::spawn(move || {
            // 模拟异步工作 / Simulate async work
            thread::sleep(Duration::from_millis(100));
            let mut data = data_clone.lock().unwrap();
            data.push(i + 10);
            println!("  Async task {} completed", i);
        });
        handles.push(handle);
    }

    // 等待所有任务完成 / Wait for all tasks to complete
    for handle in handles {
        handle.join().unwrap();
    }

    println!("最终数据 / Final data: {:?}", *shared_data.lock().unwrap());
}

/// 演示 Rust 1.90 的其他新特性 / Demonstrate Other Rust 1.90 New Features

/// 演示改进的模式匹配 / Demonstrate Improved Pattern Matching
#[allow(dead_code)]
#[allow(unused_variables)]
fn demonstrate_improved_pattern_matching() {
    println!("\n=== 改进的模式匹配演示 / Improved Pattern Matching Demo ===");

    // 复杂模式匹配 / Complex pattern matching
    let data = vec![
        (1, "first"),
        (2, "second"),
        (3, "third"),
        (4, "fourth"),
    ];

    for (num, text) in data {
        match (num, text) {
            (1, "first") => println!("First item"),
            (n, t) if n % 2 == 0 => println!("Even number: {} with text: {}", n, t),
            (n, _) => println!("Odd number: {}", n),
        }
    }

    // 结构体模式匹配 / Struct pattern matching
    #[derive(Debug)]
    struct Point {
        x: i32,
        y: i32,
        z: Option<i32>,
    }

    let points = vec![
        Point { x: 0, y: 0, z: Some(0) },
        Point { x: 1, y: 2, z: None },
        Point { x: 3, y: 4, z: Some(5) },
    ];

    for point in points {
        match point {
            Point { x: 0, y: 0, z: Some(0) } => println!("Origin point"),
            Point { x, y, z: Some(z) } => println!("3D point: ({}, {}, {})", x, y, z),
            Point { x, y, z: None } => println!("2D point: ({}, {})", x, y),
        }
    }
}

/// 演示增强的借用检查器 / Demonstrate Enhanced Borrow Checker
#[allow(dead_code)]
#[allow(unused_variables)]
fn demonstrate_enhanced_borrow_checker() {
    println!("\n=== 增强的借用检查器演示 / Enhanced Borrow Checker Demo ===");

    let mut data = vec![1, 2, 3, 4, 5];

    // Rust 1.90 支持更智能的借用分析
    // Rust 1.90 supports smarter borrow analysis
    let (first_half, second_half) = data.split_at_mut(3);

    // 可以同时修改不同部分
    // Can modify different parts simultaneously
    for item in first_half.iter_mut() {
        *item *= 2;
    }

    for item in second_half.iter_mut() {
        *item *= 3;
    }

    println!("修改后的数据 / Modified data: {:?}", data);
}

/// 演示智能指针优化 / Demonstrate Smart Pointer Optimization
#[allow(dead_code)]
#[allow(unused_variables)]
fn demonstrate_smart_pointer_optimization() {
    println!("\n=== 智能指针优化演示 / Smart Pointer Optimization Demo ===");

    use std::rc::Rc;
    use std::cell::RefCell;

    // Rc<RefCell<T>> 内部可变性
    // Rc<RefCell<T>> interior mutability
    let shared_data = Rc::new(RefCell::new(vec![1, 2, 3]));
    let data_clone1 = Rc::clone(&shared_data);
    let data_clone2 = Rc::clone(&shared_data);

    // 可以同时修改共享数据
    // Can modify shared data simultaneously
    data_clone1.borrow_mut().push(4);
    data_clone2.borrow_mut().push(5);

    println!("共享数据 / Shared data: {:?}", shared_data.borrow());
    println!("引用计数 / Reference count: {}", Rc::strong_count(&shared_data));
}

/// 演示性能优化 / Demonstrate Performance Optimization
#[allow(dead_code)]
#[allow(unused_variables)]
fn demonstrate_performance_optimization() {
    println!("\n=== 性能优化演示 / Performance Optimization Demo ===");

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
    println!("快速加法结果 / Fast add result: {}", result1);
    println!("慢速计算结果 / Slow calculation result: {}", result2);

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
    println!("矩阵总和 / Matrix sum: {}", sum);
}

/// 演示错误处理改进 / Demonstrate Error Handling Improvements
#[allow(dead_code)]
#[allow(unused_variables)]
fn demonstrate_error_handling_improvements() {
    println!("\n=== 错误处理改进演示 / Error Handling Improvements Demo ===");

    // 自定义错误类型
    // Custom error types
    #[derive(Debug)]
    enum MathError {
        DivisionByZero,
        NegativeSquareRoot,
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
        Ok(result) => println!("复杂计算结果 / Complex calculation result: {}", result),
        Err(error) => println!("复杂计算错误 / Complex calculation error: {}", error),
    }

    match complex_calculation(10, 0, 16.0) {
        Ok(result) => println!("复杂计算结果 / Complex calculation result: {}", result),
        Err(error) => println!("复杂计算错误 / Complex calculation error: {}", error),
    }
}
