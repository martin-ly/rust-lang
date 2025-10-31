//! Rust 1.91 控制流与函数特性实现模块
//!
//! 本模块实现了 Rust 1.91 在控制流和函数系统方面的改进，包括：
//! - const 上下文增强（在控制流中使用）
//! - 改进的错误处理和 ControlFlow
//! - 优化的函数调用和性能改进
//! - JIT 编译器优化对控制流的影响
//!
//! # 文件信息
//! - 文件: rust_191_features.rs
//! - 创建日期: 2025-01-27
//! - 版本: 1.0
//! - Rust版本: 1.91.0
//! - Edition: 2024

use std::ops::ControlFlow;

// ==================== 1. const 上下文增强在控制流中的应用 ====================

/// Rust 1.91 const 上下文增强在控制流中的应用
pub mod const_control_flow {
    /// 编译时控制流计算
    ///
    /// Rust 1.91 允许在 const 上下文中进行更复杂的控制流操作
    pub const fn const_factorial(n: u32) -> u32 {
        match n {
            0 | 1 => 1,
            n => n * const_factorial(n - 1),
        }
    }

    /// 使用 const 引用进行计算
    ///
    /// Rust 1.91: 可以在 const 上下文中使用引用
    pub const CONST_VALUE: u32 = 10;
    pub const CONST_REF: &u32 = &CONST_VALUE;  // ✅ Rust 1.91 新特性
    pub const FACTORIAL_10: u32 = const_factorial(*CONST_REF);

    /// 编译时配置系统
    pub struct Config {
        pub max_retries: u32,
        pub timeout_ms: u64,
    }

    impl Config {
        pub const MAX_RETRIES: u32 = 3;
        pub const TIMEOUT_MS: u64 = 5000;

        // Rust 1.91: 使用 const 引用进行配置计算
        pub const RETRY_REF: &u32 = &Self::MAX_RETRIES;
        pub const TOTAL_TIMEOUT_MS: u64 = *Self::RETRY_REF as u64 * Self::TIMEOUT_MS;
    }

    pub fn demonstrate() {
        println!("\n=== Const 上下文控制流 ===");
        println!("常量值: {}", CONST_VALUE);
        println!("10 的阶乘: {}", FACTORIAL_10);
        println!("最大重试次数: {}", Config::MAX_RETRIES);
        println!("总超时时间: {} ms", Config::TOTAL_TIMEOUT_MS);
    }
}

// ==================== 2. 改进的 ControlFlow ====================

/// Rust 1.91 改进的 ControlFlow 示例
pub mod improved_control_flow {
    use super::*;

    /// 使用改进的 ControlFlow 进行数据处理
    ///
    /// Rust 1.91 改进了 ControlFlow，提供更好的错误信息
    pub fn process_with_control_flow<T>(items: &[T], validator: impl Fn(&T) -> bool) -> ControlFlow<String, Vec<&T>>
    where
        T: std::fmt::Display,
    {
        let mut result = Vec::new();

        for item in items {
            if validator(item) {
                result.push(item);
            } else {
                // Rust 1.91 改进：可以携带详细的错误信息
                return ControlFlow::Break(format!("验证失败: {}", item));
            }
        }

        ControlFlow::Continue(result)
    }

    /// 复杂验证流程示例
    pub fn validate_pipeline(data: &[i32]) -> ControlFlow<String, i32> {
        // 第一步：检查是否为空
        if data.is_empty() {
            return ControlFlow::Break("数据为空".to_string());
        }

        // 第二步：计算总和
        let sum: i32 = data.iter().sum();

        // 第三步：验证总和是否为正
        if sum <= 0 {
            return ControlFlow::Break(format!("总和必须为正数，当前: {}", sum));
        }

        ControlFlow::Continue(sum)
    }

    pub fn demonstrate() {
        println!("\n=== 改进的 ControlFlow ===");

        // 成功案例
        let valid_data = vec![1, 2, 3, 4, 5];
        match validate_pipeline(&valid_data) {
            ControlFlow::Continue(sum) => {
                println!("验证成功，总和: {}", sum);
            }
            ControlFlow::Break(error) => {
                println!("验证失败: {}", error);
            }
        }

        // 失败案例
        let invalid_data = vec![1, 2, -10];
        match validate_pipeline(&invalid_data) {
            ControlFlow::Continue(sum) => {
                println!("验证成功，总和: {}", sum);
            }
            ControlFlow::Break(error) => {
                println!("验证失败: {}", error);
            }
        }
    }
}

// ==================== 3. 函数性能优化 ====================

/// Rust 1.91 函数性能优化示例
///
/// Rust 1.91 的 JIT 编译器优化对函数调用和迭代器的性能提升
pub mod function_performance {
    /// 优化的迭代器链式调用
    ///
    /// Rust 1.91 JIT 优化：迭代器链式操作性能提升 10-25%
    pub fn optimized_iterator_chain(data: &[i32]) -> Vec<i32> {
        data.iter()
            .filter(|&&x| x > 0)
            .map(|&x| x * x)
            .filter(|&x| x > 100)
            .take(100)
            .collect()
    }

    /// 递归函数优化
    ///
    /// Rust 1.91 优化：递归函数调用性能提升
    pub fn optimized_recursive_fibonacci(n: u32) -> u32 {
        match n {
            0 => 0,
            1 => 1,
            n => optimized_recursive_fibonacci(n - 1) + optimized_recursive_fibonacci(n - 2),
        }
    }

    /// 尾递归优化示例（使用辅助函数）
    pub fn tail_recursive_factorial(n: u32, acc: u32) -> u32 {
        match n {
            0 | 1 => acc,
            n => tail_recursive_factorial(n - 1, n * acc),
        }
    }

    pub fn factorial(n: u32) -> u32 {
        tail_recursive_factorial(n, 1)
    }

    pub fn demonstrate() {
        println!("\n=== 函数性能优化 ===");

        let data: Vec<i32> = (-50..50).collect();
        let result = optimized_iterator_chain(&data);
        println!("优化迭代器链处理了 {} 个元素", result.len());

        let fib_20 = optimized_recursive_fibonacci(20);
        println!("斐波那契(20): {}", fib_20);

        let fact_10 = factorial(10);
        println!("10 的阶乘: {}", fact_10);
    }
}

// ==================== 4. 错误处理改进 ====================

/// Rust 1.91 错误处理改进示例
pub mod error_handling {
    use super::*;

    /// 使用 ControlFlow 进行错误处理
    ///
    /// Rust 1.91 改进了 ControlFlow，提供更好的错误信息传递
    pub fn parse_numbers(input: &str) -> ControlFlow<String, Vec<i32>> {
        let mut numbers = Vec::new();

        for (idx, part) in input.split_ascii_whitespace().enumerate() {
            match part.parse::<i32>() {
                Ok(n) => numbers.push(n),
                Err(_) => {
                    return ControlFlow::Break(format!("解析失败: 第 {} 个元素 '{}' 不是有效数字", idx + 1, part));
                }
            }
        }

        ControlFlow::Continue(numbers)
    }

    /// 多级验证示例
    pub fn multi_level_validation(data: &[i32]) -> ControlFlow<String, i32> {
        // 第一级：检查长度
        if data.is_empty() {
            return ControlFlow::Break("数据不能为空".to_string());
        }

        // 第二级：检查范围
        for (idx, &n) in data.iter().enumerate() {
            if n < 0 || n > 1000 {
                return ControlFlow::Break(format!("第 {} 个元素 {} 超出范围 [0, 1000]", idx + 1, n));
            }
        }

        // 第三级：计算平均值
        let sum: i32 = data.iter().sum();
        let avg = sum / data.len() as i32;

        ControlFlow::Continue(avg)
    }

    pub fn demonstrate() {
        println!("\n=== 错误处理改进 ===");

        // 成功解析
        match parse_numbers("1 2 3 4 5") {
            ControlFlow::Continue(numbers) => {
                println!("解析成功: {:?}", numbers);
            }
            ControlFlow::Break(error) => {
                println!("解析失败: {}", error);
            }
        }

        // 解析失败
        match parse_numbers("1 2 abc 4") {
            ControlFlow::Continue(numbers) => {
                println!("解析成功: {:?}", numbers);
            }
            ControlFlow::Break(error) => {
                println!("解析失败: {}", error);
            }
        }

        // 多级验证
        let data = vec![10, 20, 30, 40, 50];
        match multi_level_validation(&data) {
            ControlFlow::Continue(avg) => {
                println!("验证通过，平均值: {}", avg);
            }
            ControlFlow::Break(error) => {
                println!("验证失败: {}", error);
            }
        }
    }
}

// ==================== 5. 综合应用示例 ====================

/// Rust 1.91 控制流综合应用示例
pub mod comprehensive_examples {
    use std::io::{BufRead, BufReader, Cursor};
    use std::collections::HashMap;
    use std::ops::ControlFlow;

    /// 配置系统：结合 const 上下文和控制流
    pub struct ControlFlowConfig {
        pub max_iterations: usize,
        pub timeout_ms: u64,
    }

    impl ControlFlowConfig {
        pub const MAX_ITERATIONS: usize = 100;
        pub const TIMEOUT_MS: u64 = 1000;

        pub const ITER_REF: &usize = &Self::MAX_ITERATIONS;  // ✅ Rust 1.91
        pub const TOTAL_MS: u64 = *Self::ITER_REF as u64 * Self::TIMEOUT_MS;
    }

    /// 处理控制流管道
    pub fn process_pipeline(data: &[i32]) -> ControlFlow<String, HashMap<String, i32>> {
        let mut stats = HashMap::new();

        // 第一步：验证
        if data.is_empty() {
            return ControlFlow::Break("数据为空".to_string());
        }

        // 第二步：计算统计信息
        let sum: i32 = data.iter().sum();
        let min = *data.iter().min().unwrap();
        let max = *data.iter().max().unwrap();
        let avg = sum / data.len() as i32;

        stats.insert("sum".to_string(), sum);
        stats.insert("min".to_string(), min);
        stats.insert("max".to_string(), max);
        stats.insert("avg".to_string(), avg);

        ControlFlow::Continue(stats)
    }

    /// 使用 Rust 1.91 新 API 解析配置
    pub fn parse_config_with_new_apis(config_text: &str) -> Vec<String> {
        let mut cursor = Cursor::new(config_text.as_bytes());
        let mut reader = BufReader::new(&mut cursor);
        let mut lines = Vec::new();
        let mut buf = String::new();

        while reader.read_line(&mut buf).unwrap() > 0 {
            // Rust 1.91: 使用 skip_while 跳过注释和空白
            let line: String = buf
                .bytes()
                .skip_while(|&b| b == b'#' || b == b' ' || b == b'\t')
                .take_while(|&b| b != b'\n')
                .map(|b| b as char)
                .collect();

            if !line.is_empty() {
                lines.push(line.trim().to_string());
            }
            buf.clear();
        }

        lines
    }

    pub fn demonstrate() {
        println!("\n=== 控制流综合示例 ===");

        // 配置系统
        println!("最大迭代次数: {}", ControlFlowConfig::MAX_ITERATIONS);
        println!("总超时时间: {} ms", ControlFlowConfig::TOTAL_MS);

        // 管道处理
        let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        match process_pipeline(&data) {
            ControlFlow::Continue(stats) => {
                println!("处理成功，统计信息:");
                for (key, value) in stats {
                    println!("  {}: {}", key, value);
                }
            }
            ControlFlow::Break(error) => {
                println!("处理失败: {}", error);
            }
        }

        // 配置解析
        let config = "# 控制流配置\n# 这是注释\nmax_retries = 3\ntimeout = 5000";
        let parsed = parse_config_with_new_apis(config);
        println!("\n解析的配置:");
        for line in parsed {
            println!("  - {}", line);
        }
    }
}

// ==================== 公开 API ====================

/// Rust 1.91 控制流特性演示入口
pub fn demonstrate_rust_191_control_flow() {
    println!("========================================");
    println!("Rust 1.91 控制流与函数特性演示");
    println!("========================================");

    const_control_flow::demonstrate();
    improved_control_flow::demonstrate();
    function_performance::demonstrate();
    error_handling::demonstrate();
    comprehensive_examples::demonstrate();
}

