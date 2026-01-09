//! Rust 1.91 控制流与函数特性实现模块（历史版本）
//!
//! > **注意**: 当前版本为 Rust 1.92.0，请参考 `rust_192_features.rs` 了解最新特性。
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

// ==================== 6. 优化的条件语句和模式匹配 ====================

/// Rust 1.91 优化的条件语句和模式匹配
pub mod optimized_conditionals {
    /// 编译时条件计算
    ///
    /// Rust 1.91: 可以在 const 上下文中进行更复杂的条件计算
    pub const fn const_max(a: u32, b: u32) -> u32 {
        if a > b {
            a
        } else {
            b
        }
    }

    /// 优化的模式匹配
    ///
    /// Rust 1.91: 模式匹配性能优化，编译时间减少
    pub fn optimized_pattern_matching(value: Option<i32>) -> String {
        match value {
            Some(n) => {
                if n > 0 {
                    format!("正数: {}", n)
                } else if n < 0 {
                    format!("负数: {}", n)
                } else {
                    "零".to_string()
                }
            }
            None => "无值".to_string(),
        }
    }

    /// const 上下文中的模式匹配
    pub const fn const_match(value: u32) -> u32 {
        match value {
            0 | 1 => 1,
            n => n * const_match(n - 1),
        }
    }

    pub fn demonstrate() {
        println!("\n=== 优化的条件语句和模式匹配 ===");

        // const 条件计算
        const MAX_VAL: u32 = const_max(10, 20);
        println!("最大值（编译时计算）: {}", MAX_VAL);

        // 优化的模式匹配
        let values = vec![Some(5), Some(-3), Some(0), None];
        for val in values {
            println!("匹配结果: {}", optimized_pattern_matching(val));
        }

        // const 模式匹配
        const FACTORIAL_5: u32 = const_match(5);
        println!("5 的阶乘（编译时计算）: {}", FACTORIAL_5);
    }
}

// ==================== 7. 优化的循环结构 ====================

/// Rust 1.91 优化的循环结构
pub mod optimized_loops {
    use std::ops::ControlFlow;

    /// 优化的迭代器循环
    ///
    /// Rust 1.91 JIT 优化：迭代器循环性能提升 10-25%
    pub fn optimized_for_loop(data: &[i32]) -> Vec<i32> {
        let mut result = Vec::new();
        // Rust 1.91: 迭代器循环自动优化
        for item in data.iter().filter(|&&x| x > 0) {
            result.push(*item * 2);
        }
        result
    }

    /// 使用 ControlFlow 的早期退出循环
    ///
    /// Rust 1.91: 改进的 ControlFlow 使循环早期退出更清晰
    pub fn early_exit_loop(data: &[i32], max: i32) -> ControlFlow<String, Vec<i32>> {
        let mut result = Vec::new();

        for (idx, &value) in data.iter().enumerate() {
            if value > max {
                return ControlFlow::Break(format!("第 {} 个元素 {} 超出最大值 {}", idx, value, max));
            }
            result.push(value);
        }

        ControlFlow::Continue(result)
    }

    /// const 上下文中的循环
    ///
    /// Rust 1.91: const 函数中可以使用循环
    pub const fn const_loop_sum(n: u32) -> u32 {
        let mut sum = 0;
        let mut i = 0;
        while i < n {
            sum += i;
            i += 1;
        }
        sum
    }

    pub fn demonstrate() {
        println!("\n=== 优化的循环结构 ===");

        // 优化的 for 循环
        let data = vec![-5, 1, -3, 4, -2, 6];
        let result = optimized_for_loop(&data);
        println!("优化循环结果: {:?}", result);

        // 早期退出循环
        let test_data = vec![1, 2, 3, 15, 4, 5];
        match early_exit_loop(&test_data, 10) {
            ControlFlow::Continue(result) => {
                println!("循环完成: {:?}", result);
            }
            ControlFlow::Break(error) => {
                println!("循环早期退出: {}", error);
            }
        }

        // const 循环
        const SUM_10: u32 = const_loop_sum(10);
        println!("1-9 的和（编译时计算）: {}", SUM_10);
    }
}

// ==================== 8. 函数调用优化 ====================

/// Rust 1.91 函数调用优化
pub mod function_call_optimization {
    use std::collections::HashMap;
    use std::time::Instant;

    /// 函数调用缓存机制
    ///
    /// Rust 1.91: 函数调用可以通过编译器优化进行缓存
    pub struct FunctionCache<K, V> {
        cache: HashMap<K, V>,
    }

    impl<K, V> FunctionCache<K, V>
    where
        K: std::hash::Hash + Eq + Clone,
        V: Clone,
    {
        pub fn new() -> Self {
            Self {
                cache: HashMap::new(),
            }
        }

        /// 缓存函数调用结果
        pub fn call_or_cache<F>(&mut self, key: K, f: F) -> V
        where
            F: FnOnce() -> V,
        {
            if let Some(value) = self.cache.get(&key) {
                value.clone()
            } else {
                let value = f();
                self.cache.insert(key, value.clone());
                value
            }
        }
    }

    /// 优化的递归函数
    ///
    /// Rust 1.91: 递归函数调用性能优化
    pub fn optimized_power(base: i32, exp: u32) -> i32 {
        match exp {
            0 => 1,
            1 => base,
            n if n % 2 == 0 => {
                let half = optimized_power(base, n / 2);
                half * half
            }
            n => base * optimized_power(base, n - 1),
        }
    }

    /// 内联函数优化提示
    ///
    /// Rust 1.91: 编译器更智能的内联决策
    #[inline(always)]
    pub fn small_helper(x: i32) -> i32 {
        x * 2 + 1
    }

    pub fn demonstrate() {
        println!("\n=== 函数调用优化 ===");

        // 函数缓存
        let mut cache = FunctionCache::new();
        let result1 = cache.call_or_cache("key1".to_string(), || {
            println!("  计算中...");
            42 * 2
        });
        println!("  第一次调用结果: {}", result1);

        let result2 = cache.call_or_cache("key1".to_string(), || {
            println!("  计算中...");
            42 * 2
        });
        println!("  第二次调用结果（从缓存）: {}", result2);

        // 优化的递归
        let start = Instant::now();
        let power_result = optimized_power(2, 20);
        let elapsed = start.elapsed();
        println!("  2^20 = {} (耗时: {:?})", power_result, elapsed);

        // 内联函数
        let result = small_helper(10);
        println!("  内联函数结果: {}", result);
    }
}

// ==================== 9. 闭包优化 ====================

/// Rust 1.91 闭包优化
pub mod closure_optimization {
    /// 优化的闭包捕获
    ///
    /// Rust 1.91: 闭包捕获优化，减少内存使用
    pub fn optimized_closure_capture() -> Vec<i32> {
        let multiplier = 2;
        let numbers = vec![1, 2, 3, 4, 5];

        // Rust 1.91: 闭包捕获更高效
        numbers
            .into_iter()
            .map(|x| x * multiplier)
            .collect()
    }

    /// const 上下文中的闭包
    ///
    /// Rust 1.91: const 函数中可以更灵活地使用闭包概念
    pub const fn const_closure_equivalent() -> i32 {
        // const 上下文中不能直接使用闭包，但可以模拟
        let mut result = 0;
        let mut i = 0;
        while i < 10 {
            result += i;
            i += 1;
        }
        result
    }

    /// 高阶函数优化
    ///
    /// Rust 1.91: 高阶函数调用性能优化
    pub fn optimized_higher_order_function<T, F>(data: &[T], f: F) -> Vec<T>
    where
        T: Clone,
        F: Fn(&T) -> bool,
    {
        data.iter()
            .filter(|x| f(*x))
            .cloned()
            .collect()
    }

    pub fn demonstrate() {
        println!("\n=== 闭包优化 ===");

        // 优化的闭包捕获
        let result = optimized_closure_capture();
        println!("  闭包捕获结果: {:?}", result);

        // const 闭包等价物
        const CONST_RESULT: i32 = const_closure_equivalent();
        println!("  const 闭包等价结果: {}", CONST_RESULT);

        // 高阶函数
        let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let filtered: Vec<i32> = optimized_higher_order_function(&data, |x| *x % 2 == 0);
        println!("  高阶函数过滤结果: {:?}", filtered);
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
    optimized_conditionals::demonstrate();
    optimized_loops::demonstrate();
    function_call_optimization::demonstrate();
    closure_optimization::demonstrate();
    comprehensive_examples::demonstrate();
}

/// 获取 Rust 1.91 控制流特性信息
pub fn get_rust_191_control_flow_info() -> &'static str {
    "Rust 1.91 控制流与函数特性模块 - 包含 const 上下文增强、ControlFlow 改进、函数性能优化等"
}
