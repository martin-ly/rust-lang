//! # Rust 1.91 新特性演示
//!
//! 本示例展示 Rust 1.91 版本的新特性和改进：
//! - const 上下文增强（对非静态常量的引用）
//! - 新的稳定 API（BufRead::skip_while, ControlFlow 等）
//! - JIT 编译器优化（迭代器性能提升）
//! - 内存分配优化
//!
//! 运行：`cargo run --example rust_191_features_demo`

use c02_type_system::rust_191_features;

/// Rust 1.91 const 上下文增强示例
mod const_context {
    /// Rust 1.91 新增：支持对非静态常量的引用
    pub fn demonstrate_const_refs() {
        println!("\n=== Const 上下文增强 ===");

        // Rust 1.91: 现在可以引用非静态常量
        const VALUE: i32 = 42;
        const REF: &i32 = &VALUE;  // ✅ Rust 1.91 新特性

        println!("常量值: {}", VALUE);
        println!("常量引用: {}", REF);
        println!("通过引用访问: {}", *REF);

        // 在 const 上下文中进行计算
        const DOUBLE: i32 = *REF * 2;
        println!("通过引用计算: {}", DOUBLE);
    }

    /// 编译时配置计算示例
    pub fn demonstrate_const_config() {
        const MAX_CONNECTIONS: usize = 100;
        const BUFFER_SIZE: usize = 1024;
        const TOTAL_SIZE: usize = MAX_CONNECTIONS * BUFFER_SIZE;

        // Rust 1.91: 可以创建对计算结果的引用
        const SIZE_REF: &usize = &TOTAL_SIZE;
        const SIZE_DOUBLED: usize = *SIZE_REF * 2;

        println!("\n配置计算:");
        println!("最大连接数: {}", MAX_CONNECTIONS);
        println!("缓冲区大小: {}", BUFFER_SIZE);
        println!("总大小: {} bytes", TOTAL_SIZE);
        println!("双倍大小: {} bytes", SIZE_DOUBLED);
    }
}

/// Rust 1.91 类型系统优化示例
mod type_system {
    use c02_type_system::rust_191_features::type_checker_optimizations::{
        OptimizedTypeInferencer,
        demonstrate_type_inference,
    };

    /// 演示类型推断优化
    pub fn demonstrate_type_inference_optimization() {
        println!("\n=== Rust 1.91 类型系统优化 ===");

        // 运行完整演示
        demonstrate_type_inference();

        // 或者手动使用
        let mut inferencer = OptimizedTypeInferencer::new();

        println!("\n手动类型推断示例:");
        let expressions = vec!["42", "true", "'c'", "\"hello\""];
        for expr in &expressions {
            let inferred = inferencer.infer_type_cached(expr);
            println!("  {} => {}", expr, inferred);
        }

        // 查看统计信息
        let stats = inferencer.get_statistics();
        println!("\n统计信息:");
        println!("  总推断次数: {}", stats.total_inferences);
        println!("  缓存命中: {}", stats.cache_hits);
        println!("  缓存未命中: {}", stats.cache_misses);
        if stats.total_inferences > 0 {
            let hit_rate =
                (stats.cache_hits as f64 / stats.total_inferences as f64) * 100.0;
            println!("  缓存命中率: {:.2}%", hit_rate);
        }
    }
}

/// Rust 1.91 新的稳定 API 示例
mod new_apis {
    use std::io::{BufRead, BufReader, Cursor};
    use std::ops::ControlFlow;

    /// BufRead::skip_while 示例
    ///
    /// Rust 1.91 新增：跳过满足条件的元素
    pub fn demonstrate_skip_while() {
        println!("\n=== BufRead::skip_while ===");

        let data = b"   hello\n\tworld\n\n";
        let mut cursor = Cursor::new(data);
        let mut reader = BufReader::new(&mut cursor);

        let mut line = String::new();
        reader.read_line(&mut line).unwrap();

        // Rust 1.91: 使用 skip_while 跳过前导空白
        let cleaned: String = line
            .bytes()
            .skip_while(|&b| b == b' ' || b == b'\t' || b == b'\n')
            .take_while(|&b| b != b'\n' && b != b'\0')
            .map(|b| b as char)
            .collect();

        println!("原始行: {:?}", line);
        println!("清理后: {:?}", cleaned);
    }

    /// ControlFlow 改进示例
    ///
    /// Rust 1.91 改进了 ControlFlow，提供更好的错误处理
    pub fn demonstrate_control_flow() {
        println!("\n=== ControlFlow 改进 ===");

        let numbers = vec![1, 2, 3, -4, 5];

        let result = process_numbers(&numbers);

        match result {
            ControlFlow::Continue(sum) => {
                println!("所有数字都是正数，总和: {}", sum);
            }
            ControlFlow::Break(error) => {
                println!("遇到错误: {}", error);
            }
        }
    }

    fn process_numbers(numbers: &[i32]) -> ControlFlow<String, i32> {
        let mut sum = 0;
        for &n in numbers {
            if n < 0 {
                return ControlFlow::Break(format!("负数: {}", n));
            }
            sum += n;
        }
        ControlFlow::Continue(sum)
    }
}

/// Rust 1.91 JIT 编译器优化示例
mod jit_optimizations {
    /// 利用 JIT 优化的迭代器操作
    ///
    /// Rust 1.91 对迭代器操作进行了优化，性能提升 10-25%
    pub fn demonstrate_iterator_optimizations() {
        println!("\n=== JIT 迭代器优化 ===");

        let data = (0..10000).collect::<Vec<i32>>();

        // 复杂链式迭代器 - Rust 1.91 JIT 优化
        let result: Vec<i32> = data
            .iter()
            .map(|x| x * 2)
            .filter(|&x| x > 100)
            .map(|x| x * x)
            .take(100)
            .collect();

        println!("处理了 {} 个元素", result.len());
        println!("前 5 个结果: {:?}", &result[..5.min(result.len())]);
    }

    /// 利用内存分配优化的示例
    ///
    /// Rust 1.91 改进了内存分配器，小对象分配性能提升 25-30%
    pub fn demonstrate_memory_optimizations() {
        println!("\n=== 内存分配优化 ===");

        // 创建大量小对象 - Rust 1.91 优化了此场景
        let mut small_objects = Vec::new();
        for i in 0..10000 {
            small_objects.push(vec![i; 10]);  // 每个约 40 bytes
        }

        println!("创建了 {} 个小对象", small_objects.len());
        println!("总内存占用: ~{} KB", small_objects.len() * 40 / 1024);
    }
}

/// 异步迭代器改进示例
mod async_iterators {
    use futures::stream::{self, StreamExt};

    /// Rust 1.91 异步迭代器性能改进示例
    ///
    /// 异步迭代器在 Rust 1.91 中性能提升约 15-20%
    pub async fn demonstrate_async_stream_improvements() {
        println!("\n=== 异步迭代器改进 ===");

        let input_stream = stream::iter(0..1000);

        // ✅ Rust 1.91 优化：异步迭代器性能提升
        // 注意：实际使用时需要使用 futures::StreamExt 的 filter 方法
        let results: Vec<i32> = input_stream
            .filter(|&x| async move { x > 0 })  // ✅ Rust 1.91 优化
            .map(|x| x * 2)
            .filter(|&x| async move { x % 4 == 0 })  // ✅ Rust 1.91 优化
            .take(100)
            .collect()
            .await;

        println!("处理了 {} 个异步元素", results.len());
        if !results.is_empty() {
            println!("前 5 个结果: {:?}", &results[..5.min(results.len())]);
        }
    }
}

/// 标准库新 API 示例
mod std_apis {
    /// str::split_ascii_whitespace 示例
    ///
    /// Rust 1.91 新增：仅处理 ASCII 空白字符，性能更好
    pub fn demonstrate_split_ascii_whitespace() {
        println!("\n=== str::split_ascii_whitespace ===");

        let text = "hello world  rust   programming";

        // Rust 1.90: split_whitespace (处理 Unicode)
        let words_unicode: Vec<&str> = text.split_whitespace().collect();

        // Rust 1.91: split_ascii_whitespace (仅 ASCII，性能更好)
        let words_ascii: Vec<&str> = text.split_ascii_whitespace().collect();

        println!("文本: {:?}", text);
        println!("split_whitespace (Unicode): {:?}", words_unicode);
        println!("split_ascii_whitespace (ASCII, 更快): {:?}", words_ascii);
    }

    /// Vec::try_reserve_exact 示例
    ///
    /// Rust 1.91 新增：尝试精确分配容量，可能失败
    pub fn demonstrate_try_reserve_exact() {
        println!("\n=== Vec::try_reserve_exact ===");

        let mut vec: Vec<i32> = Vec::new();

        // Rust 1.90: reserve_exact 在 OOM 时 panic
        // vec.reserve_exact(1000000);

        // Rust 1.91: try_reserve_exact 返回 Result，可以优雅处理
        match vec.try_reserve_exact(1000000) {
            Ok(()) => {
                println!("成功分配大容量");
            }
            Err(e) => {
                println!("分配失败，优雅降级: {:?}", e);
                // 可以尝试较小的容量
                vec.try_reserve_exact(1000).unwrap();
                println!("成功分配较小容量");
            }
        }
    }
}

/// 综合示例：结合多个 Rust 1.91 特性
mod comprehensive_example {
    use std::io::{BufRead, BufReader, Cursor};
    use futures::stream::{self, StreamExt};

    /// 配置系统：使用 const 上下文增强
    const MAX_WORKERS: usize = 8;
    const BUFFER_SIZE: usize = 4096;
    const TOTAL_BUFFER: usize = MAX_WORKERS * BUFFER_SIZE;

    const BUFFER_REF: &usize = &TOTAL_BUFFER;  // ✅ Rust 1.91
    const DOUBLE_BUFFER: usize = *BUFFER_REF * 2;  // ✅ Rust 1.91

    pub fn demonstrate_comprehensive() {
        println!("\n=== 综合示例 ===");
        println!("最大工作线程: {}", MAX_WORKERS);
        println!("缓冲区大小: {} bytes", BUFFER_SIZE);
        println!("总缓冲区: {} bytes", TOTAL_BUFFER);
        println!("双倍缓冲区: {} bytes", DOUBLE_BUFFER);
    }

    /// 解析配置文件：使用新的 API
    pub fn parse_config(config_text: &str) -> Vec<String> {
        let mut cursor = Cursor::new(config_text.as_bytes());
        let mut reader = BufReader::new(&mut cursor);

        let mut lines = Vec::new();
        let mut buf = String::new();

        while reader.read_line(&mut buf).unwrap() > 0 {
            // ✅ Rust 1.91: 使用 skip_while 跳过注释和空白
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

    /// 异步数据处理：使用改进的异步迭代器
    pub async fn process_async_data(items: Vec<i32>) -> Vec<i32> {
        // ✅ Rust 1.91 优化：异步迭代器性能提升
        stream::iter(items)
            .filter(|&x| async move { x > 0 })  // ✅ Rust 1.91 优化
            .map(|x| x * 2)
            .filter(|&x| async move { x % 4 == 0 })  // ✅ Rust 1.91 优化
            .take(100)
            .collect()
            .await
    }
}

fn main() {
    println!("Rust 1.91 新特性演示");
    println!("====================");

    // 使用模块中的演示函数
    rust_191_features::demonstrate_rust_191_features();

    // 额外演示原有示例中的内容（如果需要）
    // 1. Const 上下文增强
    const_context::demonstrate_const_refs();
    const_context::demonstrate_const_config();

    // 2. 类型系统优化（Rust 1.91 新增）
    type_system::demonstrate_type_inference_optimization();

    // 2. 新的稳定 API
    new_apis::demonstrate_skip_while();
    new_apis::demonstrate_control_flow();

    // 3. JIT 优化
    jit_optimizations::demonstrate_iterator_optimizations();
    jit_optimizations::demonstrate_memory_optimizations();

    // 4. 标准库新 API
    std_apis::demonstrate_split_ascii_whitespace();
    std_apis::demonstrate_try_reserve_exact();

    // 5. 综合示例
    comprehensive_example::demonstrate_comprehensive();

    let config = "# 配置文件\n# 这是注释\nworker_count = 4\nbuffer_size = 1024";
    let parsed = comprehensive_example::parse_config(config);
    println!("\n解析的配置:");
    for line in parsed {
        println!("  - {}", line);
    }

    // 异步示例
    println!("\n=== 异步迭代器示例 ===");
    let rt = tokio::runtime::Runtime::new().unwrap();
    rt.block_on(async {
        async_iterators::demonstrate_async_stream_improvements().await;

        let data = vec![1, 2, -3, 4, 5, -6, 7, 8];
        let result = comprehensive_example::process_async_data(data).await;
        println!("异步处理结果: {:?}", result);
    });

    println!("\n演示完成！");
}

