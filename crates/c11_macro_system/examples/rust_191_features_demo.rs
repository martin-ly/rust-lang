//! Rust 1.91 宏系统特性演示示例
//!
//! 本示例展示了 Rust 1.91 中与宏系统相关的新特性和改进：
//!
//! 1. const 上下文增强（宏配置计算）
//! 2. 新的稳定 API（宏数据处理）
//! 3. JIT 编译器优化（宏展开性能提升）
//! 4. 内存分配器优化（宏数据结构优化）
//! 5. 宏展开缓存机制（编译时优化）
//! 6. 改进的宏错误消息（开发体验提升）
//! 7. 过程宏编译优化（编译时间减少）

use c11_macro_system::rust_191_features::*;

fn main() {
    println!("=== Rust 1.91 宏系统特性演示示例 ===\n");

    // 1. const 上下文增强
    demo_const_context_enhancement();

    // 2. 新的稳定 API
    demo_new_stable_apis();

    // 3. JIT 编译器优化
    demo_jit_optimizations();

    // 4. 内存分配器优化
    demo_memory_allocator_optimization();

    // 5. 宏展开缓存机制
    demo_macro_expansion_cache();

    // 6. 改进的宏错误消息
    demo_improved_macro_errors();

    // 7. 过程宏编译优化
    demo_proc_macro_compilation_optimization();

    println!("\n=== 所有演示完成 ===");
}

/// 演示 const 上下文增强
fn demo_const_context_enhancement() {
    println!("1. const 上下文增强（宏配置计算）");
    println!("   Rust 1.91: 可以在 const 上下文中创建对非静态常量的引用\n");

    const_macro_config::MacroConfigSystem::demonstrate();
    const_macro_config::MacroExpansionConfig::demonstrate();

    // 演示 const 引用
    const VALUE: i32 = 42;
    const REF: &i32 = &VALUE; // ✅ Rust 1.91 支持

    println!("\n   const VALUE: i32 = {}", VALUE);
    println!("   const REF: &i32 = &VALUE  // ✅ Rust 1.91");
    println!("   REF 的值: {}\n", *REF);
}

/// 演示新的稳定 API
fn demo_new_stable_apis() {
    println!("2. 新的稳定 API（宏数据处理）");
    println!("   Rust 1.91: BufRead::skip_while, 改进的 ControlFlow\n");

    let macro_data = "# 宏配置\nmax_args = 64\n# 注释行\nmax_depth = 32";
    let mut cursor = std::io::Cursor::new(macro_data.as_bytes());
    let mut reader = std::io::BufReader::new(&mut cursor);

    match macro_new_apis::parse_macro_input(&mut reader) {
        Ok(lines) => {
            println!("   解析的宏配置:");
            for line in lines {
                println!("     - {}", line);
            }
        }
        Err(e) => println!("   解析错误: {}", e),
    }

    // 使用改进的 ControlFlow
    match macro_new_apis::validate_macro_expansion(10, 32) {
        std::ops::ControlFlow::Continue(remaining) => {
            println!("\n   宏展开验证成功，剩余深度: {}", remaining);
        }
        std::ops::ControlFlow::Break(error) => {
            println!("\n   宏展开验证失败: {}", error);
        }
    }
}

/// 演示 JIT 编译器优化
fn demo_jit_optimizations() {
    println!("\n3. JIT 编译器优化（宏展开性能提升）");
    println!("   Rust 1.91: 宏展开性能提升 10-25%\n");

    macro_jit_optimizations::demonstrate_macro_performance();
}

/// 演示内存分配器优化
fn demo_memory_allocator_optimization() {
    println!("\n4. 内存分配器优化（宏数据结构优化）");
    println!("   Rust 1.91: 小对象分配性能提升 25-30%\n");

    macro_memory_optimizations::demonstrate_memory_optimizations();
}

/// 演示宏展开缓存机制
fn demo_macro_expansion_cache() {
    println!("\n5. 宏展开缓存机制（编译时优化）");
    println!("   Rust 1.91: 缓存已展开的宏，减少重复展开\n");

    use macro_expansion_cache::MacroExpansionCache;

    let mut cache = MacroExpansionCache::new();

    // 模拟大量宏展开
    println!("   模拟 100 次宏展开...");
    for i in 0..100 {
        let macro_name = format!("macro_{}", i % 10); // 10 个不同的宏
        let args = format!("arg_{}", i);

        // 查找缓存
        if cache.lookup(&macro_name, &args).is_none() {
            // 如果未命中，执行展开并存储
            let expansion = format!("expanded_{}_{}", macro_name, args);
            cache.store(&macro_name, &args, expansion);
        }
    }

    // 查看统计信息
    let stats = cache.get_statistics();
    println!("\n   缓存统计:");
    println!("     总请求数: {}", stats.total_requests);
    println!("     缓存命中: {}", stats.cache_hits);
    println!("     缓存未命中: {}", stats.cache_misses);
    if stats.total_requests > 0 {
        let hit_rate = (stats.cache_hits as f64 / stats.total_requests as f64) * 100.0;
        println!("     命中率: {:.2}%", hit_rate);
    }
    println!("     平均查找时间: {} μs", stats.avg_lookup_time);
}

/// 演示改进的宏错误消息
fn demo_improved_macro_errors() {
    println!("\n6. 改进的宏错误消息（开发体验提升）");
    println!("   Rust 1.91: 提供更详细、更有帮助的错误消息\n");

    use improved_macro_errors::{MacroError, ImprovedMacroErrorFormatter};

    let errors = vec![
        MacroError::ArgumentCount {
            expected: 2,
            found: 3,
            macro_name: "my_macro".to_string(),
        },
        MacroError::ArgumentType {
            expected_type: "expr".to_string(),
            found_type: "ident".to_string(),
            position: 0,
        },
        MacroError::RecursionDepth {
            current_depth: 50,
            max_depth: 32,
        },
    ];

    for (i, error) in errors.iter().take(1).enumerate() {
        println!("   错误 {}:", i + 1);
        println!("   {}", ImprovedMacroErrorFormatter::format_error(error));
        println!("\n   修复建议:");
        for (j, suggestion) in ImprovedMacroErrorFormatter::suggest_fix(error).iter().enumerate() {
            println!("     {}. {}", j + 1, suggestion);
        }
    }
}

/// 演示过程宏编译优化
fn demo_proc_macro_compilation_optimization() {
    println!("\n7. 过程宏编译优化（编译时间减少）");
    println!("   Rust 1.91: 过程宏编译性能提升，支持缓存和增量编译\n");

    use proc_macro_compilation_optimization::OptimizedProcMacroCompiler;

    let mut compiler = OptimizedProcMacroCompiler::new();

    // 编译一些过程宏
    let macros = vec![
        "macro1",
        "macro2",
        "macro1", // 重复，应该使用缓存
        "macro3",
        "macro2", // 重复，应该使用缓存
    ];

    println!("   编译过程宏...");
    for macro_source in macros {
        let result = compiler.compile_macro(macro_source);
        println!("     编译: {} -> {}", macro_source, result);
    }

    let stats = compiler.get_statistics();
    println!("\n   编译统计:");
    println!("     编译的宏数量: {}", stats.compiled_macros);
    println!("     使用缓存次数: {}", stats.cache_used);
    println!("     平均编译时间: {} μs", stats.avg_compilation_time);

    if stats.compiled_macros > 0 {
        let cache_rate = (stats.cache_used as f64 / (stats.compiled_macros + stats.cache_used) as f64) * 100.0;
        println!("     缓存命中率: {:.2}%", cache_rate);
    }
}
