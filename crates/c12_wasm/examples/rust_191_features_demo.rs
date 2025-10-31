//! Rust 1.91 WebAssembly 特性演示示例
//!
//! 本示例展示了 Rust 1.91 在 WebAssembly 场景中的应用，包括：
//!
//! 1. const 上下文增强（WASM 配置计算）
//! 2. 新的稳定 API（WASM 数据处理）
//! 3. JIT 编译器优化（WASM 性能提升）
//! 4. 内存分配器优化（WASM 内存优化）
//! 5. WASM 编译优化（类型检查器优化）
//! 6. wasm-bindgen 集成优化
//! 7. WASM 二进制大小优化
//! 8. WASM 运行时性能优化

use c12_wasm::rust_191_features::*;

fn main() {
    println!("=== Rust 1.91 WebAssembly 特性演示 ===\n");

    // 1. Const 上下文增强
    demo_const_context();

    // 2. 新的稳定 API
    demo_new_apis();

    // 3. JIT 编译器优化
    demo_jit_optimizations();

    // 4. 内存分配器优化
    demo_memory_optimizations();

    // 5. WASM 编译优化
    demo_compilation_optimizations();

    // 6. wasm-bindgen 集成优化
    demo_wasm_bindgen_optimizations();

    // 7. WASM 二进制大小优化
    demo_binary_size_optimizations();

    // 8. WASM 运行时性能优化
    demo_runtime_optimizations();

    println!("\n=== 所有演示完成 ===");
}

/// 演示 const 上下文增强
fn demo_const_context() {
    println!("1. Const 上下文增强（WASM 配置计算）");
    println!("   Rust 1.91: 可以在 const 上下文中创建对非静态常量的引用\n");

    const_wasm_config::WasmConfigSystem::demonstrate();
    const_wasm_config::WasmExportConfig::demonstrate();
}

/// 演示新的稳定 API
fn demo_new_apis() {
    println!("\n2. 新的稳定 API（WASM 数据处理）");
    println!("   Rust 1.91: BufRead::skip_while, ControlFlow 改进\n");

    use std::io::{BufReader, Cursor};
    use std::ops::ControlFlow;

    let wasm_data = "# WASM 配置\nmax_memory_pages = 65536\n# 注释行\nstack_size = 1048576";
    let mut cursor = Cursor::new(wasm_data.as_bytes());
    let mut reader = BufReader::new(&mut cursor);

    match wasm_new_apis::parse_wasm_config(&mut reader) {
        Ok(lines) => {
            println!("   解析的 WASM 配置:");
            for line in lines {
                println!("     - {}", line);
            }
        }
        Err(e) => println!("   解析错误: {}", e),
    }

    // 使用改进的 ControlFlow
    match wasm_new_apis::validate_wasm_memory(1000, 65536) {
        ControlFlow::Continue(remaining) => {
            println!("\n   WASM 内存验证成功，剩余页数: {}", remaining);
        }
        ControlFlow::Break(error) => {
            println!("\n   WASM 内存验证失败: {}", error);
        }
    }
}

/// 演示 JIT 编译器优化
fn demo_jit_optimizations() {
    println!("\n3. JIT 编译器优化（WASM 性能提升）");
    println!("   Rust 1.91: 迭代器操作性能提升 10-25%\n");

    wasm_jit_optimizations::demonstrate_wasm_performance();
}

/// 演示内存分配器优化
fn demo_memory_optimizations() {
    println!("\n4. 内存分配器优化（WASM 内存优化）");
    println!("   Rust 1.91: 小对象分配性能提升 25-30%\n");

    wasm_memory_optimizations::demonstrate_memory_optimizations();
}

/// 演示 WASM 编译优化
fn demo_compilation_optimizations() {
    println!("\n5. WASM 编译优化（类型检查器优化）");
    println!("   Rust 1.91: 编译时间减少 10-20%\n");

    wasm_compilation_optimizations::demonstrate_compilation_performance();
}

/// 演示 wasm-bindgen 集成优化
fn demo_wasm_bindgen_optimizations() {
    println!("\n6. wasm-bindgen 集成优化");
    println!("   Rust 1.91: 使用 const 上下文优化配置\n");

    wasm_bindgen_optimizations::demonstrate_wasm_bindgen_config();
}

/// 演示 WASM 二进制大小优化
fn demo_binary_size_optimizations() {
    println!("\n7. WASM 二进制大小优化");
    println!("   Rust 1.91: 代码生成更紧凑，二进制大小减少约 5-10%\n");

    wasm_binary_size_optimizations::demonstrate_binary_size_optimization();
}

/// 演示 WASM 运行时性能优化
fn demo_runtime_optimizations() {
    println!("\n8. WASM 运行时性能优化");
    println!("   Rust 1.91: JIT 优化和内存分配优化提升运行时性能\n");

    wasm_runtime_optimizations::demonstrate_runtime_optimization();
}

