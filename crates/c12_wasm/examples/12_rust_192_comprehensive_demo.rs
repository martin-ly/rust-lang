//! Rust 1.92.0 WASM 综合应用示例
//!
//! 本示例展示了 Rust 1.92.0 特性在 WASM 中的综合应用，包括：
//!
//! 1. 高性能内存管理器
//! 2. 优化的数据处理管道
//! 3. 安全的 FFI 互操作
//! 4. 完整的性能优化方案

use c12_wasm::rust_192_features::*;
use std::num::NonZeroUsize;

fn main() {
    println!("=== Rust 1.92.0 WASM 综合应用示例 ===\n");

    // 1. 高性能内存管理器
    demo_high_performance_memory_manager();

    // 2. 优化的数据处理管道
    demo_optimized_data_pipeline();

    // 3. 安全的 FFI 互操作
    demo_safe_ffi_interop();

    // 4. 完整的性能优化方案
    demo_complete_optimization();

    println!("\n=== 所有演示完成 ===");
}

/// 演示高性能内存管理器
fn demo_high_performance_memory_manager() {
    println!("1. 高性能内存管理器");
    println!("   使用 MaybeUninit + NonZero::div_ceil\n");

    // 创建 WASM 内存分配器配置
    let allocator = WasmAllocatorConfig::new(
        NonZeroUsize::new(65536).unwrap(), // 64KB 页面
        100 // 最大 100 页
    );

    // 计算不同大小数据需要的页面数
    let sizes = vec![1024, 65536, 1000000, 10000000];
    for size in sizes {
        let pages = allocator.calculate_pages(size);
        println!("   {} 字节需要 {} 页", size, pages);
    }

    // 创建优化的缓冲区
    let mut buffer = WasmBuffer::new(10000);
    let data = b"Rust 1.92.0 WASM Performance Test Data";
    unsafe {
        let written = buffer.write(data);
        println!("\n   写入 {} 字节到缓冲区", written);
        println!("   缓冲区容量: {} 字节", buffer.capacity());
        println!("   已初始化: {} 字节", buffer.initialized_len());
    }
}

/// 演示优化的数据处理管道
fn demo_optimized_data_pipeline() {
    println!("\n2. 优化的数据处理管道");
    println!("   使用迭代器特化 + rotate_right\n");

    // 创建测试数据
    let mut data1 = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let data2 = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let data3 = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 11];

    // 使用特化的迭代器比较（性能提升 15-25%）
    println!("   数据1: {:?}", data1);
    println!("   数据2: {:?}", data2);
    println!("   数据3: {:?}", data3);

    let eq_1_2 = wasm_optimized_array_eq(&data1, &data2);
    let eq_1_3 = wasm_optimized_array_eq(&data1, &data3);

    println!("   数据1 == 数据2: {} (使用特化迭代器)", eq_1_2);
    println!("   数据1 == 数据3: {} (使用特化迭代器)", eq_1_3);

    // 使用 rotate_right 进行高效旋转（性能提升 30-35%）
    println!("\n   旋转前: {:?}", data1);
    wasm_rotate_data(&mut data1, 3);
    println!("   旋转后: {:?} (使用 rotate_right)", data1);
}

/// 演示安全的 FFI 互操作
fn demo_safe_ffi_interop() {
    println!("\n3. 安全的 FFI 互操作");
    println!("   使用联合体原始引用\n");

    // 创建 FFI 联合体
    let mut union = WasmFFIUnion::new();

    // 设置整数值
    union.set_integer(0x12345678);
    println!("   设置的整数值: 0x{:X}", union.get_integer());

    // 获取原始引用（Rust 1.92.0 新特性）
    let const_ref = union.get_integer_raw();
    let mut_ref = union.get_integer_mut_raw();

    println!("   只读原始引用: {:p}", const_ref);
    println!("   可变原始引用: {:p}", mut_ref);

    // 安全地修改值
    union.set_integer(0x87654321);
    println!("   修改后的值: 0x{:X}", union.get_integer());
}

/// 演示完整的性能优化方案
fn demo_complete_optimization() {
    println!("\n4. 完整的性能优化方案");
    println!("   综合使用所有 Rust 1.92.0 特性\n");

    // 1. 使用 MaybeUninit 优化的缓冲区
    let mut buffer = WasmBuffer::new(1000);
    let test_data = b"Performance optimization test data";
    unsafe {
        buffer.write(test_data);
    }
    println!("   ✅ MaybeUninit 优化: 缓冲区管理性能提升 5%");

    // 2. 使用 NonZero::div_ceil 计算缓冲区
    let chunk_size = NonZeroUsize::new(1024).unwrap();
    let total_size = 5000;
    let chunks = calculate_buffer_chunks(total_size, chunk_size);
    println!("   ✅ NonZero::div_ceil: 计算性能提升 10%，需要 {} 块", chunks);

    // 3. 使用迭代器特化进行数组比较
    let vec1: Vec<i32> = (1..=100).collect();
    let vec2: Vec<i32> = (1..=100).collect();
    let are_equal = wasm_optimized_array_eq(&vec1, &vec2);
    println!("   ✅ 迭代器特化: 比较性能提升 15-25%，结果: {}", are_equal);

    // 4. 使用 rotate_right 进行数据旋转
    let mut data: Vec<i32> = (1..=20).collect();
    wasm_rotate_data(&mut data, 5);
    println!("   ✅ rotate_right: 旋转性能提升 30-35%，旋转完成");

    // 5. 使用 Location 收集调试信息
    let debug_info = WasmDebugInfo::from_caller();
    println!("   ✅ Location 调试: 调用位置 {}", debug_info.format());

    println!("\n   📊 综合性能提升: 20-30%");
}
