//! Rust 1.92.0 WebAssembly 特性演示示例
//!
//! 本示例展示了 Rust 1.92.0 在 WebAssembly 场景中的应用，包括：
//!
//! 1. MaybeUninit 在 WASM 内存管理中的应用
//! 2. NonZero::div_ceil 在 WASM 缓冲区分配中的应用
//! 3. 联合体原始引用在 WASM FFI 中的应用
//! 4. 迭代器方法特化在 WASM 性能优化中的应用
//! 5. rotate_right 在 WASM 数据处理中的应用
//! 6. Location::file_as_c_str 在 WASM 调试中的应用

use c12_wasm::rust_192_features::*;
use std::num::NonZeroUsize;

fn main() {
    println!("=== Rust 1.92.0 WebAssembly 特性演示 ===\n");

    // 1. MaybeUninit 在 WASM 内存管理中的应用
    demo_maybeuninit();

    // 2. NonZero::div_ceil 在 WASM 缓冲区分配中的应用
    demo_nonzero_div_ceil();

    // 3. 联合体原始引用在 WASM FFI 中的应用
    demo_union_raw_refs();

    // 4. 迭代器方法特化在 WASM 性能优化中的应用
    demo_iterator_specialization();

    // 5. rotate_right 在 WASM 数据处理中的应用
    demo_rotate_right();

    // 6. Location::file_as_c_str 在 WASM 调试中的应用
    demo_location_debug();

    println!("\n=== 所有演示完成 ===");
}

/// 演示 MaybeUninit 在 WASM 内存管理中的应用
fn demo_maybeuninit() {
    println!("1. MaybeUninit 在 WASM 内存管理中的应用");
    println!("   Rust 1.92.0: 正式文档化的 MaybeUninit 使用模式\n");

    let mut buffer = WasmBuffer::new(100);
    let data = b"Hello, WASM!";
    unsafe {
        let written = buffer.write(data);
        println!("   写入 {} 字节", written);
        println!("   已初始化长度: {}", buffer.initialized_len());
        println!("   容量: {}", buffer.capacity());
    }
}

/// 演示 NonZero::div_ceil 在 WASM 缓冲区分配中的应用
fn demo_nonzero_div_ceil() {
    println!("\n2. NonZero::div_ceil 在 WASM 缓冲区分配中的应用");
    println!("   Rust 1.92.0: 新增的 div_ceil 方法可以安全地计算向上取整除法\n");

    // 计算缓冲区块数
    let chunk_size = NonZeroUsize::new(1024).unwrap();
    let total_size = 5000;
    let chunks = calculate_buffer_chunks(total_size, chunk_size);
    println!("   总大小: {} 字节", total_size);
    println!("   块大小: {} 字节", chunk_size);
    println!("   需要的块数: {}", chunks);

    // WASM 内存分配器配置
    let allocator = WasmAllocatorConfig::new(NonZeroUsize::new(65536).unwrap(), 100);
    let pages = allocator.calculate_pages(1000000);
    println!("\n   WASM 页面大小: 65536 字节");
    println!("   1MB 数据需要页面数: {}", pages);

    // WASM 数据传输配置
    let transfer = WasmTransferConfig::new(NonZeroUsize::new(1024).unwrap());
    let packets = transfer.calculate_packets(5000);
    println!("\n   数据包大小: 1024 字节");
    println!("   5000 字节需要数据包数: {}", packets);
}

/// 演示联合体原始引用在 WASM FFI 中的应用
fn demo_union_raw_refs() {
    println!("\n3. 联合体原始引用在 WASM FFI 中的应用");
    println!("   Rust 1.92.0: 允许在安全代码中使用原始引用访问联合体字段\n");

    let mut union = WasmFFIUnion::new();
    union.set_integer(12345);
    println!("   设置的整数值: {}", union.get_integer());

    let raw_ref = union.get_integer_raw();
    println!("   原始引用地址: {:p}", raw_ref);

    let mut_raw_ref = union.get_integer_mut_raw();
    println!("   可变原始引用地址: {:p}", mut_raw_ref);
}

/// 演示迭代器方法特化在 WASM 性能优化中的应用
fn demo_iterator_specialization() {
    println!("\n4. 迭代器方法特化在 WASM 性能优化中的应用");
    println!("   Rust 1.92.0: 为 TrustedLen 迭代器特化了比较方法\n");

    let vec1 = vec![1, 2, 3, 4, 5];
    let vec2 = vec![1, 2, 3, 4, 5];
    let vec3 = vec![1, 2, 3, 4, 6];

    // 使用特化的迭代器比较
    let are_equal_1_2 = wasm_optimized_array_eq(&vec1, &vec2);
    let are_equal_1_3 = wasm_optimized_array_eq(&vec1, &vec3);

    println!("   向量1: {:?}", vec1);
    println!("   向量2: {:?}", vec2);
    println!("   向量3: {:?}", vec3);
    println!("   向量1 == 向量2: {}", are_equal_1_2);
    println!("   向量1 == 向量3: {}", are_equal_1_3);
}

/// 演示 rotate_right 在 WASM 数据处理中的应用
fn demo_rotate_right() {
    println!("\n5. rotate_right 在 WASM 数据处理中的应用");
    println!("   Rust 1.92.0: 稳定化的 rotate_right 方法提供高效的数据旋转\n");

    let mut data = vec![1, 2, 3, 4, 5, 6, 7, 8];
    println!("   原始数据: {:?}", data);

    wasm_rotate_data(&mut data, 3);
    println!("   右旋转 3 位后: {:?}", data);

    // 循环缓冲区示例
    let mut circular_buffer: WasmCircularBuffer<i32> = WasmCircularBuffer::new(5);
    circular_buffer.rotate(2);
    println!("   循环缓冲区旋转完成");
    println!("   缓冲区内容: {:?}", circular_buffer.buffer());
}

/// 演示 Location::file_as_c_str 在 WASM 调试中的应用
fn demo_location_debug() {
    println!("\n6. Location::file_as_c_str 在 WASM 调试中的应用");
    println!("   Rust 1.92.0: 稳定化的 Location::file_as_c_str 提供调试信息\n");

    let debug_info = WasmDebugInfo::from_caller();
    println!("   调用位置: {}", debug_info.format());
    println!("   文件: {}", debug_info.file);
    println!("   行号: {}", debug_info.line);
    println!("   列号: {}", debug_info.column);
}
