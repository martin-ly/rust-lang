//! Rust 1.92.0 WASM 特性测试
//!
//! 本测试文件包含所有 Rust 1.92.0 特性在 WASM 中的单元测试

use c12_wasm::rust_192_features::*;
use std::num::NonZeroUsize;

#[test]
fn test_wasm_buffer() {
    let mut buffer = WasmBuffer::new(100);
    assert_eq!(buffer.initialized_len(), 0);
    assert_eq!(buffer.capacity(), 100);

    unsafe {
        let data = b"test";
        let written = buffer.write(data);
        assert_eq!(written, 4);
        assert_eq!(buffer.initialized_len(), 4);

        let read_data = buffer.read(4);
        assert_eq!(read_data, b"test");
    }
}

#[test]
fn test_calculate_buffer_chunks() {
    let chunk_size = NonZeroUsize::new(1024).unwrap();

    assert_eq!(calculate_buffer_chunks(0, chunk_size), 0);
    assert_eq!(calculate_buffer_chunks(1024, chunk_size), 1);
    assert_eq!(calculate_buffer_chunks(1025, chunk_size), 2);
    assert_eq!(calculate_buffer_chunks(5000, chunk_size), 5);
}

#[test]
fn test_wasm_allocator_config() {
    let config = WasmAllocatorConfig::new(NonZeroUsize::new(65536).unwrap(), 100);

    assert_eq!(config.calculate_pages(0), 0);
    assert_eq!(config.calculate_pages(65536), 1);
    assert_eq!(config.calculate_pages(65537), 2);
    assert_eq!(config.calculate_pages(1000000), 16); // 1MB / 64KB
}

#[test]
fn test_wasm_transfer_config() {
    let config = WasmTransferConfig::new(NonZeroUsize::new(1024).unwrap());

    assert_eq!(config.calculate_packets(0), 0);
    assert_eq!(config.calculate_packets(1024), 1);
    assert_eq!(config.calculate_packets(1025), 2);
    assert_eq!(config.calculate_packets(5000), 5);
}

#[test]
fn test_wasm_ffi_union() {
    let mut union = WasmFFIUnion::new();

    union.set_integer(12345);
    assert_eq!(union.get_integer(), 12345);

    let raw_ref = union.get_integer_raw();
    assert!(!raw_ref.is_null());

    let mut_raw_ref = union.get_integer_mut_raw();
    assert!(!mut_raw_ref.is_null());
}

#[test]
fn test_wasm_optimized_array_eq() {
    let vec1 = vec![1, 2, 3, 4, 5];
    let vec2 = vec![1, 2, 3, 4, 5];
    let vec3 = vec![1, 2, 3, 4, 6];

    assert!(wasm_optimized_array_eq(&vec1, &vec2));
    assert!(!wasm_optimized_array_eq(&vec1, &vec3));
}

#[test]
fn test_wasm_optimized_vec_eq() {
    let vec1: Vec<i32> = (1..=100).collect();
    let vec2: Vec<i32> = (1..=100).collect();
    let vec3: Vec<i32> = (1..=99).collect();

    assert!(wasm_optimized_vec_eq(&vec1, &vec2));
    assert!(!wasm_optimized_vec_eq(&vec1, &vec3));
}

#[test]
fn test_wasm_rotate_data() {
    let mut data = vec![1, 2, 3, 4, 5, 6, 7, 8];
    wasm_rotate_data(&mut data, 3);

    assert_eq!(data, vec![6, 7, 8, 1, 2, 3, 4, 5]);
}

#[test]
fn test_wasm_circular_buffer() {
    let mut buffer: WasmCircularBuffer<i32> = WasmCircularBuffer::new(5);

    assert_eq!(buffer.buffer().len(), 5);

    buffer.rotate(2);
    // 验证旋转完成
    assert_eq!(buffer.buffer().len(), 5);
}

#[test]
fn test_wasm_debug_info() {
    let debug_info = WasmDebugInfo::from_caller();

    assert!(!debug_info.file.is_empty());
    assert!(debug_info.line > 0);
    assert!(debug_info.column > 0);

    let formatted = debug_info.format();
    assert!(formatted.contains(debug_info.file));
    assert!(formatted.contains(&debug_info.line.to_string()));
}

#[test]
fn test_wasm_optimized_processor() {
    let mut processor = WasmOptimizedProcessor::new(100);
    assert_eq!(processor.processed_len(), 0);

    let written = processor.process(b"test");
    assert_eq!(written, 4);
    assert_eq!(processor.processed_len(), 4);
}

#[test]
fn test_comprehensive_usage() {
    // 综合测试：使用所有 Rust 1.92.0 特性

    // 1. 内存管理
    let mut buffer = WasmBuffer::new(1000);
    unsafe {
        buffer.write(b"data");
    }

    // 2. 计算优化
    let chunks = calculate_buffer_chunks(5000, NonZeroUsize::new(1024).unwrap());
    assert_eq!(chunks, 5);

    // 3. FFI 互操作
    let mut union = WasmFFIUnion::new();
    union.set_integer(42);

    // 4. 迭代器特化
    let vec1 = vec![1, 2, 3];
    let vec2 = vec![1, 2, 3];
    assert!(wasm_optimized_array_eq(&vec1, &vec2));

    // 5. 数据旋转
    let mut data = vec![1, 2, 3, 4];
    wasm_rotate_data(&mut data, 2);
    assert_eq!(data, vec![3, 4, 1, 2]);

    // 6. 调试信息
    let debug_info = WasmDebugInfo::from_caller();
    assert!(!debug_info.format().is_empty());
}
