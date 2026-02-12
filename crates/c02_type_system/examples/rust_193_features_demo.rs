//! Rust 1.93.0 类型系统相关 API 演示
//!
//! 本示例展示 Rust 1.93.0 在类型系统、集合、内存等场景中的新 API：
//! - slice::as_array / as_mut_array - 类型安全的切片到数组转换
//! - String::into_raw_parts - 获取 String 的原始部分
//! - Vec::into_raw_parts - 获取 Vec 的原始部分
//! - MaybeUninit 增强 API（write_copy_of_slice, assume_init_ref）
//!
//! 运行: cargo run -p c02_type_system --example rust_193_features_demo

use std::mem::MaybeUninit;

fn main() {
    println!("🚀 Rust 1.93.0 类型系统相关 API 演示\n");

    demonstrate_slice_as_array();
    demonstrate_string_into_raw_parts();
    demonstrate_vec_into_raw_parts();
    demonstrate_maybeuninit_enhanced();

    println!("\n✅ 演示完成");
}

/// slice::as_array (Rust 1.93) - 类型安全的切片到固定长度数组引用
fn demonstrate_slice_as_array() {
    println!("--- slice::as_array / as_mut_array ---");
    let v = vec![1, 2, 3, 4];
    let slice: &[i32] = &v;
    if let Some(arr) = slice.as_array::<4>() {
        println!("  as_array::<4>: {:?}", arr);
    }
    assert!(slice.as_array::<5>().is_none());

    let mut v2 = vec![10, 20, 30];
    let slice_mut: &mut [i32] = &mut v2;
    if let Some(arr) = slice_mut.as_mut_array::<3>() {
        arr[0] += 1;
        println!("  as_mut_array::<3> 修改后: {:?}", arr);
    }
}

/// String::into_raw_parts (Rust 1.93)
fn demonstrate_string_into_raw_parts() {
    println!("\n--- String::into_raw_parts ---");
    let s = String::from("hello");
    let (ptr, len, capacity) = s.into_raw_parts();
    println!("  原始指针: {:?}, len: {}, capacity: {}", ptr, len, capacity);
    let s = unsafe { String::from_raw_parts(ptr, len, capacity) };
    println!("  重建 String: \"{}\"", s);
}

/// Vec::into_raw_parts (Rust 1.93)
fn demonstrate_vec_into_raw_parts() {
    println!("\n--- Vec::into_raw_parts ---");
    let v = vec![1, 2, 3];
    let (ptr, len, capacity) = v.into_raw_parts();
    println!("  原始指针: {:?}, len: {}, capacity: {}", ptr, len, capacity);
    let v = unsafe { Vec::from_raw_parts(ptr, len, capacity) };
    println!("  重建 Vec: {:?}", v);
}

/// MaybeUninit 增强 API (Rust 1.93)
fn demonstrate_maybeuninit_enhanced() {
    println!("\n--- MaybeUninit 增强 API ---");
    let mut buf: [MaybeUninit<u8>; 8] = std::array::from_fn(|_| MaybeUninit::uninit());
    let data = [1u8, 2, 3, 4];
    // Rust 1.93: write_copy_of_slice
    buf[..4].write_copy_of_slice(&data);
    let initialized = unsafe { buf[..4].assume_init_ref() };
    println!("  write_copy_of_slice + assume_init_ref: {:?}", initialized);
}
