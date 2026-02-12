//! Rust 1.93.0 所有权与内存相关 API 演示
//!
//! 本示例展示 Rust 1.93.0 在所有权、内存、集合等场景中的新 API：
//! - String::into_raw_parts / Vec::into_raw_parts
//! - MaybeUninit 切片方法 (assume_init_drop, write_copy_of_slice 等)
//! - slice::as_array
//!
//! 运行: cargo run --example rust_193_features_demo

use std::mem::MaybeUninit;

fn main() {
    println!("🚀 Rust 1.93.0 所有权与内存 API 演示\n");

    demonstrate_string_into_raw_parts();
    demonstrate_vec_into_raw_parts();
    demonstrate_maybeuninit_slice_methods();
    demonstrate_slice_as_array();

    println!("\n✅ 演示完成");
}

/// String::into_raw_parts (Rust 1.93)
fn demonstrate_string_into_raw_parts() {
    println!("--- String::into_raw_parts ---");
    let s = String::from("hello");
    let (ptr, len, cap) = s.into_raw_parts();
    // 重建 String（unsafe，仅演示）
    let _reconstructed = unsafe { String::from_raw_parts(ptr, len, cap) };
    println!("  len={}, cap={}", len, cap);
}

/// Vec::into_raw_parts (Rust 1.93)
fn demonstrate_vec_into_raw_parts() {
    println!("\n--- Vec::into_raw_parts ---");
    let v = vec![1, 2, 3];
    let (ptr, len, cap) = v.into_raw_parts();
    let _reconstructed: Vec<i32> = unsafe { Vec::from_raw_parts(ptr, len, cap) };
    println!("  len={}, cap={}", len, cap);
}

/// MaybeUninit 切片方法 (Rust 1.93)
fn demonstrate_maybeuninit_slice_methods() {
    println!("\n--- MaybeUninit 切片方法 ---");
    let mut buf: [MaybeUninit<u8>; 4] = [MaybeUninit::uninit(); 4];
    // write_copy_of_slice (Rust 1.93)
    let src: [u8; 4] = [1, 2, 3, 4];
    buf.as_mut_slice().write_copy_of_slice(&src);
    // assume_init_ref 读取（Rust 1.93）
    let view: &[u8] = unsafe { buf.as_slice().assume_init_ref() };
    println!("  write_copy_of_slice 结果: {:?}", view);
}

/// slice::as_array (Rust 1.93)
fn demonstrate_slice_as_array() {
    println!("\n--- slice::as_array ---");
    let v = vec![10, 20, 30];
    let slice: &[i32] = &v;
    if let Some(arr) = slice.as_array::<3>() {
        println!("  as_array::<3>: {:?}", arr);
    }
}
