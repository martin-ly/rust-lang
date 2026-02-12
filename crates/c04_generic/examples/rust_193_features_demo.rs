//! Rust 1.93.0 泛型编程相关 API 演示
//!
//! 本示例展示 Rust 1.93.0 在泛型、集合、类型转换等场景中的新 API：
//! - slice::as_array - 泛型切片到数组的类型安全转换
//! - Vec::into_raw_parts - 泛型向量的内存布局
//! - Duration::from_nanos_u128 - 泛型时间计算
//!
//! 运行: cargo run -p c04_generic --example rust_193_features_demo

use std::time::Duration;

fn main() {
    println!("🚀 Rust 1.93.0 泛型编程相关 API 演示\n");

    demonstrate_generic_as_array();
    demonstrate_generic_into_raw_parts();
    demonstrate_duration_in_generic();

    println!("\n✅ 演示完成");
}

fn generic_as_array<T: std::fmt::Debug>(slice: &[T]) -> Option<&[T; 4]> {
    slice.as_array::<4>()
}

fn demonstrate_generic_as_array() {
    println!("--- slice::as_array 泛型用法 ---");
    let v = vec![1, 2, 3, 4];
    if let Some(arr) = generic_as_array(&v) {
        println!("  泛型 as_array: {:?}", arr);
    }
}

fn demonstrate_generic_into_raw_parts() {
    println!("\n--- Vec::into_raw_parts 泛型 ---");
    let v: Vec<i32> = vec![10, 20, 30];
    let (ptr, len, cap) = v.into_raw_parts();
    let v = unsafe { Vec::from_raw_parts(ptr, len, cap) };
    println!("  重建 Vec<i32>: {:?}", v);
}

fn demonstrate_duration_in_generic() {
    println!("\n--- Duration::from_nanos_u128 在泛型时间计算中 ---");
    let nanos: u128 = 1_000_000_000;
    let d = Duration::from_nanos_u128(nanos);
    println!("  {} ns = {:?}", nanos, d);
}
