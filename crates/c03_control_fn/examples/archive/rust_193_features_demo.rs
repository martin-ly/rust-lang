//! Rust 1.93.0 控制流与函数相关特性演示
//!
//! 本示例展示 Rust 1.93.0 在控制流、格式化、时间等场景中的新 API：
//! - Duration::from_nanos_u128
//! - char::MAX_LEN_UTF8 / char::MAX_LEN_UTF16
//! - std::fmt::from_fn
//! - slice::as_array / as_mut_array
//!
//! 运行: cargo run --example rust_193_features_demo

use std::fmt;
use std::time::Duration;

fn main() {
    println!("🚀 Rust 1.93.0 控制流与函数相关 API 演示\n");

    demonstrate_duration_from_nanos_u128();
    demonstrate_char_constants();
    demonstrate_fmt_from_fn();
    demonstrate_slice_as_array();

    println!("\n✅ 演示完成");
}

/// Duration::from_nanos_u128 (Rust 1.93)
fn demonstrate_duration_from_nanos_u128() {
    println!("--- Duration::from_nanos_u128 ---");
    let nanos: u128 = 1_000_000_000; // 1 秒
    let d = Duration::from_nanos_u128(nanos);
    println!("  {} ns = {:?}", nanos, d);
    assert_eq!(d.as_secs(), 1);
}

/// char::MAX_LEN_UTF8 / char::MAX_LEN_UTF16 (Rust 1.93)
fn demonstrate_char_constants() {
    println!("\n--- char 常量 ---");
    println!("  MAX_LEN_UTF8: {}", char::MAX_LEN_UTF8);
    println!("  MAX_LEN_UTF16: {}", char::MAX_LEN_UTF16);
}

/// std::fmt::from_fn (Rust 1.93) - 用于格式化回调
fn demonstrate_fmt_from_fn() {
    println!("\n--- fmt::from_fn ---");
    let debug = fmt::from_fn(|f: &mut fmt::Formatter<'_>| write!(f, "custom_debug"));
    println!("  Debug 输出: {:?}", debug);
}

/// slice::as_array (Rust 1.93) - 安全将切片转为固定长度数组引用
fn demonstrate_slice_as_array() {
    println!("\n--- slice::as_array ---");
    let v = vec![1, 2, 3, 4];
    let slice: &[i32] = &v;
    if let Some(arr) = slice.as_array::<4>() {
        println!("  as_array::<4>: {:?}", arr);
    }
    // 长度不匹配返回 None
    assert!(slice.as_array::<5>().is_none());
}
