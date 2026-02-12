//! Rust 1.93.0 宏系统相关 API 演示
//!
//! 本示例展示 Rust 1.93.0 在宏展开、类型检查等场景中的新 API：
//! - slice::as_array - 宏生成的切片到数组转换
//! - Duration::from_nanos_u128 - 宏展开计时
//! - offset_of! 类型 well-formed 检查 (Rust 1.93)
//!
//! 注意: offset_of! 在 1.93 中加强了类型检查，详见 toolchain 兼容性文档
//!
//! 运行: cargo run -p c11_macro_system --example rust_193_features_demo

use std::time::Duration;

fn main() {
    println!("🚀 Rust 1.93.0 宏系统相关 API 演示\n");

    demonstrate_macro_as_array();
    demonstrate_duration_from_nanos();
    demonstrate_char_constants();

    println!("\n✅ 演示完成");
}

fn demonstrate_macro_as_array() {
    println!("--- slice::as_array 宏生成数据 ---");
    let data = vec![1, 2, 3, 4];
    if let Some(arr) = data.as_slice().as_array::<4>() {
        println!("  宏可处理 as_array: {:?}", arr);
    }
}

fn demonstrate_duration_from_nanos() {
    println!("\n--- Duration::from_nanos_u128 宏展开计时 ---");
    let nanos: u128 = 1_000_000; // 1ms
    let d = Duration::from_nanos_u128(nanos);
    println!("  {:?}", d);
}

fn demonstrate_char_constants() {
    println!("\n--- char 常量 (Rust 1.93) 编码缓冲区 ---");
    println!("  MAX_LEN_UTF8: {}", char::MAX_LEN_UTF8);
    println!("  MAX_LEN_UTF16: {}", char::MAX_LEN_UTF16);
}
