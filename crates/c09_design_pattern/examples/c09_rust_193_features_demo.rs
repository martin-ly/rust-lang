//! Rust 1.93.0 设计模式相关 API 演示
//!
//! 本示例展示 Rust 1.93.0 在设计模式、数据转换等场景中的新 API：
//! - slice::as_array - 建造者模式中的固定大小验证
//! - Duration::from_nanos_u128 - 策略模式中的高精度配置
//! - fmt::from_fn - 自定义格式化器模式
//!
//! 运行: cargo run -p c09_design_pattern --example rust_193_features_demo
use std::fmt;

fn main() {
    println!("🚀 Rust 1.93.0 设计模式相关 API 演示\n");

    demonstrate_builder_with_as_array();
    demonstrate_fmt_from_fn();
    demonstrate_duration_strategy();

    println!("\n✅ 演示完成");
}

fn demonstrate_builder_with_as_array() {
    println!("--- slice::as_array 在建造者模式中 ---");
    let config = vec![1, 2, 3, 4];
    if let Some(arr) = config.as_slice().as_array::<4>() {
        println!("  配置块有效: {:?}", arr);
    }
}

fn demonstrate_fmt_from_fn() {
    println!("\n--- fmt::from_fn 自定义格式化 ---");
    let debug = fmt::from_fn(|f: &mut fmt::Formatter<'_>| write!(f, "custom_pattern"));
    println!("  输出: {:?}", debug);
}

fn demonstrate_duration_strategy() {
    println!("\n--- Duration::from_nanos_u128 策略配置 ---");
    let nanos: u128 = 500_000_000;
    let d = std::time::Duration::from_nanos_u128(nanos);
    println!("  延迟策略: {:?}", d);
}
