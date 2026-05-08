//! Rust 1.93.0 进程管理相关 API 演示
//!
//! 本示例展示 Rust 1.93.0 在进程、超时、数据传递等场景中的新 API：
//! - Duration::from_nanos_u128 - 高精度纳秒级超时
//! - String::into_raw_parts - 进程间数据传递
//! - VecDeque::pop_front_if - 进程输出队列过滤
//!
//! 运行: cargo run -p c07_process --example rust_193_features_demo
use std::collections::VecDeque;
use std::process::Command;
use std::time::Duration;

fn main() {
    println!("🚀 Rust 1.93.0 进程管理相关 API 演示\n");

    demonstrate_duration_timeout();
    demonstrate_vecdeque_output_filter();
    demonstrate_string_raw_parts();

    println!("\n✅ 演示完成");
}

fn demonstrate_duration_timeout() {
    println!("--- Duration::from_nanos_u128 超时配置 ---");
    let nanos: u128 = 1_000_000_000; // 1 秒
    let timeout = Duration::from_nanos_u128(nanos);
    println!("  超时配置: {:?}", timeout);
    let _ = Command::new("echo").arg("hello").output();
    println!("  进程执行完成");
}

fn demonstrate_vecdeque_output_filter() {
    println!("\n--- VecDeque::pop_front_if 输出过滤 ---");
    let mut queue = VecDeque::from([("stdout", 1), ("stderr", 2), ("stdout", 3)]);
    while let Some((_ty, id)) = queue.pop_front_if(|(t, _)| *t == "stdout") {
        println!("  处理 stdout 行: {}", id);
    }
    println!("  剩余 stderr 行: {}", queue.len());
}

fn demonstrate_string_raw_parts() {
    println!("\n--- String::into_raw_parts 数据传递 ---");
    let s = String::from("process_data");
    let (ptr, len, cap) = s.into_raw_parts();
    let s = unsafe { String::from_raw_parts(ptr, len, cap) };
    println!("  重建字符串: \"{}\"", s);
}
