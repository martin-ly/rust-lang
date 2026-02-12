//! Rust 1.93.0 网络编程相关 API 演示
//!
//! 本示例展示 Rust 1.93.0 在网络、缓冲、超时等场景中的新 API：
//! - Duration::from_nanos_u128 - 高精度网络超时
//! - slice::as_array - 固定大小网络包解析
//! - VecDeque::pop_front_if - 接收缓冲过滤
//!
//! 运行: cargo run -p c10_networks --example rust_193_features_demo

use std::collections::VecDeque;
use std::time::Duration;

fn main() {
    println!("🚀 Rust 1.93.0 网络编程相关 API 演示\n");

    demonstrate_network_timeout();
    demonstrate_packet_parsing();
    demonstrate_receive_buffer_filter();

    println!("\n✅ 演示完成");
}

fn demonstrate_network_timeout() {
    println!("--- Duration::from_nanos_u128 网络超时 ---");
    let nanos: u128 = 1_000_000_000; // 1 秒
    let timeout = Duration::from_nanos_u128(nanos);
    println!("  TCP 超时配置: {:?}", timeout);
}

fn demonstrate_packet_parsing() {
    println!("\n--- slice::as_array 固定大小包解析 ---");
    let packet = vec![0x01, 0x02, 0x03, 0x04];
    if let Some(header) = packet.as_slice().as_array::<4>() {
        println!("  包头: {:?}", header);
    }
}

fn demonstrate_receive_buffer_filter() {
    println!("\n--- VecDeque::pop_front_if 接收缓冲过滤 ---");
    let mut buf = VecDeque::from([0u8, 0, 1, 2, 3, 4]);
    while buf.pop_front_if(|b: &mut u8| *b == 0).is_some() {}
    println!("  过滤前端零字节后: {:?}", buf);
}
