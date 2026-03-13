//! Rust 1.93.0 线程与并发相关 API 演示
//!
//! 本示例展示 Rust 1.93.0 在线程、并发、任务队列等场景中的新 API：
//! - VecDeque::pop_front_if / pop_back_if - 条件性弹出，适合任务过滤
//! - Duration::from_nanos_u128 - 高精度纳秒级计时
//! - slice::as_array - 固定大小缓冲区的类型安全访问
//!
//! 运行: cargo run -p c05_threads --example rust_193_features_demo
use std::collections::VecDeque;
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

fn main() {
    println!("🚀 Rust 1.93.0 线程与并发相关 API 演示\n");

    demonstrate_vecdeque_pop_if();
    demonstrate_duration_from_nanos_u128();
    demonstrate_slice_as_array_in_worker();

    println!("\n✅ 演示完成");
}

/// VecDeque::pop_front_if / pop_back_if (Rust 1.93) - 条件性弹出
fn demonstrate_vecdeque_pop_if() {
    println!("--- VecDeque::pop_front_if / pop_back_if ---");
    let mut queue = VecDeque::from([-1, 2, 3, 5, 150, -2, 99]);

    // 从前端移除负数
    while queue.pop_front_if(|x| *x < 0).is_some() {}
    println!("  移除前端负数后: {:?}", queue);

    // 从后端移除大于 50 的数（99, 150 依次被移除）
    while queue.pop_back_if(|x| *x > 50).is_some() {}
    println!("  移除后端大于50的数后: {:?}", queue);
}

/// Duration::from_nanos_u128 (Rust 1.93) - 高精度纳秒计时
fn demonstrate_duration_from_nanos_u128() {
    println!("\n--- Duration::from_nanos_u128 ---");
    let nanos: u128 = 1_500_000_000; // 1.5 秒
    let d = Duration::from_nanos_u128(nanos);
    println!("  {} ns = {:?}", nanos, d);
    assert_eq!(d.as_secs(), 1);
    assert_eq!(d.subsec_nanos(), 500_000_000);

    // 在实际线程中使用
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let delay = Duration::from_nanos_u128(100_000_000); // 100ms
        thread::sleep(delay);
        tx.send(()).unwrap();
    });
    rx.recv().unwrap();
    println!("  线程 sleep 100ms 完成");
}

/// slice::as_array (Rust 1.93) - 在 worker 中处理固定大小块
fn demonstrate_slice_as_array_in_worker() {
    println!("\n--- slice::as_array 在并发数据处理中 ---");
    let data = vec![1u8, 2, 3, 4, 5, 6, 7, 8];
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        let chunks: Vec<&[u8]> = data.chunks(4).collect();
        for chunk in chunks {
            if let Some(arr) = chunk.as_array::<4>() {
                tx.send(*arr).unwrap();
            }
        }
        drop(tx);
    });

    let mut received = Vec::new();
    while let Ok(arr) = rx.recv() {
        received.push(arr);
    }
    println!("  接收到的 4 元素块: {:?}", received);
}
