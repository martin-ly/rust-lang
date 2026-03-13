//! Rust 1.93.0 算法与集合相关 API 演示
//!
//! 本示例展示 Rust 1.93.0 在算法、集合等场景中的新 API：
//! - VecDeque::pop_front_if / pop_back_if
//! - BTreeMap::append
//! - slice::as_array
//! - Duration::from_nanos_u128
//!
//! 运行: cargo run -p c08_algorithms --example rust_193_features_demo
use std::collections::{BTreeMap, VecDeque};
use std::time::Duration;

fn main() {
    println!("🚀 Rust 1.93.0 算法与集合 API 演示\n");

    demonstrate_vecdeque_pop_if();
    demonstrate_btreemap_append();
    demonstrate_slice_as_array();
    demonstrate_duration_from_nanos_u128();

    println!("\n✅ 演示完成");
}

/// VecDeque::pop_front_if / pop_back_if (Rust 1.93)
fn demonstrate_vecdeque_pop_if() {
    println!("--- VecDeque::pop_*_if ---");
    let mut deque: VecDeque<i32> = VecDeque::from([1, 2, 3, 4, 5]);

    // pop_front_if: 弹出满足条件的队首元素（谓词接收 &mut T）
    if let Some(v) = deque.pop_front_if(|x: &mut i32| -> bool { *x < 3 }) {
        println!("  pop_front_if(|x| x<3): {}", v);
    }
    println!("  剩余: {:?}", deque);

    // pop_back_if: 弹出满足条件的队尾元素（谓词接收 &mut T）
    if let Some(v) = deque.pop_back_if(|x: &mut i32| -> bool { *x > 4 }) {
        println!("  pop_back_if(|x| x>4): {}", v);
    }
    println!("  最终: {:?}", deque);
}

/// BTreeMap::append (Rust 1.93 - 行为：相同 key 保留目标)
fn demonstrate_btreemap_append() {
    println!("\n--- BTreeMap::append ---");
    let mut a: BTreeMap<&str, i32> = BTreeMap::from([("x", 1), ("y", 2)]);
    let mut b: BTreeMap<&str, i32> = BTreeMap::from([("y", 20), ("z", 3)]);

    a.append(&mut b);
    println!("  append 后 a: {:?}", a);
    println!("  注意: 相同 key 'y' 保留目标(20)，b  consume 后为空");
}

/// slice::as_array (Rust 1.93)
fn demonstrate_slice_as_array() {
    println!("\n--- slice::as_array ---");
    let v = vec![10, 20, 30, 40];
    let slice: &[i32] = &v[..3];
    if let Some(arr) = slice.as_array::<3>() {
        println!("  as_array::<3>: {:?}", arr);
    }
}

/// Duration::from_nanos_u128 (Rust 1.93)
fn demonstrate_duration_from_nanos_u128() {
    println!("\n--- Duration::from_nanos_u128 ---");
    let nanos: u128 = 1_500_000_000; // 1.5 秒
    let d = Duration::from_nanos_u128(nanos);
    println!("  from_nanos_u128(1_500_000_000): {:?}", d);
}
