//! 无锁数据结构示例
//!
//! 展示 `c08_algorithms::data_structure` 中基于 `crossbeam-epoch` 的：
//!
//! - `LockFreeStack` (Treiber Stack)
//! - `LockFreeQueue` (Michael-Scott Queue)
//! - `HazardPointer` / epoch 内存回收桥接
//!
//! 运行方式：
//! ```bash
//! cargo run -p c08_algorithms --example lock_free_data_structures_demo
//! ```

use std::sync::Arc;
use std::thread;

use c08_algorithms::data_structure::hazard_pointer::{HazardPointer, load_protected, publish};
use c08_algorithms::data_structure::lock_free_queue::LockFreeQueue;
use c08_algorithms::data_structure::lock_free_stack::LockFreeStack;

fn main() {
    println!("🔓 无锁数据结构演示\n");
    println!("{}", "=".repeat(60));

    demo_treiber_stack();
    demo_ms_queue();
    demo_hazard_pointer_bridge();
    demo_concurrent_stack();
    demo_concurrent_queue();
}

fn demo_treiber_stack() {
    println!("\n📚 Treiber Stack (LIFO)");
    println!("{}", "-".repeat(60));

    let stack = LockFreeStack::new();
    stack.push("first");
    stack.push("second");
    stack.push("third");

    while let Some(value) = stack.pop() {
        println!("  pop -> {}", value);
    }
    println!("  栈空: {}", stack.is_empty());
}

fn demo_ms_queue() {
    println!("\n📚 Michael-Scott Queue (FIFO)");
    println!("{}", "-".repeat(60));

    let queue = LockFreeQueue::new();
    queue.enqueue("alice");
    queue.enqueue("bob");
    queue.enqueue("carol");

    while let Some(value) = queue.dequeue() {
        println!("  dequeue -> {}", value);
    }
    println!("  队列空: {}", queue.is_empty());
}

fn demo_hazard_pointer_bridge() {
    println!("\n📚 Hazard Pointer / EBR 桥接");
    println!("{}", "-".repeat(60));

    // HazardPointer 是对 crossbeam-epoch Guard 的薄包装。
    let hp = HazardPointer::new();
    let guard = hp.guard();

    // 演示 publish：将 Owned 节点发布为共享指针。
    let owned = crossbeam_epoch::Owned::new(String::from("shared node"));
    let _shared = publish(owned, guard);

    // 演示 load_protected：在 Guard 保护下安全读取 Atomic。
    let atomic = crossbeam_epoch::Atomic::new(42);
    let shared = load_protected(&atomic, guard);

    unsafe {
        println!("  受保护读取 -> {}", *shared.deref());
    }

    // HazardPointer 在 drop 时自动 unpin，显式 clear 表达语义。
    hp.clear();
    println!("  Hazard Pointer 已清除");
}

fn demo_concurrent_stack() {
    println!("\n🧵 并发 Treiber Stack");
    println!("{}", "-".repeat(60));

    const THREADS: usize = 4;
    const OPS: usize = 1000;

    let stack = Arc::new(LockFreeStack::new());
    let mut handles = vec![];

    for t in 0..THREADS {
        let s = Arc::clone(&stack);
        handles.push(thread::spawn(move || {
            for i in 0..OPS {
                s.push(t * OPS + i);
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    let mut count = 0;
    while stack.pop().is_some() {
        count += 1;
    }
    println!("  并发入栈 {} 次，成功弹出 {} 次", THREADS * OPS, count);
    assert_eq!(count, THREADS * OPS);
}

fn demo_concurrent_queue() {
    println!("\n🧵 并发 Michael-Scott Queue");
    println!("{}", "-".repeat(60));

    const THREADS: usize = 4;
    const OPS: usize = 1000;

    let queue = Arc::new(LockFreeQueue::new());
    let mut handles = vec![];

    for t in 0..THREADS {
        let q = Arc::clone(&queue);
        handles.push(thread::spawn(move || {
            for i in 0..OPS {
                q.enqueue(t * OPS + i);
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    let mut count = 0;
    while queue.dequeue().is_some() {
        count += 1;
    }
    println!("  并发入队 {} 次，成功出队 {} 次", THREADS * OPS, count);
    assert_eq!(count, THREADS * OPS);
}
