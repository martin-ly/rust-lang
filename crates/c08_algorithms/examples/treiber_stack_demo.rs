// [来源: Treiber 1986 / Rust Atomics and Locks]
//! Treiber Stack 无锁栈使用示例。
//!
//! 运行方式：
//!
//! ```bash
//! cargo run -p c08_algorithms --example treiber_stack_demo
//! ```

use std::sync::Arc;
use std::thread;

use c08_algorithms::data_structure::treiber_stack::TreiberStack;

fn main() {
    println!("=== Treiber Stack 单线程演示 ===");
    let stack = TreiberStack::new();
    assert!(stack.is_empty());

    for i in 1..=5 {
        stack.push(i);
        println!("push({}) -> stack empty? {}", i, stack.is_empty());
    }

    while let Some(value) = stack.pop() {
        println!("pop() -> {}", value);
    }
    println!("final empty? {}", stack.is_empty());

    println!("\n=== Treiber Stack 多线程压入演示 ===");
    let stack = Arc::new(TreiberStack::new());
    const THREADS: usize = 4;
    const OPS: usize = 1000;

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
    println!(
        "{} 个线程各压入 {} 个元素，最终弹出总数: {} (expected {})",
        THREADS,
        OPS,
        count,
        THREADS * OPS
    );
    assert_eq!(count, THREADS * OPS);

    println!("\n=== Treiber Stack 多线程混合操作演示 ===");
    let stack = Arc::new(TreiberStack::new());
    let mut handles = vec![];

    for t in 0..THREADS {
        let s = Arc::clone(&stack);
        handles.push(thread::spawn(move || {
            for i in 0..OPS {
                s.push(t * OPS + i);
                if i % 2 == 0 {
                    s.pop();
                }
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    let mut remaining = 0;
    while stack.pop().is_some() {
        remaining += 1;
    }
    println!("混合操作后栈中剩余元素数: {}", remaining);

    println!("\nTreiber Stack 演示完成 ✅");
}
