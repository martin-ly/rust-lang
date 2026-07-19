// 并发案例：原子操作与数据一致性
// 理论映射：对应“原子操作”与“并发安全性”定理（见 01_formal_concurrency_model.md 附录）

use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;

fn main() {
    let counter = AtomicUsize::new(0);
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = &counter;
        let handle = thread::spawn(move || {
            counter.fetch_add(1, Ordering::SeqCst);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("结果: {}", counter.load(Ordering::SeqCst));
} 