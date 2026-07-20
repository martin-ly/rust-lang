// 并发安全、Send/Sync、原子性示例
// 工程意义：演示Rust如何通过类型系统和同步原语保证并发安全，适用于Kani/Prusti等工具验证

use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }
    for handle in handles {
        handle.join().unwrap();
    }
    assert_eq!(*counter.lock().unwrap(), 10);
}

// 形式化注释：
// ∀t. own(t, counter) ⇒ exclusive(counter)
// TypeCheck(p) = ✓ ⇒ NoDataRaces(p)
// 工具建议：Kani/Prusti 可验证并发安全与数据竞争免疫 