//! 原子类型与内存序
//! 
//! 涵盖 `AtomicBool`/`AtomicUsize` 基本操作、`Ordering` 含义、
//! `compare_exchange` 与自旋计数器示例。

use std::hint;
use std::sync::atomic::{fence, AtomicBool, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::Duration;

/// 展示最常用的原子操作与不同内存序
pub fn atomic_basics_demo() {
    let flag = AtomicBool::new(false);
    let counter = AtomicUsize::new(0);

    // Relaxed 适用于仅计数、无因果依赖的场景
    for _ in 0..10 {
        counter.fetch_add(1, Ordering::Relaxed);
    }

    // Release- Acquire 搭配，建立“先发生于”关系
    flag.store(true, Ordering::Release);
    let seen = flag.load(Ordering::Acquire);

    // SeqCst 提供全局的强序（通常性能更差）
    fence(Ordering::SeqCst);

    println!("atomic counter={}, seen={}", counter.load(Ordering::Relaxed), seen);
}

/// compare_exchange 常见用法
pub fn compare_exchange_demo() {
    let value = AtomicUsize::new(5);

    // 期望是 5，成功则写入 10
    let _ = value
        .compare_exchange(5, 10, Ordering::AcqRel, Ordering::Acquire)
        .expect("CAS should succeed");

    // 再次尝试会失败，返回当前值
    let _ = value
        .compare_exchange(5, 20, Ordering::AcqRel, Ordering::Acquire)
        .err()
        .unwrap();

    assert_eq!(value.load(Ordering::Relaxed), 10);
}

/// 自旋递增：多个线程在无锁场景下增计数
pub fn spin_increment(num_threads: usize, iters_per_thread: usize) -> usize {
    let shared = Arc::new(AtomicUsize::new(0));
    let mut handles = Vec::new();

    for _ in 0..num_threads {
        let c = Arc::clone(&shared);
        handles.push(thread::spawn(move || {
            for _ in 0..iters_per_thread {
                // 使用 fetch_add 是最佳实践；这里演示 CAS 自旋写法
                loop {
                    let cur = c.load(Ordering::Relaxed);
                    if c
                        .compare_exchange(cur, cur + 1, Ordering::AcqRel, Ordering::Acquire)
                        .is_ok()
                    {
                        break;
                    }
                    // 自旋提示，减少功耗/提升性能
                    hint::spin_loop();
                }
            }
        }));
    }

    for h in handles { h.join().unwrap(); }
    shared.load(Ordering::Relaxed)
}

/// 可见性示例：一个线程写入，另一个线程读取
pub fn visibility_demo() -> usize {
    let ready = Arc::new(AtomicBool::new(false));
    let data = Arc::new(AtomicUsize::new(0));

    let t_ready = Arc::clone(&ready);
    let t_data = Arc::clone(&data);
    let writer = thread::spawn(move || {
        t_data.store(42, Ordering::Relaxed);
        // 发布（Release）写，使后续读取可以 Acquire 到
        t_ready.store(true, Ordering::Release);
    });

    let r_ready = Arc::clone(&ready);
    let r_data = Arc::clone(&data);
    let reader = thread::spawn(move || {
        while !r_ready.load(Ordering::Acquire) {
            thread::sleep(Duration::from_millis(1));
        }
        r_data.load(Ordering::Relaxed)
    });

    writer.join().unwrap();
    reader.join().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atomic_basics_demo() {
        atomic_basics_demo();
    }

    #[test]
    fn test_compare_exchange_demo() {
        compare_exchange_demo();
    }

    #[test]
    fn test_spin_increment() {
        let total = spin_increment(4, 10_000);
        assert_eq!(total, 4 * 10_000);
    }

    #[test]
    fn test_visibility_demo() {
        assert_eq!(visibility_demo(), 42);
    }
}