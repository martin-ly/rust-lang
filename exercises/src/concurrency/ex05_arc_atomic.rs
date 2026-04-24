//! # 练习 5: Arc + Atomic
//!
//! **难度**: Medium  
//! **考点**: Arc、AtomicUsize、无锁并发
//!
//! ## 题目描述
//!
//! 使用 Atomic 类型实现无锁计数器，避免 Mutex 的开销。

use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

/// 无锁计数器
#[derive(Debug)]
pub struct AtomicCounter {
    count: AtomicUsize,
}

impl AtomicCounter {
    pub fn new(initial: usize) -> Self {
        Self {
            count: AtomicUsize::new(initial),
        }
    }

    /// 原子递增并返回新值
    pub fn increment(&self) -> usize {
        self.count.fetch_add(1, Ordering::SeqCst) + 1
    }

    /// 获取当前值
    pub fn get(&self) -> usize {
        self.count.load(Ordering::SeqCst)
    }

    /// 批量递增
    pub fn add(&self, n: usize) -> usize {
        self.count.fetch_add(n, Ordering::SeqCst) + n
    }
}

/// 创建共享的无锁计数器
pub fn create_atomic_counter(initial: usize) -> Arc<AtomicCounter> {
    Arc::new(AtomicCounter::new(initial))
}

/// 多线程并发递增
pub fn atomic_concurrent_increment(counter: &Arc<AtomicCounter>, per_thread: usize, threads: usize) {
    let mut handles = Vec::new();

    for _ in 0..threads {
        let counter = Arc::clone(counter);
        let handle = thread::spawn(move || {
            for _ in 0..per_thread {
                counter.increment();
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_atomic_counter() {
        let counter = AtomicCounter::new(0);
        assert_eq!(counter.increment(), 1);
        assert_eq!(counter.increment(), 2);
        assert_eq!(counter.get(), 2);
    }

    #[test]
    fn test_atomic_concurrent() {
        let counter = create_atomic_counter(0);
        atomic_concurrent_increment(&counter, 1000, 10);
        assert_eq!(counter.get(), 10000);
    }

    #[test]
    fn test_atomic_add() {
        let counter = AtomicCounter::new(5);
        assert_eq!(counter.add(10), 15);
        assert_eq!(counter.get(), 15);
    }
}
