//! # 练习 2: Mutex 计数器 / Exercise 2: Mutex Counter
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: Mutex、Arc、线程间共享可变状态
//!   Mutex, Arc, sharing mutable state across threads
//!
//! ## 题目描述 / Problem Description
//!
//! 使用 `Arc<Mutex<T>>` 实现线程安全的计数器。
//! Use `Arc<Mutex<T>>` to implement a thread-safe counter.

use std::sync::{Arc, Mutex};
use std::thread;

/// 创建线程安全的计数器
/// Creates a thread-safe counter
pub fn create_counter(initial: i32) -> Arc<Mutex<i32>> {
    Arc::new(Mutex::new(initial))
}

/// 多个线程同时递增计数器
/// Increments the counter concurrently from multiple threads
pub fn increment_concurrently(counter: &Arc<Mutex<i32>>, increments: usize, threads: usize) {
    let mut handles = Vec::new();

    for _ in 0..threads {
        let counter = Arc::clone(counter);
        let handle = thread::spawn(move || {
            for _ in 0..increments {
                let mut num = counter.lock().unwrap();
                *num += 1;
            }
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }
}

/// 获取当前计数器值
/// Gets the current counter value
pub fn get_count(counter: &Arc<Mutex<i32>>) -> i32 {
    *counter.lock().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mutex_counter() {
        let counter = create_counter(0);
        increment_concurrently(&counter, 100, 10);
        assert_eq!(get_count(&counter), 1000);
    }

    #[test]
    fn test_counter_with_initial() {
        let counter = create_counter(50);
        increment_concurrently(&counter, 10, 5);
        assert_eq!(get_count(&counter), 100);
    }
}
