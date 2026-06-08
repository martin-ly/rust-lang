//! # 练习 1: 创建线程 / Exercise 1: Spawning Threads
//!
//! **难度 / Difficulty**: Easy  
//! **考点 / Focus**: std::thread::spawn、join
//!   std::thread::spawn, join
//!
//! ## 题目描述 / Problem Description
//!
//! 创建线程并发执行任务，收集结果。
//! Spawn threads to execute tasks concurrently and collect results.

use std::thread;

/// 创建多个线程计算数字的平方
/// Spawns multiple threads to compute squares of numbers
pub fn parallel_squares(numbers: Vec<i32>) -> Vec<i32> {
    let mut handles = Vec::new();

    for n in numbers {
        let handle = thread::spawn(move || n * n);
        handles.push(handle);
    }

    let mut results = Vec::new();
    for handle in handles {
        results.push(handle.join().unwrap());
    }
    results
}

/// 使用线程计算从 1 到 n 的和
/// Uses a thread to compute the sum from 1 to n
pub fn threaded_sum(n: u64) -> u64 {
    let handle = thread::spawn(move || (1..=n).sum());
    handle.join().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parallel_squares() {
        let nums = vec![1, 2, 3, 4, 5];
        let mut result = parallel_squares(nums);
        result.sort(); // 线程完成顺序不确定 / Completion order is non-deterministic
        assert_eq!(result, vec![1, 4, 9, 16, 25]);
    }

    #[test]
    fn test_threaded_sum() {
        assert_eq!(threaded_sum(10), 55);
        assert_eq!(threaded_sum(100), 5050);
    }
}
