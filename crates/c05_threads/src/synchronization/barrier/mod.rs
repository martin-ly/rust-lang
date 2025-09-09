//! 屏障（Barrier）示例
//!
//! 展示：
//! - 基本 `Barrier` 同步
//! - 多阶段屏障（多轮栅栏）
//! - 并行任务分批执行

use std::sync::{Arc, Barrier};
use std::thread;

/// 基本屏障：所有线程到达后再继续
pub fn basic_barrier(num_threads: usize) {
    let barrier = Arc::new(Barrier::new(num_threads));
    let mut handles = Vec::new();

    for i in 0..num_threads {
        let b = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            // do some work
            println!("T{} before barrier", i);
            b.wait();
            println!("T{} after barrier", i);
        }));
    }

    for h in handles { h.join().unwrap(); }
}

/// 多阶段同步：同一批线程跨多个阶段使用同一个屏障
pub fn multi_phase_barrier(num_threads: usize, phases: usize) {
    let barrier = Arc::new(Barrier::new(num_threads));
    let mut handles = Vec::new();

    for _ in 0..num_threads {
        let b = Arc::clone(&barrier);
        handles.push(thread::spawn(move || {
            for _phase in 0..phases {
                // do phase work
                // println!("phase {} work", phase);
                b.wait();
                // println!("phase {} done", phase);
            }
        }));
    }

    for h in handles { h.join().unwrap(); }
}

/// 分批执行：把任务切成多批，每批次末尾用屏障等待
pub fn batched_parallel_sum(nums: &[u64], batch_size: usize, workers: usize) -> u64 {
    assert!(workers > 0 && batch_size > 0);
    let barrier = Arc::new(Barrier::new(workers));
    let shared_nums = Arc::new(nums.to_vec());
    let partials = Arc::new((0..workers).map(|_| std::sync::Mutex::new(0u64)).collect::<Vec<_>>());

    let mut handles = Vec::new();
    for id in 0..workers {
        let b = Arc::clone(&barrier);
        let data = Arc::clone(&shared_nums);
        let parts = Arc::clone(&partials);
        handles.push(thread::spawn(move || {
            let mut start = id * batch_size;
            let mut round = 0;
            while start < data.len() {
                let end = ((round + 1) * workers * batch_size + id * batch_size).min(data.len());
                let end = end.min(start + batch_size);
                let mut local = 0u64;
                for x in &data[start..end] { local += *x; }
                *parts[id].lock().unwrap() += local;

                // 本轮结束，等待其它线程
                b.wait();
                round += 1;
                start += workers * batch_size;
            }
        }));
    }

    for h in handles { h.join().unwrap(); }
    partials.iter().map(|m| *m.lock().unwrap()).sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_barrier() {
        basic_barrier(4);
    }

    #[test]
    fn test_multi_phase_barrier() {
        multi_phase_barrier(4, 3);
    }

    #[test]
    fn test_batched_parallel_sum() {
        let v: Vec<u64> = (1..=10_000).collect();
        let s = batched_parallel_sum(&v, 128, 4);
        let expect: u64 = v.iter().sum();
        assert_eq!(s, expect);
    }
}