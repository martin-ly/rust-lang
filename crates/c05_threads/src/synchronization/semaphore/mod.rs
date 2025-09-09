//! 计数信号量（基于通道/Condvar 简化实现）
//! - 限流并发度
//! - 异步无依赖，纯 std 同步原语

use std::sync::{Arc, Condvar, Mutex};
use std::thread;

/// 一个简单的计数信号量实现（阻塞版）
#[derive(Clone)]
pub struct Semaphore {
    inner: Arc<(Mutex<usize>, Condvar)>,
}

impl Semaphore {
    pub fn new(permits: usize) -> Self {
        Self { inner: Arc::new((Mutex::new(permits), Condvar::new())) }
    }

    pub fn acquire(&self) {
        let (lock, cvar) = &*self.inner;
        let mut avail = lock.lock().unwrap();
        while *avail == 0 {
            avail = cvar.wait(avail).unwrap();
        }
        *avail -= 1;
    }

    pub fn release(&self) {
        let (lock, cvar) = &*self.inner;
        let mut avail = lock.lock().unwrap();
        *avail += 1;
        cvar.notify_one();
    }
}

/// 使用信号量限制并发：并行下载/计算的最大并发数
pub fn throttle_concurrency(tasks: usize, max_parallel: usize) -> usize {
    let sem = Semaphore::new(max_parallel);
    let mut handles = Vec::new();
    let completed = Arc::new(Mutex::new(0usize));

    for _ in 0..tasks {
        let s = sem.clone();
        let done = Arc::clone(&completed);
        handles.push(thread::spawn(move || {
            s.acquire();
            // do work
            {
                let mut d = done.lock().unwrap();
                *d += 1;
            }
            s.release();
        }));
    }

    for h in handles { h.join().unwrap(); }
    *completed.lock().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_semaphore_throttle_concurrency() {
        let done = throttle_concurrency(100, 8);
        assert_eq!(done, 100);
    }
}