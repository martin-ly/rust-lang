//! 共享状态与取消标志
//! - 使用 `Arc<AtomicBool>` 进行跨线程停止信号
//! - 使用 `Arc<Mutex<T>>` 维护共享可变状态

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/// 安全取消：向工作线程广播停止信号
pub fn cooperative_cancellation(workers: usize, ticks: usize) -> usize {
    let cancel = Arc::new(AtomicBool::new(false));
    let progress = Arc::new(Mutex::new(0usize));

    let mut handles = Vec::new();
    for _ in 0..workers {
        let c = Arc::clone(&cancel);
        let p = Arc::clone(&progress);
        handles.push(thread::spawn(move || {
            let mut local = 0usize;
            while !c.load(Ordering::Acquire) {
                local += 1;
                if local >= ticks {
                    break;
                }
                thread::sleep(Duration::from_millis(1));
            }
            *p.lock().unwrap() += local;
        }));
    }

    // 让线程跑一会
    thread::sleep(Duration::from_millis((ticks as u64).min(10)));
    cancel.store(true, Ordering::Release);

    for h in handles {
        h.join().unwrap();
    }
    *progress.lock().unwrap()
}

/// 共享可变状态：多个线程累加到一个共享 Vec
pub fn shared_vec_sum(workers: usize, each: usize) -> usize {
    let data = Arc::new(Mutex::new(Vec::<usize>::new()));
    let mut handles = Vec::new();
    for id in 0..workers {
        let d = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let mut local = 0usize;
            for i in 0..each {
                local += id + i;
            }
            d.lock().unwrap().push(local);
        }));
    }
    for h in handles {
        h.join().unwrap();
    }
    data.lock().unwrap().iter().sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cooperative_cancellation() {
        let _ = cooperative_cancellation(4, 20);
    }

    #[test]
    fn test_shared_vec_sum() {
        let s = shared_vec_sum(4, 10);
        assert!(s > 0);
    }
}
