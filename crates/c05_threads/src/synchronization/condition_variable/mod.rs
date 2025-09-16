//! 条件变量（Condvar）示例
//! - 经典生产者/消费者
//! - 超时等待与虚假唤醒处理

use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::{Duration, Instant};

/// 简单的有界队列：生产者/消费者
pub fn bounded_queue_demo(
    capacity: usize,
    producers: usize,
    consumers: usize,
    items: usize,
) -> usize {
    let queue = Arc::new((
        Mutex::new(VecDeque::<usize>::new()),
        Condvar::new(),
        Condvar::new(),
    ));

    let mut handles = Vec::new();

    // 生产者
    for pid in 0..producers {
        let q = Arc::clone(&queue);
        handles.push(thread::spawn(move || {
            for i in 0..items {
                let (lock, not_full, not_empty) = &*q;
                let mut buf = lock.lock().unwrap();
                while buf.len() >= capacity {
                    buf = not_full.wait(buf).unwrap();
                }
                buf.push_back(i + pid * items);
                not_empty.notify_one();
            }
        }));
    }

    // 消费者
    let consumed_total = Arc::new(Mutex::new(0usize));
    for _ in 0..consumers {
        let q = Arc::clone(&queue);
        let total = Arc::clone(&consumed_total);
        handles.push(thread::spawn(move || {
            // 总消费数量未知，这里根据 producers*items 进行退出控制
            let total_target = producers * items;
            loop {
                let (lock, not_full, not_empty) = &*q;
                let mut buf = lock.lock().unwrap();
                while buf.is_empty() {
                    // 若消费总数已达目标，退出
                    if *total.lock().unwrap() >= total_target {
                        return;
                    }
                    buf = not_empty.wait(buf).unwrap();
                }
                if let Some(_v) = buf.pop_front() {
                    *total.lock().unwrap() += 1;
                    not_full.notify_one();
                }
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }
    *consumed_total.lock().unwrap()
}

/// 超时等待：直到某事件发生或达到截止时间
pub fn wait_with_timeout_demo(timeout_ms: u64) -> bool {
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let (lock, cvar) = &*pair;

    let start = Instant::now();
    let p2 = Arc::clone(&pair);
    let _notifier = thread::spawn(move || {
        // 模拟：可能比超时更晚才设置完成
        thread::sleep(Duration::from_millis(timeout_ms + 10));
        let (l, cv) = &*p2;
        let mut done = l.lock().unwrap();
        *done = true;
        cv.notify_all();
    });

    let done = lock.lock().unwrap();
    let res = cvar
        .wait_timeout_while(done, Duration::from_millis(timeout_ms), |d| !*d)
        .unwrap();

    let (_guard, wait_result) = res;
    let timed_out = wait_result.timed_out();
    let _elapsed = start.elapsed();
    !timed_out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bounded_queue_demo() {
        let consumed = bounded_queue_demo(32, 3, 2, 1_000);
        assert_eq!(consumed, 3 * 1_000);
    }

    #[test]
    fn test_wait_with_timeout_demo() {
        // 通常会超时，返回 false
        let ok = wait_with_timeout_demo(20);
        assert!(!ok);
    }
}
