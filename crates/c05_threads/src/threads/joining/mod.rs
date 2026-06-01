//! 1) 基本 join
//! 1) this join
//! 1) 基this join
//! 2) 多线程 join 汇聚结果
//! 2) thread join result
//! 2) 多thread join 汇聚result
//! 4) join error handlingand panic propagation（补充）
use std::sync::mpsc;
use std::thread;
use std::time::Duration;

/// 基本 join 示例
/// this join example
/// 基this join Example of
pub fn basic_join() {
    let handle = thread::spawn(|| {
        thread::sleep(Duration::from_millis(20));
        42
    });
    let v = handle.join().expect("线程应成功完成");
    println!("join result={}", v);
}

/// 多线程 join 并汇聚结果
/// thread join and result
pub fn join_multiple_and_collect(n: usize) -> i32 {
    let mut handles = Vec::new();
    for i in 0..n as i32 {
        handles.push(thread::spawn(move || i * i));
    }
    handles
        .into_iter()
        .map(|h| h.join().expect("线程应成功完成"))
        .sum()
}

/// 使用通道模拟“join 带超时”
/// channel “join ”
pub fn join_with_timeout_simulated(timeout_ms: u64) -> Option<i32> {
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        thread::sleep(Duration::from_millis(50));
        let _ = tx.send(7);
    });
    rx.recv_timeout(Duration::from_millis(timeout_ms)).ok()
}

pub fn join_with_panic_handling() -> bool {
    let handle = thread::spawn(|| {
        panic!("boom");
    });
    handle.join().is_err()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_join() {
        basic_join();
    }

    #[test]
    fn test_join_multiple_and_collect() {
        let s = join_multiple_and_collect(4);
        // 0^2 + 1^2 + 2^2 + 3^2 = 14
        assert_eq!(s, 14);
    }

    #[test]
    fn test_join_with_timeout_simulated() {
        assert_eq!(join_with_timeout_simulated(10), None); // 10ms 超时
        assert_eq!(join_with_timeout_simulated(100), Some(7)); // 足够等待
    }

    #[test]
    fn test_join_with_panic_handling() {
        assert!(join_with_panic_handling());
    }
}
