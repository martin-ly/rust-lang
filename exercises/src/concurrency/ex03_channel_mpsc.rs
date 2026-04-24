//! # 练习 3: MPSC 通道
//!
//! **难度**: Easy  
//! **考点**: mpsc::channel、多生产者单消费者
//!
//! ## 题目描述
//!
//! 使用通道在线程间传递消息。

use std::sync::mpsc;
use std::thread;

/// 创建多个生产者线程，发送数字，收集所有结果
pub fn collect_from_workers(num_workers: usize, items_per_worker: usize) -> Vec<usize> {
    let (tx, rx) = mpsc::channel();

    for worker_id in 0..num_workers {
        let tx = tx.clone();
        thread::spawn(move || {
            for i in 0..items_per_worker {
                tx.send(worker_id * items_per_worker + i).unwrap();
            }
        });
    }

    // 丢弃原始发送者，这样当所有克隆都结束时通道会关闭
    drop(tx);

    rx.iter().collect()
}

/// 发送一批工作并确认收到所有结果
pub fn send_and_confirm(values: Vec<i32>) -> Vec<i32> {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        for v in values {
            tx.send(v * 2).unwrap();
        }
    });

    rx.iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_collect_from_workers() {
        let mut result = collect_from_workers(3, 2);
        result.sort();
        assert_eq!(result, vec![0, 1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_send_and_confirm() {
        let values = vec![1, 2, 3, 4, 5];
        let result = send_and_confirm(values);
        assert_eq!(result, vec![2, 4, 6, 8, 10]);
    }
}
