//! Rust 1.93.0 异步编程 特性模块
#![allow(clippy::incompatible_msrv)]

use std::collections::VecDeque;
use std::fmt;

/// 使用 `fmt::from_fn` 创建异步日志格式化器
pub fn create_async_log_formatter(task_id: u64) -> impl fmt::Display {
    fmt::from_fn(move |f: &mut fmt::Formatter<'_>| write!(f, "[async-task-{}]", task_id))
}

/// 异步风格的 `VecDeque` 条件消费（模拟异步缓冲区）
pub fn consume_async_buffer(deque: &mut VecDeque<i32>) -> Vec<i32> {
    let mut consumed = Vec::new();
    // 先消费前端小值
    while let Some(v) = deque.pop_front_if(|x| *x <= 5) {
        consumed.push(v);
    }
    // 再消费后端大值
    while let Some(v) = deque.pop_back_if(|x| *x >= 100) {
        consumed.push(v);
    }
    consumed
}

/// 演示将格式化器用于异步结果输出
pub fn format_async_results(results: &[i32]) -> String {
    let formatter = fmt::from_fn(|f: &mut fmt::Formatter<'_>| {
        write!(f, "results=[")?;
        for (i, r) in results.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", r)?;
        }
        write!(f, "]")
    });
    format!("{}", formatter)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_async_log_formatter() {
        let fmt = create_async_log_formatter(42);
        assert_eq!(format!("{}", fmt), "[async-task-42]");
    }

    #[test]
    fn test_consume_async_buffer() {
        let mut deque = VecDeque::from([1, 2, 3, 50, 200, 150]);
        let consumed = consume_async_buffer(&mut deque);
        assert_eq!(consumed, vec![1, 2, 3, 150, 200]);
        assert_eq!(deque, VecDeque::from([50]));
    }

    #[test]
    fn test_format_async_results() {
        assert_eq!(format_async_results(&[10, 20, 30]), "results=[10, 20, 30]");
    }
}
