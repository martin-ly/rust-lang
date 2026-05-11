//! Rust 1.97 特性跟踪模块 —— 进程与 FFI
#![allow(clippy::incompatible_msrv)]

use std::collections::VecDeque;
use std::io;

/// # Rust 1.97 特性演示
///
/// 展示 `io::Error::other` 和 `VecDeque::resize` 在进程管理中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `io::Error::other` 快速创建进程错误
    pub fn process_error(reason: &str) -> io::Error {
        io::Error::other(reason)
    }

    /// 使用 `VecDeque::resize` 管理进程参数队列
    pub fn resize_args_queue(args: VecDeque<String>, expected_len: usize) -> VecDeque<String> {
        let mut queue = args;
        queue.resize(expected_len, String::from(""));
        queue
    }

    /// 结合两者进行进程启动验证
    pub fn validate_process_args(args: VecDeque<String>) -> Result<VecDeque<String>, io::Error> {
        if args.is_empty() {
            return Err(io::Error::other("进程参数不能为空"));
        }
        let mut queue = args;
        queue.resize(3, String::from("default"));
        Ok(queue)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_process_error() {
        let err = Rust197Features::process_error("fork failed");
        assert_eq!(err.kind(), io::ErrorKind::Other);
    }

    #[test]
    fn test_resize_args_queue() {
        let q = VecDeque::from(vec!["a".to_string()]);
        let result = Rust197Features::resize_args_queue(q, 3);
        assert_eq!(result.len(), 3);
        assert_eq!(result[0], "a");
        assert_eq!(result[1], "");
        assert_eq!(result[2], "");
    }

    #[test]
    fn test_validate_process_args() {
        let q = VecDeque::from(vec!["prog".to_string()]);
        let result = Rust197Features::validate_process_args(q).unwrap();
        assert_eq!(result.len(), 3);
        assert_eq!(result[0], "prog");

        let empty: VecDeque<String> = VecDeque::new();
        assert!(Rust197Features::validate_process_args(empty).is_err());
    }
}
