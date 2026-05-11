//! Rust 1.97 特性跟踪模块 —— 控制流
#![allow(clippy::incompatible_msrv)]

use std::io;

/// # Rust 1.97 特性演示
///
/// 展示 `Option::is_none_or` 和 `io::Error::other` 在控制流中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `Option::is_none_or` 简化控制流判断
    pub fn allow_access(role: Option<&str>) -> bool {
        role.is_none_or(|r| r == "admin" || r == "user")
    }

    /// 使用 `io::Error::other` 快速创建 IO 错误
    pub fn create_io_error(message: &str) -> io::Error {
        io::Error::other(message)
    }

    /// 结合两者进行错误处理流程控制
    pub fn process_input(input: Option<&str>) -> Result<String, io::Error> {
        if input.is_none_or(|s| s.is_empty()) {
            return Err(io::Error::other("输入为空或无效"));
        }
        Ok(input.unwrap().to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_allow_access() {
        assert!(Rust197Features::allow_access(None));
        assert!(Rust197Features::allow_access(Some("admin")));
        assert!(Rust197Features::allow_access(Some("user")));
        assert!(!Rust197Features::allow_access(Some("guest")));
    }

    #[test]
    fn test_create_io_error() {
        let err = Rust197Features::create_io_error("磁盘已满");
        assert_eq!(err.kind(), io::ErrorKind::Other);
    }

    #[test]
    fn test_process_input() {
        assert!(Rust197Features::process_input(None).is_err());
        assert!(Rust197Features::process_input(Some("")).is_err());
        assert_eq!(
            Rust197Features::process_input(Some("hello")).unwrap(),
            "hello"
        );
    }
}
