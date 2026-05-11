//! Rust 1.97 特性跟踪模块 —— 嵌入式
#![allow(clippy::incompatible_msrv)]

use std::io;

/// # Rust 1.97 特性演示
///
/// 展示 `io::Error::other` 和 `std::iter::repeat_n` 在嵌入式场景中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `io::Error::other` 快速创建嵌入式设备错误
    pub fn device_error(reason: &str) -> io::Error {
        io::Error::other(reason)
    }

    /// 使用 `repeat_n` 生成初始化字节序列
    pub fn fill_register(value: u8, count: usize) -> Vec<u8> {
        std::iter::repeat_n(value, count).collect()
    }

    /// 结合两者进行寄存器配置验证
    pub fn validate_register_config(
        values: Vec<u8>,
        expected_len: usize,
    ) -> Result<Vec<u8>, io::Error> {
        if values.len() != expected_len {
            return Err(io::Error::other("寄存器配置长度不匹配"));
        }
        Ok(values)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_device_error() {
        let err = Rust197Features::device_error("I2C timeout");
        assert_eq!(err.kind(), io::ErrorKind::Other);
    }

    #[test]
    fn test_fill_register() {
        assert_eq!(
            Rust197Features::fill_register(0xFF, 4),
            vec![0xFF, 0xFF, 0xFF, 0xFF]
        );
        assert!(Rust197Features::fill_register(0x00, 0).is_empty());
    }

    #[test]
    fn test_validate_register_config() {
        let values = vec![0x01, 0x02, 0x03];
        assert_eq!(
            Rust197Features::validate_register_config(values.clone(), 3).unwrap(),
            values
        );
        assert!(Rust197Features::validate_register_config(values, 5).is_err());
    }
}
