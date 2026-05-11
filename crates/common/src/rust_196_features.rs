//! Rust 1.96 特性跟踪模块 —— 通用工具场景
#![allow(clippy::incompatible_msrv)]

use std::collections::VecDeque;

/// # Rust 1.96 特性演示
///
/// 展示 `VecDeque::resize`、`if let guards` 在通用工具中的使用。
pub struct Rust196Features;

impl Rust196Features {
    /// 使用 `VecDeque::resize` 管理通用环形缓冲区
    pub fn resize_ring_buffer<T: Clone>(buffer: VecDeque<T>, len: usize, fill: T) -> VecDeque<T> {
        let mut buf = buffer;
        buf.resize(len, fill);
        buf
    }

    /// 使用 `if let` guards 验证配置值
    pub fn validate_config_value(value: Option<&str>) -> Result<i32, &'static str> {
        match value {
            Some(s)
                if let Ok(n) = s.parse::<i32>()
                    && n >= 0 =>
            {
                Ok(n)
            }
            Some(_) => Err("配置值必须是非负整数"),
            None => Err("配置值缺失"),
        }
    }

    /// 使用 `core::pin::pin!` 在栈上固定临时数据
    pub fn pin_temp_data(data: String) -> usize {
        let pinned = std::pin::pin!(data);
        pinned.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_resize_ring_buffer() {
        let buf = VecDeque::from(vec![1, 2]);
        let result = Rust196Features::resize_ring_buffer(buf, 5, 0);
        assert_eq!(result.len(), 5);
        assert_eq!(Vec::from(result), vec![1, 2, 0, 0, 0]);
    }

    #[test]
    fn test_validate_config_value() {
        assert_eq!(Rust196Features::validate_config_value(Some("42")), Ok(42));
        assert_eq!(
            Rust196Features::validate_config_value(Some("-1")),
            Err("配置值必须是非负整数")
        );
        assert_eq!(
            Rust196Features::validate_config_value(Some("abc")),
            Err("配置值必须是非负整数")
        );
        assert_eq!(
            Rust196Features::validate_config_value(None),
            Err("配置值缺失")
        );
    }

    #[test]
    fn test_pin_temp_data() {
        assert_eq!(Rust196Features::pin_temp_data("hello".to_string()), 5);
    }
}
