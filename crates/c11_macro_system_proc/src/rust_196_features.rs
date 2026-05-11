//! Rust 1.96 特性模块 —— 过程宏场景
//!
//! 本模块展示 Rust 1.96 在过程宏上下文中的关键特性：
//! - `VecDeque::resize`
//! - `std::iter::repeat_n`

#![allow(clippy::incompatible_msrv)]

use std::collections::VecDeque;

/// # Rust 1.96 特性演示
pub struct Rust196Features;

impl Rust196Features {
    /// `VecDeque::resize` — 调整双端队列大小
    ///
    /// 在宏处理过程中动态调整 token 缓冲区大小。
    pub fn token_buffer_resize() -> VecDeque<&'static str> {
        let mut buffer = VecDeque::from(["ident", "="]);
        buffer.resize(5, "placeholder");
        buffer
    }

    /// `std::iter::repeat_n` — 有限次重复
    ///
    /// 生成 N 个相同值的迭代器，比 `std::iter::repeat(...).take(N)` 更简洁。
    pub fn repeat_placeholder(n: usize) -> Vec<i32> {
        std::iter::repeat_n(0, n).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_token_buffer_resize() {
        let buffer = Rust196Features::token_buffer_resize();
        assert_eq!(
            buffer,
            VecDeque::from(["ident", "=", "placeholder", "placeholder", "placeholder"])
        );
    }

    #[test]
    fn test_repeat_placeholder() {
        let v = Rust196Features::repeat_placeholder(4);
        assert_eq!(v, vec![0, 0, 0, 0]);
    }

    #[test]
    fn test_repeat_placeholder_empty() {
        let v = Rust196Features::repeat_placeholder(0);
        assert!(v.is_empty());
    }
}
