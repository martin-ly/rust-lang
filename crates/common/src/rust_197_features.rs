//! Rust 1.97 特性跟踪模块 —— 通用工具
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 特性演示
///
/// 展示 `Option::is_none_or`、`Result::is_ok_and` 和 `repeat_n` 在通用工具中的使用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `Option::is_none_or` 进行通用验证
    pub fn is_none_or_valid<T: PartialOrd>(opt: Option<T>, min: T) -> bool {
        opt.is_none_or(|v| v >= min)
    }

    /// 使用 `Result::is_ok_and` 进行通用结果检查
    pub fn is_ok_and_matches<T: PartialEq>(result: Result<T, &'static str>, expected: T) -> bool {
        result.is_ok_and(|v| v == expected)
    }

    /// 使用 `repeat_n` 生成通用重复序列
    pub fn repeat_value<T: Clone>(value: T, count: usize) -> Vec<T> {
        std::iter::repeat_n(value, count).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_none_or_valid() {
        assert!(Rust197Features::is_none_or_valid(None, 10));
        assert!(Rust197Features::is_none_or_valid(Some(15), 10));
        assert!(!Rust197Features::is_none_or_valid(Some(5), 10));
    }

    #[test]
    fn test_is_ok_and_matches() {
        assert!(Rust197Features::is_ok_and_matches(Ok(42), 42));
        assert!(!Rust197Features::is_ok_and_matches(Ok(42), 0));
        assert!(!Rust197Features::is_ok_and_matches(Err("fail"), 42));
    }

    #[test]
    fn test_repeat_value() {
        assert_eq!(
            Rust197Features::repeat_value('*', 5),
            vec!['*', '*', '*', '*', '*']
        );
        assert_eq!(
            Rust197Features::repeat_value("item".to_string(), 2),
            vec!["item", "item"]
        );
    }
}
