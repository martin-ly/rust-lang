//! Rust 1.97 特性跟踪模块 —— 泛型
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 特性演示
///
/// 展示 `std::iter::repeat_n` 和 `Vec::pop_if` 在泛型编程中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `repeat_n` 生成泛型重复序列
    pub fn repeat_value<T: Clone>(value: T, count: usize) -> Vec<T> {
        std::iter::repeat_n(value, count).collect()
    }

    /// 使用 `Vec::pop_if` 在泛型上下文中条件弹出
    pub fn pop_if_matches<T>(
        vec: &mut Vec<T>,
        predicate: impl FnOnce(&mut T) -> bool,
    ) -> Option<T> {
        vec.pop_if(predicate)
    }

    /// 组合 repeat_n 与 pop_if 构建泛型缓冲池
    pub fn create_and_drain_buffer<T: Clone>(value: T, count: usize) -> (Vec<T>, Option<T>) {
        let mut buf: Vec<T> = std::iter::repeat_n(value, count).collect();
        let last = buf.pop_if(|_| true);
        (buf, last)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_repeat_value() {
        assert_eq!(Rust197Features::repeat_value(7, 3), vec![7, 7, 7]);
        assert_eq!(
            Rust197Features::repeat_value("x".to_string(), 2),
            vec!["x", "x"]
        );
    }

    #[test]
    fn test_pop_if_matches() {
        let mut v = vec![1, 2, 3];
        assert_eq!(
            Rust197Features::pop_if_matches(&mut v, |x| *x == 3),
            Some(3)
        );
        assert_eq!(v, vec![1, 2]);
    }

    #[test]
    fn test_create_and_drain_buffer() {
        let (buf, last) = Rust197Features::create_and_drain_buffer(0, 4);
        assert_eq!(buf, vec![0, 0, 0]);
        assert_eq!(last, Some(0));
    }
}
