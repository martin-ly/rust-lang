//! Rust 1.97 特性跟踪模块 —— 算法
#![allow(clippy::incompatible_msrv)]

use std::collections::VecDeque;

/// # Rust 1.97 特性演示
///
/// 展示 `repeat_n`、`Vec::pop_if` 和 `VecDeque::resize` 在算法中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `repeat_n` 生成初始化序列
    pub fn fill_sequence<T: Clone>(value: T, count: usize) -> Vec<T> {
        std::iter::repeat_n(value, count).collect()
    }

    /// 使用 `Vec::pop_if` 条件性移除末尾元素
    pub fn pop_if_greater(vec: &mut Vec<i32>, threshold: i32) -> Option<i32> {
        vec.pop_if(|x| *x > threshold)
    }

    /// 使用 `VecDeque::resize` 调整环形缓冲区大小
    pub fn resize_deque<T: Clone>(deque: VecDeque<T>, len: usize, fill: T) -> VecDeque<T> {
        let mut d = deque;
        d.resize(len, fill);
        d
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fill_sequence() {
        assert_eq!(Rust197Features::fill_sequence(0, 5), vec![0, 0, 0, 0, 0]);
        assert_eq!(
            Rust197Features::fill_sequence("a".to_string(), 2),
            vec!["a", "a"]
        );
    }

    #[test]
    fn test_pop_if_greater() {
        let mut v = vec![1, 2, 10];
        assert_eq!(Rust197Features::pop_if_greater(&mut v, 5), Some(10));
        assert_eq!(v, vec![1, 2]);

        let mut v2 = vec![1, 2, 3];
        assert_eq!(Rust197Features::pop_if_greater(&mut v2, 5), None);
        assert_eq!(v2, vec![1, 2, 3]);
    }

    #[test]
    fn test_resize_deque() {
        let d = VecDeque::from(vec![1, 2]);
        let result = Rust197Features::resize_deque(d, 4, 0);
        assert_eq!(result.len(), 4);
        assert_eq!(Vec::from(result), vec![1, 2, 0, 0]);
    }
}
