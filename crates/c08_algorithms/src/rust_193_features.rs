//! Rust 1.93.0 算法 特性模块
//! Rust 1.93.0 algorithm features module
#![allow(clippy::incompatible_msrv)]

use std::collections::VecDeque;

/// 使用 `VecDeque::pop_front_if` 移除前导零
pub fn trim_leading_zeros(deque: &mut VecDeque<i32>) -> Vec<i32> {
    let mut removed = Vec::new();
    while let Some(v) = deque.pop_front_if(|x| *x == 0) {
        removed.push(v);
    }
    removed
}

/// 使用 `VecDeque::pop_back_if` 移除尾部大于阈值的元素
pub fn trim_tail_greater_than(deque: &mut VecDeque<i32>, limit: i32) -> Vec<i32> {
    let mut removed = Vec::new();
    while let Some(v) = deque.pop_back_if(|x| *x > limit) {
        removed.push(v);
    }
    removed
}

/// 使用 `slice::as_array` 提取定长子数组用于算法处理
pub fn extract_window<const N: usize>(slice: &[i32]) -> Option<&[i32; N]> {
    slice.as_array::<N>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_trim_leading_zeros() {
        let mut deque = VecDeque::from([0, 0, 1, 2, 3]);
        let removed = trim_leading_zeros(&mut deque);
        assert_eq!(removed, vec![0, 0]);
        assert_eq!(deque, VecDeque::from([1, 2, 3]));
    }

    #[test]
    fn test_trim_tail_greater_than() {
        let mut deque = VecDeque::from([1, 2, 3, 10, 20]);
        let removed = trim_tail_greater_than(&mut deque, 5);
        assert_eq!(removed, vec![20, 10]);
        assert_eq!(deque, VecDeque::from([1, 2, 3]));
    }

    #[test]
    fn test_extract_window() {
        let data = [5, 6, 7, 8];
        assert_eq!(extract_window::<4>(&data), Some(&[5, 6, 7, 8]));
        assert_eq!(extract_window::<2>(&[5, 6]), Some(&[5, 6]));
        assert_eq!(extract_window::<10>(&data), None);
    }
}
