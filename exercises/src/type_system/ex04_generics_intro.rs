//! # 练习 4: 泛型入门
//!
//! **难度**: Medium  
//! **考点**: 泛型函数、类型约束
//!
//! ## 题目描述
//!
//! 实现泛型函数，使其适用于多种类型。

use std::cmp::Ordering;

/// 泛型二分查找
pub fn binary_search<T: Ord>(arr: &[T], target: &T) -> Option<usize> {
    let mut left = 0usize;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
        match arr[mid].cmp(target) {
            Ordering::Equal => return Some(mid),
            Ordering::Less => left = mid + 1,
            Ordering::Greater => right = mid,
        }
    }
    None
}

/// 交换两个可变引用指向的值
pub fn swap<T>(a: &mut T, b: &mut T) {
    std::mem::swap(a, b);
}

/// 返回切片中的最大元素
pub fn max_in_slice<T: Ord>(slice: &[T]) -> Option<&T> {
    slice.iter().max()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binary_search_found() {
        let arr = [1, 3, 5, 7, 9];
        assert_eq!(binary_search(&arr, &5), Some(2));
    }

    #[test]
    fn test_binary_search_not_found() {
        let arr = [1, 3, 5, 7, 9];
        assert_eq!(binary_search(&arr, &4), None);
    }

    #[test]
    fn test_swap() {
        let mut a = 5;
        let mut b = 10;
        swap(&mut a, &mut b);
        assert_eq!(a, 10);
        assert_eq!(b, 5);
    }

    #[test]
    fn test_max_in_slice() {
        assert_eq!(max_in_slice(&[3, 1, 4, 1, 5]), Some(&5));
        assert_eq!(max_in_slice(&[] as &[i32]), None);
    }

    #[test]
    fn test_binary_search_strings() {
        let words = vec!["apple", "banana", "cherry", "date"];
        assert_eq!(binary_search(&words, &"cherry"), Some(2));
    }
}
