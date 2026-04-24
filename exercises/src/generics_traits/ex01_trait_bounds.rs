//! # 练习 1: 特质约束
//!
//! **难度**: Easy  
//! **考点**: trait bound、where 子句
//!
//! ## 题目描述
//!
//! 实现一个泛型函数，要求类型必须实现 Display 和 PartialOrd，
//! 返回格式化后的最大值描述字符串。

use std::fmt::Display;

/// 返回两个值中较大者的描述
pub fn describe_max<T: Display + PartialOrd>(a: T, b: T) -> String {
    if a > b {
        format!("较大值是: {}", a)
    } else {
        format!("较大值是: {}", b)
    }
}

/// 使用 where 子句的泛型函数：检查切片是否全部相等
pub fn all_equal<T>(slice: &[T]) -> bool
where
    T: PartialEq,
{
    if slice.len() <= 1 {
        return true;
    }
    let first = &slice[0];
    slice.iter().all(|item| item == first)
}

/// 约束类型必须实现 Clone，返回克隆的副本
pub fn cloned_pair<T: Clone>(value: T) -> (T, T) {
    (value.clone(), value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_describe_max() {
        assert_eq!(describe_max(10, 5), "较大值是: 10");
        assert_eq!(describe_max(3.14, 2.71), "较大值是: 3.14");
    }

    #[test]
    fn test_all_equal() {
        assert!(all_equal(&[1, 1, 1]));
        assert!(!all_equal(&[1, 2, 1]));
        assert!(all_equal(&[] as &[i32]));
        assert!(all_equal(&[42]));
    }

    #[test]
    fn test_cloned_pair() {
        let pair = cloned_pair(String::from("hello"));
        assert_eq!(pair.0, "hello");
        assert_eq!(pair.1, "hello");
    }
}
