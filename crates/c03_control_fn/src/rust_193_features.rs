//! Rust 1.93.0 控制流与函数 特性模块
#![allow(clippy::incompatible_msrv)]

use std::collections::VecDeque;
use std::fmt;

/// 使用 `fmt::from_fn` 从闭包创建 `impl Display`
pub fn create_greeting_formatter(name: &str) -> impl fmt::Display + use<'_> {
    fmt::from_fn(move |f: &mut fmt::Formatter<'_>| write!(f, "Hello, {}!", name))
}

/// 使用 `VecDeque::pop_front_if` 过滤队首元素
pub fn pop_front_negative(deque: &mut VecDeque<i32>) -> Vec<i32> {
    let mut popped = Vec::new();
    while let Some(v) = deque.pop_front_if(|x| *x < 0) {
        popped.push(v);
    }
    popped
}

/// 使用 `VecDeque::pop_back_if` 过滤队尾元素
pub fn pop_back_greater_than(deque: &mut VecDeque<i32>, threshold: i32) -> Vec<i32> {
    let mut popped = Vec::new();
    while let Some(v) = deque.pop_back_if(|x| *x > threshold) {
        popped.push(v);
    }
    popped
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fmt_from_fn() {
        let formatter = create_greeting_formatter("Rust 1.93");
        assert_eq!(format!("{}", formatter), "Hello, Rust 1.93!");
    }

    #[test]
    fn test_pop_front_if() {
        let mut deque = VecDeque::from([-5, -1, 0, 3, 7]);
        let negatives = pop_front_negative(&mut deque);
        assert_eq!(negatives, vec![-5, -1]);
        assert_eq!(deque, VecDeque::from([0, 3, 7]));
    }

    #[test]
    fn test_pop_back_if() {
        let mut deque = VecDeque::from([1, 2, 3, 10, 20]);
        let big = pop_back_greater_than(&mut deque, 5);
        assert_eq!(big, vec![20, 10]);
        assert_eq!(deque, VecDeque::from([1, 2, 3]));
    }
}
