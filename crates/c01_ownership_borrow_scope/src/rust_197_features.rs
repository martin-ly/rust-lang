//! Rust 1.97 特性跟踪模块 —— 所有权与内存管理
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 特性演示
///
/// 展示 `std::pin::pin!` 和 `Vec::pop_if` 在所有权管理中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `pin!` 在栈上固定值，避免堆分配
    pub fn stack_pin_value<T>(value: T) -> T
    where
        T: Clone,
    {
        let pinned = std::pin::pin!(value.clone());
        pinned.clone()
    }

    /// 使用 `Vec::pop_if` 条件性地弹出最后一个元素
    pub fn pop_if_even(values: &mut Vec<i32>) -> Option<i32> {
        values.pop_if(|x| *x % 2 == 0)
    }

    /// 结合所有权转移与条件弹出
    pub fn transfer_and_pop_if(
        mut values: Vec<String>,
        predicate: impl FnOnce(&mut String) -> bool,
    ) -> (Vec<String>, Option<String>) {
        let popped = values.pop_if(predicate);
        (values, popped)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stack_pin_value() {
        assert_eq!(Rust197Features::stack_pin_value(42), 42);
        assert_eq!(Rust197Features::stack_pin_value(String::from("pin")), "pin");
    }

    #[test]
    fn test_pop_if_even() {
        let mut v = vec![1, 3, 4];
        assert_eq!(Rust197Features::pop_if_even(&mut v), Some(4));
        assert_eq!(v, vec![1, 3]);

        let mut v2 = vec![1, 3, 5];
        assert_eq!(Rust197Features::pop_if_even(&mut v2), None);
        assert_eq!(v2, vec![1, 3, 5]);
    }

    #[test]
    fn test_transfer_and_pop_if() {
        let v = vec!["a".to_string(), "bb".to_string()];
        let (remaining, popped) = Rust197Features::transfer_and_pop_if(v, |s| s.len() > 1);
        assert_eq!(popped, Some("bb".to_string()));
        assert_eq!(remaining, vec!["a".to_string()]);
    }
}
