//! # Brown University CRP Ownership Inventory — Program 08
//!
//! **来源 / Source**: Brown University CRP Ownership Inventory 样题
//! **主题 / Topic**: 循环中的所有权 / Ownership in Loops
//!
//! ## 学习目标 / Learning Goal
//!
//! 掌握在迭代过程中转移所有权、使用引用迭代，以及何时需要 `.clone()`。
//! Master ownership transfer during iteration, iterating by reference,
//! and when `.clone()` is needed.
//!
//! ## TODO
//!
//! 1. 实现 `take_ownership_loop`，通过 for 循环消费 Vec 并拼接所有字符串。
//! 2. 实现 `borrow_loop`，不消费输入 Vec，只借用拼接。
//! 3. 比较两种写法在所有权和性能上的差异。

/// 消费（move）Vec 中的所有 String，拼接成一个长字符串。
/// Consumes (moves) all Strings in a Vec and concatenates them into one long String.
pub fn take_ownership_loop(words: Vec<String>) -> String {
    let mut result = String::new();
    // TODO: 使用 for 循环获取每个 String 的所有权并拼接到 result。
    // 注意：这里 words 被消费后不能再使用。
    for word in words {
        result.push_str(&word);
    }
    result
}

/// 不消费 Vec，只借用其中的 String 进行拼接。
/// Borrows the Vec and concatenates its Strings without taking ownership.
pub fn borrow_loop(words: &[String]) -> String {
    let mut result = String::new();
    // TODO: 使用引用迭代，使 words 在函数返回后仍然可用。
    for word in words {
        result.push_str(word);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_take_ownership_loop() {
        let words = vec![String::from("hello"), String::from(" "), String::from("world")];
        let result = take_ownership_loop(words);
        assert_eq!(result, "hello world");
        // words 已被消费，不能再使用
    }

    #[test]
    fn test_borrow_loop() {
        let words = vec![String::from("rust"), String::from(" "), String::from("safe")];
        let result = borrow_loop(&words);
        assert_eq!(result, "rust safe");
        // words 仍然可用
        assert_eq!(words.len(), 3);
    }
}
