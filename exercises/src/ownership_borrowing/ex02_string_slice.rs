//! # 练习 2: 字符串 Slice / Exercise 2: String Slices
//!
//! **难度 / Difficulty**: Easy  
//! **考点 / Focus**: String、&str、slice 的关系 / Relationship between String, &str, and slices
//!
//! ## 题目描述 / Problem Description
//!
//! 实现一个函数，返回字符串的第一个单词。
//! 如果字符串中没有空格，则返回整个字符串。
//! Implement a function that returns the first word of a string.
//! If the string contains no spaces, return the entire string.
//!
//! ## 提示 / Hints
//!
//! - 使用 `split_whitespace()` 或手动查找空格位置
//!   Use `split_whitespace()` or manually find the space position
//! - 返回类型使用 `&str` 以避免所有权转移
//!   Use `&str` as the return type to avoid ownership transfer

/// 返回字符串的第一个单词
/// Returns the first word of a string
pub fn first_word(s: &str) -> &str {
    match s.find(' ') {
        Some(idx) => &s[..idx],
        None => s,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_first_word_normal() {
        let s = String::from("hello world");
        assert_eq!(first_word(&s), "hello");
    }

    #[test]
    fn test_first_word_no_space() {
        let s = "rust";
        assert_eq!(first_word(s), "rust");
    }

    #[test]
    fn test_first_word_empty() {
        assert_eq!(first_word(""), "");
    }

    #[test]
    fn test_first_word_multiple_spaces() {
        let s = "foo bar baz";
        assert_eq!(first_word(s), "foo");
    }
}
