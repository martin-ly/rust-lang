//! # 练习 2: 字符串 Slice
//!
//! **难度**: Easy  
//! **考点**: String、&str、slice 的关系
//!
//! ## 题目描述
//!
//! 实现一个函数，返回字符串的第一个单词。
//! 如果字符串中没有空格，则返回整个字符串。
//!
//! ## 提示
//!
//! - 使用 `split_whitespace()` 或手动查找空格位置
//! - 返回类型使用 `&str` 以避免所有权转移

/// 返回字符串的第一个单词
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
