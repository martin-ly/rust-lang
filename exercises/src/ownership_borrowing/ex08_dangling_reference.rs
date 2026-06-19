//! # 练习 8: 避免悬垂引用 / Exercise 8: Avoiding Dangling References
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: 返回值所有权、不能返回局部数据的引用
//!   Return value ownership; cannot return references to local data
//!
//! ## 题目描述 / Problem Description
//!
//! 实现 `first_char`，返回输入字符串的第一个字符。
//! 若输入为空字符串，则返回 `'?'`。
//!
//! 本练习重点：理解为什么函数不能返回对局部 `String` 的引用，
//! 以及如何通过返回 `String` 或 `char` 来避免悬垂引用。
//!
//! ## 提示 / Hints
//!
//! - `s.chars().next()` 返回 `Option<char>`
//! - 返回 `char` 是 Copy 类型，不涉及所有权转移问题

/// 返回字符串的第一个字符；空字符串返回 '?'
/// Returns the first character of a string; returns '?' for empty strings
pub fn first_char(s: &str) -> char {
    s.chars().next().unwrap_or('?')
}

/// 返回一个将输入字符串转换为大写的新 String
/// Returns a new uppercased String from the input
pub fn to_excited(s: &str) -> String {
    let upper = s.to_uppercase();
    format!("{}!", upper)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_first_char() {
        let s = String::from("hello");
        assert_eq!(first_char(&s), 'h');
        // s 仍可用 / s is still usable
        assert_eq!(s, "hello");
    }

    #[test]
    fn test_first_char_empty() {
        assert_eq!(first_char(""), '?');
    }

    #[test]
    fn test_to_excited() {
        let s = String::from("rust");
        let excited = to_excited(&s);
        assert_eq!(excited, "RUST!");
        // s 仍可用 / s is still usable
        assert_eq!(s, "rust");
    }
}
