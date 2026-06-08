//! # 练习 3: 可变引用规则 / Exercise 3: Mutable Borrowing Rules
//!
//! **难度 / Difficulty**: Easy  
//! **考点 / Focus**: 可变引用的排他性、可变与不可变引用不能共存
//!   Exclusivity of mutable references; mutable and immutable references cannot coexist
//!
//! ## 题目描述 / Problem Description
//!
//! 实现一个函数 `append_greeting`，接收一个 `&mut String`，
//! 在其末尾追加 `"，你好！"`。
//! Implement a function `append_greeting` that takes a `&mut String`
//! and appends `"，你好！"` to its end.
//!
//! 同时实现 `count_chars`，返回字符串的字符数（不获取所有权）。
//! Also implement `count_chars` that returns the character count (without taking ownership).

/// 在字符串末尾追加问候语
/// Appends a greeting to the end of a string
pub fn append_greeting(s: &mut String) {
    s.push_str("，你好！");
}

/// 返回字符串的字符数
/// Returns the number of characters in a string
pub fn count_chars(s: &str) -> usize {
    s.chars().count()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_append_greeting() {
        let mut s = String::from("Rust");
        append_greeting(&mut s);
        assert_eq!(s, "Rust，你好！");
    }

    #[test]
    fn test_count_chars() {
        let s = String::from("Rust语言");
        assert_eq!(count_chars(&s), 6);
    }

    #[test]
    fn test_borrow_rules() {
        let mut s = String::from("test");
        append_greeting(&mut s);
        // 可变借用结束后，可以进行不可变借用
        // After the mutable borrow ends, an immutable borrow is allowed
        assert_eq!(count_chars(&s), 8); // "test，你好！" = 8 chars
    }
}
