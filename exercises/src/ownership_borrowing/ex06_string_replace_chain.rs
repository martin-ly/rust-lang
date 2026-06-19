//! # 练习 6: 字符串替换链 / Exercise 6: String Replacement Chain
//!
//! **难度 / Difficulty**: Easy  
//! **考点 / Focus**: 理解 `&str` 借用、`String` 返回值与所有权链
//!
//! ## 题目描述 / Problem Description
//!
//! 实现 `make_exciting`，输入一个 `&str`，依次将其中的 `.` 替换为 `!`、`?` 替换为 `‽`，
//! 返回一个新的 `String`。
//!
//! 注意：输入是借用，不能获取其所有权；输出必须拥有新分配的所有权。
//!
//! ## 要求 / Requirements
//!
//! - 不得修改函数签名 / Do not modify the function signature
//! - 不得使用 `unsafe` / Do not use `unsafe`

/// 将字符串中的 `.` 替换为 `!`，`?` 替换为 `‽`，返回新的 String
/// Replaces `.` with `!` and `?` with `‽`, returning a new String
pub fn make_exciting(s: &str) -> String {
    // 先替换 `.`，再替换 `?`，每一步都返回新的 String
    // First replace `.`, then replace `?`; each step returns a new String
    s.replace(".", "!").replace("?", "‽")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_make_exciting() {
        let input = String::from("Hello. How are you?");
        let output = make_exciting(&input);
        assert_eq!(output, "Hello! How are you‽");
        // input 仍应可用 / input should still be usable
        assert_eq!(input, "Hello. How are you?");
    }

    #[test]
    fn test_no_punctuation() {
        assert_eq!(make_exciting("rust"), "rust");
    }

    #[test]
    fn test_empty() {
        assert_eq!(make_exciting(""), "");
    }
}
