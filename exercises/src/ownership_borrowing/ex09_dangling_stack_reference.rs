//! # 练习 9: 避免悬垂栈引用 / Exercise 9: Avoiding Dangling Stack References
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: 为什么不能从函数返回指向局部 `String` 的 `&str`
//!   Why returning `&str` pointing to a local `String` is invalid
//!
//! ## 题目描述 / Problem Description
//!
//! 实现 `make_separator`，输入一个 `&str`，返回由该字符串重复两次组成的新 `String`。
//! 例如 `make_separator("-")` 返回 `"--"`。
//!
//! 本练习强调：当函数内部需要构造新数据时，必须返回拥有所有权的 `String`，
//! 而非对局部变量的引用。
//!
//! ## 提示 / Hints
//!
//! - 使用 `format!("{}{}", s, s)` 或 `s.to_string() + s` 创建新的 `String`
//! - 不要尝试返回 `&str`，因为局部 `String` 在函数返回时会被释放

/// 将输入字符串重复两次，返回新的 String
/// Repeats the input string twice, returning a new String
pub fn make_separator(s: &str) -> String {
    format!("{}{}", s, s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_make_separator() {
        let pattern = String::from("-");
        let sep = make_separator(&pattern);
        assert_eq!(sep, "--");
        // pattern 仍可用 / pattern is still usable
        assert_eq!(pattern, "-");
    }

    #[test]
    fn test_make_separator_empty() {
        assert_eq!(make_separator(""), "");
    }

    #[test]
    fn test_make_separator_multi_char() {
        assert_eq!(make_separator("=="), "====");
    }
}
