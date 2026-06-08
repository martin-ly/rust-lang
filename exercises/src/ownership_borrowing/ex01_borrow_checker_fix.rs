//! # 练习 1: 修复借用检查错误 / Exercise 1: Fix Borrow Checker Errors
//!
//! **难度 / Difficulty**: Easy  
//! **考点 / Focus**: 理解所有权转移与借用规则 / Understanding ownership transfer and borrowing rules
//!
//! ## 题目描述 / Problem Description
//!
//! 下面的函数需要返回输入字符串的长度，但当前实现会导致编译错误。
//! 请修复代码，使其能够编译通过并通过所有测试。
//! The function below needs to return the length of the input string,
//! but the current implementation causes a compilation error.
//! Please fix the code so it compiles and passes all tests.
//!
//! ## 要求 / Requirements
//!
//! - 不能修改函数签名 / Do not modify the function signature
//! - 使用借用而非所有权转移 / Use borrowing instead of ownership transfer

/// 返回字符串的长度，同时保持原字符串可用
/// Returns the length of a string while keeping the original string usable
pub fn get_length(s: &str) -> usize {
    s.len()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_get_length() {
        let s = String::from("hello");
        let len = get_length(&s);
        assert_eq!(len, 5);
        // 确保 s 仍然可用 / Ensure s is still usable
        assert_eq!(s, "hello");
    }

    #[test]
    fn test_empty_string() {
        let s = String::new();
        assert_eq!(get_length(&s), 0);
    }
}
