//! # 练习 1: 修复借用检查错误
//!
//! **难度**: Easy  
//! **考点**: 理解所有权转移与借用规则
//!
//! ## 题目描述
//!
//! 下面的函数需要返回输入字符串的长度，但当前实现会导致编译错误。
//! 请修复代码，使其能够编译通过并通过所有测试。
//!
//! ## 要求
//!
//! - 不能修改函数签名
//! - 使用借用而非所有权转移

/// 返回字符串的长度，同时保持原字符串可用
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
        // 确保 s 仍然可用
        assert_eq!(s, "hello");
    }

    #[test]
    fn test_empty_string() {
        let s = String::new();
        assert_eq!(get_length(&s), 0);
    }
}
