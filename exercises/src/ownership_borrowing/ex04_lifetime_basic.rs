//! # 练习 4: 基础生命周期标注
//!
//! **难度**: Medium  
//! **考点**: 显式生命周期标注、生命周期省略规则
//!
//! ## 题目描述
//!
//! 为函数添加正确的生命周期标注，使其能够编译通过。
//! 函数返回两个字符串切片中较长的一个。

/// 返回两个字符串切片中较长的一个
pub fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}

/// 返回以空格分割后的第一个字段
pub fn first_field(s: &str) -> &str {
    match s.find(' ') {
        Some(idx) => &s[..idx],
        None => s,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_longest_first() {
        let s1 = String::from("abcdef");
        let s2 = "xyz";
        assert_eq!(longest(&s1, s2), "abcdef");
    }

    #[test]
    fn test_longest_second() {
        let s1 = "ab";
        let s2 = String::from("xyzw");
        assert_eq!(longest(s1, &s2), "xyzw");
    }

    #[test]
    fn test_first_field() {
        let s = "hello world rust";
        assert_eq!(first_field(s), "hello");
    }
}
