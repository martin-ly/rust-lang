//! # 练习 8: Luhn 算法 / Exercise 8: Luhn Algorithm
//!
//! **难度 / Difficulty**: Medium  
//! **考点 / Focus**: 迭代器、字符处理、错误处理
//!
//! ## 题目描述 / Problem Description
//!
//! 实现 Luhn 校验算法，用于验证信用卡号等标识符。
//!
//! 对应 Google Comprehensive Rust Day 4 Testing 练习：Luhn Algorithm。
//!
//! ## Luhn 算法步骤
//!
//! 1. 从右向左，对每一位数字编号（最右边为第 1 位）
//! 2. 奇数位（1, 3, 5...）保持原值
//! 3. 偶数位（2, 4, 6...）乘以 2；若结果大于 9，则减去 9
//! 4. 所有位求和，若总和能被 10 整除则有效
//!
//! 空格允许出现，应被忽略；出现非数字字符应返回错误。
//!
//! ## 要求 / Requirements
//!
//! - 不得使用 `unsafe` / Do not use `unsafe`
//! - 输入为空或仅空格时返回 `false`

/// 验证 Luhn 校验码是否有效
/// Validate a Luhn checksum
#[allow(clippy::manual_is_multiple_of)] // 教学中 `sum % 10 == 0` 更直观
pub fn is_valid(code: &str) -> bool {
    let digits: Vec<u32> = code
        .chars()
        .filter(|c| !c.is_whitespace())
        .map(|c| c.to_digit(10))
        .collect::<Option<Vec<_>>>()
        .unwrap_or_default();

    if digits.len() <= 1 {
        return false;
    }

    let sum: u32 = digits
        .iter()
        .rev()
        .enumerate()
        .map(|(i, &d)| {
            if i % 2 == 0 {
                d
            } else {
                let doubled = d * 2;
                if doubled > 9 { doubled - 9 } else { doubled }
            }
        })
        .sum();

    sum % 10 == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_luhn() {
        assert!(is_valid("4532015112830366")); // Visa test card
    }

    #[test]
    fn test_valid_with_spaces() {
        assert!(is_valid("4532 0151 1283 0366"));
    }

    #[test]
    fn test_invalid_luhn() {
        assert!(!is_valid("4532015112830367"));
    }

    #[test]
    fn test_too_short() {
        assert!(!is_valid("0"));
        assert!(!is_valid("  "));
    }

    #[test]
    fn test_non_digit() {
        assert!(!is_valid("4532-0151-1283-0366"));
    }
}
