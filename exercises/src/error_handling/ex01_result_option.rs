//! # 练习 1: Result 与 Option
//!
//! **难度**: Easy  
//! **考点**: Result、Option、? 运算符
//!
//! ## 题目描述
//!
//! 掌握 Result 和 Option 的基本操作与转换。

/// 安全除法，除零时返回 None
pub fn safe_divide(a: f64, b: f64) -> Option<f64> {
    if b == 0.0 {
        None
    } else {
        Some(a / b)
    }
}

/// 解析字符串为整数，失败时返回错误信息
pub fn parse_positive_int(s: &str) -> Result<u32, &'static str> {
    match s.parse::<u32>() {
        Ok(n) if n > 0 => Ok(n),
        Ok(_) => Err("数字必须大于 0"),
        Err(_) => Err("无效的整数字符串"),
    }
}

/// 链式操作：先解析，再检查范围，最后加倍
pub fn parse_and_double(s: &str) -> Result<u32, &'static str> {
    let n = parse_positive_int(s)?;
    if n > 1000 {
        return Err("数字太大");
    }
    Ok(n * 2)
}

/// Option 和 Result 的相互转换
pub fn option_to_result(opt: Option<i32>) -> Result<i32, &'static str> {
    opt.ok_or("值为空")
}

/// 尝试从多个 Option 中获取第一个 Some
pub fn first_some(values: Vec<Option<i32>>) -> Option<i32> {
    values.into_iter().flatten().next()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_safe_divide() {
        assert_eq!(safe_divide(10.0, 2.0), Some(5.0));
        assert_eq!(safe_divide(10.0, 0.0), None);
    }

    #[test]
    fn test_parse_positive_int() {
        assert_eq!(parse_positive_int("42"), Ok(42));
        assert_eq!(parse_positive_int("0"), Err("数字必须大于 0"));
        assert_eq!(parse_positive_int("abc"), Err("无效的整数字符串"));
    }

    #[test]
    fn test_parse_and_double() {
        assert_eq!(parse_and_double("5"), Ok(10));
        assert_eq!(parse_and_double("0"), Err("数字必须大于 0"));
        assert_eq!(parse_and_double("2000"), Err("数字太大"));
    }

    #[test]
    fn test_option_to_result() {
        assert_eq!(option_to_result(Some(5)), Ok(5));
        assert_eq!(option_to_result(None), Err("值为空"));
    }

    #[test]
    fn test_first_some() {
        assert_eq!(first_some(vec![None, Some(2), Some(3)]), Some(2));
        assert_eq!(first_some(vec![None, None]), None);
    }
}
