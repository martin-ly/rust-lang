//! # 练习 3: 错误传播
//!
//! **难度**: Medium  
//! **考点**: ? 运算符、map_err、错误转换
//!
//! ## 题目描述
//!
//! 在多层调用中优雅地传播错误。

use std::fs;
use std::num::ParseIntError;

/// 读取文件并解析第一行为整数
pub fn read_first_line_as_int(path: &str) -> Result<i32, String> {
    let content = fs::read_to_string(path).map_err(|e| format!("读取失败: {}", e))?;
    let first_line = content.lines().next().ok_or("文件为空")?;
    let num = first_line
        .trim()
        .parse::<i32>()
        .map_err(|e: ParseIntError| format!("解析失败: {}", e))?;
    Ok(num)
}

/// 链式计算：先解析字符串，再计算平方根，最后加倍
pub fn complex_calculation(input: &str) -> Result<f64, &'static str> {
    let n: f64 = input
        .parse()
        .map_err(|_| "无法解析为数字")?;
    if n < 0.0 {
        return Err("不能对负数开方");
    }
    let sqrt = n.sqrt();
    Ok(sqrt * 2.0)
}

/// 收集所有错误而不是提前返回
pub fn parse_all(inputs: &[&str]) -> (Vec<i32>, Vec<String>) {
    let mut successes = Vec::new();
    let mut errors = Vec::new();

    for input in inputs {
        match input.parse::<i32>() {
            Ok(n) => successes.push(n),
            Err(e) => errors.push(format!("'{}' 解析错误: {}", input, e)),
        }
    }

    (successes, errors)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    #[test]
    fn test_read_first_line_as_int() {
        let mut temp = tempfile::NamedTempFile::new().unwrap();
        write!(temp, "42\nsecond line").unwrap();
        let result = read_first_line_as_int(temp.path().to_str().unwrap());
        assert_eq!(result.unwrap(), 42);
    }

    #[test]
    fn test_complex_calculation_ok() {
        assert!((complex_calculation("9").unwrap() - 6.0).abs() < 0.0001);
    }

    #[test]
    fn test_complex_calculation_negative() {
        assert_eq!(complex_calculation("-4"), Err("不能对负数开方"));
    }

    #[test]
    fn test_parse_all() {
        let (ok, err) = parse_all(&["1", "abc", "3", "xyz"]);
        assert_eq!(ok, vec![1, 3]);
        assert_eq!(err.len(), 2);
    }
}
