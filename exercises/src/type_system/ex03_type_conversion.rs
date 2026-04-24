//! # 练习 3: 类型转换
//!
//! **难度**: Easy  
//! **考点**: From/Into 特质、类型安全转换
//!
//! ## 题目描述
//!
//! 为自定义类型实现 From 和 Into 特质，实现类型之间的安全转换。

/// 温度单位：摄氏度
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Celsius(pub f64);

/// 温度单位：华氏度
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Fahrenheit(pub f64);

impl From<Fahrenheit> for Celsius {
    fn from(f: Fahrenheit) -> Self {
        Celsius((f.0 - 32.0) * 5.0 / 9.0)
    }
}

impl From<Celsius> for Fahrenheit {
    fn from(c: Celsius) -> Self {
        Fahrenheit(c.0 * 9.0 / 5.0 + 32.0)
    }
}

/// 包装一个可能很大的数字，提供安全的 i32 转换
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SafeNumber(pub i64);

impl From<SafeNumber> for Option<i32> {
    fn from(n: SafeNumber) -> Self {
        if n.0 >= i32::MIN as i64 && n.0 <= i32::MAX as i64 {
            Some(n.0 as i32)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fahrenheit_to_celsius() {
        let f = Fahrenheit(32.0);
        let c: Celsius = f.into();
        assert_eq!(c, Celsius(0.0));
    }

    #[test]
    fn test_celsius_to_fahrenheit() {
        let c = Celsius(100.0);
        let f: Fahrenheit = c.into();
        assert!((f.0 - 212.0).abs() < 0.001);
    }

    #[test]
    fn test_safe_number_valid() {
        let n = SafeNumber(42);
        let opt: Option<i32> = n.into();
        assert_eq!(opt, Some(42));
    }

    #[test]
    fn test_safe_number_overflow() {
        let n = SafeNumber(i64::MAX);
        let opt: Option<i32> = n.into();
        assert_eq!(opt, None);
    }
}
