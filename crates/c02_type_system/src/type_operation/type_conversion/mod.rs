//! 类型转换：`as`、`From`/`Into`、`TryFrom`/`TryInto`、`parse`。

/// 使用 `as` 做显式数值转换。
pub fn int_to_float() -> f64 {
    let n: i32 = 10;
    n as f64
}

/// 使用 `parse` 将字符串转换为整数。
pub fn parse_i32(s: &str) -> Result<i32, std::num::ParseIntError> {
    s.parse::<i32>()
}

/// 摄氏度。
pub struct Celsius(pub f64);

/// 华氏度。
pub struct Fahrenheit(pub f64);

impl From<Celsius> for Fahrenheit {
    fn from(c: Celsius) -> Self {
        Fahrenheit(c.0 * 9.0 / 5.0 + 32.0)
    }
}

impl From<Fahrenheit> for Celsius {
    fn from(f: Fahrenheit) -> Self {
        Celsius((f.0 - 32.0) * 5.0 / 9.0)
    }
}

/// 可失败的 `i64` → `i32` 转换。
pub fn try_convert_i64_to_i32(v: i64) -> Result<i32, &'static str> {
    i32::try_from(v).map_err(|_| "value out of i32 range")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_as_cast() {
        assert_eq!(int_to_float(), 10.0);
    }

    #[test]
    fn test_parse() {
        assert_eq!(parse_i32("42").unwrap(), 42);
        assert!(parse_i32("abc").is_err());
    }

    #[test]
    fn test_temperature_conversion() {
        let f: Fahrenheit = Celsius(0.0).into();
        assert!((f.0 - 32.0).abs() < 1e-10);

        let c: Celsius = Fahrenheit(212.0).into();
        assert!((c.0 - 100.0).abs() < 1e-10);
    }

    #[test]
    fn test_try_convert() {
        assert_eq!(try_convert_i64_to_i32(42_i64).unwrap(), 42);
        assert!(try_convert_i64_to_i32(i64::MAX).is_err());
    }
}
