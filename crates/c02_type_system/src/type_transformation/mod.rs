//! 类型变换：用 `map`、`and_then`、`From` 等组合子在类型之间移动数据。

/// 把 `Option` 转换为 `Result`。
pub fn option_to_result(o: Option<i32>) -> Result<i32, &'static str> {
    o.ok_or("missing value")
}

/// 对 `Option` 做类型保持的映射。
pub fn double_option(o: Option<i32>) -> Option<i32> {
    o.map(|x| x * 2)
}

/// 对 `Result` 做类型变换。
pub fn map_result(r: Result<i32, &'static str>) -> Result<u32, &'static str> {
    r.map(|x| x as u32)
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_option_to_result() {
        assert_eq!(option_to_result(Some(42)), Ok(42));
        assert_eq!(option_to_result(None), Err("missing value"));
    }

    #[test]
    fn test_double_option() {
        assert_eq!(double_option(Some(21)), Some(42));
        assert_eq!(double_option(None), None);
    }

    #[test]
    fn test_map_result() {
        assert_eq!(map_result(Ok(-1)), Ok(u32::MAX));
        assert_eq!(map_result(Err("fail")), Err("fail"));
    }

    #[test]
    fn test_temperature_transform() {
        let f: Fahrenheit = Celsius(100.0).into();
        assert!((f.0 - 212.0).abs() < 1e-10);
    }
}
