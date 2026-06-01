//! Rust 1.97 特性跟踪模块 —— 设计模式
//! Rust 1.97 featurestracingmodule design pattern
#![allow(clippy::incompatible_msrv)]

use std::ffi::CString;
use std::fmt;
use std::num::NonZeroU32;
use std::str::FromStr;

/// # Rust 1.97 设计模式特性演示
/// # Rust 1.97 design feature demonstration
///
/// Rust 1.97 稳定化的核心设计模式相关 API：
/// Rust 1.97 core design API：
/// - `FromStr` for `CString` — 从字符串解析 C 字符串
/// - `FromStr` for `CString` string C string
/// - `LowerExp` / `UpperExp` for `NonZero` — 科学计数法格式化
/// - `Option::as_slice` / `as_mut_slice` Null Object pattern
pub struct Rust197DesignPatternFeatures;

impl Rust197DesignPatternFeatures {
    /// 使用 `FromStr` for `CString` 从字符串创建 C 字符串
    /// use `FromStr` for `CString` stringcreate C string
    ///
    /// 如果输入包含 NUL 字节，返回错误。
    /// if NUL ，。
    pub fn parse_c_string(input: &str) -> Result<CString, CStringParseError> {
        CString::from_str(input).map_err(|_| CStringParseError)
    }

    /// 使用 `NonZeroU32` 的科学计数法格式化
    ///
    /// Rust 1.97 为 `NonZero` 类型实现了 `LowerExp` 和 `UpperExp`。
    pub fn format_nonzero_scientific(n: NonZeroU32) -> (String, String) {
        let lower = format!("{:e}", n);
        let upper = format!("{:E}", n);
        (lower, upper)
    }

    /// 使用 `Option::as_slice` 实现 Null Object 模式
    /// use `Option::as_slice` implementation Null Object pattern
    /// `None` as ，`Some` as element ，
    /// 统一处理"可能存在的值"和"空值"两种情况。
    /// "may in "and ""situation 。
    pub fn option_to_slice<T>(opt: &Option<T>) -> &[T] {
        opt.as_slice()
    }
}

/// `CString` 解析错误的标记类型
/// `CString` error type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CStringParseError;

impl fmt::Display for CStringParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "input contains NUL byte, cannot create C string")
    }
}

impl std::error::Error for CStringParseError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_c_string_valid() {
        let result = Rust197DesignPatternFeatures::parse_c_string("hello");
        assert!(result.is_ok());
        assert_eq!(result.unwrap().to_bytes(), b"hello");
    }

    #[test]
    fn test_parse_c_string_with_nul() {
        let result = Rust197DesignPatternFeatures::parse_c_string("he\0llo");
        assert!(result.is_err());
    }

    #[test]
    fn test_format_nonzero_scientific() {
        let n = NonZeroU32::new(1000).unwrap();
        let (lower, upper) = Rust197DesignPatternFeatures::format_nonzero_scientific(n);
        assert_eq!(lower, "1e3");
        assert_eq!(upper, "1E3");
    }

    #[test]
    fn test_option_to_slice_some() {
        let opt = Some(42);
        let slice = Rust197DesignPatternFeatures::option_to_slice(&opt);
        assert_eq!(slice, &[42]);
    }

    #[test]
    fn test_option_to_slice_none() {
        let opt: Option<i32> = None;
        let slice = Rust197DesignPatternFeatures::option_to_slice(&opt);
        assert!(slice.is_empty());
    }
}
