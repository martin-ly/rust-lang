//! Rust 1.95 特性 —— 通用工具场景

use std::ops::ControlFlow;

/// # 真实 Rust 1.95 特性演示
///
/// 展示 `ControlFlow::map_break`、 `const {}` 以及 `if let` guards 在通用工具中的使用。
pub struct RealRust195Features;

impl RealRust195Features {
    /// 使用 `ControlFlow::map_break` 对错误值进行映射
    pub fn control_flow_map_demo() -> ControlFlow<i32, ()> {
        ControlFlow::Break(21).map_break(|e| e * 2)
    }

    /// 使用 `const {}` 计算泛型类型大小
    pub const fn const_block_generic_size() -> usize {
        const { std::mem::size_of::<u64>() }
    }

    /// 使用 `if let` guard 分类 `Option<String>`
    pub fn classify_option_with_guard(opt: Option<String>) -> Result<&'static str, &'static str> {
        match opt {
            Some(s)
                if let Ok(n) = s.parse::<i32>()
                    && n > 0 =>
            {
                Ok("positive number")
            }
            Some(s) if s.is_empty() => Ok("empty string"),
            Some(_) => Ok("non-empty non-number"),
            None => Err("missing value"),
        }
    }
}

#[cfg(test)]
mod real_rust_195_tests {
    use super::*;

    #[test]
    fn test_control_flow_map_demo() {
        assert_eq!(
            RealRust195Features::control_flow_map_demo(),
            ControlFlow::Break(42)
        );
    }

    #[test]
    fn test_const_block_generic_size() {
        const { assert!(RealRust195Features::const_block_generic_size() == 8) };
    }

    #[test]
    fn test_classify_option_with_guard() {
        assert_eq!(
            RealRust195Features::classify_option_with_guard(Some("42".to_string())),
            Ok("positive number")
        );
        assert_eq!(
            RealRust195Features::classify_option_with_guard(Some("".to_string())),
            Ok("empty string")
        );
        assert_eq!(
            RealRust195Features::classify_option_with_guard(Some("hello".to_string())),
            Ok("non-empty non-number")
        );
        assert_eq!(
            RealRust195Features::classify_option_with_guard(None),
            Err("missing value")
        );
    }
}
