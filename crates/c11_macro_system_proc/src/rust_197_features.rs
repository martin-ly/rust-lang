//! Rust 1.97 特性跟踪模块 —— 过程宏
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 特性演示
///
/// 展示 `std::iter::repeat_n` 和 `Option::is_none_or` 在过程宏中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `repeat_n` 生成重复的派生属性
    pub fn repeat_derives(trait_name: &str, count: usize) -> Vec<String> {
        std::iter::repeat_n(format!("#[derive({})]", trait_name), count).collect()
    }

    /// 使用 `Option::is_none_or` 验证可选宏属性
    pub fn is_valid_attribute(attr: Option<&str>) -> bool {
        attr.is_none_or(|a| !a.is_empty())
    }

    /// 组合两者检查宏输入
    pub fn check_macro_input(input: Option<&str>, expected_len: usize) -> Vec<String> {
        match input {
            Some(a) if !a.is_empty() => std::iter::repeat_n(a.to_string(), expected_len).collect(),
            _ => Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_repeat_derives() {
        assert_eq!(
            Rust197Features::repeat_derives("Clone", 2),
            vec!["#[derive(Clone)]", "#[derive(Clone)]"]
        );
    }

    #[test]
    fn test_is_valid_attribute() {
        assert!(Rust197Features::is_valid_attribute(None));
        assert!(Rust197Features::is_valid_attribute(Some("derive")));
        assert!(!Rust197Features::is_valid_attribute(Some("")));
    }

    #[test]
    fn test_check_macro_input() {
        assert_eq!(
            Rust197Features::check_macro_input(Some("ident"), 2),
            vec!["ident", "ident"]
        );
        assert!(Rust197Features::check_macro_input(Some(""), 2).is_empty());
        assert!(Rust197Features::check_macro_input(None, 2).is_empty());
    }
}
