//! Rust 1.97 特性跟踪模块 —— 宏系统
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 特性演示
///
/// 展示 `std::iter::repeat_n` 和 `Vec::pop_if` 在宏系统中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `repeat_n` 生成重复的宏令牌占位符
    pub fn repeat_tokens(token: &str, count: usize) -> Vec<String> {
        std::iter::repeat_n(token.to_string(), count).collect()
    }

    /// 使用 `Vec::pop_if` 条件性移除最后一个宏参数
    pub fn pop_if_variadic(params: &mut Vec<String>) -> Option<String> {
        params.pop_if(|p| p.starts_with("..."))
    }

    /// 组合两者构建宏参数列表
    pub fn build_macro_params(base: &str, repeat_count: usize) -> (Vec<String>, Option<String>) {
        let mut params: Vec<String> = std::iter::repeat_n(base.to_string(), repeat_count).collect();
        params.push("...rest".to_string());
        let variadic = params.pop_if(|p| p.starts_with("..."));
        (params, variadic)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_repeat_tokens() {
        assert_eq!(
            Rust197Features::repeat_tokens("$ident", 3),
            vec!["$ident", "$ident", "$ident"]
        );
        assert!(Rust197Features::repeat_tokens("$ident", 0).is_empty());
    }

    #[test]
    fn test_pop_if_variadic() {
        let mut v = vec!["a".to_string(), "...rest".to_string()];
        assert_eq!(
            Rust197Features::pop_if_variadic(&mut v),
            Some("...rest".to_string())
        );
        assert_eq!(v, vec!["a"]);

        let mut v2 = vec!["a".to_string()];
        assert_eq!(Rust197Features::pop_if_variadic(&mut v2), None);
    }

    #[test]
    fn test_build_macro_params() {
        let (params, variadic) = Rust197Features::build_macro_params("$x", 2);
        assert_eq!(params, vec!["$x", "$x"]);
        assert_eq!(variadic, Some("...rest".to_string()));
    }
}
