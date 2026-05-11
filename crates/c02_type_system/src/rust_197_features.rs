//! Rust 1.97 特性跟踪模块 —— 类型系统
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 特性演示
///
/// 展示 `Option::is_none_or` 和 `Result::is_ok_and` 在类型系统中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `Option::is_none_or` 检查值是否为空或不满足条件
    pub fn check_optional_value(opt: Option<i32>, threshold: i32) -> bool {
        opt.is_none_or(|v| v > threshold)
    }

    /// 使用 `Result::is_ok_and` 验证结果是否成功且值有效
    pub fn validate_result<T: Ord>(result: Result<T, &'static str>, min: T) -> bool {
        result.is_ok_and(|v| v >= min)
    }

    /// 组合两种 API 进行类型级验证
    pub fn combined_validation(maybe_value: Option<Result<i32, &'static str>>) -> bool {
        maybe_value.is_none_or(|res| res.is_ok_and(|v| v > 0))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_check_optional_value() {
        assert!(Rust197Features::check_optional_value(None, 10));
        assert!(Rust197Features::check_optional_value(Some(15), 10));
        assert!(!Rust197Features::check_optional_value(Some(5), 10));
    }

    #[test]
    fn test_validate_result() {
        assert!(Rust197Features::validate_result(Ok(10), 5));
        assert!(Rust197Features::validate_result(Ok(5), 5));
        assert!(!Rust197Features::validate_result(Ok(3), 5));
        assert!(!Rust197Features::validate_result(Err("fail"), 5));
    }

    #[test]
    fn test_combined_validation() {
        assert!(Rust197Features::combined_validation(None));
        assert!(Rust197Features::combined_validation(Some(Ok(5))));
        assert!(!Rust197Features::combined_validation(Some(Ok(-1))));
        assert!(!Rust197Features::combined_validation(Some(Err("error"))));
    }
}
