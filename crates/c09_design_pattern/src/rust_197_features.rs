//! Rust 1.97 特性跟踪模块 —— 设计模式
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 特性演示
///
/// 展示 `Option::is_none_or` 和 `Result::is_ok_and` 在设计模式中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `Option::is_none_or` 实现空对象模式验证
    pub fn is_valid_or_empty(opt: Option<i32>, min: i32) -> bool {
        opt.is_none_or(|v| v >= min)
    }

    /// 使用 `Result::is_ok_and` 实现策略模式结果验证
    pub fn strategy_succeeded<T: PartialEq>(result: Result<T, &'static str>, expected: T) -> bool {
        result.is_ok_and(|v| v == expected)
    }

    /// 组合两者构建守卫条件
    pub fn guard_condition(
        maybe_result: Option<Result<i32, &'static str>>,
        threshold: i32,
    ) -> bool {
        maybe_result.is_none_or(|res| res.is_ok_and(|v| v >= threshold))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_valid_or_empty() {
        assert!(Rust197Features::is_valid_or_empty(None, 10));
        assert!(Rust197Features::is_valid_or_empty(Some(10), 10));
        assert!(!Rust197Features::is_valid_or_empty(Some(5), 10));
    }

    #[test]
    fn test_strategy_succeeded() {
        assert!(Rust197Features::strategy_succeeded(
            Ok("done".to_string()),
            "done".to_string()
        ));
        assert!(!Rust197Features::strategy_succeeded(
            Ok("fail".to_string()),
            "done".to_string()
        ));
        assert!(!Rust197Features::strategy_succeeded(
            Err("error"),
            "done".to_string()
        ));
    }

    #[test]
    fn test_guard_condition() {
        assert!(Rust197Features::guard_condition(None, 10));
        assert!(Rust197Features::guard_condition(Some(Ok(15)), 10));
        assert!(!Rust197Features::guard_condition(Some(Ok(5)), 10));
        assert!(!Rust197Features::guard_condition(Some(Err("fail")), 10));
    }
}
