//! # 练习 6: `if let` guards in match arms (Rust 1.95)
//!
//! **难度**: Medium  
//! **考点**: `if let` guards、match arm 条件守卫、与 `let chains` 的对比
//!
//! ## 背景
//!
//! Rust 1.95 稳定了 match arm 中的 `if let` guards，允许在模式匹配的守卫中
//! 直接使用 `if let` 绑定，而无需嵌套额外的 match 或 if let 表达式。
//!
//! 之前（Rust 2021）：
//! ```ignore
//! match value {
//!     Some(x) => {
//!         if let Ok(n) = x.parse::<i32>() {
//!             // ...
//!         }
//!     }
//!     _ => {}
//! }
//! ```
//!
//! 现在（Rust 1.95+）：
//! ```ignore
//! match value {
//!     Some(x) if let Ok(n) = x.parse::<i32>() => { /* ... */ }
//!     _ => {}
//! }
//! ```
//!
//! ## 要求
//!
//! - 使用 `if let` guard 简化嵌套模式匹配
//! - 对比 `if let` guard 与 `let chains` (`if let A = a && let B = b`) 的适用场景
//! - 在复杂枚举上应用 `if let` guard

/// 使用 `if let` guard 解析并分类消息
///
/// 输入是一个 `Option<String>`：
/// - 如果内容可以解析为整数，返回 `"number: {n}"`
/// - 如果以 `"cmd:"` 开头，返回 `"command: {rest}"`
/// - 其他非空字符串，返回 `"text: {s}"`
/// - `None` 返回 `"empty"`
pub fn classify_message(msg: Option<String>) -> String {
    match msg {
        // TODO: 使用 if let guard 匹配可解析为整数的内容
        // 使用 ref s 避免在 guard 中借用时与其他 arm 的所有权冲突
        Some(ref s) if let Ok(n) = s.parse::<i32>() => format!("number: {n}"),
        // TODO: 使用 if let guard 匹配以 "cmd:" 开头的字符串
        Some(ref s) if let Some(rest) = s.strip_prefix("cmd:") => format!("command: {rest}"),
        // TODO: 匹配其他非空字符串
        Some(s) => format!("text: {s}"),
        None => "empty".to_string(),
    }
}

/// 使用 `if let` guard 处理嵌套的 `Result<Option<T>, E>`
///
/// 规则：
/// - `Ok(Some(n))` 且 `n > 0` → `"positive: {n}"`
/// - `Ok(Some(n))` 且 `n <= 0` → `"non-positive: {n}"`
/// - `Ok(None)` → `"missing"`
/// - `Err(e)` → `"error: {e}"`
pub fn describe_nested_value(value: Result<Option<i32>, &'static str>) -> String {
    match value {
        // 使用 Ok(Some(n)) 直接匹配，然后在内部根据 n 的值分支
        Ok(Some(n)) => {
            if n > 0 {
                format!("positive: {n}")
            } else {
                format!("non-positive: {n}")
            }
        }
        // Ok(_) 覆盖 Ok(None) 和任何其他未被 guard 覆盖的 Ok 变体
        Ok(_) => "missing".to_string(),
        Err(e) => format!("error: {e}"),
    }
}

/// 对比：`if let` guard vs `let chains`
///
/// 以下两种写法在语义上等价：
///
/// ```ignore
/// // 写法 A: if let guard（在 match arm 中）
/// match x {
///     Some(s) if let Ok(n) = s.parse::<i32>() => { ... }
///     _ => {}
/// }
///
/// // 写法 B: let chains（在 if 条件中）
/// if let Some(s) = x && let Ok(n) = s.parse::<i32>() { ... }
/// ```
///
/// 本函数返回 `true`，表示两种写法确实等价（只是使用场景不同）。
pub fn if_let_guard_equivalent_to_let_chains() -> bool {
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_classify_message_number() {
        assert_eq!(classify_message(Some("42".to_string())), "number: 42");
        assert_eq!(classify_message(Some("-3".to_string())), "number: -3");
    }

    #[test]
    fn test_classify_message_command() {
        assert_eq!(
            classify_message(Some("cmd:reload".to_string())),
            "command: reload"
        );
        assert_eq!(classify_message(Some("cmd:".to_string())), "command: ");
    }

    #[test]
    fn test_classify_message_text() {
        assert_eq!(
            classify_message(Some("hello world".to_string())),
            "text: hello world"
        );
    }

    #[test]
    fn test_classify_message_empty() {
        assert_eq!(classify_message(None), "empty");
    }

    #[test]
    fn test_describe_nested_value() {
        assert_eq!(describe_nested_value(Ok(Some(5))), "positive: 5");
        assert_eq!(describe_nested_value(Ok(Some(0))), "non-positive: 0");
        assert_eq!(describe_nested_value(Ok(Some(-3))), "non-positive: -3");
        assert_eq!(describe_nested_value(Ok(None)), "missing");
        assert_eq!(describe_nested_value(Err("invalid")), "error: invalid");
    }

    #[test]
    fn test_equivalence() {
        assert!(if_let_guard_equivalent_to_let_chains());
    }

    #[test]
    fn test_if_let_guard_vs_let_chains() {
        let x: Option<String> = Some("42".to_string());

        // 写法 A: if let guard
        let result_a = match x {
            Some(ref s) if let Ok(n) = s.parse::<i32>() => format!("guard: {n}"),
            _ => "other".to_string(),
        };

        // 写法 B: let chains
        let result_b = if let Some(ref s) = x
            && let Ok(n) = s.parse::<i32>()
        {
            format!("chain: {n}")
        } else {
            "other".to_string()
        };

        assert_eq!(result_a, "guard: 42");
        assert_eq!(result_b, "chain: 42");
    }
}
