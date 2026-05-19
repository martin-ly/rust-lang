//! Rust 1.93.0 宏系统 特性模块
#![allow(clippy::incompatible_msrv)]

use std::fmt;

/// 使用 `fmt::from_fn` 创建宏展开追踪格式化器
pub fn macro_trace_formatter(name: &str, line: u32) -> impl fmt::Display + use<'_> {
    fmt::from_fn(move |f: &mut fmt::Formatter<'_>| write!(f, "[macro:{}@L{}]", name, line))
}

/// 使用 `fmt::from_fn` 构建条件格式化输出
pub fn conditional_formatter(show_debug: bool, value: i32) -> impl fmt::Display {
    fmt::from_fn(move |f: &mut fmt::Formatter<'_>| {
        if show_debug {
            write!(f, "DEBUG: value={}", value)
        } else {
            write!(f, "{}", value)
        }
    })
}

/// 组合多个 `fmt::from_fn` 创建结构化日志输出
pub fn structured_log_formatter(level: &str, msg: &str) -> impl fmt::Display {
    let level = level.to_string();
    let msg = msg.to_string();
    fmt::from_fn(move |f: &mut fmt::Formatter<'_>| write!(f, "[{}] {}", level.to_uppercase(), msg))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_macro_trace_formatter() {
        let out = macro_trace_formatter("my_macro", 42);
        assert_eq!(format!("{}", out), "[macro:my_macro@L42]");
    }

    #[test]
    fn test_conditional_formatter() {
        let debug = conditional_formatter(true, 99);
        let normal = conditional_formatter(false, 99);
        assert_eq!(format!("{}", debug), "DEBUG: value=99");
        assert_eq!(format!("{}", normal), "99");
    }

    #[test]
    fn test_structured_log_formatter() {
        let log = structured_log_formatter("info", "compilation complete");
        assert_eq!(format!("{}", log), "[INFO] compilation complete");
    }
}
