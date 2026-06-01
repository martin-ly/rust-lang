//! # Rust 1.96.0 特性 — 进程管理与系统编程模块
//! # Rust 1.96.0 feature — process and system module
//!
//! 本模块展示 Rust 1.96.0 中与进程管理、系统编程、懒加载相关的稳定特性：
//! This module demonstrates Rust 1.96.0 in and process 、system 、feature ：
//! - `From<T> for LazyCell<T, F>` / `LazyLock<T, F>` — 值直接构造懒加载容器
//! - `assert_matches!` / `debug_assert_matches!` — 模式匹配断言
//! - `core::range::Range` — 进程 ID 范围、资源限制范围的可复用迭代
//! - `core::range::Range` — process ID scope 、scope
//!
//! # 版本信息
//! # this
//! - Rust 版本: 1.96.0+ stable
//! - 稳定日期: 2026-05-28
//! - date : 2026-05-28
//! - Edition: 2024

use std::assert_matches;
use std::cell::LazyCell;
use std::sync::LazyLock;

// ============================================================================
// 1. From<T> for LazyCell<T, F> / LazyLock<T, F> (1.96 stable)
// ============================================================================

/// # 懒加载容器的 `From` 实现
/// # `From`
///
/// Rust 1.96 稳定了从值直接构造 `LazyCell` 和 `LazyLock` 的 `From` 实现，
/// Rust 1.96 from `LazyCell` and `LazyLock` `From` ，
/// 无需显式提供初始化闭包。这在进程级配置和全局状态管理中特别有用。
/// 。in process and global state in useful 。
///
/// ## 进程管理应用场景
/// ## process application scenario
/// - 进程配置的单例懒加载
/// - process singleton
/// - 系统资源信息的延迟初始化
/// - system
/// - 环境变量的缓存封装
/// - environment variable
pub struct LazyFromExamples;

impl LazyFromExamples {
    /// 从值直接构造 LazyLock（无需闭包）
    /// from LazyLock（）
    pub fn process_config_from_value() -> LazyLock<String> {
        LazyLock::from("production".to_string())
    }

    /// 从值直接构造 LazyCell
    /// from LazyCell
    pub fn thread_local_config_from_value() -> LazyCell<Vec<String>> {
        LazyCell::from(vec!["--verbose".to_string(), "--secure".to_string()])
    }

    /// 进程 PID 表的懒加载初始化
    /// process PID
    pub fn pid_table() -> &'static LazyLock<Vec<u32>> {
        static TABLE: LazyLock<Vec<u32>> = LazyLock::new(|| vec![1, 2, 4, 8, 16]);
        &TABLE
    }
}

// ============================================================================
// 2. assert_matches! / debug_assert_matches! (1.96.0 stable)
// ============================================================================

/// # 模式匹配断言在进程管理中的应用
/// # in process in application
///
/// `assert_matches!` 允许对 `Result`、`Option` 和自定义枚举进行模式匹配断言，
/// `assert_matches!` to `Result`、`Option` and definition enum ，
/// 在进程状态验证和错误处理测试中非常有用。
/// in process state and error handling in useful 。
pub struct ProcessAssertMatchesExamples;

impl ProcessAssertMatchesExamples {
    /// 验证进程退出状态
    /// process state
    pub fn verify_exit_status(status: Result<i32, &'static str>) -> bool {
        assert_matches!(status, Ok(code) if code >= 0);
        true
    }

    /// 验证进程信号
    /// process
    pub fn verify_signal(signal: Option<i32>) -> bool {
        assert_matches!(signal, Some(sig) if sig > 0 && sig < 64);
        true
    }
}

// ============================================================================
// 3. core::range::Range 在进程管理中的应用
// ============================================================================

/// # `core::range::Range` 在进程资源管理中的应用
/// # `core::range::Range` in process in application
///
/// Rust 1.96.0 的 `core::range::Range` 实现 `Copy`，可多次迭代，
/// 适合表示进程 ID 范围、内存地址范围、资源限制等。
/// represent process ID scope 、memory scope 、etc. 。
pub struct ProcessRangeExamples;

impl ProcessRangeExamples {
    /// 验证 PID 是否在有效范围内
    /// PID in effective scope inside
    pub fn is_valid_pid(pid: u32) -> bool {
        use core::range::Range;
        let valid_range: Range<u32> = Range {
            start: 1,
            end: 32768,
        };
        valid_range.into_iter().any(|p| p == pid)
    }

    /// 进程优先级范围分类
    /// process scope classification
    pub fn priority_category(nice_level: i8) -> &'static str {
        use core::range::RangeInclusive;
        match nice_level {
            n if (RangeInclusive {
                start: -20,
                last: -10,
            })
            .into_iter()
            .any(|x| x == n) =>
            {
                "high"
            }
            n if (RangeInclusive { start: -9, last: 0 })
                .into_iter()
                .any(|x| x == n) =>
            {
                "normal"
            }
            n if (RangeInclusive { start: 1, last: 10 })
                .into_iter()
                .any(|x| x == n) =>
            {
                "low"
            }
            n if (RangeInclusive {
                start: 11,
                last: 19,
            })
            .into_iter()
            .any(|x| x == n) =>
            {
                "idle"
            }
            _ => "invalid",
        }
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lazy_lock_from() {
        let lazy: LazyLock<i32> = LazyLock::from(100);
        assert_eq!(*lazy, 100);
    }

    #[test]
    fn test_lazy_cell_from() {
        let cell: LazyCell<String> = LazyCell::from("test".to_string());
        assert_eq!(&**cell, "test");
    }

    #[test]
    fn test_process_config_from_value() {
        let config = LazyFromExamples::process_config_from_value();
        assert_eq!(*config, "production");
    }

    #[test]
    fn test_pid_table() {
        let table = LazyFromExamples::pid_table();
        assert_eq!(table.len(), 5);
        assert_eq!(table[0], 1);
    }

    #[test]
    fn test_verify_exit_status() {
        assert!(ProcessAssertMatchesExamples::verify_exit_status(Ok(0)));
        assert!(ProcessAssertMatchesExamples::verify_exit_status(Ok(42)));
    }

    #[test]
    fn test_priority_category() {
        assert_eq!(ProcessRangeExamples::priority_category(-15), "high");
        assert_eq!(ProcessRangeExamples::priority_category(0), "normal");
        assert_eq!(ProcessRangeExamples::priority_category(5), "low");
        assert_eq!(ProcessRangeExamples::priority_category(15), "idle");
    }

    #[test]
    fn test_is_valid_pid() {
        assert!(ProcessRangeExamples::is_valid_pid(1));
        assert!(ProcessRangeExamples::is_valid_pid(1000));
        assert!(!ProcessRangeExamples::is_valid_pid(0));
        assert!(!ProcessRangeExamples::is_valid_pid(50000));
    }
}
