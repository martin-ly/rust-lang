//! Rust 1.96 特性模块 —— 宏系统场景
//!
//! 本模块展示 Rust 1.96 稳定新特性在宏系统学习中的应用：
//! - `expr` metavariable 传递给 `cfg`
//! - `assert_matches!` 用于宏展开结果测试
//! - `core::range` 用于 token span 范围表示
//! - `ManuallyDrop` 用于宏卫生标记类型

#![allow(clippy::incompatible_msrv)]

use std::assert_matches;
use std::mem::ManuallyDrop;

// ============================================================================
// Rust 1.96: expr metavariable to cfg（保留并维护）
// ============================================================================

/// 在 Rust 1.96 之前，声明式宏中的 `expr` fragment specifier
/// 不能用于 `#[cfg(...)]` 属性参数。1.96 放宽了这一限制，
/// 允许通过宏参数动态生成条件编译属性。
macro_rules! cfg_conditional {
    ($cond:expr, $item:item) => {
        #[cfg($cond)]
        $item
    };
}

// 使用宏生成平台相关的辅助函数
cfg_conditional!(
    target_os = "windows",
    fn _platform_id() -> &'static str {
        "windows"
    }
);
cfg_conditional!(
    not(target_os = "windows"),
    fn _platform_id() -> &'static str {
        "unix-like"
    }
);

/// 条件编译宏的实用包装
pub struct ExprMetavariableToCfgExamples;

impl ExprMetavariableToCfgExamples {
    /// 返回当前平台标识（通过条件编译宏生成）
    pub fn platform_hint() -> &'static str {
        _platform_id()
    }

    /// 演示：使用宏根据 cfg 条件选择不同的实现
    pub fn cfg_select_hint() -> &'static str {
        _platform_id()
    }
}

// ============================================================================
// Rust 1.96.0: assert_matches! 用于宏展开结果测试
// ============================================================================

/// 宏展开结果的枚举表示
#[derive(Debug, Clone, PartialEq)]
pub enum ExpansionResult {
    /// 展开成功
    Success {
        /// 生成的 token 数量
        tokens: usize,
        /// span 数量
        span_count: usize,
    },
    /// 展开出错
    Error {
        /// 错误信息
        message: &'static str,
        /// 所在行号
        line: u32,
    },
    /// 空展开
    Empty,
}

/// 宏展开结果断言工具
pub struct MacroExpansionAssertions;

impl MacroExpansionAssertions {
    /// 检查宏展开是否成功
    pub fn assert_success(result: &ExpansionResult) {
        assert_matches!(result, ExpansionResult::Success { .. });
    }

    /// 检查宏展开错误信息
    pub fn assert_error_with_message(result: &ExpansionResult, expected: &str) {
        assert_matches!(
            result,
            ExpansionResult::Error { message, .. } if *message == expected
        );
    }

    /// 检查宏展开是否为空
    pub fn assert_empty(result: &ExpansionResult) {
        assert_matches!(result, ExpansionResult::Empty);
    }
}

// ============================================================================
// Rust 1.96.0: core::range 用于 token span 范围
// ============================================================================

/// 使用 `core::range` 表示宏 token 的 span 范围
pub struct TokenSpanRange {
    /// 左闭右开范围
    pub range: core::range::Range<usize>,
    /// 闭区间范围
    pub range_inclusive: core::range::RangeInclusive<usize>,
}

impl TokenSpanRange {
    /// 创建新的 token span 范围
    pub fn new(start: usize, end: usize) -> Self {
        Self {
            range: core::range::Range { start, end },
            range_inclusive: core::range::RangeInclusive { start, last: end },
        }
    }

    /// 检查位置是否在范围内
    pub fn contains(&self, pos: usize) -> bool {
        self.range.start <= pos && pos < self.range.end
    }

    /// 获取范围长度
    pub fn len(&self) -> usize {
        self.range.end - self.range.start
    }

    /// 是否为空范围
    pub fn is_empty(&self) -> bool {
        self.range.start == self.range.end
    }
}

// ============================================================================
// Rust 1.96: ManuallyDrop 用于宏卫生标记类型
// ============================================================================

/// 宏卫生标记：使用 ManuallyDrop 包装标识符，避免在分析阶段被自动释放
pub struct HygieneMarker<T> {
    inner: ManuallyDrop<T>,
}

impl<T> HygieneMarker<T> {
    /// 创建新的卫生标记
    pub fn new(value: T) -> Self {
        Self {
            inner: ManuallyDrop::new(value),
        }
    }

    /// 获取内部值的引用
    pub fn get(&self) -> &T {
        &self.inner
    }

    /// 获取内部值（消费 self，不调用 drop）
    pub fn into_inner(self) -> T {
        ManuallyDrop::into_inner(self.inner)
    }
}

// ============================================================================
// 演示函数
// ============================================================================

/// 演示 Rust 1.96 新特性
pub fn demonstrate_rust_196_features() {
    println!("\n=== Rust 1.96 宏系统特性演示 ===");

    // core::range for token spans
    let span = TokenSpanRange::new(10, 25);
    println!(
        "Token span: {}..{} (len={})",
        span.range.start,
        span.range.end,
        span.len()
    );

    // assert_matches!
    let result = ExpansionResult::Success {
        tokens: 42,
        span_count: 5,
    };
    MacroExpansionAssertions::assert_success(&result);

    // ManuallyDrop hygiene marker
    let marker = HygieneMarker::new("macro_ident");
    println!("Hygiene marker: {}", marker.get());
}

/// 获取特性信息
pub fn get_rust_196_macro_info() -> String {
    "Rust 1.96.0 宏系统特性:\n- expr metavariable to cfg\n- assert_matches! for macro expansion \
     testing\n- core::range for token span ranges\n- ManuallyDrop for macro hygiene markers"
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Rust 1.96: expr metavariable to cfg（保留测试）
    #[test]
    fn test_expr_metavariable_to_cfg_compiles() {
        let hint = ExprMetavariableToCfgExamples::platform_hint();
        assert!(!hint.is_empty());
        assert!(hint == "windows" || hint == "unix-like");
    }

    #[test]
    fn test_cfg_conditional_macro() {
        let result = ExprMetavariableToCfgExamples::cfg_select_hint();
        assert!(!result.is_empty());
    }

    // assert_matches! 测试
    #[test]
    fn test_assert_success() {
        let result = ExpansionResult::Success {
            tokens: 10,
            span_count: 2,
        };
        MacroExpansionAssertions::assert_success(&result);
    }

    #[test]
    #[should_panic]
    fn test_assert_success_panics_on_error() {
        let result = ExpansionResult::Error {
            message: "fail",
            line: 1,
        };
        MacroExpansionAssertions::assert_success(&result);
    }

    #[test]
    fn test_assert_error_with_message() {
        let result = ExpansionResult::Error {
            message: "expected",
            line: 5,
        };
        MacroExpansionAssertions::assert_error_with_message(&result, "expected");
    }

    #[test]
    fn test_assert_empty() {
        let result = ExpansionResult::Empty;
        MacroExpansionAssertions::assert_empty(&result);
    }

    // core::range 测试
    #[test]
    fn test_token_span_range_contains() {
        let span = TokenSpanRange::new(10, 20);
        assert!(span.contains(10));
        assert!(span.contains(15));
        assert!(!span.contains(20));
        assert!(!span.contains(25));
    }

    #[test]
    fn test_token_span_range_len() {
        let span = TokenSpanRange::new(5, 15);
        assert_eq!(span.len(), 10);
        assert!(!span.is_empty());
    }

    #[test]
    fn test_token_span_range_empty() {
        let span = TokenSpanRange::new(5, 5);
        assert_eq!(span.len(), 0);
        assert!(span.is_empty());
    }

    #[test]
    fn test_range_inclusive_fields() {
        let ri = core::range::RangeInclusive { start: 1, last: 5 };
        assert_eq!(ri.start, 1);
        assert_eq!(ri.last, 5);
    }

    // ManuallyDrop 测试
    #[test]
    fn test_hygiene_marker_new_and_get() {
        let marker = HygieneMarker::new(42);
        assert_eq!(*marker.get(), 42);
    }

    #[test]
    fn test_hygiene_marker_into_inner() {
        let marker = HygieneMarker::new(vec![1, 2, 3]);
        let inner = marker.into_inner();
        assert_eq!(inner, vec![1, 2, 3]);
    }

    #[test]
    fn test_get_rust_196_macro_info() {
        let info = get_rust_196_macro_info();
        assert!(!info.is_empty());
        assert!(info.contains("assert_matches!"));
        assert!(info.contains("core::range"));
    }
}
