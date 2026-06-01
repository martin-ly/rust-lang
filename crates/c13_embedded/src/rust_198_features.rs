//! Rust 1.98 Nightly 前瞻 —— 嵌入式/系统编程实验特性
//! Rust 1.98 Nightly before —— /system feature
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.98 Nightly 嵌入式前瞻
/// - `core::intrinsics::breakpoint` — 软件断点（调试器 hook）
/// - `#[rustc_align(N)]` — 函数级别对齐控制
/// - `#[rustc_align(N)]` — function level to
/// **⚠️ 需要 nightly Rust + `#![feature(core_intrinsics, fn_align)]`**
pub struct Rust198EmbeddedFeatures;

impl Rust198EmbeddedFeatures {
    /// 触发调试断点
    /// point
    /// 当程序在调试器下运行时，这会暂停执行并允许检查状态。
    /// when program in under runtime ，and allow state 。
    /// when program in under runtime ，and state 。
    /// 在没有调试器的环境中，断点指令可能导致信号/异常。
    /// in environment in ，point may /。
    /// 仅应在调试场景或已配置异常处理器的嵌入式系统中使用。
    /// in scenario or configuration system in 。
    /// in scenario or system in 。
    #[inline(never)]
    pub unsafe fn trigger_debug_breakpoint() {
        core::intrinsics::breakpoint();
    }

    /// 返回一个具有指定函数对齐的函数指针
    /// has function to function pointer
    /// 当前 nightly 使用 `#[rustc_align(...)]`（非 `#[repr(align(...))]`）。
    /// whenbefore nightly Use `#[rustc_align(...)]`（非 `#[repr(align(...))]`）。
    #[rustc_align(64)]
    pub fn cache_line_aligned_function() -> i32 {
        42
    }

    #[rustc_align(16)]
    pub fn simd_aligned_entry() -> i32 {
        -559038737i32 // 0xDEAD_BEEF as i32
    }

    /// 检查当前平台是否为调试构建
    /// when before platform as
    pub fn is_debug_build() -> bool {
        cfg!(debug_assertions)
    }

    /// 在调试构建中触发断点，release 构建中跳过
    /// in in point ，release in
    pub fn debug_break_if_debug() {
        if cfg!(debug_assertions) {
            // SAFETY: 仅在 debug 构建中执行，通常有调试器 attached 或可被忽略
            unsafe { Rust198EmbeddedFeatures::trigger_debug_breakpoint() };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cache_line_aligned_function() {
        // 验证函数可调用（对齐属性不影响返回值）
        assert_eq!(Rust198EmbeddedFeatures::cache_line_aligned_function(), 42);
    }

    #[test]
    fn test_simd_aligned_entry() {
        assert_eq!(Rust198EmbeddedFeatures::simd_aligned_entry(), -559038737i32);
    }

    #[test]
    fn test_is_debug_build() {
        // 该测试在不同构建模式下结果不同，但不应 panic
        let _ = Rust198EmbeddedFeatures::is_debug_build();
    }

    #[test]
    fn test_debug_break_if_debug_no_panic() {
        // 验证 is_debug_build 返回值一致性
        // 注意: 不直接调用 debug_break_if_debug，因为 breakpoint() 会导致调试中断
        assert_eq!(
            Rust198EmbeddedFeatures::is_debug_build(),
            cfg!(debug_assertions)
        );
    }
}
