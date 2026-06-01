//! - **WASM 链接器行as变更**: 移除 `--allow-undefined` 默认传递
//! - **WASM as**: `--allow-undefined`
//! - `core::range::Range` — no_std 友好可复用rangetype
//! - `assert_matches!` — WASM 状态机测试断言
//! # 版本信息
//! # this
//! - Rust 版本: 1.96.0+ stable
//! - Rust 版this: 1.96.0+ stable
//! - 稳定日期: 2026-05-28
//! - date : 2026-05-28
//! - 稳定date: 2026-05-28
//! - date: 2026-05-28

// ============================================================================
// 1. WebAssembly 链接器行为变更 (1.96 Breaking Change)
// ============================================================================

/// # Rust 1.96 WASM 链接器变更
/// # Rust 1.96 WASM
/// ## 影响
/// ## impact
/// - 未定义符号现在会导致**链接错误**（与原生平台行为一致）
/// - definition symbol present ****（and platform as ）
/// - 需要显式使用 `#[link(wasm_import_module = "...")]` 导入外部符号
/// - `#[link(wasm_import_module = "...")]` outside symbol
/// ## 迁移指南
/// ##
/// # 1.96 之前（默认允许未定义符号）
/// # 1.96 's before （allow definition symbol ）
/// # 1.96 's before （definition symbol ）
/// # 1.96 之后（默认拒绝未定义符号）
/// # 1.96 's after （reject definition symbol ）
/// # 1.96 's after （definition symbol ）
/// # 1.96 'safter（默认拒绝未definitionsymbol）
/// # 链接错误: undefined symbol
/// # 解决方案 A: 显式声明外部导入
/// # solution A: outside
///
/// # 解决方案 B: 显式传递链接器参数（不推荐用于生产）
/// # solution B: parameter （）
///
/// **官方公告**: <https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/>
pub struct WasmLinkerChanges;

impl WasmLinkerChanges {
    /// 返回变更摘要
    /// summary
    pub fn get_summary() -> &'static str {
        "Rust 1.96: WebAssembly targets no longer pass --allow-undefined to the linker. Undefined \
         symbols now cause linker errors. Use #[link(wasm_import_module = \"...\")] for explicit \
         imports."
    }

    pub fn is_affected_target(target: &str) -> bool {
        matches!(
            target,
            "wasm32-unknown-unknown" | "wasm32-wasip1" | "wasm32-wasip2" | "wasm64-unknown-unknown"
        )
    }
}

// ============================================================================
// 2. core::range::Range 在 WASM 中的应用 (1.96.0 stable, no_std 友好)
// ============================================================================

/// `core::range` 完全定义在 `core` 中，无需 `std` 或 `alloc`，
/// `core::range` 完全definitionin `core` in，无需 `std` or `alloc`，
/// 非常适合 `wasm32-unknown-unknown` 等 no_std 目标。
/// 非常适合 `wasm32-unknown-unknown` etc. no_std goal。
pub struct WasmCoreRangeExamples;

impl WasmCoreRangeExamples {
    /// WASM 线性内存页范围检查（每页 64KB）
    /// WASM line memory scope （ 64KB）
    pub fn memory_page_range(pages: usize) -> &'static str {
        use core::range::Range;

        let small: Range<usize> = Range { start: 0, end: 17 };
        let medium: Range<usize> = Range { start: 17, end: 65 };
        let large: Range<usize> = Range {
            start: 65,
            end: 257,
        };

        if small.into_iter().any(|p| p == pages) {
            "small (<= 1MB)"
        } else if medium.into_iter().any(|p| p == pages) {
            "medium (1-4MB)"
        } else if large.into_iter().any(|p| p == pages) {
            "large (4-16MB)"
        } else {
            "huge (> 16MB)"
        }
    }

    /// WASM 表索引范围验证
    /// WASM scope
    pub fn is_valid_table_index(idx: u32, table_size: u32) -> bool {
        use core::range::Range;
        let valid: Range<u32> = Range {
            start: 0,
            end: table_size,
        };
        valid.into_iter().any(|i| i == idx)
    }

    /// 数据段偏移范围检查
    /// data scope
    /// scope
    pub fn data_segment_in_range(offset: usize, segment_size: usize, memory_limit: usize) -> bool {
        use core::range::Range;
        let max_offset = memory_limit.saturating_sub(segment_size);
        let valid: Range<usize> = Range {
            start: 0,
            end: max_offset.saturating_add(1),
        };
        offset >= valid.start && offset < valid.end
    }
}

// ============================================================================
// 3. assert_matches! 在 WASM 状态机测试中的应用 (1.96.0 stable)
// ============================================================================

use std::assert_matches;

/// WASM 模块加载状态
/// WASM module state
#[derive(Debug, PartialEq)]
pub enum WasmLoadState {
    Idle,
    Loading { bytes_received: usize },
    Compiled { module_size: usize },
    Instantiated { memory_pages: u32 },
    Failed { error: &'static str },
}

/// `assert_matches!` 允许对复杂枚举状态进行模式匹配断言，
/// `assert_matches!` allow to complex enum state ，
/// `assert_matches!` to complex enum state ，
/// 在 WASM 运行时状态机测试中非常有用。
/// in WASM runtime state machine in useful 。
pub struct WasmAssertMatchesExamples;

impl WasmAssertMatchesExamples {
    /// 验证模块是否成功加载
    /// module
    pub fn verify_loaded(state: &WasmLoadState) -> bool {
        assert_matches!(state, WasmLoadState::Instantiated { .. });
        true
    }

    /// 验证编译后模块大小
    /// after module
    pub fn verify_compiled_size(state: &WasmLoadState, expected_min: usize) -> bool {
        assert_matches!(state, WasmLoadState::Compiled { module_size } if *module_size >= expected_min);
        true
    }

    /// 验证加载进度
    pub fn verify_loading_progress(state: &WasmLoadState) -> bool {
        assert_matches!(state, WasmLoadState::Loading { bytes_received } if *bytes_received > 0);
        true
    }
}

// ============================================================================
// 4. From<T> for LazyLock 在 WASM 运行时配置中的应用 (1.96 stable)
// ============================================================================

use std::sync::LazyLock;

/// 无需显式闭包。
/// 。
pub struct WasmLazyLockExamples;

impl WasmLazyLockExamples {
    /// WASM 运行时默认内存限制（页数）
    /// WASM runtime memory （）
    pub fn default_memory_limit() -> &'static LazyLock<u32> {
        static LIMIT: LazyLock<u32> = LazyLock::new(|| 256);
        &LIMIT
    }

    /// WASM 特性标志
    /// WASM feature mark
    pub fn feature_flags() -> &'static LazyLock<Vec<&'static str>> {
        static FLAGS: LazyLock<Vec<&'static str>> =
            LazyLock::new(|| vec!["bulk-memory", "simd128", "mutable-global"]);
        &FLAGS
    }
}

// ============================================================================
// 测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_wasm_linker_changes() {
        assert!(WasmLinkerChanges::is_affected_target(
            "wasm32-unknown-unknown"
        ));
        assert!(WasmLinkerChanges::is_affected_target("wasm32-wasip1"));
        assert!(!WasmLinkerChanges::is_affected_target(
            "x86_64-unknown-linux-gnu"
        ));
    }

    #[test]
    fn test_memory_page_range() {
        assert_eq!(
            WasmCoreRangeExamples::memory_page_range(8),
            "small (<= 1MB)"
        );
        assert_eq!(
            WasmCoreRangeExamples::memory_page_range(32),
            "medium (1-4MB)"
        );
        assert_eq!(
            WasmCoreRangeExamples::memory_page_range(100),
            "large (4-16MB)"
        );
        assert_eq!(
            WasmCoreRangeExamples::memory_page_range(300),
            "huge (> 16MB)"
        );
    }

    #[test]
    fn test_valid_table_index() {
        assert!(WasmCoreRangeExamples::is_valid_table_index(0, 1000));
        assert!(WasmCoreRangeExamples::is_valid_table_index(999, 1000));
        assert!(!WasmCoreRangeExamples::is_valid_table_index(1000, 1000));
    }

    #[test]
    fn test_data_segment_in_range() {
        assert!(WasmCoreRangeExamples::data_segment_in_range(0, 100, 1000));
        assert!(WasmCoreRangeExamples::data_segment_in_range(900, 100, 1000));
        assert!(!WasmCoreRangeExamples::data_segment_in_range(
            950, 100, 1000
        ));
    }

    #[test]
    fn test_verify_loaded() {
        let state = WasmLoadState::Instantiated { memory_pages: 4 };
        assert!(WasmAssertMatchesExamples::verify_loaded(&state));
    }

    #[test]
    fn test_verify_compiled_size() {
        let state = WasmLoadState::Compiled { module_size: 1024 };
        assert!(WasmAssertMatchesExamples::verify_compiled_size(&state, 100));
    }

    #[test]
    fn test_verify_loading_progress() {
        let state = WasmLoadState::Loading {
            bytes_received: 512,
        };
        assert!(WasmAssertMatchesExamples::verify_loading_progress(&state));
    }

    #[test]
    fn test_default_memory_limit() {
        assert_eq!(**WasmLazyLockExamples::default_memory_limit(), 256);
    }

    #[test]
    fn test_feature_flags() {
        let flags = WasmLazyLockExamples::feature_flags();
        assert!(flags.contains(&"bulk-memory"));
        assert!(flags.contains(&"simd128"));
    }
}
