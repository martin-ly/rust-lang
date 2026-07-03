//! Rust 1.96 特性模块 —— 过程宏场景
//! **当前稳定 patch**: Rust 1.96.1（基于 Rust 1.96.0 特性集）
//! Rust 1.96 feature module —— scenario
//! - `assert_matches!` 用于过程宏诊断测试
//! - `assert_matches!`
//! - `never type` 元组 coercion 用于错误路径

#![allow(clippy::incompatible_msrv, dead_code, unreachable_code)]

use std::assert_matches;
use std::sync::LazyLock;

// ============================================================================
// Rust 1.96.0: assert_matches! 用于过程宏诊断测试
// ============================================================================

/// 过程宏诊断结果的枚举表示
/// result enum represent
#[derive(Debug, Clone, PartialEq)]
pub enum ProcMacroDiagnostic {
    /// 解析成功
    ParseOk,
    /// 语法错误
    /// syntax
    SyntaxError {
        /// 错误描述
        /// describe
        /// 错误describe
        description: &'static str,
        /// 错误位置
        /// position
        /// 错误position
        offset: usize,
    },
    /// 不支持的语法结构
    /// syntax structure
    /// structure
    Unsupported {
        /// 结构名称
        /// structure
        construct: &'static str,
    },
    /// 编译通过，无诊断信息
    /// ，
    Clean,
}

/// 过程宏诊断断言工具
/// tool
pub struct ProcMacroDiagnosticAssertions;

impl ProcMacroDiagnosticAssertions {
    /// 断言诊断为解析成功
    /// as
    pub fn assert_parse_ok(diag: &ProcMacroDiagnostic) {
        assert_matches!(diag, ProcMacroDiagnostic::ParseOk);
    }

    /// 断言诊断为指定类型的语法错误
    /// as type syntax
    /// as type
    pub fn assert_syntax_error_at(diag: &ProcMacroDiagnostic, expected_offset: usize) {
        assert_matches!(
            diag,
            ProcMacroDiagnostic::SyntaxError { offset, .. } if *offset == expected_offset
        );
    }

    /// 断言诊断为不支持的结构
    /// as structure
    /// 断言诊断as不Supportsstructure
    pub fn assert_unsupported(diag: &ProcMacroDiagnostic, name: &str) {
        assert_matches!(
            diag,
            ProcMacroDiagnostic::Unsupported { construct } if *construct == name
        );
    }

    /// 断言诊断完全干净
    pub fn assert_clean(diag: &ProcMacroDiagnostic) {
        assert_matches!(diag, ProcMacroDiagnostic::Clean);
    }
}

// ============================================================================
// Rust 1.96: From<T> for LazyLock 用于过程宏元数据缓存
// ============================================================================

pub struct MacroMetadataCache {
    /// 支持的属性列表（立即初始化，无需闭包）
    /// attribute （，）
    supported_attrs: LazyLock<Vec<&'static str>>,
    /// 版本信息（立即初始化）
    /// this （）
    version_info: LazyLock<String>,
}

impl MacroMetadataCache {
    /// 创建新的元数据缓存
    /// data cache
    pub fn new() -> Self {
        Self {
            supported_attrs: LazyLock::from(vec!["derive", "inline", "test", "cfg", "allow"]),
            version_info: LazyLock::from("1.96.1".to_string()),
        }
    }

    /// 检查是否支持指定属性
    /// attribute
    pub fn is_attr_supported(&self, attr: &str) -> bool {
        self.supported_attrs.contains(&attr)
    }

    /// 获取版本信息
    /// this
    pub fn version(&self) -> &str {
        &self.version_info
    }

    /// 获取支持属性数量
    /// attribute quantity
    pub fn attr_count(&self) -> usize {
        self.supported_attrs.len()
    }
}

impl Default for MacroMetadataCache {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Rust 1.96: never type 元组 coercion 用于错误路径
// ============================================================================

/// 模拟过程宏展开中的错误结果元组
/// in result
/// in错误路径on，`panic!()` Return `!` type，可自动 coercing as
/// 元组中的任意类型，从而统一返回类型。
/// in type ，thereby type 。
pub fn error_tuple_with_never() -> (usize, &'static str, u32) {
    if false {
        // 正常路径永远不会执行，但类型检查通过
        return (0, "ok", 0);
    }
    // panic!() 返回 !，在元组上下文中自动 coercion 为 (usize, &'static str, u32)
    (0, panic!("proc macro expansion failed"), 0)
}

/// 另一个错误路径示例：使用 unreachable!()
/// example ： unreachable!()
/// 另一个错误路径Example of：Use unreachable!()
pub fn unreachable_tuple_with_never() -> (bool, u64) {
    if false {
        return (true, 42);
    }
    // unreachable!() 返回 !， coercion 为 (bool, u64)
    (false, unreachable!("invalid proc macro state"))
}

/// 演示函数
/// demonstration function
pub fn demonstrate_rust_196_features() {
    println!("\n=== Rust 1.96 过程宏特性演示 ===");

    // LazyLock::from for metadata cache
    let cache = MacroMetadataCache::new();
    println!("Version: {}", cache.version());
    println!("Supported attrs: {}", cache.attr_count());

    // assert_matches! for diagnostic testing
    let diag = ProcMacroDiagnostic::Clean;
    ProcMacroDiagnosticAssertions::assert_clean(&diag);
}

#[cfg(test)]
mod tests {
    use super::*;

    // assert_matches! 测试
    #[test]
    fn test_assert_parse_ok() {
        let diag = ProcMacroDiagnostic::ParseOk;
        ProcMacroDiagnosticAssertions::assert_parse_ok(&diag);
    }

    #[test]
    #[should_panic]
    fn test_assert_parse_ok_fails_on_error() {
        let diag = ProcMacroDiagnostic::SyntaxError {
            description: "missing semicolon",
            offset: 10,
        };
        ProcMacroDiagnosticAssertions::assert_parse_ok(&diag);
    }

    #[test]
    fn test_assert_syntax_error_at() {
        let diag = ProcMacroDiagnostic::SyntaxError {
            description: "unexpected token",
            offset: 42,
        };
        ProcMacroDiagnosticAssertions::assert_syntax_error_at(&diag, 42);
    }

    #[test]
    fn test_assert_unsupported() {
        let diag = ProcMacroDiagnostic::Unsupported {
            construct: "async_trait",
        };
        ProcMacroDiagnosticAssertions::assert_unsupported(&diag, "async_trait");
    }

    #[test]
    fn test_assert_clean() {
        let diag = ProcMacroDiagnostic::Clean;
        ProcMacroDiagnosticAssertions::assert_clean(&diag);
    }

    // LazyLock::from 测试
    #[test]
    fn test_metadata_cache_attrs() {
        let cache = MacroMetadataCache::new();
        assert!(cache.is_attr_supported("derive"));
        assert!(cache.is_attr_supported("test"));
        assert!(!cache.is_attr_supported("unknown"));
    }

    #[test]
    fn test_metadata_cache_version() {
        let cache = MacroMetadataCache::new();
        assert_eq!(cache.version(), "1.96.1");
    }

    #[test]
    fn test_metadata_cache_attr_count() {
        let cache = MacroMetadataCache::new();
        assert_eq!(cache.attr_count(), 5);
    }

    // never type 元组 coercion 测试
    // 注意：这些函数在 panic/unreachable 路径上永远不会正常返回，
    // 但类型检查证明 coercion 是有效的。
    #[test]
    #[should_panic(expected = "proc macro expansion failed")]
    fn test_error_tuple_with_never() {
        error_tuple_with_never();
    }

    #[test]
    #[should_panic(expected = "invalid proc macro state")]
    fn test_unreachable_tuple_with_never() {
        unreachable_tuple_with_never();
    }
}
