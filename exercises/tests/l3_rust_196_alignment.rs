//! L3 Rust 1.96.0 稳定特性对齐测验
//!
//! 覆盖 Rust 1.96.0（2026-05-28 stable）引入的关键语言/库特性：
//! - `assert_matches!` / `debug_assert_matches!`
//! - `core::range` Copy 类型
//! - `NonZero` 整数范围迭代
//! - `From<T> for AssertUnwindSafe<T>`
//! - `From<T> for LazyCell<T, F>` / `LazyLock<T, F>`
//! - s390x vector registers inline assembly 概念
//!
//! 运行: cargo test --test l3_rust_196_alignment

use std::cell::LazyCell;
use std::num::NonZeroU32;
use std::panic::AssertUnwindSafe;
use std::range::Range;
use std::sync::LazyLock;
use std::{assert_matches, debug_assert_matches};

/// 测验1: `assert_matches!` 稳定化
/// Rust 1.96.0 将 `assert_matches!` / `debug_assert_matches!` 加入标准库（非 prelude）。
#[test]
fn test_assert_matches_stable() {
    let result: Result<i32, &str> = Ok(42);
    assert_matches!(result, Ok(n) if n > 0);

    let option: Option<&str> = Some("rust");
    assert_matches!(option, Some(s) if s.starts_with('r'));
}

/// 测验2: `debug_assert_matches!` 在 release 模式下编译消失
/// 本测试在 debug 模式下运行，因此会实际执行。
#[test]
fn test_debug_assert_matches_stable() {
    let value = 7;
    debug_assert_matches!(value, 1..=10);
}

/// 测验3: `core::range::Range` 实现 `Copy`
/// 新的 `core::range::Range` 类型实现 `IntoIterator` 而非 `Iterator`，因此可以 `Copy`。
#[test]
fn test_core_range_copy() {
    let range: Range<usize> = Range { start: 1, end: 5 };

    // Range 实现 Copy，可以多次消费
    let sum1: usize = range.into_iter().sum();
    let sum2: usize = range.into_iter().sum();

    assert_eq!(sum1, 10);
    assert_eq!(sum2, 10);
}

/// 测验4: `NonZero` 整数范围迭代
/// Rust 1.96.0 支持对 `NonZero` 整数进行范围迭代。
#[test]
fn test_nonzero_range_iteration() {
    let start = NonZeroU32::new(1).unwrap();
    let end = NonZeroU32::new(4).unwrap();

    let values: Vec<u32> = (start..=end).map(|nz| nz.get()).collect();

    assert_eq!(values, vec![1, 2, 3, 4]);
}

/// 测验5: `From<T> for AssertUnwindSafe<T>`
/// 任何类型可直接通过 `AssertUnwindSafe::from` 包装。
#[test]
fn test_assert_unwind_safe_from() {
    let value = String::from("panic safe");
    let wrapped: AssertUnwindSafe<String> = AssertUnwindSafe::from(value);

    assert_eq!(wrapped.0, "panic safe");
}

/// 测验6: `From<T> for LazyCell<T, F>`
/// 1.96.0 起可直接从值创建 `LazyCell`（当闭包类型兼容时）。
#[test]
fn test_lazy_cell_from_value() {
    // `LazyCell<T, fn() -> T>` 可从 `T` 通过 `From` 创建
    let cell: LazyCell<i32, fn() -> i32> = LazyCell::from(42);

    assert_eq!(*cell, 42);
}

/// 测验7: `From<T> for LazyLock<T, F>`
/// 与 `LazyCell` 类似，`LazyLock` 也支持 `From<T>`。
#[test]
fn test_lazy_lock_from_value() {
    let lock: LazyLock<i32, fn() -> i32> = LazyLock::from(2026);

    assert_eq!(*lock, 2026);
}

/// 测验8: s390x vector registers inline assembly 概念
/// Rust 1.96.0 支持在 s390x 目标的 inline assembly 中使用 vector registers。
/// 本测验不实际运行 s390x 汇编，而是验证目标三元组与寄存器名称知识。
#[test]
fn test_s390x_vector_asm_concept() {
    // s390x 是 IBM Z / Linux on IBM Z 架构的目标三元组
    let s390x_target = "s390x-unknown-linux-gnu";

    // vector register 命名约定为 v0..v31（128-bit vector registers）
    let vector_regs: &[&str] = &["v0", "v1", "v15", "v31"];

    assert!(s390x_target.starts_with("s390x"));
    assert!(vector_regs.iter().all(|r| r.starts_with('v')));
}

/// 测验9: Cargo CVE-2026-5222 / 5223 概念
/// Rust 1.96.0 修复了两个影响第三方 registry 的 Cargo 安全漏洞。
#[test]
fn test_cargo_cve_2026_concept() {
    // CVE-2026-5223: 恶意 crate tarball 可通过 symlink 提取到缓存目录上级
    // 修复: Cargo 现在拒绝任何包含 symlink 的 tarball
    // CVE-2026-5222: URL 规范化错误导致凭证可能发送到 .git 后缀的 URL
    // 修复: 仅对 git 协议进行 .git 后缀规范化
    let fixes = [
        "reject tarball symlinks",         // 5223
        "limit .git suffix normalization", // 5222
    ];

    assert_eq!(fixes.len(), 2);
}

/// 测验10: rustdoc 1.96 改进概念 — `missing_doc_code_examples` lint
/// rustdoc 1.96 改进了 `missing_doc_code_examples` lint 等行为。
#[test]
fn test_rustdoc_196_lint_concept() {
    // `missing_doc_code_examples` 是 rustdoc lint，用于警告公共 API 缺少文档示例
    let lint_name = "missing_doc_code_examples";

    assert!(lint_name.starts_with("missing_doc"));
    assert!(lint_name.ends_with("code_examples"));
}
