# Rust 1.96 Stable 升级计划

> **Bloom 层级**: L2 (理解)

**预计发布时间**: 2026-05-28
**当前状态**: 准备中
**负责人**: 自动化 + 维护者审核

---

## 一、升级范围

| 组件 | 当前版本 | 目标版本 | 文件 |
|:---|:---:|:---:|:---|
| Rust toolchain | 1.95.0 | 1.96.0 | `rust-toolchain.toml` (如存在) |
| Workspace MSRV | 1.95.0 | 1.96.0 | `Cargo.toml` |
| Crate MSRV | 1.95.0 | 1.96.0 | `crates/*/Cargo.toml` (14 个 crate) |
| CI Rust 版本 | 1.95.0 | 1.96.0 | `.github/workflows/*.yml` |

---

## 二、更新检查表

### 2.1 Cargo.toml 更新

- [ ] 根 `Cargo.toml`：`rust-version = "1.96.0"`
- [ ] `crates/c01_ownership_borrow_scope/Cargo.toml`
- [ ] `crates/c02_type_system/Cargo.toml`
- [ ] `crates/c03_control_fn/Cargo.toml`
- [ ] `crates/c04_generic/Cargo.toml`
- [ ] `crates/c05_threads/Cargo.toml`
- [ ] `crates/c06_async/Cargo.toml`
- [ ] `crates/c07_process/Cargo.toml`
- [ ] `crates/c08_algorithms/Cargo.toml`
- [ ] `crates/c09_design_pattern/Cargo.toml`
- [ ] `crates/c10_networks/Cargo.toml`
- [ ] `crates/c11_macro_system/Cargo.toml`
- [ ] `crates/c11_macro_system_proc/Cargo.toml`
- [ ] `crates/c12_wasm/Cargo.toml`
- [ ] `crates/c13_embedded/Cargo.toml`
- [ ] `crates/common/Cargo.toml`
- [ ] `crates/integration_tests/Cargo.toml`

### 2.2 CI 工作流更新

- [ ] `.github/workflows/ci.yml`: `RUST_VERSION: 1.96.0`
- [ ] `.github/workflows/ci_optimized.yml`: toolchain 版本
- [ ] `.github/workflows/docs-preview.yml`: toolchain 版本
- [ ] `.github/workflows/miri.yml`: nightly 保持
- [ ] `.github/workflows/weekly-dependency-check.yml`: toolchain 版本
- [ ] `.github/workflows/weekly-deps.yml`: toolchain 版本

### 2.3 概念文件状态更新

将以下文件中的"1.96 预览/待跟踪"状态更新为"1.96 已稳定"：

| 文件 | 当前状态 | 更新动作 |
|:---|:---|:---|
| `concept/02_intermediate/05_assert_matches.md` | 预览 | 标记为 ✅ 1.96 稳定 |
| `concept/02_intermediate/06_range_types.md` | 待跟踪 | 标记为 ✅ 1.96 稳定 |
| `concept/07_future/05_rust_version_tracking.md` | v1.11 | 更新至 v1.12，记录 1.96 发布 |

### 2.4 验证步骤

- [ ] `cargo check --workspace --all-features`
- [ ] `cargo test --workspace`
- [ ] `cargo clippy --workspace --all-features -- -D warnings`
- [ ] `cargo doc --workspace --no-deps`
- [ ] `python scripts/concept_audit.py` (0 死链接)
- [ ] `python scripts/code_block_compiler.py` (100% 通过)
- [ ] Miri 验证（13/15 crate）

---

## 三、1.96 新特性项目覆盖确认

| 特性 | 概念文件 | Crate 验证 | 状态 |
|:---|:---|:---:|:---:|
| `assert_matches!` | `concept/02_intermediate/05_assert_matches.md` | c02_type_system | ✅ |
| `core::range` 迭代器 | `concept/02_intermediate/06_range_types.md` | c02_type_system | ✅ |
| `NonZero` 范围迭代 | `concept/02_intermediate/06_range_types.md` | c02_type_system | ✅ |
| `From<T> for LazyCell/LazyLock` | `concept/02_intermediate/08_interior_mutability.md` | - | 🟡 |
| `ManuallyDrop` 常量模式 | `concept/01_foundation/04_type_system.md` | - | 🟡 |
| `expr` metavariable to `cfg` | `concept/03_advanced/04_macros.md` | - | 🟡 |
| never type tuple coercion | `concept/02_intermediate/02_generics.md` | - | 🟡 |

---

## 四、时间线

| 日期 | 事件 |
|:---|:---|
| 2026-05-23 | 升级计划完成，等待 1.96 发布 |
| 2026-05-28 | Rust 1.96.0 stable 预计发布 |
| 2026-05-28~29 | 执行升级检查表 |
| 2026-05-30 | 全项目验证，质量基线报告更新 |

---

> **[来源: Rust Release Schedule](https://forge.rust-lang.org/release/release-notes.html)**
> **[来源: releases.rs](https://releases.rs/)**

---

## 相关文档

- [Rust 版本跟踪](../../concept/07_future/05_rust_version_tracking.md)
- [迁移指南](../MIGRATION_GUIDE_2026.md)
