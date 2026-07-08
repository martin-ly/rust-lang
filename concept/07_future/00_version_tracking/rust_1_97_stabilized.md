# Rust 1.97.0 稳定特性

> **EN**: Rust 1.97.0 Stabilized Features
> **Summary**: Rust 1.97.0 于 2026-07-09 进入 stable 通道。本文档汇总已稳定的语言、标准库、工具链与目标平台特性；完整实现与示例参见权威页 `rust_1_97_preview.md`。
>
> **受众**: [进阶] / [专家]
> **内容分级**: [参考级]
> **对应 Rust 版本**: **1.97.0 stable**（项目 `rust-toolchain.toml` 保持 `stable` 通道，由 rustup 自动解析）
> **最后更新**: 2026-07-09
> **状态**: ✅ 已对齐 Rust 1.97.0 stable
>
> **权威来源**: · [Rust 1.97.0 Release Notes](https://releases.rs/docs/1.97.0/) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/)
>
> **前置概念**: [Rust 版本跟踪](05_rust_version_tracking.md) · [Rust 1.96 稳定特性](rust_1_96_stabilized.md)
> **后置概念**: [Rust 1.97.0 前沿特性预览](rust_1_97_preview.md) · [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md)

---

## 1. 已稳定特性概览

Rust 1.97.0 主要带来以下类别的改进：

### 1.1 语言与编译器

- `#[must_use]` lint 扩展至 `Result<T, E>` / `ControlFlow<B, C>` 的内部类型。
- 空 `#[export_name = ""]` 现在被明确拒绝。
- `linker-messages` 恢复为默认 `warn`。
- 修复 struct 模式中元组索引简写的正确性回归。
- `pin!` 宏阻止隐式 deref coercions。

### 1.2 标准库 API

- `NonZeroU*` / `NonZeroI*` 新增位查询方法：`highest_one`、`lowest_one`、`bit_width`。
- `char::is_control()` 成为 `const fn`。
- `Option<NonZero*>` 的 niche 编码优先使用 `-1` 表示 `None`。
- `NonZeroU32::midpoint` / `isqrt` 稳定。
- `ptr::fn_addr_eq` 稳定。
- `const size_of_val` / `align_of_val` 稳定。
- `BuildHasherDefault::new` 成为 `const fn`。
- `Box::as_ptr` 稳定。
- `Option::as_slice` / `as_mut_slice` 稳定。

### 1.3 目标平台与工具链

- 新增 `cfg_target_has_atomic_equal_alignment` 条件编译标志。
- `WSAESHUTDOWN` 错误码映射。
- NVIDIA GPU 目标基线提升。

### 1.4 推迟到 1.98 的候选特性

- `VecDeque::truncate_front`
- `VecDeque::retain_back`
- `Vec::into_non_null`

---

## 2. 权威来源与示例

> **完整特性说明、代码示例与迁移建议**请参见项目权威页：
>
> - [`concept/07_future/00_version_tracking/rust_1_97_preview.md`](rust_1_97_preview.md)
> - [`crates/c08_algorithms/src/rust_197_features.rs`](../../../crates/c08_algorithms/src/rust_197_features.rs)
>
> 工具链快速参考请参见：
>
> - [`docs/06_toolchain/06_21_rust_1_97_features.md`](../../../docs/06_toolchain/06_21_rust_1_97_features.md)

---

## 3. 项目构建说明

本项目 `rust-toolchain.toml` 保持 `channel = "stable"`，由 rustup 自动解析当前 latest stable。Rust 1.97.0 发布后，`stable` 将逐步解析到 1.97.0；在 CI 与本地环境中无需手动切换工具链版本号。

如需在 1.96.1 环境下编译，`#[cfg(nightly)]` 分支不会启用，代码中的等效实现（fallback）可保证向后兼容。
