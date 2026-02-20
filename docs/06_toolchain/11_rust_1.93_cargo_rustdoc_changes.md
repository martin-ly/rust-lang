# Rust 1.93 Cargo 与 Rustdoc 变更详解

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 目录

- [Rust 1.93 Cargo 与 Rustdoc 变更详解](#rust-193-cargo-与-rustdoc-变更详解)
  - [目录](#目录)
  - [Cargo 变更](#cargo-变更)
    - [CARGO\_CFG\_DEBUG\_ASSERTIONS](#cargo_cfg_debug_assertions)
    - [cargo tree --format 长格式](#cargo-tree---format-长格式)
    - [cargo clean --workspace](#cargo-clean---workspace)
  - [Rustdoc 变更](#rustdoc-变更)
    - [移除 #!\[doc(document\_private\_items)\]](#移除-docdocument_private_items)
    - [宏搜索过滤](#宏搜索过滤)
    - [import 搜索过滤](#import-搜索过滤)
    - [文档属性校验](#文档属性校验)
  - [相关文档](#相关文档)

---

## Cargo 变更

### CARGO_CFG_DEBUG_ASSERTIONS

**变更**：Cargo 1.93 在 build scripts 中根据 profile 启用 `CARGO_CFG_DEBUG_ASSERTIONS` 环境变量。

**影响**：依赖 `static-init` 1.0.1–1.0.3 的 crate 可能编译失败，错误为 "failed to resolve: use of unresolved module or unlinked crate `parking_lot`"。

**解决方案**：升级 `static-init` 或检查依赖。

**参考**：[Issue #150646](https://github.com/rust-lang/rust/issues/150646#issuecomment-3718964342)

---

### cargo tree --format 长格式

**变更**：`cargo tree` 支持 `--format` 变量的长格式。

**示例**：

```bash
# 长格式变量示例
cargo tree --format "{p} {l} {r}"
```

**参考**：[PR #16204](https://github.com/rust-lang/cargo/pull/16204)

---

### cargo clean --workspace

**变更**：`cargo clean` 新增 `--workspace` 选项，可清理整个 workspace。

**示例**：

```bash
# 清理整个 workspace 的 target 目录
cargo clean --workspace
```

**参考**：[PR #16263](https://github.com/rust-lang/cargo/pull/16263)

---

## Rustdoc 变更

### 移除 #![doc(document_private_items)]

**变更**：`#![doc(document_private_items)]` 属性已被移除。

**影响**：若 crate 使用了该属性，编译会报错。应改用其他方式展示私有项文档。

**参考**：[PR #146495](https://github.com/rust-lang/rust/pull/146495)

---

### 宏搜索过滤

**变更**：在 rustdoc 的 "macros" 搜索过滤中，现在包含 attribute 宏和 derive 宏。

**影响**：搜索宏时结果更完整。

**参考**：[PR #148176](https://github.com/rust-lang/rust/pull/148176)

---

### import 搜索过滤

**变更**：在 rustdoc 的 `import` 搜索过滤中，现在包含 extern crates。

**影响**：搜索 import 时结果更完整。

**参考**：[PR #148301](https://github.com/rust-lang/rust/pull/148301)

---

### 文档属性校验

**变更**：若 `html_favicon_url`、`html_logo_url`、`html_playground_url`、`issue_tracker_base_url` 或 `html_no_source` 有缺失值、意外值或类型错误，rustdoc 将发出 deny-by-default lint `rustdoc::invalid_doc_attributes`。

**解决方案**：检查并修正 crate 级文档属性配置。

```toml
# Cargo.toml 示例
[package.metadata.docs.rs]
# 确保这些属性有有效值
```

**参考**：[PR #149197](https://github.com/rust-lang/rust/pull/149197)

---

## 相关文档

- [Rust 1.93 完整变更清单](./07_rust_1.93_full_changelog.md)
- [Rust 1.93 兼容性注意事项](./06_rust_1.93_compatibility_notes.md)
- [Cargo 速查卡](../quick_reference/cargo_cheatsheet.md)
- [rustdoc 高级用法](./03_rustdoc_advanced.md)

---

**最后对照 releases.rs**: 2026-02-14
