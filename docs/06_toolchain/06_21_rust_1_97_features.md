# Rust 1.97.0 特性参考

> **EN**: Rust 1.97.0 Feature Reference
> **Summary**: Rust 1.97.0 已于 2026-07-09 进入 stable 通道。本页为工具链参考入口，指向 `concept/` 中的权威详解与代码示例。
> **Rust 版本**: 1.97.0 stable

---

## 权威来源

- [`concept/07_future/00_version_tracking/rust_1_97_preview.md`](../../concept/07_future/00_version_tracking/rust_1_97_preview.md) — Rust 1.97.0 稳定特性详解（single source of truth）
- [`concept/07_future/00_version_tracking/rust_1_97_stabilized.md`](../../concept/07_future/00_version_tracking/rust_1_97_stabilized.md) — Rust 1.97.0 稳定特性摘要
- [`concept/07_future/00_version_tracking/rust_1_98_preview.md`](../../concept/07_future/00_version_tracking/rust_1_98_preview.md) — Rust 1.98+ 前沿特性预览

## 代码示例

参见 [`crates/c08_algorithms/src/rust_197_features.rs`](../../crates/c08_algorithms/src/rust_197_features.rs)。

## 工具链说明

本项目 `rust-toolchain.toml` 保持 `channel = "stable"`，由 rustup 自动解析当前 latest stable，无需手动锁定到 `1.97.0`。
