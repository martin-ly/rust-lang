# Rust 1.90 Cargo 和包管理完整指南

**EN**: Rust 1.90 Cargo and Package Management Guide
**Summary**: Cargo guide stub for the c02_type_system crate; full Rust crate/package concepts live in `concept/` authority pages.

> **权威来源**: 本文件为 crate 工具入口 stub，完整概念解释请见：
> [`concept/01_foundation/07_modules_and_items/11_crates_and_source_files.md`](../../concept/01_foundation/07_modules_and_items/11_crates_and_source_files.md)
>
> 根据 [AGENTS.md](../../AGENTS.md) §2 Canonical 规则与 §6.4 `crates/` 治理规则，
> 通用 Rust 概念解释统一维护在 `concept/` 中；`crates/` 目录仅保留与本 crate 直接相关的可运行代码与独特实现说明。
> 本文件仅保留摘要、速查与链接。

## 主题导航

| 主题 | 权威来源 |
| :--- | :--- |
| Crate 与源文件 | [`concept/01_foundation/07_modules_and_items/11_crates_and_source_files.md`](../../concept/01_foundation/07_modules_and_items/11_crates_and_source_files.md) |
| Cargo Manifest | [`concept/06_ecosystem/01_cargo/10_cargo_manifest_reference.md`](../../concept/06_ecosystem/01_cargo/10_cargo_manifest_reference.md) |
| Cargo Workspaces | [`concept/06_ecosystem/01_cargo/14_cargo_workspaces.md`](../../concept/06_ecosystem/01_cargo/14_cargo_workspaces.md) |
| Cargo 构建优化 | [`concept/06_ecosystem/01_cargo/02_cargo_build_optimization.md`](../../concept/06_ecosystem/01_cargo/02_cargo_build_optimization.md) |

## 实践入口

- 本 crate 的 `Cargo.toml` 与 `examples/` 展示包管理相关配置与示例。
- 工具链实践指南请见 [`docs/09_toolchain/`](../../docs/09_toolchain/)。
