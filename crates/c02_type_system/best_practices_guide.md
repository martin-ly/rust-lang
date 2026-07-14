# Rust 1.90 最佳实践指南

**EN**: Rust 1.90 Best Practices Guide
**Summary**: Best-practices entry stub for the c02_type_system crate; full Rust language guidance lives in `concept/` authority pages.

> **权威来源**: 本文件为 crate 最佳实践入口 stub，完整概念解释请见：
> [`concept/01_foundation/02_type_system/01_type_system.md`](../../concept/01_foundation/02_type_system/01_type_system.md)
>
> 根据 [AGENTS.md](../../AGENTS.md) §2 Canonical 规则与 §6.4 `crates/` 治理规则，
> 通用 Rust 概念解释统一维护在 `concept/` 中；`crates/` 目录仅保留与本 crate 直接相关的可运行代码与独特实现说明。
> 本文件仅保留摘要、速查与链接。

## 主题导航

| 主题 | 权威来源 |
| :--- | :--- |
| 类型系统基础 | [`concept/01_foundation/02_type_system/01_type_system.md`](../../concept/01_foundation/02_type_system/01_type_system.md) |
| 所有权与借用 | [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md) |
| 泛型 | [`concept/02_intermediate/01_generics/01_generics.md`](../../concept/02_intermediate/01_generics/01_generics.md) |
| Trait | [`concept/02_intermediate/00_traits/01_traits.md`](../../concept/02_intermediate/00_traits/01_traits.md) |
| 错误处理 | [`concept/02_intermediate/03_error_handling/01_error_handling.md`](../../concept/02_intermediate/03_error_handling/01_error_handling.md) |
| 并发编程 | [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../concept/03_advanced/00_concurrency/01_concurrency.md) |
| 性能优化 | [`concept/06_ecosystem/10_performance/01_performance.md`](../../concept/06_ecosystem/10_performance/01_performance.md) |

## 实践入口

- 本 crate 的 `src/` 与 `examples/` 目录包含类型系统相关可编译示例。
- 工程实践指南请见 [`docs/05_practice/`](../../docs/05_practice/)。
