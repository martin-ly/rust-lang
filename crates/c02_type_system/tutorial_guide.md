# Rust 1.90 高级特性教程指南

**EN**: Rust 1.90 Advanced Features Tutorial Guide
**Summary**: Learning entry stub for advanced Rust type-system and programming topics; full explanations live in `concept/` authority pages.

> **权威来源**: 本文件为学习入口 stub，完整概念解释请见：
> [`concept/01_foundation/02_type_system/04_type_system.md`](../../concept/01_foundation/02_type_system/04_type_system.md)
>
> 根据 [AGENTS.md](../../AGENTS.md) §2 Canonical 规则与 §6.4 `crates/` 治理规则，
> 通用 Rust 概念解释统一维护在 `concept/` 中；`crates/` 目录仅保留与本 crate 直接相关的可运行代码与独特实现说明。
> 本文件仅保留摘要、速查与链接。

## 速查要点

- 高级类型系统概念（GATs、TAIT、复杂生命周期、类型约束）见 `concept/` 类型系统相关权威页。
- 泛型与 trait 是 Rust 零成本抽象的基石；trait bound 用 `where` 子句组织更清晰。
- 异步与并发编程需区分 OS 线程、`async`/`await`、数据并行与 Actor 模型的适用场景。
- WebAssembly 与性能优化属于生态/工程实践，参考 `concept/06_ecosystem/` 与 `docs/` 实践指南。

## 主题导航

| 主题 | 权威来源 |
| :--- | :--- |
| 类型系统基础 | [`concept/01_foundation/02_type_system/04_type_system.md`](../../concept/01_foundation/02_type_system/04_type_system.md) |
| 高级类型系统 | [`concept/02_intermediate/04_types_and_conversions/20_type_system_advanced.md`](../../concept/02_intermediate/04_types_and_conversions/20_type_system_advanced.md) |
| 泛型 | [`concept/02_intermediate/01_generics/02_generics.md`](../../concept/02_intermediate/01_generics/02_generics.md) |
| Trait | [`concept/02_intermediate/00_traits/01_traits.md`](../../concept/02_intermediate/00_traits/01_traits.md) |
| 生命周期 | [`concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`](../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) |
| 模式匹配 | [`concept/01_foundation/04_control_flow/40_patterns.md`](../../concept/01_foundation/04_control_flow/40_patterns.md) |
| 错误处理 | [`concept/02_intermediate/03_error_handling/01_error_handling.md`](../../concept/02_intermediate/03_error_handling/01_error_handling.md) |
| 并发模型 | [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../concept/03_advanced/00_concurrency/01_concurrency.md) |
| 异步编程 | [`concept/03_advanced/01_async/02_async.md`](../../concept/03_advanced/01_async/02_async.md) |
| 性能优化 | [`concept/06_ecosystem/10_performance/01_performance.md`](../../concept/06_ecosystem/10_performance/01_performance.md) |

## 实践入口

- 本 crate 的 `src/` 与 `examples/` 目录包含与类型系统相关的可编译示例。
- 系统化的练习与项目请见 [`exercises/`](../../exercises/) 与 [`docs/03_practice/`](../../docs/03_practice/)。
