> **EN**: Basic Threading in Rust (crate example index)
> **Summary**: A stub page pointing to the canonical concept authority for Rust threading basics. The c05_threads crate provides runnable examples; general explanations live in `concept/`.

# Rust 基础线程操作（c05_threads 示例索引）

> **权威来源**: 通用线程概念、线程创建、`Send`/`Sync`、线程安全等完整解释见
> [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../../concept/03_advanced/00_concurrency/01_concurrency.md)。

本文件原为 `c05_threads` crate 的通用线程概念教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/03_advanced/00_concurrency/`，此处仅保留索引与
canonical 链接。

## 本 crate 相关示例

- `crates/c05_threads/examples/`：线程创建、`scoped threads`、线程池、同步原语等可运行示例。
- `crates/c05_threads/src/`：c05_threads crate 的 API 实现与练习骨架。

## 快速导航

| 主题 | 权威来源 |
| :--- | :--- |
| 线程创建与 `thread::spawn` | [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../../concept/03_advanced/00_concurrency/01_concurrency.md) |
| `Send` / `Sync` 判定 | [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../../concept/03_advanced/00_concurrency/01_concurrency.md) |
| 线程同步原语对比 | [`concept/03_advanced/00_concurrency/01_concurrency.md`](../../../concept/03_advanced/00_concurrency/01_concurrency.md) |
| 并发模式与并行算法 | [`concept/03_advanced/00_concurrency/19_parallel_distributed_pattern_spectrum.md`](../../../concept/03_advanced/00_concurrency/19_parallel_distributed_pattern_spectrum.md) |
