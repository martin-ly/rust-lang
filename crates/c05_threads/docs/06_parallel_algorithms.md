> **EN**: Parallel Algorithms in Rust (crate example index)
> **Summary**: A stub page pointing to the canonical concept authority for parallel and distributed patterns. The c05_threads crate provides runnable Rayon and hand-rolled parallel examples.

# Rust 并行算法（c05_threads 示例索引）

> **权威来源**: 并行算法分类、Fork-Join、数据并行、任务并行、工作窃取等完整解释见
> [`concept/03_advanced/00_concurrency/19_parallel_distributed_pattern_spectrum.md`](../../../concept/03_advanced/00_concurrency/19_parallel_distributed_pattern_spectrum.md)。

本文件原为 `c05_threads` crate 的通用并行算法教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/03_advanced/00_concurrency/`，此处仅保留索引与
canonical 链接。

## 本 crate 相关示例

- `crates/c05_threads/examples/`：`rayon::join`、并行迭代、工作窃取等可运行示例。
- `crates/c05_threads/benches/`：并行性能基准测试。

## 快速导航

| 主题 | 权威来源 |
| :--- | :--- |
| 并行/分布式模式谱系 | [`concept/03_advanced/00_concurrency/19_parallel_distributed_pattern_spectrum.md`](../../../concept/03_advanced/00_concurrency/19_parallel_distributed_pattern_spectrum.md) |
| 并发模式详解 | [`concept/03_advanced/00_concurrency/10_concurrency_patterns.md`](../../../concept/03_advanced/00_concurrency/10_concurrency_patterns.md) |
| 原子操作与内存序 | [`concept/03_advanced/00_concurrency/11_atomics_and_memory_ordering.md`](../../../concept/03_advanced/00_concurrency/11_atomics_and_memory_ordering.md) |
| 无锁数据结构 | [`concept/03_advanced/00_concurrency/16_lock_free.md`](../../../concept/03_advanced/00_concurrency/16_lock_free.md) |
