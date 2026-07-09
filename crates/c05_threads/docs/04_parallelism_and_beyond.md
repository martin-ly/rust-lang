# 第 4 章：并行计算与生态系统

> **EN**: Threading / Concurrency Guide (crate example index)
> **Summary**: A stub page pointing to the canonical concept authority. General Rust explanations have been migrated to `concept/`; runnable examples remain in the crate.

> **权威来源**: 通用 Rust 概念解释已迁移至 canonical authority page:
> [`concept/03_advanced/00_concurrency/19_parallel_distributed_pattern_spectrum.md`](../../../concept/03_advanced/00_concurrency/19_parallel_distributed_pattern_spectrum.md).

本文件原为对应 crate 的通用概念教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/`，此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 主题速览

- 1. 并发 (Concurrency) vs. 并行 (Parallelism)
  - 1.1. 形式化区分
  - 1.2. Rust 的模型映射
- 2. 数据并行：Rayon 库
  - 2.1. 核心理念：轻松将串行改为并行
  - 2.2. 并行迭代器 (`ParallelIterator`)
  - 2.3. 工作窃取 (Work-Stealing) 调度
- 3. 其他关键并发/并行库
  - 3.1. `crossbeam`: 更强大的通道与工具
  - 3.2. `tokio` 和 `async-std [已归档]`: 异步运行时
- 4. 哲学批判性分析
  - 4.1. 抽象层次的提升
  - 4.2. "无畏"的边界
- 5. 总结
