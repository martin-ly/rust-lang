# 第 5 章：高级主题与总结

> **EN**: Threading / Concurrency Guide (crate example index)
> **Summary**: A stub page pointing to the canonical concept authority. General Rust explanations have been migrated to `concept/`; runnable examples remain in the crate.

> **权威来源**: 通用 Rust 概念解释已迁移至 canonical authority page:
> [`concept/03_advanced/00_concurrency/11_atomics_and_memory_ordering.md`](../../../concept/03_advanced/00_concurrency/11_atomics_and_memory_ordering.md).

本文件原为对应 crate 的通用概念教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/`，此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 主题速览

- 1. Atomics：原子类型
  - 1.1. 硬件层面的并发基石
  - 1.2. 内存排序 (Memory Ordering)
- 2. 无锁编程 (Lock-Free Programming)
  - 2.1. 理念与优势
  - 2.2. 挑战与危险
- 3. 本分册核心思想总结
  - 3.1. 所有权作为并发的中心法则
  - 3.2. 两种范式，一个目标
  - 3.3. 抽象的力量
- 4. 哲学批判性分析
  - 4.1. "无畏"的真正含义
  - 4.2. 未来的方向：`async/await`
- 5. 最终总结
