# Rust 1.91 异步编程改进文档（历史版本）

> **EN**: Async Guide (crate example index)
> **Summary**: A stub page pointing to the canonical concept authority. General Rust explanations have been migrated to `concept/`; runnable examples remain in the crate.

> **权威来源**: 通用 Rust 概念解释已迁移至 canonical authority page:
> [`concept/07_future/00_version_tracking/rust_1_91_stabilized.md`](../../../concept/07_future/00_version_tracking/rust_1_91_stabilized.md).

本文件原为对应 crate 的通用概念教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/`，此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 主题速览

- 概述
- 异步迭代器改进
  - Rust 1.91 改进概述
  - 核心改进
  - 性能对比
- const 上下文增强在异步配置中的应用
  - Rust 1.91 改进概述1
  - 核心改进1
  - 实际应用场景
- JIT 编译器优化对异步代码的影响
  - Rust 1.91 改进概述2
  - 核心改进2
- 内存分配优化对异步场景的影响
  - Rust 1.91 改进概述3
  - 核心改进3
- 异步错误处理改进
  - Rust 1.91 改进概述4
  - 核心改进4
  - 实际应用
- 实际应用示例
  - 示例 1: 高性能异步流处理
  - 示例 2: 异步任务管理器
  - 示例 3: 异步缓存系统
- 迁移指南
  - 从 Rust 1.90 迁移到 Rust 1.91
  - 兼容性说明
- 总结
