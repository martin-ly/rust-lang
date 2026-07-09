# Rust 1.92.0 线程并发改进文档

> **EN**: Threading / Concurrency Guide (crate example index)
> **Summary**: A stub page pointing to the canonical concept authority. General Rust explanations have been migrated to `concept/`; runnable examples remain in the crate.

> **权威来源**: 通用 Rust 概念解释已迁移至 canonical authority page:
> [`concept/07_future/00_version_tracking/rust_1_92_stabilized.md`](../../../concept/07_future/00_version_tracking/rust_1_92_stabilized.md).

本文件原为对应 crate 的通用概念教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/`，此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 主题速览

- 概述
- MaybeUninit 在并发编程中的应用
  - Rust 1.92.0 改进概述
- rotate_right 在线程池管理中的应用
- NonZero::div_ceil 在线程数量计算中的应用
- 实际应用示例
- 迁移指南
  - 从 Rust 1.91 迁移到 Rust 1.92.0
- RwLockWriteGuard::downgrade (Rust 1.92.0 新增) ⭐
  - 使用场景
  - 代码示例
  - 性能优势
- 展开表默认启用 (Rust 1.92.0 新增) ⭐
  - 配置说明
  - 优势
- panic::catch_unwind 性能优化 (Rust 1.92.0 新增) ⭐
  - 性能影响
  - 使用示例
- 总结
