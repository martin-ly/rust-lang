# 消息传递模式

> **EN**: Threading / Concurrency Guide (crate example index)
> **Summary**: A stub page pointing to the canonical concept authority. General Rust explanations have been migrated to `concept/`; runnable examples remain in the crate.

> **权威来源**: 通用 Rust 概念解释已迁移至 canonical authority page:
> [`concept/03_advanced/00_concurrency/10_concurrency_patterns.md`](../../../concept/03_advanced/00_concurrency/10_concurrency_patterns.md).

本文件原为对应 crate 的通用概念教程。根据 AGENTS.md §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/`，此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 主题速览

- 概述
- Actor模型实现
  - 1. 基础Actor框架
  - 2. 高级Actor特性
- 高级通道通信
  - 1. 类型安全通道
  - 2. 背压控制通道
- 发布订阅模式
  - 1. 类型安全的事件总线
  - 2. 异步事件流
- 总结
