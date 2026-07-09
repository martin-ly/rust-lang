> **EN**: Cross-Thread Ownership
> **Summary**: Stub for cross-thread ownership pointing to the canonical concurrency authority.

# Concurrency（并发模型） — Crate Docs Stub

> **权威来源**: [Concurrency（并发模型）](../../../../concept/03_advanced/00_concurrency/01_concurrency.md)

本文件原为对应 crate 的通用概念教程/参考。根据 [AGENTS.md](../../../../AGENTS.md) §6.4 治理规则，
通用 Rust 概念解释已在 `concept/` 中维护为单一权威来源；此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/` 目录。

## 主题导航

| 主题 | 权威来源 |
| :--- | :--- |
| Send 与 Sync | [01_concurrency.md#二概念属性矩阵attribute-matrix](01_concurrency.md#二概念属性矩阵attribute-matrix) |
| Arc + Mutex 模式 | [01_concurrency.md#72-正确示例mutex-共享状态](01_concurrency.md#72-正确示例mutex-共享状态) |
| Scoped Threads | [01_concurrency.md#71-正确示例spawn--move-闭包](01_concurrency.md#71-正确示例spawn--move-闭包) |
| 原子类型 | [01_concurrency.md#31b-c11-memory-model-在-rust-中的精确映射](01_concurrency.md#31b-c11-memory-model-在-rust-中的精确映射) |

## 本地资源

- [Crate README](../../../../crates/c01_ownership_borrow_scope/README.md) — 本 crate 总览与入口
