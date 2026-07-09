> **EN**: Self-Referential Structures
> **Summary**: Stub for self-referential structs pointing to the canonical Pin/Unpin authority.

# Pin 与 Unpin：自引用类型的不动性保证 — Crate Docs Stub

> **权威来源**: [Pin 与 Unpin：自引用类型的不动性保证](../../../../concept/03_advanced/01_async/06_pin_unpin.md)

本文件原为对应 crate 的通用概念教程/参考。根据 [AGENTS.md](../../../../AGENTS.md) §6.4 治理规则，
通用 Rust 概念解释已在 `concept/` 中维护为单一权威来源；此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/` 目录。

## 主题导航

| 主题 | 权威来源 |
| :--- | :--- |
| 自引用问题 | [06_pin_unpin.md#11-问题自引用类型的移动陷阱](06_pin_unpin.md#11-问题自引用类型的移动陷阱) |
| Pin 与 Unpin | [06_pin_unpin.md#12-pin-的设计承诺不再移动](06_pin_unpin.md#12-pin-的设计承诺不再移动) |
| 自引用结构安全构建 | [06_pin_unpin.md#22-自引用结构体的安全构建](06_pin_unpin.md#22-自引用结构体的安全构建) |
| Async 中的自引用 | [06_pin_unpin.md#23-与-asyncawait-的关系](06_pin_unpin.md#23-与-asyncawait-的关系) |

## 本地资源

- [Crate README](../../../../crates/c01_ownership_borrow_scope/README.md) — 本 crate 总览与入口
