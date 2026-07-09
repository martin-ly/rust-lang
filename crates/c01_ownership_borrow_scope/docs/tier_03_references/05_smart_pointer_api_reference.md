> **EN**: Smart Pointer API Reference
> **Summary**: API reference stub pointing to the canonical smart-pointers authority. Code examples remain in the c01 crate.

# 智能指针：堆内存管理与共享语义 — Crate Docs Stub

> **权威来源**: [智能指针：堆内存管理与共享语义](../../../../concept/02_intermediate/02_memory_management/12_smart_pointers.md)

本文件原为对应 crate 的通用概念教程/参考。根据 [AGENTS.md](../../../../AGENTS.md) §6.4 治理规则，
通用 Rust 概念解释已在 `concept/` 中维护为单一权威来源；此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/` 目录。

## 主题导航

| 主题 | 权威来源 |
| :--- | :--- |
| Box<T> | [12_smart_pointers.md#12-box独占堆分配](12_smart_pointers.md#12-box独占堆分配) |
| Rc<T> / Arc<T> | [12_smart_pointers.md#13-rc-与-arc引用计数共享](12_smart_pointers.md#13-rc-与-arc引用计数共享) |
| RefCell<T> | [12_smart_pointers.md#21-refcell-与-cell内部可变性](12_smart_pointers.md#21-refcell-与-cell内部可变性) |
| Weak<T> | [12_smart_pointers.md#模式-5-weak-打破循环引用](12_smart_pointers.md#模式-5-weak-打破循环引用) |

## 本地资源

- [Crate README](../../../../crates/c01_ownership_borrow_scope/README.md) — 本 crate 总览与入口
