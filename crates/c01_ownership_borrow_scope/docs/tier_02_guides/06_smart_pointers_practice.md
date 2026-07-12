> **EN**: Smart Pointers Practice Guide (c01 guide index)
> **Summary**: Stub pointing to the canonical smart pointer and interior mutability authorities. Practical examples remain in the c01 crate.

# C01 智能指针 - 实践指南

> **权威来源**: 通用 Rust 概念解释已迁移至 canonical authority page:
> [`concept/02_intermediate/02_memory_management/04_smart_pointers.md`](../../../../concept/02_intermediate/02_memory_management/04_smart_pointers.md)。

本文件原为对应 crate 的通用概念指南。根据 [AGENTS.md](../../../../AGENTS.md) §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/`，此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 快速导航

| 主题 | 权威来源 |
| :--- | :--- |
| 智能指针概述 | [concept/02_intermediate/02_memory_management/04_smart_pointers.md](../../../../concept/02_intermediate/02_memory_management/04_smart_pointers.md) |
| `Box<T>` | [concept/02_intermediate/02_memory_management/04_smart_pointers.md](../../../../concept/02_intermediate/02_memory_management/04_smart_pointers.md) |
| `Rc<T>` / `Arc<T>` | [concept/02_intermediate/02_memory_management/04_smart_pointers.md](../../../../concept/02_intermediate/02_memory_management/04_smart_pointers.md) |
| 内部可变性 | [concept/02_intermediate/02_memory_management/02_interior_mutability.md](../../../../concept/02_intermediate/02_memory_management/02_interior_mutability.md) |
| `RefCell<T>` / `Mutex<T>` | [concept/02_intermediate/02_memory_management/02_interior_mutability.md](../../../../concept/02_intermediate/02_memory_management/02_interior_mutability.md) |
| `Cow<T>` | [concept/02_intermediate/02_memory_management/03_cow_and_borrowed.md](../../../../concept/02_intermediate/02_memory_management/03_cow_and_borrowed.md) |
