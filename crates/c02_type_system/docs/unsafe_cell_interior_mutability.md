---
title: UnsafeCell 与内部可变性
lang: zh-CN
---

要点：

- `UnsafeCell<T>` 是内部可变性的底层原语，`Cell`/`RefCell`/原子类型均基于它。
- `RefCell` 运行时检查借用规则；`Cell` 提供按值读写（`Copy` 友好）。
- 并发场景使用 `Mutex`/`RwLock`/原子类型，不可跨线程滥用 `RefCell`。

示例与测试：见 `examples/unsafe_cell_interior_mutability.rs` 与 `tests/unsafe_cell_interior_mutability_tests.rs`。
