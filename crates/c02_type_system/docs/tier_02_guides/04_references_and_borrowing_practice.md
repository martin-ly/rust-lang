> **EN**: References and Borrowing Practice Guide (c02 guide index)
> **Summary**: Stub pointing to the canonical borrowing and lifetimes authorities. Practical examples remain in the c02 crate.

# C02 类型系统 - 引用与借用实践指南

> **权威来源**: 通用 Rust 概念解释已迁移至 canonical authority page:
> [`concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md`](../../../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md)。

本文件原为对应 crate 的通用概念指南。根据 [AGENTS.md](../../../../AGENTS.md) §6.4 治理规则，
通用 Rust 概念解释已迁移至 `concept/`，此处仅保留索引与 canonical 链接。
具体可运行示例请参见本 crate 的 `examples/` 与 `src/bin/` 目录。

## 快速导航

| 主题 | 权威来源 |
| :--- | :--- |
| 引用规则（`&T` / `&mut T`） | [concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md](../../../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) |
| 借用检查器 | [concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md](../../../../concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) |
| 生命周期 | [concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md](../../../../concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) |
| 引用与泛型 | [concept/02_intermediate/01_generics/01_generics.md](../../../../concept/02_intermediate/01_generics/01_generics.md) |
| 智能指针与引用 | [concept/02_intermediate/02_memory_management/04_smart_pointers.md](../../../../concept/02_intermediate/02_memory_management/04_smart_pointers.md) |
| 引用模式匹配 | [concept/01_foundation/04_control_flow/02_patterns.md](../../../../concept/01_foundation/04_control_flow/02_patterns.md) |
