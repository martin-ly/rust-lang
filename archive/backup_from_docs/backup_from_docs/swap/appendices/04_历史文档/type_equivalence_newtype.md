---
title: 类型等价、透明封装与 Newtype 边界
lang: zh-CN
---

要点：

- Newtype（`struct Wrapper(T);`）提供语义隔离，不等价于子类型；可通过 `Deref` 提供便捷访问，但不会自动替代底层类型。
- `type Alias = T` 仅是别名，等价于 `T`；不会生成新类型。
- `#[repr(transparent)]` 用于 FFI/ABI 透明性，但不改变类型系统等价关系。

示例与测试：见 `examples/type_equivalence_newtype_examples.rs` 与 `tests/type_equivalence_newtype_tests.rs`。
