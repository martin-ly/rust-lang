---
title: NonNull 与裸指针 API
lang: zh-CN
---

要点：

- `*const T`/`*mut T` 为裸指针，读写需 `unsafe`；不参与借用检查。
- `NonNull<T>` 表达“非空裸指针”，常用于自定义分配器/容器内部。
- 与 `Box::into_raw`/`from_raw`、`Vec::as_mut_ptr` 等协作时，需保证配对与别名规则。

示例与测试：见 `examples/nonnull_raw_pointers.rs` 与 `tests/nonnull_raw_pointers_tests.rs`。
