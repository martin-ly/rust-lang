---
title: const 评估、const fn 与关联常量
lang: zh-CN
---

要点：

- `const fn` 在编译期可求值；限制随稳定版本逐步放宽。
- 关联常量（`trait`/`impl` 内的 `const`）用于为类型/实现提供编译期常量接口。
- 常量泛型与关联常量常配合用于在类型层编码大小信息。

示例与测试：见 `examples/const_eval_assoc_consts.rs` 与 `tests/const_eval_assoc_consts_tests.rs`。
