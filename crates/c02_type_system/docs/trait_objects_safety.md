---
title: Trait 对象与对象安全
lang: zh-CN
---

核心要点：

- 对象安全（object safety）：Trait 可用于 `dyn Trait` 的条件。
- 常见不对象安全项：带有 `Self: Sized` 限制的方法、返回 `Self`、泛型方法等（需用 `where Self: Sized` 限制只在具体类型上可用）。
- 动态分发与静态分发：`&dyn Trait`/`Box<dyn Trait>` vs `impl Trait`/泛型。

示例与测试：见 `examples/trait_objects_safety.rs` 与 `tests/trait_objects_safety_tests.rs`。
