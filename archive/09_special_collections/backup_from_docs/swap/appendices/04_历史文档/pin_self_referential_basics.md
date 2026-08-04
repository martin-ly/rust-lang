---
title: Pin 与自引用基础
lang: zh-CN
---

要点：

- `Pin<P>` 承诺“内存地址不再改变”，保护含自引用结构或需要固定地址的类型。
- 常与 `Box`/`Arc`/`Pin`/`Unpin` 配合；大多数类型默认 `Unpin`。
- 自引用结构通常需自定义构造流程，避免移动破坏引用。

示例与测试：见 `examples/pin_self_referential_basics.rs` 与 `tests/pin_self_referential_basics_tests.rs`。
