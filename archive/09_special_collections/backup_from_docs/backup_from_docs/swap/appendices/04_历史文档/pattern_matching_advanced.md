---
title: 模式匹配进阶：可反驳性、match ergonomics、守卫
lang: zh-CN
---

要点：

- 不可反驳（irrefutable）模式用于 `let`/函数参数；可反驳（refutable）用于 `if let`/`while let`/`match` 分支。
- match ergonomics：自动引用/解引用/借用，使匹配更简洁。
- 守卫 `if` 与 `@` 绑定、`..` 忽略、`_|` 兜底。

示例与测试：见 `examples/pattern_matching_advanced.rs` 与 `tests/pattern_matching_advanced_tests.rs`。
