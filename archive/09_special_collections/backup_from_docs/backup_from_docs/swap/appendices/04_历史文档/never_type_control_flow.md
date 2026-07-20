---
title: never 类型（!）与控制流
lang: zh-CN
---

要点：

- `!` 表示“无返回”的发散类型：函数永不返回（`panic!`、`loop {}`、`std::process::exit`）。
- `!` 可在推断中作为“底类型”参与分支合并，使表达式类型统一。
- 与 `Result<T, !>`/`Infallible` 的关系：不可失败的场景可表达为永不产生错误分支。

示例与测试：见 `examples/never_type_control_flow.rs` 与 `tests/never_type_control_flow_tests.rs`。
