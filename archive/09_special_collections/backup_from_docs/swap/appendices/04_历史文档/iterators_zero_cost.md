---
title: 迭代器与零成本抽象
lang: zh-CN
---

要点：

- 迭代器适配器链经单态化与内联后可近乎零成本。
- `into_iter`/`iter`/`iter_mut` 的选择影响所有权与借用。
- `FromIterator`/`Extend`：集合构建与增量合并。

示例与测试：见 `examples/iterators_zero_cost.rs` 与 `tests/iterators_zero_cost_tests.rs`。
