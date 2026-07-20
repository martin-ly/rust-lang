---
title: 泛型 where 子句与性能考量
lang: zh-CN
---

要点：

- where 子句让约束更清晰：将长的 trait 约束从签名参数处移至 where 块。
- 性能：静态分发（泛型/`impl Trait`）倾向于内联与单态化；动态分发（`dyn Trait`）有间接开销但带来存储/ABI 灵活性。
- 小技巧：为热路径保留静态分发；边界扩展点使用 trait 对象；在 `#[inline]`、LTO/PGO 下评估。

示例与测试：见 `examples/generics_where_performance.rs` 与 `tests/generics_where_performance_tests.rs`。
