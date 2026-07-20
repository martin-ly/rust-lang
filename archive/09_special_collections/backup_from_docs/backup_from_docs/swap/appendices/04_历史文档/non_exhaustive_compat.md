---
title: #[non_exhaustive] 与向后兼容策略
lang: zh-CN
---

要点：

- `#[non_exhaustive]` 用于结构体/枚举，表示未来可能新增字段/变体。
- 下游在匹配枚举时必须有兜底 `_`，构造结构体不能用字面量必须通过构造函数。
- 公共 API 的演进依赖该属性保持可扩展空间。

示例与测试：见 `examples/non_exhaustive_compat.rs` 与 `tests/non_exhaustive_compat_tests.rs`。
