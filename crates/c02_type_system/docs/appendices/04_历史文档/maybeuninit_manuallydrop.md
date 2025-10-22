---
title: MaybeUninit 与 ManuallyDrop 的初始化/析构控制
lang: zh-CN
---

要点：

- `MaybeUninit<T>` 允许延迟初始化与无 UB 地跳过清零；完成初始化后用 `assume_init` 或者 `write` + 安全转换。
- `ManuallyDrop<T>` 抑制析构自动运行，需手动 drop；适合自定义资源管理场景。
- 二者常与 `Pin`/`unsafe` 协作，必须严格遵守“初始化一次、析构一次”原则。

示例与测试：见 `examples/maybeuninit_manuallydrop.rs` 与 `tests/maybeuninit_manuallydrop_tests.rs`。
