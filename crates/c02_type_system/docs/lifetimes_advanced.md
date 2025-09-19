---
title: 生命周期进阶（省略规则、约束、HRTB）
lang: zh-CN
---

目标：系统讲清 Rust 生命周期在 1.90 语境下的实用规则与边界。

内容提要：

- 生命周期省略规则（三条核心规则）
- 结构体/impl 中的引用字段与生命周期参数
- 返回引用与输入引用的关系（同生共死）
- HRTB（Higher-Ranked Trait Bounds，for<'a> 语法）
- 'static 与字符串字面量、闭包捕获差异

关键要点：

- 省略规则侧重“函数签名”推断，结构体/impl 必须显式标注。
- 借用不超过被借用者是根律，返回引用必须来自参数或更长生命周期资源。
- HRTB 表达“对任意生命周期均成立”的约束，常见于闭包/函数指针泛化。

参考示例：`examples/lifetimes_examples.rs`，配套测试：`tests/lifetimes_examples_tests.rs`。
