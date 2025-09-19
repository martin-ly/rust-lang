---
title: 变型（Variance）、GATs 与 HRTB 全面解释
lang: zh-CN
---

目标：厘清 Rust 中协变/逆变/不变的直觉与规则，解释 GATs（泛型关联类型）的动机与用法，并结合 HRTB 统一理解高阶生命周期约束。

一、变型（Variance）

- 协变（Covariant）：若 `T1 <: T2`，则 `F<T1> <: F<T2>`。如 `&'a T` 对 `'a` 协变。
- 逆变（Contravariant）：若 `T1 <: T2`，则 `F<T2> <: F<T1>`。如函数参数位置。
- 不变（Invariant）：无上述关系。如 `&'a mut T` 与 `Vec<T>` 对 `T` 不变。

常见结论：

- `&'a T` 对 `'a` 协变；`&'a mut T` 对 `'a` 不变。
- `Box<T>`、`Vec<T>` 对 `T` 通常不变（内部可变/所有权语义导致）。

二、GATs（泛型关联类型）

动机：在 Trait 中为关联类型增添“还依赖额外参数”的能力，从而表达“返回与输入生命周期/参数相关的类型”。

三、HRTB（Higher-Ranked Trait Bounds）

语法：`for<'a> ...` 表示该约束对“任意生命周期”均成立，常见于接受引用的闭包/函数指针的泛化。

示例与测试：见 `examples/variance_examples.rs` 与 `tests/variance_tests.rs`。
