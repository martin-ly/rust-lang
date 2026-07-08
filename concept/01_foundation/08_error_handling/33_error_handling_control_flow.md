# 错误处理控制流（Error Handling Control Flow）
>
> **EN**: Error Handling Control Flow
> **Summary**: Error handling patterns in Rust control flow, covering the `?` operator, `FromResidual`, `try` blocks, and boundary design recommendations.
>
> **受众**: [初学者] / [进阶]
> **层级**: L1 基础概念
> **Bloom 层级**: 理解 → 应用
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **状态**: 从 `crates/c03_control_fn/docs/error_handling_control_flow_1_90.md` 迁移整理
>
> **主要来源**: [The Rust Reference — The ? operator](https://doc.rust-lang.org/reference/expressions/operator-expr.html#the-question-mark-operator) · [The Rust Programming Language — Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html) · [Rust By Example — Error handling](https://doc.rust-lang.org/rust-by-example/error.html)
>
> **前置概念**: [Error Handling 基础](32_error_handling_basics.md) · [Control Flow](../04_control_flow/07_control_flow.md) · [Functions](../07_modules_and_items/12_functions.md)
> **后置概念**: [Error Handling 深入](../../02_intermediate/03_error_handling/04_error_handling.md) · [Iterator Patterns](../../02_intermediate/07_iterators_and_closures/15_iterator_patterns.md)

---

## 📊 目录

- [错误处理控制流（Error Handling Control Flow）](#错误处理控制流error-handling-control-flow)
  - [📊 目录](#-目录)
  - [`?` 运算符与早退](#-运算符与早退)
  - [`FromResidual` 与跨类型传播](#fromresidual-与跨类型传播)
  - [`try` 块（稳定）](#try-块稳定)
  - [边界设计建议](#边界设计建议)

本篇聚焦 `Result`/`Option` 与 `?` 运算符、`FromResidual` 残差机制、`try` 块、错误转换与边界设计。

## `?` 运算符与早退

```rust
fn read_number(s: &str) -> Result<i32, String> {
    let num: i32 = s.trim().parse().map_err(|_| "parse".to_string())?;
    Ok(num)
}
```

要点：`?` 等价于 `match` 早退；自动从错误类型转换到函数返回错误类型。

## `FromResidual` 与跨类型传播

`?` 依赖 `Try`/`FromResidual` 将如 `Option::None`、`Result::Err` 转化为调用者返回类型的残差。

```rust
fn opt_chain(x: Option<i32>) -> Option<i32> {
    let y = Some(1)?; // None 则直接返回 None
    Some(x? + y)
}
```

## `try` 块（稳定）

将一段内部使用 `?` 的表达式整体化，便于在表达式位置编写错误传播逻辑。

```rust
fn sum3(a: Result<i32, &'static str>, b: Result<i32, &'static str>) -> Result<i32, &'static str> {
    let s: Result<i32, _> = try { a? + b? };
    s
}
```

## 边界设计建议

- 对外 API 使用语义明确的错误类型（可结合 `thiserror`）；
- 小范围 `try` 块提升表达式可读性；
- 仅在需要时引入 `anyhow`/`eyre` 等动态错误类型。

---
