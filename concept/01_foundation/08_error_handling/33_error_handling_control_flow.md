> **内容分级**: [入门实践级]

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
> **L0 关联**: 本页属于 L1 基础概念层；全局知识拓扑参见 [Rust 知识体系全局思维导图](../../00_meta/00_framework/knowledge_mindmap.md)。
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
  - [认知路径与推理骨架](#认知路径与推理骨架)
    - [认知路径](#认知路径)
    - [定理链](#定理链)
    - [反向推理](#反向推理)
    - [反命题](#反命题)

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

---

## 认知路径与推理骨架

### 认知路径

1. **从显式 `match` 开始**：先理解如何用 `match` 处理 `Result`/`Option`。
2. **引入 `?` 简化传播**：掌握 `?` 的早退语义与自动类型转换。
3. **理解残差机制**：通过 `Try`/`FromResidual` 知道 `?` 为何能在 `Option` 与 `Result` 间统一工作。
4. **边界设计**：在库/API 边界处选择错误类型、错误转换策略与可恢复性设计。

### 定理链

- **T-EH-1 错误传播单调性**：若函数返回 `Result<T, E>`，则内部 `?` 只会将 `Err` 向 `E` 转换，不会引入额外成功路径。
- **T-EH-2 `?` 早退等价性**：`expr?` 在语义上等价于一段展开后的 `match`，编译器保证控制流一致。
- **T-EH-3 边界封闭性**：良好的错误边界设计将领域错误封装在 crate/模块内部，对外暴露稳定、可操作的错误类型。

### 反向推理

- 要写出扁平、可维护的错误处理代码 ⟸ 应优先使用 `?` 而非嵌套 `match`。
- 要让调用方能够准确判断失败原因 ⟸ 需要在 API 边界定义精确的错误类型并实现 `From` 转换。

### 反命题

- ❌ “`?` 会隐藏错误处理逻辑” → `?` 只是 `match` 的语法糖，错误路径仍然显式返回，只是视觉噪声更少。
- ❌ “所有函数都应该返回 `Result`” → 不可恢复或不可能失败的场景应使用 `panic!` 或纯返回值，避免过度工程化。

> **过渡提示**：掌握控制流层面的错误处理后，可继续阅读 [Error Handling 深入](../../02_intermediate/03_error_handling/04_error_handling.md) 了解自定义错误类型、`Error` trait 与生态库实践。
