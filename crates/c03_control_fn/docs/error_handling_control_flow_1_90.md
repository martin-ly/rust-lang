# 错误处理控制流（覆盖至 Rust 1.90）

## 📊 目录

- [错误处理控制流（覆盖至 Rust 1.90）](#错误处理控制流覆盖至-rust-190)
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
