# C11: Rust 宏系统 — 过程宏 (Procedural Macros)

> **配套 crate**: [c11_macro_system](../c11_macro_system/) 的过程宏实现

## 概述

本 crate 为 `c11_macro_system` 学习模块提供过程宏（Procedural Macro）示例，包括：

- **派生宏 (Derive Macros)**: 自定义 `derive` 属性
- **属性宏 (Attribute Macros)**: 自定义函数/结构体属性
- **函数式宏 (Function-like Macros)**: 类似 `macro_rules!` 但基于过程宏

## 依赖

- `proc-macro2`: Token 流处理
- `quote`: 代码生成
- `syn`: Rust 语法解析

## 使用方式

```rust
use c11_macro_system_proc::MyDerive;

#[derive(MyDerive)]
struct MyStruct {
    field: i32,
}
```

## 文档

详细文档请参阅 [c11_macro_system](../c11_macro_system/)。

## [来源: Rust Reference / Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)
