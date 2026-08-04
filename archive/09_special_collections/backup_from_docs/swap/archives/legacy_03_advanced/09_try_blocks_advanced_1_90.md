# 09. try 块进阶 (Try Blocks Advanced - Rust 1.90)

> **文档类型**：高级  
> **难度等级**：⭐⭐⭐⭐  
> **预计阅读时间**：1小时  
> **前置知识**：Result 类型、? 运算符、错误处理

## 📊 目录

- [09. try 块进阶 (Try Blocks Advanced - Rust 1.90)](#09-try-块进阶-try-blocks-advanced---rust-190)
  - [📊 目录](#-目录)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录-1)
  - [9.1. 将一段逻辑变成表达式](#91-将一段逻辑变成表达式)
  - [在表达式位置做错误映射](#在表达式位置做错误映射)
  - [Option 与 Result 混用](#option-与-result-混用)
  - [建议](#建议)

## 📖 内容概述

本文档深入讲解 `try { ... }` 表达式在复杂错误组合中的使用，包括本地化错误传播、细粒度映射，以及与 ?、Option/Result、自定义错误类型的协作。

## 🎯 学习目标

完成本文档学习后，你将能够：

- [ ] 使用 try 块简化错误处理逻辑
- [ ] 本地化错误传播范围
- [ ] 组合 Option 和 Result
- [ ] 实现细粒度错误映射
- [ ] 设计优雅的错误处理流程

## 📚 目录

- [09. try 块进阶 (Try Blocks Advanced - Rust 1.90)](#09-try-块进阶-try-blocks-advanced---rust-190)
  - [📊 目录](#-目录)
  - [📖 内容概述](#-内容概述)
  - [🎯 学习目标](#-学习目标)
  - [📚 目录](#-目录-1)
  - [9.1. 将一段逻辑变成表达式](#91-将一段逻辑变成表达式)
  - [在表达式位置做错误映射](#在表达式位置做错误映射)
  - [Option 与 Result 混用](#option-与-result-混用)
  - [建议](#建议)

---

## 9.1. 将一段逻辑变成表达式

```rust
fn sum2(a: Result<i32, &'static str>, b: Result<i32, &'static str>) -> Result<i32, &'static str> {
    let s: Result<i32, _> = try { a? + b? };
    s
}
```

## 在表达式位置做错误映射

```rust
#[derive(Debug, PartialEq)]
enum AppErr { Parse, Io }

fn parse_num(s: &str) -> Result<i32, AppErr> {
    s.parse::<i32>().map_err(|_| AppErr::Parse)
}

fn add_from_str(x: &str, y: &str) -> Result<i32, AppErr> {
    // try 块使得我们可以在一处完成 ? 传播并整体 map_err
    try { parse_num(x)? + parse_num(y)? }
}
```

## Option 与 Result 混用

```rust
fn head_plus_parsed(rest: &[&str]) -> Option<i32> {
    let v: Option<i32> = try {
        let s = *rest.get(0)?;
        let n = s.parse::<i32>().ok()?;
        n
    };
    v
}
```

## 建议

- 在复杂表达式中使用 `try` 收拢局部错误传播，减少临时变量；
- 与 `map_err`/自定义错误枚举配合，清晰表达边界；
- 对外接口维持稳定的错误类型，内部自由组合。
