# 📖 C14宏系统 - 术语表

> **文档定位**: Rust宏系统核心概念和术语定义  
> **最后更新**: 2025-10-20

---

## 📊 目录

- [📖 C14宏系统 - 术语表](#-c14宏系统---术语表)
  - [📊 目录](#-目录)
  - [A](#a)
    - [AST (Abstract Syntax Tree)](#ast-abstract-syntax-tree)
  - [C](#c)
    - [Crate](#crate)
  - [D](#d)
    - [Declarative Macro](#declarative-macro)
    - [Derive Macro](#derive-macro)
    - [DSL (Domain Specific Language)](#dsl-domain-specific-language)
  - [E](#e)
    - [Expansion](#expansion)
    - [`expr`](#expr)
  - [F](#f)
    - [Fragment Specifier](#fragment-specifier)
    - [Function-like Macro](#function-like-macro)
  - [H](#h)
    - [Hygiene](#hygiene)
  - [I](#i)
    - [`ident`](#ident)
  - [M](#m)
    - [`macro_rules!`](#macro_rules)
    - [`#[macro_export]`](#macro_export)
    - [Metaprogramming](#metaprogramming)
  - [P](#p)
    - [Pattern Matching](#pattern-matching)
    - [Procedural Macro](#procedural-macro)
    - [`proc-macro`](#proc-macro)
  - [Q](#q)
    - [`quote`](#quote)
  - [R](#r)
    - [Recursion](#recursion)
    - [Repetition](#repetition)
  - [S](#s)
    - [`syn`](#syn)
  - [T](#t)
    - [Token](#token)
    - [TokenStream](#tokenstream)
    - [`tt` (Token Tree)](#tt-token-tree)
    - [`ty`](#ty)
  - [符号](#符号)
    - [`$` {#dollar}](#-dollar)
    - [`$(...)*` {#dollarzero-or-more}](#-dollarzero-or-more)
    - [`$(...)+` {#dollarone-or-more}](#-dollarone-or-more)
    - [`$(...)?` {#dollarzero-or-one}](#-dollarzero-or-one)
    - [`$(,)?` {#dollaroptional-trailing-comma}](#-dollaroptional-trailing-comma)
  - [相关工具](#相关工具)
    - [cargo-expand](#cargo-expand)
    - [rust-analyzer](#rust-analyzer)
    - [trybuild](#trybuild)
  - [片段指定符完整列表](#片段指定符完整列表)
  - [相关文档](#相关文档)

## A

### AST (Abstract Syntax Tree)

**抽象语法树** - 源代码的树状表示，过程宏通过操作AST来生成代码。

---

## C

### Crate

**包** - 宏可以在同一crate内使用，或通过`#[macro_export]`导出给其他crate使用。

---

## D

### Declarative Macro

**声明宏** - 使用`macro_rules!`定义的模式匹配宏，也称为"macro by example"。

```rust
macro_rules! vec_of_strings {
    ($($x:expr),*) => { vec![$($x.to_string()),*] };
}
```

### Derive Macro

**派生宏** - 过程宏的一种，用于自动实现trait。

```rust
#[derive(Debug, Clone)]
struct Point { x: i32, y: i32 }
```

### DSL (Domain Specific Language)

**领域特定语言** - 针对特定问题域设计的语言，可以使用宏实现。

---

## E

### Expansion

**宏展开** - 编译器将宏调用替换为实际代码的过程。

### `expr`

**表达式片段指定符** - 在宏模式中匹配任意Rust表达式。

```rust
macro_rules! double {
    ($x:expr) => { $x * 2 };
}
```

---

## F

### Fragment Specifier

**片段指定符** - 在宏模式中指定可以匹配的语法类型，如`expr`、`ident`、`ty`等。

### Function-like Macro

**函数式宏** - 过程宏的一种，看起来像函数调用。

```rust
let query = sql!("SELECT * FROM users");
```

---

## H

### Hygiene

**卫生性** - 宏的一个特性，确保宏内部定义的标识符不会与外部冲突。

```rust
macro_rules! define_x {
    () => { let x = 42; };  // 这个x不影响外部
}
```

---

## I

### `ident`

**标识符片段指定符** - 匹配Rust标识符（变量名、函数名等）。

```rust
macro_rules! create_fn {
    ($name:ident) => {
        fn $name() { }
    };
}
```

---

## M

### `macro_rules!`

**声明宏定义** - 定义声明宏的关键字。

```rust
macro_rules! my_macro {
    () => { ... };
}
```

### `#[macro_export]`

**宏导出属性** - 使宏可以被其他crate使用。

```rust
#[macro_export]
macro_rules! public_macro {
    () => { ... };
}
```

### Metaprogramming

**元编程** - 编写能够生成或操作其他程序的程序，宏是Rust的元编程工具。

---

## P

### Pattern Matching

**模式匹配** - 声明宏通过模式匹配来选择不同的展开规则。

```rust
macro_rules! calc {
    (add $a:expr, $b:expr) => { $a + $b };
    (sub $a:expr, $b:expr) => { $a - $b };
}
```

### Procedural Macro

**过程宏** - 使用Rust代码编写的宏，有三种类型：派生宏、属性宏、函数式宏。

### `proc-macro`

**过程宏crate类型** - 专门用于定义过程宏的crate类型。

```toml
[lib]
proc-macro = true
```

---

## Q

### `quote`

**代码生成库** - 用于在过程宏中生成Rust代码的库。

```rust
use quote::quote;
let code = quote! {
    fn hello() { println!("Hello"); }
};
```

---

## R

### Recursion

**递归** - 宏可以递归调用自己来处理重复的模式。

```rust
macro_rules! count {
    () => { 0 };
    ($x:expr, $($rest:expr),*) => {
        1 + count!($($rest),*)
    };
}
```

### Repetition

**重复** - 使用`$(...)*`或`$(...)+`语法来处理可变数量的输入。

```rust
macro_rules! vec_of_strings {
    ($($x:expr),*) => {  // 0个或多个
        vec![$($x.to_string()),*]
    };
}
```

---

## S

### `syn`

**语法解析库** - 用于在过程宏中解析Rust语法的库。

```rust
use syn::{parse_macro_input, DeriveInput};
let ast = parse_macro_input!(input as DeriveInput);
```

---

## T

### Token

**词法单元** - Rust代码的最小语法单位，如标识符、关键字、符号等。

### TokenStream

**Token流** - Token的序列，是过程宏的输入和输出类型。

```rust
use proc_macro::TokenStream;

#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // ...
}
```

### `tt` (Token Tree)

**Token树片段指定符** - 可以匹配任意单个token或用括号括起来的token序列。

```rust
macro_rules! accept_anything {
    ($($tt:tt)*) => { };  // 接受任意token
}
```

### `ty`

**类型片段指定符** - 匹配Rust类型。

```rust
macro_rules! make_struct {
    ($name:ident, $ty:ty) => {
        struct $name { value: $ty }
    };
}
```

---

## 符号

### `$` {#dollar}

**变量前缀** - 在宏中标记变量和重复模式。

### `$(...)*` {#dollarzero-or-more}

**零个或多个重复** - 匹配零个或多个重复的模式。

### `$(...)+` {#dollarone-or-more}

**一个或多个重复** - 匹配至少一个重复的模式。

### `$(...)?` {#dollarzero-or-one}

**零个或一个** - 匹配可选的模式。

### `$(,)?` {#dollaroptional-trailing-comma}

**可选的尾随逗号** - 允许但不要求尾随逗号。

```rust
macro_rules! vec_of_strings {
    ($($x:expr),* $(,)?) => {  // 允许尾随逗号
        vec![$($x.to_string()),*]
    };
}
```

---

## 相关工具

### cargo-expand

**宏展开工具** - 查看宏展开后的代码。

```bash
cargo install cargo-expand
cargo expand
```

### rust-analyzer

**Rust语言服务器** - 提供IDE功能，包括宏展开提示。

### trybuild

**编译测试框架** - 用于测试过程宏的编译行为。

```rust
#[test]
fn test_proc_macro() {
    let t = trybuild::TestCases::new();
    t.pass("tests/pass/*.rs");
}
```

---

## 片段指定符完整列表

| 指定符 | 匹配内容 | 示例 |
|--------|---------|------|
| `item` | 项（函数、结构体等） | `fn foo() {}` |
| `block` | 代码块 | `{ let x = 1; }` |
| `stmt` | 语句 | `let x = 1;` |
| `pat` | 模式 | `Some(x)` |
| `expr` | 表达式 | `1 + 2` |
| `ty` | 类型 | `Vec<i32>` |
| `ident` | 标识符 | `foo` |
| `path` | 路径 | `std::vec::Vec` |
| `tt` | Token树 | `(a b c)` |
| `meta` | 属性内容 | `derive(Debug)` |
| `lifetime` | 生命周期 | `'a` |
| `vis` | 可见性 | `pub` |
| `literal` | 字面量 | `42`, `"text"` |

---

## 相关文档

- [主索引](./00_MASTER_INDEX.md) - 完整学习导航
- [FAQ](./FAQ.md) - 常见问题解答
- [README](../README.md) - 模块概述

---

**最后更新**: 2025-10-20  
**维护者**: Rust学习社区

有术语补充或修正？欢迎贡献！
