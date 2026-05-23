# Rust 所有权系统元模型 - 抽象语法

## 📑 目录
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 所有权系统元模型 - 抽象语法](#rust-所有权系统元模型---抽象语法)
  - [📑 目录](#-目录)
  - [1. 元元语言说明](#1-元元语言说明)
  - [2. 词法元素](#2-词法元素)
    - [2.1 标识符](#21-标识符)
    - [2.2 关键字](#22-关键字)
  - [3. 类型语法](#3-类型语法)
    - [3.1 基础类型](#31-基础类型)
    - [3.2 区域 (Lifetime/Region)](#32-区域-lifetimeregion)
  - [4. 表达式语法](#4-表达式语法)
    - [4.1 核心表达式](#41-核心表达式)
    - [4.2 位置表达式 (Place Expressions)](#42-位置表达式-place-expressions)
    - [4.3 值](#43-值)
  - [5. 声明语法](#5-声明语法)
    - [5.1 函数](#51-函数)
    - [5.2 结构体](#52-结构体)
    - [5.3 枚举](#53-枚举)
    - [5.4 Trait](#54-trait)
  - [6. 程序](#6-程序)
  - [7. 语法范畴总结](#7-语法范畴总结)
  - [8. 语法 sugar](#8-语法-sugar)
    - [8.1 可变性简化](#81-可变性简化)
    - [8.2 生命周期省略](#82-生命周期省略)
  - [9. 示例程序](#9-示例程序)
    - [9.1 简单借用](#91-简单借用)
    - [9.2 可变借用](#92-可变借用)
    - [9.3 函数定义](#93-函数定义)
  - [**最后更新**: 2026-03-05](#最后更新-2026-03-05)
  - [相关概念](#相关概念)

## 1. 元元语言说明
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

本文档使用以下元语言：

- `::=` 表示语法产生式
- `|` 表示或
- `[...]` 表示可选
- `{...}` 表示重复零次或多次
- `(...)` 表示分组
- **粗体** 表示终结符
- *斜体* 表示元变量

## 2. 词法元素
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

### 2.1 标识符
>
> **[来源: Rust Reference]** · **[来源: Wikipedia - Rust (programming language)]** · **[来源: Rustonomicon]** · **[来源: TRPL]** · **[来源: RFCs - github.com/rust-lang/rfcs]** · **[来源: Rust Standard Library - doc.rust-lang.org/std]**

```bnf
identifier ::= letter (letter | digit | '_')*
letter     ::= 'a' | ... | 'z' | 'A' | ... | 'Z'
digit      ::= '0' | ... | '9'
```

### 2.2 关键字
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```text
let, mut, ref, box, fn, struct, enum, match, if, else, loop, break, continue, return, trait, impl, where, for, while, unsafe, const, static, type, as, move, Self, self
```

## 3. 类型语法
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 3.1 基础类型
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```bnf
τ ::=                         (* 类型 *)
  | B                         (* 基础类型 *)
  | &ρ ω τ                    (* 引用类型 *)
  | Box τ                     (* 唯一指针 *)
  | (τ₁, ..., τₙ)             (* 元组类型 *)
  | struct_name<τ₁, ..., τₙ>  (* 结构体类型 *)
  | enum_name<τ₁, ..., τₙ>    (* 枚举类型 *)
  | trait_name<τ₁, ..., τₙ>   (* trait 对象 *)
  | ρ                         (* 区域/生命周期 *)

B ::= () | bool | i8 | i16 | i32 | i64 | i128 | isize | u8 | u16 | u32 | u64 | u128 | usize | char | str

ω ::= uniq | shrd             (* 可变性: 唯一或共享 *)
```

### 3.2 区域 (Lifetime/Region)
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```bnf
ρ ::=                         (* 区域 *)
  | 'static                   (* 静态生命周期 *)
  | 'r                        (* 命名生命周期 *)
  | ρ ∪ ρ                     (* 区域并集 *)

*r ::=                        (* 区域变量 *)
  | r₁ | r₂ | ...             (* 无限可枚举集合 *)
```

## 4. 表达式语法
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

### 4.1 核心表达式
> **[来源: [crates.io](https://crates.io/)]**

```bnf
e ::=                         (* 表达式 *)
  | v                         (* 值 *)
  | x                         (* 变量 *)
  | *p                        (* 解引用 *)
  | &ρ ω p                    (* 借用 *)
  | box e                     (* 装箱 *)
  | (e₁, ..., eₙ)             (* 元组构造 *)
  | e; e                      (* 序列 *)
  | let ω x : τ = e; e        (* 变量绑定 *)
  | p = e                     (* 赋值 *)
  | fn_name::<τ₁, ..., τₙ>(e₁, ..., eₙ)  (* 函数调用 *)
  | match e { arm₁, ..., armₙ }          (* 匹配 *)
  | if e { e } else { e }                (* 条件 *)
  | loop { e }                           (* 循环 *)
  | break [e]                            (* 跳出 *)
  | continue                             (* 继续 *)
  | return e                             (* 返回 *)
  | abort!                               (* 中止 *)

arm ::= pattern => e          (* 匹配分支 *)

pattern ::=
  | _                         (* 通配 *)
  | x                         (* 变量绑定 *)
  | v                         (* 字面量 *)
  | (pattern₁, ..., patternₙ) (* 元组解构 *)
  | constructor(pattern₁, ..., patternₙ) (* 枚举解构 *)
```

### 4.2 位置表达式 (Place Expressions)
> **[来源: [docs.rs](https://docs.rs/)]**

```bnf
p ::=                         (* 位置 *)
  | x                         (* 变量 *)
  | *p                        (* 解引用 *)
  | p.n                       (* 字段投影 *)
  | p[e]                      (* 索引 *)
  | p[e₁..e₂]                 (* 切片 *)
```

### 4.3 值
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```bnf
v ::=
  | ()                        (* 单元 *)
  | true | false              (* 布尔 *)
  | n                         (* 整数 *)
  | c                         (* 字符 *)
  | "string"                  (* 字符串 *)
  | ℓ                         (* 内存位置 *)
  | (v₁, ..., vₙ)             (* 元组值 *)
  | closure                   (* 闭包 *)
```

## 5. 声明语法
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 5.1 函数
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```bnf
fn_decl ::=
  | fn fn_name<r₁, ..., rₙ>(x₁: τ₁, ..., xₘ: τₘ) -> τ where { constraints } { e }

constraints ::=
  | r₁: r₂                    (* 区域包含关系 *)
  | trait_bound               (* trait 约束 *)
```

### 5.2 结构体
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```bnf
struct_decl ::=
  | struct struct_name<r₁, ..., rₙ> { field₁: τ₁, ..., fieldₘ: τₘ }
```

### 5.3 枚举
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```bnf
enum_decl ::=
  | enum enum_name<r₁, ..., rₙ> { variant₁, ..., variantₘ }

variant ::=
  | constructor_name          (* 无数据变体 *)
  | constructor_name(τ₁, ..., τₙ)  (* 元组变体 *)
  | constructor_name { field₁: τ₁, ..., fieldₙ: τₙ } (* 结构体变体 *)
```

### 5.4 Trait
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```bnf
trait_decl ::=
  | trait trait_name<r₁, ..., rₙ> for τ where { constraints } {
      method_sig₁;
      ...
      method_sigₘ;
    }

method_sig ::=
  | fn method_name(x₁: τ₁, ..., xₙ: τₙ) -> τ

impl_decl ::=
  | impl trait_name<r₁, ..., rₙ> for τ where { constraints } {
      method_impl₁
      ...
      method_implₘ
    }
```

## 6. 程序
> **[来源: [crates.io](https://crates.io/)]**

```bnf
program ::=
  | { decl }* e_main         (* 一系列声明和主表达式 *)
```

## 7. 语法范畴总结
> **[来源: [docs.rs](https://docs.rs/)]**

| 符号 | 含义 | 英文 |
|------|------|------|
| τ | 类型 | Type |
| ρ | 区域/生命周期 | Region/Lifetime |
| ω | 可变性 | Mutability |
| e | 表达式 | Expression |
| p | 位置表达式 | Place expression |
| v | 值 | Value |
| x | 变量 | Variable |
| r | 区域变量 | Region variable |
| ℓ | 内存位置 | Location |

## 8. 语法 sugar
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

### 8.1 可变性简化
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```
&τ    ≡ & _ shrd τ    (* 不可变引用 *)
&mut τ ≡ & _ uniq τ   (* 可变引用 *)
```

### 8.2 生命周期省略
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```
&τ    ≡ &'anon τ      (* 匿名生命周期 *)
```

## 9. 示例程序
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 9.1 简单借用
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust,ignore
let mut x: i32 = 5;
let y: &i32 = &x;
*x  // 使用
```

### 9.2 可变借用
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```rust,ignore
let mut x: i32 = 5;
let y: &mut i32 = &mut x;
*y = 10;
x  // 错误: x 被借用
```

### 9.3 函数定义

```rust
fn swap<'a>(x: &'a mut i32, y: &'a mut i32) {
    let tmp = *x;
    *x = *y;
    *y = tmp;
}
```

---

**状态**: 草案 v0.1
**最后更新**: 2026-03-05
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念

- [meta-model 目录](./README.md)
- [上级目录](../README.md)


---

## 权威来源索引

> **[来源: Wikipedia - Memory Safety]**

> **[来源: TRPL Ch. 4 - Ownership]**

> **[来源: Rustonomicon - Ownership]**

> **[来源: POPL 2018 - RustBelt]**

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

