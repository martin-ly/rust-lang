# 宏卫生性深度解析

> **文档类型**: Tier 4 - 高级主题
> **难度**: ⭐⭐⭐⭐⭐ 专家
> **最后更新**: 2026-02-28

---

## 📋 目录

- [宏卫生性深度解析](#宏卫生性深度解析)
  - [📋 目录](#-目录)
  - [1. 什么是宏卫生性](#1-什么是宏卫生性)
  - [2. 语法上下文 (Syntax Context)](#2-语法上下文-syntax-context)
    - [2.1 核心概念](#21-核心概念)
    - [2.2 上下文标记](#22-上下文标记)
  - [3. 标识符分类](#3-标识符分类)
    - [3.1 绑定 (Binding)](#31-绑定-binding)
    - [3.2 引用 (Reference)](#32-引用-reference)
    - [3.3 标签 (Label)](#33-标签-label)
  - [4. 跨 Crate 卫生性](#4-跨-crate-卫生性)
    - [4.1 导出宏的卫生性](#41-导出宏的卫生性)
  - [5. 打破卫生性 (故意)](#5-打破卫生性-故意)
    - [5.1 使用 `Span::mixed_site()`](#51-使用-spanmixed_site)
    - [5.2 使用 `Span::call_site()`](#52-使用-spancall_site)
  - [6. 实现细节](#6-实现细节)
    - [6.1 Span ID 系统](#61-span-id-系统)
    - [6.2 标记 (Mark)](#62-标记-mark)
  - [7. 最佳实践](#7-最佳实践)
    - [7.1 保持卫生性](#71-保持卫生性)
    - [7.2 文档说明](#72-文档说明)
  - [**最后更新**: 2026-02-28](#最后更新-2026-02-28)

## 1. 什么是宏卫生性

宏卫生性（Hygiene）确保宏生成的代码不会意外捕获或干扰外部作用域的标识符。

```rust
// 卫生的宏 - 不会污染外部作用域
macro_rules! define_var {
    ($name:ident, $value:expr) => {
        let $name = $value;
    };
}

fn main() {
    define_var!(x, 42);  // 创建一个局部的 x
    println!("{}", x);    // ✅ 正常编译

    let x = 10;          // ✅ 可以重新定义，不冲突
}
```

---

## 2. 语法上下文 (Syntax Context)

### 2.1 核心概念

```text
标识符 = 符号名 + 语法上下文 ID

语法上下文 ID 决定标识符来自哪个作用域：
- 调用 site's 上下文
- 宏定义处的上下文
- 混合上下文
```

### 2.2 上下文标记

```rust
// 宏定义时的上下文
macro_rules! hygienic {
    () => {
        let x = 1;  // 标记为 "宏定义上下文"
    };
}

fn main() {
    hygienic!();   // 调用 site's 上下文与宏定义上下文分离
    let x = 2;     // 不同的语法上下文，不会冲突
}
```

---

## 3. 标识符分类

### 3.1 绑定 (Binding)

```rust
macro_rules! bind {
    ($name:ident) => {
        let $name = 42;  // $name 是绑定位置
    };
}

fn main() {
    bind!(x);          // x 绑定到宏内部的 let
    println!("{}", x); // ✅ 使用绑定的 x
}
```

### 3.2 引用 (Reference)

```rust
macro_rules! reference {
    ($name:ident) => {
        println!("{}", $name);  // $name 是引用位置
    };
}

fn main() {
    let y = 42;
    reference!(y);     // y 引用外部的绑定
}
```

### 3.3 标签 (Label)

```rust
macro_rules! with_label {
    ($label:lifetime) => {
        $label: loop { break $label; }
    };
}

fn main() {
    with_label!('outer);  // 标签也是卫生的
}
```

---

## 4. 跨 Crate 卫生性

### 4.1 导出宏的卫生性

```rust
// crate A: my_macros/src/lib.rs
#[macro_export]
macro_rules! export_hygienic {
    ($name:ident) => {
        let $name = "from macro";
    };
}

// crate B: user/Cargo.toml
// [dependencies]
// my_macros = "1.0"

// crate B: user/src/main.rs
use my_macros::export_hygienic;

fn main() {
    export_hygienic!(x);
    let x = "from main";  // ✅ 不冲突，卫生性跨 crate 保持
}
```

---

## 5. 打破卫生性 (故意)

### 5.1 使用 `Span::mixed_site()`

```rust
use proc_macro::Span;

#[proc_macro]
pub fn unhygienic(input: TokenStream) -> TokenStream {
    let mixed = Span::mixed_site();  // 混合上下文
    // ... 使用 mixed 创建标识符
    input
}
```

### 5.2 使用 `Span::call_site()`

```rust
use proc_macro::Span;

#[proc_macro]
pub fn call_site_example(input: TokenStream) -> TokenStream {
    let call_site = Span::call_site();  // 调用者的上下文
    // ... 使用 call_site 创建标识符
    input
}
```

---

## 6. 实现细节

### 6.1 Span ID 系统

```text
Span 结构:
- lo: BytePos (起始位置)
- hi: BytePos (结束位置)
- ctxt: SyntaxContext (语法上下文 ID)

SyntaxContext 结构:
- opaque: u32 (不透明上下文 ID)
- transparent: Vec<Mark> (透明标记链)
```

### 6.2 标记 (Mark)

```text
Mark 表示宏展开层级:
- Mark 0: 顶层（无宏）
- Mark 1: 第一次宏展开
- Mark 2: 第二次宏展开（嵌套宏）
...
```

---

## 7. 最佳实践

### 7.1 保持卫生性

```rust
// ✅ 好的做法：让标识符由调用者提供
macro_rules! with_callback {
    ($callback:ident) => {
        $callback(42);
    };
}

// ❌ 避免：宏内部硬编码标识符
macro_rules! bad_example {
    () => {
        let result = 42;  // 可能捕获外部 result
    };
}
```

### 7.2 文档说明

```rust
/// 此宏在内部创建变量，但保持卫生性
///
/// 生成的变量不会与外部作用域冲突
macro_rules! hygienic_macro {
    ($name:ident) => {
        let $name = /* ... */;
    };
}
```

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-02-28
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
