# 🔧 Rust 宏系统速查卡

> **快速参考** | [完整文档](../../../crates/c11_macro_system/docs/) | [代码示例](../../../crates/c11_macro_system/examples/)
> **最后更新**: 2026-01-27 | **Rust 版本**: 1.93.0+ | **Edition**: 2024

---

## 📋 目录

- [🔧 Rust 宏系统速查卡](#-rust-宏系统速查卡)
  - [📋 目录](#-目录)
  - [🎯 核心概念](#-核心概念)
    - [声明宏 (macro\_rules!)](#声明宏-macro_rules)
    - [过程宏](#过程宏)
  - [📐 声明宏模式](#-声明宏模式)
    - [基本模式](#基本模式)
    - [片段类型](#片段类型)
  - [🔧 过程宏实现](#-过程宏实现)
    - [派生宏](#派生宏)
    - [属性宏](#属性宏)
  - [🎯 常见模式](#-常见模式)
    - [模式 1: 重复](#模式-1-重复)
    - [模式 2: 条件编译](#模式-2-条件编译)
  - [🚫 反例速查](#-反例速查)
    - [反例 1: 宏中重复求值](#反例-1-宏中重复求值)
    - [反例 2: 在宏中生成不完整代码](#反例-2-在宏中生成不完整代码)
  - [📚 相关文档](#-相关文档)
  - [🧩 相关示例代码](#-相关示例代码)
  - [🆕 Rust 1.93.0 宏系统改进](#-rust-1930-宏系统改进)
    - [`cfg` 属性在 `asm!` 行上](#cfg-属性在-asm-行上)
  - [Rust 1.92.0 宏系统改进（历史）](#rust-1920-宏系统改进历史)
    - [编译优化](#编译优化)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [相关速查卡](#相关速查卡)

---

## 🎯 核心概念

### 声明宏 (macro_rules!)

```rust
macro_rules! vec {
    ( $( $x:expr ),* ) => {
        {
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )*
            temp_vec
        }
    };
}
```

### 过程宏

```rust
// 派生宏
#[derive(Debug, Clone)]
struct MyStruct;

// 属性宏
#[route(GET, "/")]
fn handler() {}

// 函数式宏
println!("Hello, {}!", name);
```

---

## 📐 声明宏模式

### 基本模式

```rust
macro_rules! my_macro {
    // 匹配单个表达式
    ($x:expr) => { $x };

    // 匹配多个表达式
    ($($x:expr),*) => {
        vec![$($x),*]
    };

    // 匹配标识符
    ($name:ident) => {
        let $name = 42;
    };
}
```

### 片段类型

```rust
// expr: 表达式
// ident: 标识符
// ty: 类型
// path: 路径
// pat: 模式
// stmt: 语句
// block: 代码块
// item: 项
// meta: 元数据
// tt: 标记树
```

---

## 🔧 过程宏实现

### 派生宏

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let expanded = quote! {
        impl #name {
            fn hello() {
                println!("Hello from {}", stringify!(#name));
            }
        }
    };

    TokenStream::from(expanded)
}
```

### 属性宏

```rust
#[proc_macro_attribute]
pub fn my_attr(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // 处理属性宏
    item
}
```

---

## 🎯 常见模式

### 模式 1: 重复

```rust
macro_rules! repeat {
    ($($item:expr),+ $(,)?) => {
        {
            let mut v = Vec::new();
            $(
                v.push($item);
            )+
            v
        }
    };
}
```

### 模式 2: 条件编译

```rust
#[cfg(target_os = "windows")]
macro_rules! platform_specific {
    () => { "Windows" };
}

#[cfg(target_os = "linux")]
macro_rules! platform_specific {
    () => { "Linux" };
}
```

---

## 🚫 反例速查

### 反例 1: 宏中重复求值

**错误示例**:

```rust
macro_rules! bad {
    ($e:expr) => { $e + $e };
}
bad!(expensive_func());  // ❌ expensive_func() 被调用两次
```

**原因**: 宏按字面展开，表达式会重复求值。

**修正**:

```rust
macro_rules! good {
    ($e:expr) => { { let x = $e; x + x } };
}
```

---

### 反例 2: 在宏中生成不完整代码

**错误示例**:

```rust
macro_rules! bad {
    () => { fn foo() };  // ❌ 缺少函数体
}
```

**原因**: 宏展开后代码必须完整、合法。

**修正**:

```rust
macro_rules! good {
    () => { fn foo() {} };
}
```

---

## 📚 相关文档

- [宏系统完整文档](../../../crates/c11_macro_system/docs/)
- [宏系统 README](../../../crates/c11_macro_system/README.md)

## 🧩 相关示例代码

以下示例位于 `crates/c11_macro_system/examples/`，可直接运行（例如：`cargo run -p c11_macro_system --example 01_macro_rules_basics`）。

- [声明宏基础](../../../crates/c11_macro_system/examples/01_macro_rules_basics.rs)
- [模式匹配](../../../crates/c11_macro_system/examples/02_pattern_matching.rs)
- [重复语法](../../../crates/c11_macro_system/examples/03_repetition.rs)
- [递归宏](../../../crates/c11_macro_system/examples/04_recursive_macros.rs)
- [Rust 1.91 特性演示](../../../crates/c11_macro_system/examples/rust_191_features_demo.rs)
- [Rust 1.92 特性演示](../../../crates/c11_macro_system/examples/rust_192_features_demo.rs)

---

## 🆕 Rust 1.93.0 宏系统改进

### `cfg` 属性在 `asm!` 行上

**改进**: 可以在内联汇编的单个语句上使用条件编译

```rust
// Rust 1.93.0 新特性
unsafe fn platform_specific() {
    asm!(
        "mov eax, 1",
        // ✅ 1.93: 可以在单个语句上使用 cfg
        #[cfg(target_feature = "sse2")]
        "movaps xmm0, xmm1",
        #[cfg(not(target_feature = "sse2"))]
        "nop",
    );
}
```

**影响**: 简化条件编译的内联汇编代码

---

## Rust 1.92.0 宏系统改进（历史）

### 编译优化

**改进**: 宏展开性能优化，更好的错误诊断

```rust
// Rust 1.92.0 优化后的宏展开
macro_rules! my_macro {
    ($x:expr) => {
        // ✅ 更快的宏展开
        // ✅ 更好的错误定位
        println!("{}", $x);
    };
}
```

**影响**:

- 宏展开性能提升
- 更好的错误诊断
- 编译时间优化

---

## 📚 相关资源

### 官方文档

- [Rust 宏文档](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)
- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)

### 项目内部文档

- [宏系统完整文档](../../../crates/c11_macro_system/docs/)
- [宏系统研究笔记](../../research_notes/)

### 相关速查卡

- [类型系统速查卡](./type_system.md) - 宏与类型系统
- [泛型编程速查卡](./generics_cheatsheet.md) - 宏与泛型
- [模块系统速查卡](./modules_cheatsheet.md) - 宏在模块中的使用
- [测试速查卡](./testing_cheatsheet.md) - 测试宏

---

**最后更新**: 2026-01-27
**Rust 版本**: 1.93.0+ (Edition 2024)
