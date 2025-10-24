# 宏展开机制

> **文档定位**: 深入理解Rust宏的展开过程  
> **难度级别**: ⭐⭐ 进阶  
> **预计时间**: 3小时  
> **最后更新**: 2025-10-20

---


## 📊 目录

- [📋 学习目标](#学习目标)
- [1. 宏展开概述](#1-宏展开概述)
  - [1.1 编译流程中的宏](#11-编译流程中的宏)
  - [1.2 展开顺序](#12-展开顺序)
- [2. Token和TokenStream](#2-token和tokenstream)
  - [2.1 什么是Token?](#21-什么是token)
  - [2.2 TokenStream](#22-tokenstream)
  - [2.3 TokenTree](#23-tokentree)
- [3. 声明宏的展开](#3-声明宏的展开)
  - [3.1 模式匹配过程](#31-模式匹配过程)
  - [3.2 重复展开](#32-重复展开)
- [4. 过程宏的展开](#4-过程宏的展开)
  - [4.1 过程宏工作流程](#41-过程宏工作流程)
  - [4.2 派生宏展开示例](#42-派生宏展开示例)
- [5. 展开时机](#5-展开时机)
  - [5.1 早期展开 (Early Expansion)](#51-早期展开-early-expansion)
  - [5.2 正常展开 (Normal Expansion)](#52-正常展开-normal-expansion)
  - [5.3 延迟展开 (Lazy Expansion)](#53-延迟展开-lazy-expansion)
- [6. 递归展开](#6-递归展开)
  - [6.1 宏递归限制](#61-宏递归限制)
  - [6.2 递归展开过程](#62-递归展开过程)
- [7. 查看宏展开](#7-查看宏展开)
  - [7.1 使用cargo-expand](#71-使用cargo-expand)
  - [7.2 使用trace_macros](#72-使用trace_macros)
  - [7.3 使用log_syntax](#73-使用log_syntax)
- [8. 展开错误调试](#8-展开错误调试)
  - [8.1 常见错误类型](#81-常见错误类型)
    - [错误1: 模式不匹配](#错误1-模式不匹配)
    - [错误2: 递归深度超限](#错误2-递归深度超限)
  - [8.2 调试技巧](#82-调试技巧)
    - [技巧1: 逐步展开](#技巧1-逐步展开)
    - [技巧2: 打印中间结果](#技巧2-打印中间结果)
- [9. 性能考量](#9-性能考量)
  - [9.1 编译时间影响](#91-编译时间影响)
  - [9.2 运行时性能](#92-运行时性能)
- [10. 高级展开模式](#10-高级展开模式)
  - [10.1 TT Muncher模式](#101-tt-muncher模式)
  - [10.2 Push-down Accumulation](#102-push-down-accumulation)
  - [10.3 Internal Rules](#103-internal-rules)
- [📚 总结](#总结)
  - [关键要点](#关键要点)
  - [展开流程图](#展开流程图)
  - [下一步](#下一步)


## 📋 学习目标

完成本章后，你将能够：

- ✅ 理解宏展开的完整流程
- ✅ 掌握Token和TokenStream的概念
- ✅ 了解宏展开的时机和顺序
- ✅ 使用工具查看宏展开结果
- ✅ 调试宏展开问题

---

## 1. 宏展开概述

### 1.1 编译流程中的宏

```text
┌─────────────┐
│  源代码.rs  │
└──────┬──────┘
       ↓
┌──────────────┐
│ 词法分析     │  → Token流
│ (Lexing)     │
└──────┬───────┘
       ↓
┌──────────────┐
│ 语法分析     │  → 抽象语法树(AST)
│ (Parsing)    │
└──────┬───────┘
       ↓
┌──────────────┐
│ 宏展开 ⭐    │  ← 宏在这里工作
│ (Expansion)  │
└──────┬───────┘
       ↓
┌──────────────┐
│ 名称解析     │
│ (Resolution) │
└──────┬───────┘
       ↓
┌──────────────┐
│ 类型检查     │
│ (Type Check) │
└──────┬───────┘
       ↓
┌──────────────┐
│ 代码生成     │  → 机器码
│ (Codegen)    │
└──────────────┘
```

### 1.2 展开顺序

宏按照**自外向内、深度优先**的顺序展开：

```rust
// 示例
let v = vec![1, format!("{}", 2), 3];

// 展开顺序:
// 1. 先展开 format!("{}", 2)
// 2. 然后展开 vec![...]
```

---

## 2. Token和TokenStream

### 2.1 什么是Token?

**Token**是代码的最小语法单位：

```rust
let x = 42;

// 被解析为Token:
// let    - 关键字token
// x      - 标识符token
// =      - 符号token
// 42     - 字面量token
// ;      - 符号token
```

### 2.2 TokenStream

**TokenStream**是Token的序列：

```rust
// 这段代码
fn main() {}

// 表示为TokenStream:
[
    Ident("fn"),
    Ident("main"),
    Group(Parenthesis, []),
    Group(Brace, [])
]
```

### 2.3 TokenTree

TokenTree是Token的树状结构：

```rust
pub enum TokenTree {
    Group(Group),         // 括号组: (), {}, []
    Ident(Ident),        // 标识符: foo, bar
    Punct(Punct),        // 标点: +, -, *
    Literal(Literal),    // 字面量: 42, "text"
}
```

---

## 3. 声明宏的展开

### 3.1 模式匹配过程

```rust
macro_rules! my_macro {
    // 规则1
    () => { println!("No args"); };
    // 规则2
    ($x:expr) => { println!("One arg: {}", $x); };
    // 规则3
    ($x:expr, $y:expr) => { println!("Two args: {} {}", $x, $y); };
}

my_macro!(42);
```

**展开步骤**:

1. **匹配**: 尝试每个规则，直到找到匹配的
2. **绑定**: 将输入绑定到模式变量 (`$x` = 42)
3. **替换**: 用绑定的值替换模板中的变量
4. **生成**: 产生新的TokenStream

```text
输入: my_macro!(42)
  ↓
匹配规则2: ($x:expr)
  ↓
绑定: $x = 42
  ↓
替换: println!("One arg: {}", 42)
  ↓
输出TokenStream
```

### 3.2 重复展开

```rust
macro_rules! print_all {
    ($($x:expr),*) => {
        $(println!("{}", $x);)*
    };
}

print_all!(1, 2, 3);
```

**展开过程**:

```text
输入: print_all!(1, 2, 3)
  ↓
匹配: $($x:expr),*
绑定: $x = [1, 2, 3]  (重复3次)
  ↓
展开重复模板3次:
  println!("{}", 1);
  println!("{}", 2);
  println!("{}", 3);
```

---

## 4. 过程宏的展开

### 4.1 过程宏工作流程

```rust
#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // 1. 接收TokenStream
    // 2. 解析为AST (使用syn)
    // 3. 处理和转换
    // 4. 生成新的TokenStream (使用quote)
    // 5. 返回
}
```

**详细步骤**:

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyTrait)]
pub fn derive_my_trait(input: TokenStream) -> TokenStream {
    // 步骤1: 解析输入
    let ast = parse_macro_input!(input as DeriveInput);
    
    // 步骤2: 提取信息
    let name = &ast.ident;
    
    // 步骤3: 生成代码
    let expanded = quote! {
        impl MyTrait for #name {
            fn method(&self) {
                println!("MyTrait for {}", stringify!(#name));
            }
        }
    };
    
    // 步骤4: 返回TokenStream
    TokenStream::from(expanded)
}
```

### 4.2 派生宏展开示例

```rust
// 源代码
#[derive(Debug)]
struct Point {
    x: i32,
    y: i32,
}

// 展开后（简化）
struct Point {
    x: i32,
    y: i32,
}

impl std::fmt::Debug for Point {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct("Point")
            .field("x", &self.x)
            .field("y", &self.y)
            .finish()
    }
}
```

---

## 5. 展开时机

### 5.1 早期展开 (Early Expansion)

某些宏在**名称解析前**展开：

```rust
// cfg属性在很早期展开
#[cfg(target_os = "linux")]
fn linux_only() { }
```

### 5.2 正常展开 (Normal Expansion)

大多数宏在**语法分析后、名称解析前**展开：

```rust
// 标准宏
let v = vec![1, 2, 3];
```

### 5.3 延迟展开 (Lazy Expansion)

某些情况下宏展开会延迟：

```rust
// 类型相关的宏可能延迟到类型检查时
```

---

## 6. 递归展开

### 6.1 宏递归限制

Rust限制宏递归深度（默认128层）：

```rust
#![recursion_limit = "256"]  // 增加限制

macro_rules! deep_recursion {
    (0) => { 0 };
    ($n:expr) => {
        1 + deep_recursion!($n - 1)
    };
}
```

### 6.2 递归展开过程

```rust
macro_rules! count {
    () => { 0 };
    ($x:expr, $($rest:expr),*) => {
        1 + count!($($rest),*)
    };
}

// count!(1, 2, 3) 的展开:
count!(1, 2, 3)
  ↓
1 + count!(2, 3)
  ↓
1 + (1 + count!(3))
  ↓
1 + (1 + (1 + count!()))
  ↓
1 + (1 + (1 + 0))
  ↓
3
```

---

## 7. 查看宏展开

### 7.1 使用cargo-expand

**安装**:

```bash
cargo install cargo-expand
```

**使用**:

```bash
# 展开整个crate
cargo expand

# 展开特定模块
cargo expand module_name

# 展开示例
cargo expand --example my_example

# 展开并高亮语法
cargo expand --color always
```

**示例输出**:

```rust
// 原始代码
let v = vec![1, 2, 3];

// cargo expand 输出
let v = {
    let mut temp_vec = Vec::new();
    temp_vec.push(1);
    temp_vec.push(2);
    temp_vec.push(3);
    temp_vec
};
```

### 7.2 使用trace_macros

```rust
#![feature(trace_macros)]

fn main() {
    trace_macros!(true);
    let v = vec![1, 2, 3];
    trace_macros!(false);
}
```

**输出**:

```text
note: trace_macro
 --> src/main.rs:5:13
  |
5 |     let v = vec![1, 2, 3];
  |             ^^^^^^^^^^^^^^
  |
  = note: expanding `vec! { 1 , 2 , 3 }`
  = note: to `{ ... }`
```

### 7.3 使用log_syntax

```rust
#![feature(log_syntax)]

macro_rules! debug_macro {
    ($($arg:tt)*) => {
        log_syntax!($($arg)*);
    };
}
```

---

## 8. 展开错误调试

### 8.1 常见错误类型

#### 错误1: 模式不匹配

```rust
macro_rules! my_macro {
    ($x:expr, $y:expr) => { $x + $y };
}

// my_macro!(1);  // ❌ 模式不匹配
```

**调试**: 使用`cargo expand`查看

#### 错误2: 递归深度超限

```rust
macro_rules! infinite {
    () => { infinite!() };
}

// infinite!();  // ❌ recursion limit reached
```

**解决**: 增加`recursion_limit`或重写逻辑

### 8.2 调试技巧

#### 技巧1: 逐步展开

```rust
macro_rules! debug_expand {
    ($($arg:tt)*) => {
        compile_error!(stringify!($($arg)*));
    };
}

// 查看宏接收到什么
// debug_expand!(my_complex_input);
```

#### 技巧2: 打印中间结果

```rust
#[proc_macro]
pub fn debug_proc_macro(input: TokenStream) -> TokenStream {
    eprintln!("Input: {}", input);  // 编译时打印
    input
}
```

---

## 9. 性能考量

### 9.1 编译时间影响

```rust
// 简单宏 - 快速展开
macro_rules! simple {
    ($x:expr) => { $x };
}

// 复杂宏 - 慢速展开
macro_rules! complex {
    // ... 大量递归和模式匹配
}
```

**优化建议**:

- ✅ 减少递归深度
- ✅ 简化模式匹配
- ✅ 使用过程宏处理复杂逻辑

### 9.2 运行时性能

宏展开后的代码性能：

```rust
// 宏 - 零开销（内联）
macro_rules! square {
    ($x:expr) => { $x * $x };
}
let result = square!(5);  // 直接展开为 5 * 5

// 函数 - 可能有调用开销
fn square(x: i32) -> i32 { x * x }
let result = square(5);   // 函数调用
```

---

## 10. 高级展开模式

### 10.1 TT Muncher模式

逐个处理Token：

```rust
macro_rules! tt_muncher {
    () => { 0 };
    (_ $($tail:tt)*) => { 1 + tt_muncher!($($tail)*) };
}

tt_muncher!(_ _ _ _ _);  // 输出: 5
```

### 10.2 Push-down Accumulation

累积结果：

```rust
macro_rules! reverse {
    ([$($rev:tt)*] [$($first:tt),*]) => {
        vec![$($rev),*]
    };
    ([$($rev:tt)*] $first:tt $(, $rest:tt)*) => {
        reverse!([$first $($rev)*] $($rest),*)
    };
}
```

### 10.3 Internal Rules

内部辅助规则：

```rust
macro_rules! public_macro {
    ($($arg:tt)*) => {
        public_macro!(@internal $($arg)*)
    };
    (@internal $($arg:tt)*) => {
        // 实际实现
    };
}
```

---

## 📚 总结

### 关键要点

1. **宏在AST构建后展开** - 在名称解析和类型检查之前
2. **Token是基本单位** - 宏操作TokenStream
3. **自外向内展开** - 深度优先顺序
4. **使用cargo-expand调试** - 查看展开结果
5. **注意递归限制** - 默认128层

### 展开流程图

```text
源代码
  ↓
Lexing → TokenStream
  ↓
Parsing → AST
  ↓
宏展开 → 新的AST
  ↓
名称解析
  ↓
类型检查
  ↓
代码生成
```

### 下一步

- 📖 学习 [宏理论深度](./04_macro_theory.md)
- 📖 实践 [递归宏](../02_declarative/05_recursive_macros.md)
- 💻 运行: `cargo expand --example 04_recursive_macros`

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT
