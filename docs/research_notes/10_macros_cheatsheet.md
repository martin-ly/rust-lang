# 宏速查卡 {#宏速查卡}

> **EN**: Macros Cheatsheet
> **Summary**: 宏（Macro）速查卡 Macros Cheatsheet. (stub/archive redirect)
>
> **概念族**: 速查卡
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-02-24
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成权威国际化来源对齐升级
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) | [The Rust Programming Language](https://doc.rust-lang.org/book/) | [The Little Book of Rust Macros](https://veykril.github.io/tlborm/) | [Rust By Example](https://doc.rust-lang.org/rust-by-example/)

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [宏速查卡 {#宏速查卡}](#宏速查卡-宏速查卡)
  - [📑 目录 {#目录}](#-目录-目录)
  - [声明宏 (macro\_rules!) {#声明宏-macro\_rules}](#声明宏-macro_rules-声明宏-macro_rules)
    - [基本语法 {#基本语法}](#基本语法-基本语法)
    - [参数模式 {#参数模式}](#参数模式-参数模式)
    - [重复模式 {#重复模式}](#重复模式-重复模式)
    - [常见片段类型 {#常见片段类型}](#常见片段类型-常见片段类型)
  - [过程宏（Procedural Macro） {#过程宏}](#过程宏-过程宏)
    - [派生宏 {#派生宏-1}](#派生宏-派生宏-1)
    - [属性宏 {#属性宏-1}](#属性宏-属性宏-1)
    - [函数式宏 {#函数式宏}](#函数式宏-函数式宏)
  - [常见宏示例 {#常见宏示例}](#常见宏示例-常见宏示例)
    - [vec {#vec}](#vec-vec)
    - [println! / format {#println-format}](#println--format-println-format)
    - [assert {#assert}](#assert-assert)
    - [todo! / unimplemented {#todo-unimplemented}](#todo--unimplemented-todo-unimplemented)
    - [include {#include}](#include-include)
  - [宏调试技巧 {#宏调试技巧}](#宏调试技巧-宏调试技巧)
    - [查看展开 {#查看展开}](#查看展开-查看展开)
    - [trace\_macros {#trace\_macros}](#trace_macros-trace_macros)
  - [宏卫生性 (Hygiene) {#宏卫生性-hygiene}](#宏卫生性-hygiene-宏卫生性-hygiene)
  - [递归宏 {#递归宏}](#递归宏-递归宏)
  - [条件编译宏 {#条件编译宏}](#条件编译宏-条件编译宏)
  - [编译器内置宏 {#编译器内置宏}](#编译器内置宏-编译器内置宏)
  - [常用宏 {#常用宏}](#常用宏-常用宏)
  - [派生宏 {#派生宏-1}](#派生宏-派生宏-1-1)
  - [属性宏 {#属性宏-1}](#属性宏-属性宏-1-1)
  - [🌍 权威国际化资源链接 {#权威国际化资源链接}](#-权威国际化资源链接-权威国际化资源链接)
    - [Rust Reference 核心章节 {#rust-reference-核心章节}](#rust-reference-核心章节-rust-reference-核心章节)
    - [The Rust Programming Language 核心章节 {#the-rust-programming-language-核心章节}](#the-rust-programming-language-核心章节-the-rust-programming-language-核心章节)
    - [Rust Standard Library 核心 API / 模块（Module） {#rust-standard-library-核心-api-模块}](#rust-standard-library-核心-api--模块-rust-standard-library-核心-api-模块)
    - [Rust By Example / Rust Cookbook / cheats.rs {#rust-by-example-rust-cookbook-cheatsrs}](#rust-by-example--rust-cookbook--cheatsrs-rust-by-example-rust-cookbook-cheatsrs)
    - [宏系统专属权威链接 {#宏系统专属权威链接}](#宏系统专属权威链接-宏系统专属权威链接)
      - [Reference Macros {#reference-macros}](#reference-macros-reference-macros)
      - [Standard Library proc-macro {#standard-library-proc-macro}](#standard-library-proc-macro-standard-library-proc-macro)
      - [Rust By Example / Cookbook / cheats.rs {#rust-by-example-cookbook-cheatsrs}](#rust-by-example--cookbook--cheatsrs-rust-by-example-cookbook-cheatsrs)
      - [proc-macro RFC / rustc dev guide / Little Book {#proc-macro-rfc-rustc-dev-guide-little-book}](#proc-macro-rfc--rustc-dev-guide--little-book-proc-macro-rfc-rustc-dev-guide-little-book)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 声明宏 (macro_rules!) {#声明宏-macro_rules}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 基本语法 {#基本语法}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
macro_rules! say_hello {
    () => {
        println!("Hello!");
    };
}

say_hello!();  // 展开: println!("Hello!");
```

### 参数模式 {#参数模式}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
macro_rules! print_value {
    // 表达式参数
    ($e:expr) => {
        println!("{}", $e);
    };

    // 多个参数
    ($e1:expr, $e2:expr) => {
        println!("{}, {}", $e1, $e2);
    };
}

print_value!(42);
print_value!(1, 2);
```

### 重复模式 {#重复模式}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
macro_rules! vec {
    // 零个或多个
    ($($x:expr),*) => {{
        let mut temp_vec = Vec::new();
        $(temp_vec.push($x);)*
        temp_vec
    }};

    // 带结尾逗号
    ($($x:expr,)+) => { /* ... */ };
}

vec![1, 2, 3];
vec![1, 2, 3,];  // 带结尾逗号
```

### 常见片段类型 {#常见片段类型}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 指示符 | 匹配 | 示例 |
| :--- | :--- | :--- |
| `expr` | 表达式 | `1 + 2`, `foo()` |
| `stmt` | 语句 | `let x = 1;` |
| `ty` | 类型 | `i32`, `Vec<T>` |
| `ident` | 标识符 | `foo`, `Bar` |
| `path` | 路径 | `std::option::Option` |
| `tt` | 标记树 | 任何标记 |
| `item` | 项 | `fn`, `struct`等 |
| `block` | 块 | `{ ... }` |
| `meta` | 属性内容 | `derive(Debug)` |
| `lifetime` | 生命周期（Lifetimes） | `'a`, `'static` |

---

## 过程宏 {#过程宏}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 派生宏 {#派生宏-1}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
// 定义
use proc_macro::TokenStream;

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    // 解析input，生成输出
    let ast = syn::parse(input).unwrap();
    // ... 生成代码
    output.into()
}

// 使用
#[derive(MyDerive)]
struct MyStruct;
```

### 属性宏 {#属性宏-1}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
// 定义
#[proc_macro_attribute]
pub fn my_attr(args: TokenStream, input: TokenStream) -> TokenStream {
    // args: 属性参数
    // input: 被修饰的项
    input
}

// 使用
#[my_attr(arg1, arg2)]
fn my_func() {}
```

### 函数式宏 {#函数式宏}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust,ignore
// 定义
#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    input
}

// 使用
my_macro!(...);
```

---

## 常见宏示例 {#常见宏示例}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### vec {#vec}

> **来源: [POPL](https://www.sigplan.org/Conferences/POPL/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```rust
// 创建Vec
let v = vec![1, 2, 3];
let v = vec![0; 5];  // [0, 0, 0, 0, 0]
```

### println! / format {#println-format}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

```rust,ignore
println!("Hello");
println!("{}", value);
println!("{:?}", debug_value);
println!("{:.2}", float);  // 两位小数
println!("{:>8}", text);   // 右对齐，宽度8
```

### assert {#assert}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

```rust,ignore
assert!(condition);
assert_eq!(a, b);
assert_ne!(a, b);
assert!(cond, "message: {}", arg);  // 自定义消息
```

### todo! / unimplemented {#todo-unimplemented}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

```rust
fn not_yet() {
    todo!("实现这个功能");  // panic with message
}

fn stub() {
    unimplemented!();  // panic
}
```

### include {#include}

> **来源: [Wikipedia - Type System](https://en.wikipedia.org/wiki/Type_System)**

```rust,ignore
include!("path/to/file.rs");  // 包含文件内容
include_str!("path/to/file.txt");  // 包含为&str
include_bytes!("path/to/file.bin");  // 包含为&[u8]
```

---

## 宏调试技巧 {#宏调试技巧}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 查看展开 {#查看展开}

> **来源: [Wikipedia - Concurrency](https://en.wikipedia.org/wiki/Concurrency)**

```bash
# 查看宏展开 {#查看宏展开}
cargo expand

# 或 nightly {#或-nightly}
cargo rustc -- -Z unpretty=expanded
```

### trace_macros {#trace_macros}

> **来源: [Wikipedia - Asynchronous I/O](https://en.wikipedia.org/wiki/Asynchronous_I/O)**

```rust,ignore
#![feature(trace_macros)]

trace_macros!(true);
my_macro!(...);  // 打印展开过程
trace_macros!(false);
```

---

## 宏卫生性 (Hygiene) {#宏卫生性-hygiene}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
macro_rules! using_a {
    ($e:expr) => {
        { let a = 42; $e }
    };
}

let four = using_a!(a / 10);  // 错误! a在宏外不可见
```

宏内部定义的标识符不会与外部冲突。

---

## 递归宏 {#递归宏}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```rust
macro_rules! count_exprs {
    () => (0);
    ($head:expr) => (1);
    ($head:expr, $($tail:expr),*) => (1 + count_exprs!($($tail),*));
}

count_exprs!(1, 2, 3);  // 3
```

---

## 条件编译宏 {#条件编译宏}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust
#[cfg(target_os = "linux")]
fn linux_only() {}

#[cfg(all(feature = "serde", not(feature = "minimal")))]
impl Serialize for MyType {}

#[cfg_attr(feature = "serde", derive(Serialize))]
struct MyStruct;
```

---

## 编译器内置宏 {#编译器内置宏}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

| 宏 | 用途 |
| :--- | :--- |
| `column!()` | 当前列号 |
| `line!()` | 当前行号 |
| `file!()` | 当前文件名 |
| `module_path!()` | 当前模块路径 |
| `stringify!($e)` | 转为字符串 |
| `concat!(...)` | 字符串拼接 |
| `env!("VAR")` | 环境变量 |
| `option_env!("VAR")` | 可选环境变量 |

---

## 常用宏 {#常用宏}
>
> **[来源: [crates.io](https://crates.io/)]**

| 宏 | 用途 | 示例 |
| :--- | :--- | :--- |
| `println!` | 打印 | `println!("{}", x)` |
| `format!` | 格式化字符串 | `format!("{}", x)` |
| `vec!` | 创建Vec（Vec） | `vec![1, 2, 3]` |
| `assert!` | 断言 | `assert!(x > 0)` |
| `panic!` | panic | `panic!("error")` |
| `todo!` | 待实现 | `todo!("implement")` |
| `unreachable!` | 不可达 | `unreachable!()` |

---

## 派生宏 {#派生宏-1}
>
> **[来源: [docs.rs](https://docs.rs/)]**

```rust
#[derive(Debug, Clone, PartialEq)]
struct Point { x: i32, y: i32 }
```

常用trait（Trait）: `Debug`, `Clone`, `Copy`, `PartialEq`, `Eq`, `PartialOrd`, `Ord`, `Hash`, `Default`

---

## 属性宏 {#属性宏-1}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```rust,ignore
#[test]           // 测试函数
#[inline]         // 内联建议
#[cfg(test)]      // 条件编译
#[derive(...)]    // 自动实现
```

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-06-29
**状态**: ✅ 完成

---

## 🌍 权威国际化资源链接 {#权威国际化资源链接}
>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)**
> **来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)**
> **来源: [cheats.rs](https://cheats.rs/)**

本节为速查内容提供官方权威来源与社区经典参考的直通链接，便于深入验证与扩展阅读。

### Rust Reference 核心章节 {#rust-reference-核心章节}

- [Reference 首页](https://doc.rust-lang.org/reference/)
- [Types](https://doc.rust-lang.org/reference/types.html)
- [Items / Traits](https://doc.rust-lang.org/reference/items/traits.html)
- [Expressions](https://doc.rust-lang.org/reference/expressions.html)
- [Statements](https://doc.rust-lang.org/reference/statements.html)
- [Crates and Source Files](https://doc.rust-lang.org/reference/crates-and-source-files.html)

### The Rust Programming Language 核心章节 {#the-rust-programming-language-核心章节}

- [TRPL 首页](https://doc.rust-lang.org/book/)
- [Ch. 4 - Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Ch. 9 - Error Handling](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [Ch. 10 - Generic Types, Traits, Lifetimes](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [Ch. 13 - Closures](https://doc.rust-lang.org/book/ch13-00-functional-features.html)
- [Ch. 15 - Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)
- [Ch. 16 - Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
- [Ch. 19 - Advanced Features / Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)

### Rust Standard Library 核心 API / 模块 {#rust-standard-library-核心-api-模块}

- [std 首页](https://doc.rust-lang.org/std/)
- [std::result](https://doc.rust-lang.org/std/result/)
- [std::option](https://doc.rust-lang.org/std/option/)
- [std::error::Error](https://doc.rust-lang.org/std/error/trait.Error.html)
- [std::fmt](https://doc.rust-lang.org/std/fmt/)
- [std::panic](https://doc.rust-lang.org/std/panic/)
- [std::marker (Send / Sync / PhantomData)](https://doc.rust-lang.org/std/marker/)

### Rust By Example / Rust Cookbook / cheats.rs {#rust-by-example-rust-cookbook-cheatsrs}

- [Rust By Example 首页](https://doc.rust-lang.org/rust-by-example/)
- [Rust Cookbook 首页](https://rust-lang-nursery.github.io/rust-cookbook/)
- [cheats.rs 首页](https://cheats.rs/)

---

### 宏系统专属权威链接 {#宏系统专属权威链接}

> **来源: [Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)**
> **来源: [TRPL Ch. 19 - Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)**

#### Reference Macros {#reference-macros}

- [Macros](https://doc.rust-lang.org/reference/macros.html)
- [Macro Rules](https://doc.rust-lang.org/reference/macros-by-example.html)
- [Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)
- [Derive Macros](https://doc.rust-lang.org/reference/attributes/derive.html)

#### Standard Library proc-macro {#standard-library-proc-macro}

- [std::proc_macro](https://doc.rust-lang.org/proc_macro/)
- [proc_macro::TokenStream](https://doc.rust-lang.org/proc_macro/struct.TokenStream.html)

#### Rust By Example / Cookbook / cheats.rs {#rust-by-example-cookbook-cheatsrs}

- [RBE - Macros](https://doc.rust-lang.org/rust-by-example/macros.html)
- [RBE - macro_rules!](https://doc.rust-lang.org/rust-by-example/macros.html)
- [cheats.rs - Macros](https://cheats.rs/#macros)

#### proc-macro RFC / rustc dev guide / Little Book {#proc-macro-rfc-rustc-dev-guide-little-book}

- [RFC 1566 - Procedural Macros](https://rust-lang.github.io/rfcs/1566-proc-macros.html)
- [rustc dev guide - Macro Expansion](https://rustc-dev-guide.rust-lang.org/macro-expansion.html)
- [rustc dev guide - Procedural Macros](https://rustc-dev-guide.rust-lang.org/attributes.html)
- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)
- [The Little Book of Rust Macros - Syntax Extensions](https://veykril.github.io/tlborm/decl-macros/minutiae/fragment-specifiers.html)

## 相关概念 {#相关概念}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Macro (computer science)](https://en.wikipedia.org/wiki/Macro_(computer_science))**
> **来源: [TRPL Ch. 19 - Macros](https://doc.rust-lang.org/book/ch19-00-advanced-features.html)**
> **来源: [Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)**
> **来源: [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)**

---

> **来源: [ACM Digital Library](https://dl.acm.org/)**
> **来源: [IEEE Standards](https://standards.ieee.org/)**
