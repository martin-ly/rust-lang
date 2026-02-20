# 🔧 Rust 宏系统速查卡

> **快速参考** | [完整文档](../../../crates/c11_macro_system/docs/) | [代码示例](../../../crates/c11_macro_system/examples/)
> **创建日期**: 2026-01-27
> **最后更新**: 2026-01-27
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

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
    - [模式 3: 可变参数宏](#模式-3-可变参数宏)
    - [模式 4: 递归宏](#模式-4-递归宏)
  - [💡 代码示例](#-代码示例)
    - [示例 1: 实现 vec! 宏](#示例-1-实现-vec-宏)
    - [示例 2: 实现 hashmap! 宏](#示例-2-实现-hashmap-宏)
    - [示例 3: 实现 lazy\_static! 宏](#示例-3-实现-lazy_static-宏)
    - [示例 4: 测试宏](#示例-4-测试宏)
    - [示例 5: 完整过程宏示例](#示例-5-完整过程宏示例)
  - [🎯 使用场景](#-使用场景)
    - [场景: 领域特定语言（DSL）](#场景-领域特定语言dsl)
  - [🚫 反例速查](#-反例速查)
    - [反例 1: 宏中重复求值](#反例-1-宏中重复求值)
    - [反例 2: 在宏中生成不完整代码](#反例-2-在宏中生成不完整代码)
    - [反例 3: 宏中变量名污染](#反例-3-宏中变量名污染)
    - [反例 4: 重复求值问题](#反例-4-重复求值问题)
    - [反例 5: 过程宏中的错误处理](#反例-5-过程宏中的错误处理)
  - [📚 相关文档](#-相关文档)
  - [🧩 相关示例代码](#-相关示例代码)
  - [🆕 Rust 1.93.0 宏系统改进](#-rust-1930-宏系统改进)
    - [`cfg` 属性在 `asm!` 行上](#cfg-属性在-asm-行上)
  - [Rust 1.92.0 宏系统改进（历史）](#rust-1920-宏系统改进历史)
    - [编译优化](#编译优化)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [形式化理论与类型系统](#形式化理论与类型系统)
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

### 模式 3: 可变参数宏

```rust
macro_rules! log {
    // 无参数
    () => { println!("[LOG]"); };

    // 单参数
    ($msg:expr) => {
        println!("[LOG] {}", $msg);
    };

    // 格式化参数
    ($fmt:expr, $($args:tt)*) => {
        println!(concat!("[LOG] ", $fmt), $($args)*);
    };
}

// 使用
log!();
log!("Hello");
log!("Value: {}", 42);
```

### 模式 4: 递归宏

```rust
macro_rules! count {
    // 基本情况
    () => { 0 };

    // 递归情况
    ($x:tt $($rest:tt)*) => {
        1 + count!($($rest)*)
    };
}

// 使用
let n = count!(a b c d e);  // n = 5
```

---

## 💡 代码示例

### 示例 1: 实现 vec! 宏

```rust
macro_rules! my_vec {
    // 空向量
    () => {
        Vec::new()
    };

    // 带初始值的向量
    ($($x:expr),+ $(,)?) => {
        {
            let mut temp_vec = Vec::new();
            $(
                temp_vec.push($x);
            )+
            temp_vec
        }
    };

    // 重复元素 [elem; count]
    ($elem:expr; $n:expr) => {
        std::vec::from_elem($elem, $n)
    };
}

// 使用
let v1 = my_vec![];
let v2 = my_vec![1, 2, 3];
let v3 = my_vec![0; 5];  // [0, 0, 0, 0, 0]
```

### 示例 2: 实现 hashmap! 宏

```rust
macro_rules! hashmap {
    // 空 map
    () => {
        ::std::collections::HashMap::new()
    };

    // 键值对
    ($($key:expr => $value:expr),+ $(,)?) => {
        {
            let mut map = ::std::collections::HashMap::new();
            $(
                map.insert($key, $value);
            )+
            map
        }
    };
}

// 使用
let map = hashmap! {
    "name" => "Alice",
    "age" => "30",
};
```

### 示例 3: 实现 lazy_static! 宏

```rust
macro_rules! lazy_static {
    ($name:ident: $t:ty = $init:expr) => {
        static $name: ::std::sync::OnceLock<$t> = ::std::sync::OnceLock::new();

        fn $name() -> &'static $t {
            $name.get_or_init(|| $init)
        }
    };
}

// 使用
use std::collections::HashMap;

lazy_static! {
    static ref CONFIG: HashMap<String, String> = {
        let mut m = HashMap::new();
        m.insert("key".to_string(), "value".to_string());
        m
    };
}
```

### 示例 4: 测试宏

```rust
macro_rules! assert_eq_tol {
    ($left:expr, $right:expr, $tol:expr) => {
        {
            let left = $left;
            let right = $right;
            let tolerance = $tol;
            let diff = (left - right).abs();
            assert!(
                diff <= tolerance,
                "assertion failed: `({} - {}).abs() <= {}`\n  left: {}\n right: {}",
                stringify!($left),
                stringify!($right),
                stringify!($tol),
                left,
                right
            );
        }
    };
}

// 使用
let result = 3.14159;
assert_eq_tol!(result, 3.14, 0.01);
```

### 示例 5: 完整过程宏示例

```rust
// 在单独 crate 中定义
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let builder_name = quote::format_ident!("{}Builder", name);

    let expanded = quote! {
        pub struct #builder_name {
            // 字段...
        }

        impl #builder_name {
            pub fn new() -> Self {
                Self {}
            }

            pub fn build(self) -> #name {
                // 构建逻辑
                unimplemented!()
            }
        }
    };

    TokenStream::from(expanded)
}

// 使用
#[derive(Builder)]
struct Person {
    name: String,
    age: u32,
}
```

---

## 🎯 使用场景

### 场景: 领域特定语言（DSL）

宏可用于创建内部 DSL，简化特定领域代码：

```rust
// HTML 生成 DSL
macro_rules! html {
    ($tag:ident { $($children:tt)* }) => {
        HtmlElement::new(stringify!($tag))
            .children(vec![$($children)*])
    };
    ($tag:ident [$($attr:ident = $value:expr),*] { $($children:tt)* }) => {
        HtmlElement::new(stringify!($tag))
            .attrs(vec![$((stringify!($attr), $value.to_string())),*])
            .children(vec![$($children)*])
    };
}

macro_rules! text {
    ($content:expr) => {
        HtmlElement::text($content.to_string())
    };
}

// 使用
let page = html! {
    div [class = "container"] {
        h1 { text!("Hello") },
        p { text!("World") }
    }
};
```

另一个常见场景是自动化测试套件：

```rust
// 参数化测试宏
macro_rules! param_test {
    ($name:ident, $($input:expr => $expected:expr),+ $(,)?) => {
        $(
            #[test]
            fn $name() {
                let result = $input;
                assert_eq!(result, $expected);
            }
        )+
    };
}

param_test! {
    test_add,
    1 + 1 => 2,
    2 + 2 => 4,
    3 + 3 => 6,
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

### 反例 3: 宏中变量名污染

**错误示例**:

```rust
macro_rules! bad_swap {
    ($a:expr, $b:expr) => {
        let temp = $a;  // ❌ temp 可能与外部变量冲突
        $a = $b;
        $b = temp;
    };
}

let temp = 1;
let mut x = 2;
let mut y = 3;
bad_swap!(x, y);
// temp 被意外修改！
```

**原因**: 宏中使用的变量名可能与外部作用域冲突。

**修正**: 使用 `let` 绑定创建新作用域：

```rust
macro_rules! good_swap {
    ($a:expr, $b:expr) => {{
        let temp = $a;
        $a = $b;
        $b = temp;
    }};
}
```

---

### 反例 4: 重复求值问题

**错误示例**:

```rust
macro_rules! max {
    ($a:expr, $b:expr) => {
        if $a > $b { $a } else { $b }  // ❌ $a 或 $b 被求值两次
    };
}

let mut counter = 0;
let result = max!({ counter += 1; counter }, 0);
// counter 增加了 2 次，不是 1 次！
```

**原因**: 宏参数被多次使用，导致副作用重复执行。

**修正**: 使用变量绑定确保单次求值：

```rust
macro_rules! max {
    ($a:expr, $b:expr) => {{
        let a = $a;
        let b = $b;
        if a > b { a } else { b }
    }};
}
```

---

### 反例 5: 过程宏中的错误处理

**错误示例**:

```rust
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    // ❌ 没有错误处理，panic 会导致编译器崩溃
    let field = input.data.unwrap_struct().fields.iter().next().unwrap();
    // ...
}
```

**原因**: 过程宏中的 panic 会导致不友好的编译错误。

**修正**: 使用 `syn::Error` 和 `quote::quote_spanned`：

```rust
use proc_macro2::Span;
use syn::{spanned::Spanned, Error};

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let expanded = match generate_impl(&input) {
        Ok(tokens) => tokens,
        Err(e) => e.to_compile_error().into(),
    };

    TokenStream::from(expanded)
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

### 形式化理论与类型系统

- [类型系统基础](../../research_notes/type_theory/type_system_foundations.md) — 宏与类型系统的关系
- [构造能力理论](../../research_notes/type_theory/construction_capability.md) — 宏的表达能力边界
- [形式化方法概述](../../research_notes/formal_methods/README.md) — 宏安全性形式化
- [Rust 惯用法](../../research_notes/software_design_theory/06_rust_idioms.md) — 宏最佳实践形式化
- [软件设计理论](../../research_notes/software_design_theory/README.md) — 宏在设计模式中的应用

### 相关速查卡

- [类型系统速查卡](./type_system.md) - 宏与类型系统
- [泛型编程速查卡](./generics_cheatsheet.md) - 宏与泛型
- [模块系统速查卡](./modules_cheatsheet.md) - 宏在模块中的使用
- [测试速查卡](./testing_cheatsheet.md) - 测试宏

---

**最后更新**: 2026-01-27
**Rust 版本**: 1.93.0+ (Edition 2024)
