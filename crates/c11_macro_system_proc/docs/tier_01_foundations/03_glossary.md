# 术语表 - C11 Macro System

**最后更新**: 2025-12-11

本文档汇总了 Rust 宏系统中的核心术语和概念。

---

## 📋 目录

- [术语表 - C11 Macro System](#术语表---c11-macro-system)
  - [📋 目录](#-目录)
  - [🎨 宏类型术语](#-宏类型术语)
    - [Macro (宏)](#macro-宏)
    - [Declarative Macro (声明宏)](#declarative-macro-声明宏)
    - [Procedural Macro (过程宏)](#procedural-macro-过程宏)
  - [🔧 声明宏术语](#-声明宏术语)
    - [macro\_rules](#macro_rules)
    - [Pattern Matching (模式匹配)](#pattern-matching-模式匹配)
    - [Repetition (重复)](#repetition-重复)
    - [Metavariable (元变量)](#metavariable-元变量)
  - [⚙️ 过程宏术语](#️-过程宏术语)
    - [TokenStream](#tokenstream)
    - [Derive Macro (派生宏)](#derive-macro-派生宏)
    - [Attribute Macro (属性宏)](#attribute-macro-属性宏)
    - [Function-like Macro (函数式宏)](#function-like-macro-函数式宏)
    - [syn Crate](#syn-crate)
    - [quote Crate](#quote-crate)
    - [Span](#span)
  - [🧹 卫生性与作用域](#-卫生性与作用域)
    - [Hygiene (卫生性)](#hygiene-卫生性)
    - [Call Site (调用点)](#call-site-调用点)
    - [Definition Site (定义点)](#definition-site-定义点)
    - [Mixed Site (混合点)](#mixed-site-混合点)
  - [🛠️ 工具与库](#️-工具与库)
    - [cargo-expand](#cargo-expand)
    - [proc-macro2](#proc-macro2)
    - [trybuild](#trybuild)
  - [📚 元编程概念](#-元编程概念)
    - [Metaprogramming (元编程)](#metaprogramming-元编程)
    - [AST (抽象语法树)](#ast-抽象语法树)
    - [DSL (领域特定语言)](#dsl-领域特定语言)
    - [Code Generation (代码生成)](#code-generation-代码生成)
    - [Zero-Cost Abstraction (零成本抽象)](#zero-cost-abstraction-零成本抽象)
    - [Compile-time Computation (编译时计算)](#compile-time-computation-编译时计算)

---

## 🎨 宏类型术语

### Macro (宏)

编译时执行的代码生成机制，在编译前展开为 Rust 代码。

**分类**:

- **声明宏** (Declarative Macros): `macro_rules!`
- **过程宏** (Procedural Macros): 自定义 derive、属性宏、函数式宏

**特点**:

- 编译时展开
- 零运行时开销
- 类型安全

---

### Declarative Macro (声明宏)

使用 `macro_rules!` 定义的模式匹配宏。

```rust
macro_rules! vec_of_strings {
    ($($element:expr),*) => {
        vec![$(String::from($element)),*]
    };
}
```

**特点**:

- 语法简洁
- 模式匹配
- 卫生性保证

---

### Procedural Macro (过程宏)

使用 Rust 代码处理 TokenStream 的宏。

**三种类型**:

1. **Derive 宏**: `#[derive(MyTrait)]`
2. **属性宏**: `#[my_attribute]`
3. **函数式宏**: `my_macro!(input)`

```rust
#[proc_macro_derive(MyTrait)]
pub fn my_trait_derive(input: TokenStream) -> TokenStream {
    // 处理 TokenStream
}
```

---

## 🔧 声明宏术语

### macro_rules

定义声明宏的关键字。

```rust
macro_rules! say_hello {
    () => {
        println!("Hello!");
    };
}
```

---

### Pattern Matching (模式匹配)

宏的参数匹配规则。

**片段说明符** (Fragment Specifiers):

- `$name:expr` - 表达式
- `$name:ident` - 标识符
- `$name:ty` - 类型
- `$name:pat` - 模式
- `$name:stmt` - 语句
- `$name:block` - 代码块
- `$name:item` - 项（函数、结构体等）
- `$name:tt` - 单个 token 树

```rust
macro_rules! create_function {
    ($func_name:ident) => {
        fn $func_name() {
            println!("Called {}", stringify!($func_name));
        }
    };
}
```

---

### Repetition (重复)

宏参数的重复模式。

**语法**: `$(...)*` 或 `$(...)+` 或 `$(...)?`

```rust
macro_rules! sum {
    ($($num:expr),*) => {
        0 $(+ $num)*
    };
}

let result = sum!(1, 2, 3, 4); // 10
```

**符号含义**:

- `*` - 零次或多次
- `+` - 一次或多次
- `?` - 零次或一次

---

### Metavariable (元变量)

宏模式中捕获的变量，如 `$name`。

```rust
macro_rules! create_var {
    ($var_name:ident, $var_value:expr) => {
        let $var_name = $var_value;
    };
}

create_var!(x, 42); // let x = 42;
```

---

## ⚙️ 过程宏术语

### TokenStream

宏输入和输出的 token 流。

```rust
use proc_macro::TokenStream;

#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // 处理 input，返回新的 TokenStream
    input
}
```

**特点**:

- 表示代码的 token 序列
- 可解析、修改、生成

---

### Derive Macro (派生宏)

自动为类型实现 trait 的宏。

```rust
#[derive(Debug, Clone, MyTrait)]
struct MyStruct {
    field: i32,
}
```

**定义**:

```rust
#[proc_macro_derive(MyTrait)]
pub fn my_trait_derive(input: TokenStream) -> TokenStream {
    // 生成 impl MyTrait for T {}
}
```

---

### Attribute Macro (属性宏)

为代码添加元数据或修改代码的宏。

```rust
#[route(GET, "/")]
fn index() -> String {
    "Hello!".to_string()
}
```

**定义**:

```rust
#[proc_macro_attribute]
pub fn route(attr: TokenStream, item: TokenStream) -> TokenStream {
    // attr: GET, "/"
    // item: fn index() { ... }
    // 返回修改后的函数
}
```

---

### Function-like Macro (函数式宏)

看起来像函数调用的宏。

```rust
let sql = sql!(SELECT * FROM users WHERE id = 1);
```

**定义**:

```rust
#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    // 解析 SQL，生成代码
}
```

---

### syn Crate

解析 TokenStream 的库。

```rust
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyTrait)]
pub fn my_trait_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    // ...
}
```

**功能**:

- 解析 Rust 语法
- 提供 AST 数据结构
- 错误处理

---

### quote Crate

生成 TokenStream 的库。

```rust
use quote::quote;

let name = &input.ident;
let expanded = quote! {
    impl MyTrait for #name {
        fn my_method(&self) {
            println!("Hello from {}", stringify!(#name));
        }
    }
};
```

**功能**:

- 使用类 Rust 语法生成代码
- 插值变量 `#var`
- 重复 `#(...)*`

---

### Span

代码位置信息，用于错误消息。

```rust
use proc_macro::Span;

let span = Span::call_site(); // 宏调用位置
let span = ident.span();       // 标识符位置
```

**用途**:

- 精确的错误提示
- 保留源代码位置
- 调试信息

---

## 🧹 卫生性与作用域

### Hygiene (卫生性)

宏内外标识符不冲突的机制。

```rust
macro_rules! using_a {
    ($e:expr) => {
        {
            let a = 42; // 不会与外部 a 冲突
            $e
        }
    }
}

let a = 13;
let result = using_a!(a + a); // 26，使用外部 a
```

**保证**:

- 宏内定义的标识符不泄露
- 宏外标识符不被捕获（除非显式引用）

---

### Call Site (调用点)

宏被调用的位置。

```rust
// 这里是 call site
my_macro!(some_input);
```

**影响**:

- Span 信息
- 作用域解析
- 卫生性规则

---

### Definition Site (定义点)

宏被定义的位置。

```rust
// 这里是 definition site
macro_rules! my_macro {
    // ...
}
```

---

### Mixed Site (混合点)

syn 2.0+ 引入的概念，用于更精细的卫生性控制。

```rust
use proc_macro2::Span;

let span = Span::mixed_site();
```

---

## 🛠️ 工具与库

### cargo-expand

查看宏展开结果的工具。

```bash
cargo install cargo-expand
cargo expand
cargo expand my_module::my_function
```

**用途**:

- 调试宏
- 理解宏展开
- 学习宏实现

---

### proc-macro2

`proc_macro` 的独立版本，支持单元测试。

```rust
use proc_macro2::TokenStream;

fn my_helper(input: TokenStream) -> TokenStream {
    // 可以在单元测试中调用
}
```

**优势**:

- 可测试
- 跨平台
- 功能完整

---

### trybuild

测试编译错误的工具。

```rust
#[test]
fn ui_tests() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/*.rs");
}
```

**用途**:

- 测试宏的错误消息
- 确保错误提示准确

---

## 📚 元编程概念

### Metaprogramming (元编程)

编写生成或操作程序的程序。

**Rust 宏的元编程能力**:

- 代码生成
- 编译时计算
- 零成本抽象

---

### AST (抽象语法树)

代码的树状表示。

```rust
// 代码
let x = 1 + 2;

// AST (简化表示)
LetStmt {
    pat: Ident("x"),
    init: BinaryOp {
        op: Add,
        left: Lit(1),
        right: Lit(2),
    }
}
```

**在宏中**:

- syn 解析为 AST
- 操作 AST
- quote 生成代码

---

### DSL (领域特定语言)

针对特定领域的小语言。

**示例**:

```rust
html! {
    <div class="container">
        <h1>"Hello, World!"</h1>
    </div>
}
```

**实现方式**:

- 函数式宏
- 自定义解析
- 代码生成

---

### Code Generation (代码生成)

宏的核心功能，在编译时生成代码。

```rust
#[derive(Builder)]
struct User {
    name: String,
    age: u32,
}

// 自动生成 UserBuilder
let user = User::builder()
    .name("Alice".to_string())
    .age(30)
    .build();
```

---

### Zero-Cost Abstraction (零成本抽象)

宏展开后的代码性能与手写代码相同。

```rust
// 宏定义的高层抽象
for_each!(vec, |x| println!("{}", x));

// 展开后等价于
for x in vec {
    println!("{}", x);
}
```

**验证方式**:

- 查看宏展开
- 分析 LLVM IR
- 性能基准测试

---

### Compile-time Computation (编译时计算)

在编译期完成计算，运行时零开销。

```rust
const SIZE: usize = compute_size!(some_input);
```

---

**上一步**: [主索引导航](02_navigation.md)
**下一步**: [常见问题](04_faq.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
