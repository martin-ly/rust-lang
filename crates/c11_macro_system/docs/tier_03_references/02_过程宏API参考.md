# 过程宏 API 参考

**最后更新**: 2025-12-11
**适用版本**: Rust 1.92.0+

本文档提供过程宏核心 API 的完整参考，包括 `TokenStream`、`Span`、`Ident` 等关键类型。

---

## 📋 目录

- [过程宏 API 参考](#过程宏-api-参考)
  - [📋 目录](#-目录)
  - [1. 过程宏类型](#1-过程宏类型)
    - [1.1 Derive 宏](#11-derive-宏)
    - [1.2 属性宏](#12-属性宏)
    - [1.3 函数式宏](#13-函数式宏)
  - [2. TokenStream](#2-tokenstream)
    - [2.1 基本操作](#21-基本操作)
    - [2.2 创建与转换](#22-创建与转换)
    - [2.3 遍历与操作](#23-遍历与操作)
  - [3. TokenTree](#3-tokentree)
    - [3.1 TokenTree 类型](#31-tokentree-类型)
    - [3.2 模式匹配](#32-模式匹配)
    - [3.3 构建 TokenTree](#33-构建-tokentree)
  - [4. Span](#4-span)
    - [4.1 Span 类型](#41-span-类型)
    - [4.2 创建 Span](#42-创建-span)
    - [4.3 Span 操作](#43-span-操作)
    - [4.4 错误报告](#44-错误报告)
  - [5. Ident](#5-ident)
    - [5.1 创建标识符](#51-创建标识符)
    - [5.2 标识符操作](#52-标识符操作)
    - [5.3 原始标识符](#53-原始标识符)
  - [6. Literal](#6-literal)
    - [6.1 字面量类型](#61-字面量类型)
    - [6.2 创建字面量](#62-创建字面量)
    - [6.3 字面量操作](#63-字面量操作)
  - [7. Punct](#7-punct)
    - [7.1 标点符号](#71-标点符号)
    - [7.2 间距规则](#72-间距规则)
  - [8. Group](#8-group)
    - [8.1 分组类型](#81-分组类型)
    - [8.2 创建分组](#82-创建分组)
  - [9. Diagnostic API](#9-diagnostic-api)
    - [9.1 基本诊断](#91-基本诊断)
    - [9.2 多 Span 诊断](#92-多-span-诊断)
    - [9.3 诊断级别](#93-诊断级别)
  - [10. proc\_macro2](#10-proc_macro2)
    - [10.1 区别与优势](#101-区别与优势)
    - [10.2 互操作](#102-互操作)

---

## 1. 过程宏类型

### 1.1 Derive 宏

```rust
use proc_macro::TokenStream;

#[proc_macro_derive(MyTrait)]
pub fn my_trait_derive(input: TokenStream) -> TokenStream {
    // input: struct/enum 定义
    // output: impl MyTrait for T { ... }
    input
}

#[proc_macro_derive(MyTrait, attributes(my_attr))]
pub fn my_trait_derive_with_attr(input: TokenStream) -> TokenStream {
    // 支持辅助属性 #[my_attr(...)]
    input
}
```

**使用**:

```rust
#[derive(MyTrait)]
#[my_attr(param = "value")]
struct MyStruct {
    field: i32,
}
```

---

### 1.2 属性宏

```rust
use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn my_attribute(attr: TokenStream, item: TokenStream) -> TokenStream {
    // attr: 属性参数
    // item: 被标注的项
    // output: 修改后的项
    item
}
```

**使用**:

```rust
#[my_attribute(param1, param2 = "value")]
fn my_function() {
    // ...
}
```

---

### 1.3 函数式宏

```rust
use proc_macro::TokenStream;

#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // input: 任意 token 流
    // output: 任意 Rust 代码
    input
}
```

**使用**:

```rust
my_macro!(arbitrary tokens here);
```

---

## 2. TokenStream

### 2.1 基本操作

```rust
use proc_macro::TokenStream;

#[proc_macro]
pub fn token_stream_demo(input: TokenStream) -> TokenStream {
    // 检查是否为空
    if input.is_empty() {
        return TokenStream::new();
    }

    // 转换为字符串
    let input_str = input.to_string();
    println!("Input: {}", input_str);

    // 从字符串解析（不推荐）
    let parsed: TokenStream = "let x = 42;".parse().unwrap();

    parsed
}
```

---

### 2.2 创建与转换

```rust
use proc_macro::{TokenStream, TokenTree};

// 创建空流
let empty = TokenStream::new();

// 从迭代器创建
let tokens: Vec<TokenTree> = vec![/* ... */];
let stream = TokenStream::from_iter(tokens);

// 扩展流
let mut stream = TokenStream::new();
stream.extend(vec![/* TokenTree */]);

// 合并流
let combined = [stream1, stream2].into_iter().collect::<TokenStream>();
```

---

### 2.3 遍历与操作

```rust
use proc_macro::{TokenStream, TokenTree};

#[proc_macro]
pub fn iterate_tokens(input: TokenStream) -> TokenStream {
    for token in input {
        match token {
            TokenTree::Ident(ident) => {
                println!("Identifier: {}", ident);
            }
            TokenTree::Literal(lit) => {
                println!("Literal: {}", lit);
            }
            TokenTree::Punct(punct) => {
                println!("Punctuation: {}", punct);
            }
            TokenTree::Group(group) => {
                println!("Group: {:?}", group.delimiter());
                // 递归处理 group.stream()
            }
        }
    }

    TokenStream::new()
}
```

---

## 3. TokenTree

### 3.1 TokenTree 类型

```rust
pub enum TokenTree {
    Ident(Ident),       // 标识符
    Literal(Literal),   // 字面量
    Punct(Punct),       // 标点
    Group(Group),       // 分组 ()、[]、{}
}
```

---

### 3.2 模式匹配

```rust
use proc_macro::{TokenStream, TokenTree, Delimiter};

#[proc_macro]
pub fn pattern_match(input: TokenStream) -> TokenStream {
    let mut iter = input.into_iter();

    match iter.next() {
        Some(TokenTree::Ident(ident)) => {
            println!("Found identifier: {}", ident);
        }
        Some(TokenTree::Group(group)) => {
            match group.delimiter() {
                Delimiter::Parenthesis => println!("Found (...)"),
                Delimiter::Brace => println!("Found {{...}}"),
                Delimiter::Bracket => println!("Found [...]"),
                Delimiter::None => println!("Found implicit group"),
            }
        }
        _ => {}
    }

    TokenStream::new()
}
```

---

### 3.3 构建 TokenTree

```rust
use proc_macro::{TokenTree, Ident, Literal, Punct, Spacing, Span};

// 创建标识符
let ident = TokenTree::Ident(Ident::new("foo", Span::call_site()));

// 创建字面量
let lit = TokenTree::Literal(Literal::i32_unsuffixed(42));

// 创建标点
let punct = TokenTree::Punct(Punct::new('+', Spacing::Alone));

// 组合成流
let stream = TokenStream::from_iter(vec![ident, punct, lit]);
// 结果: foo + 42
```

---

## 4. Span

### 4.1 Span 类型

```rust
use proc_macro::Span;

// Span 表示源代码位置
pub struct Span { /* 内部实现 */ }
```

---

### 4.2 创建 Span

```rust
use proc_macro::Span;

// 调用点 span（宏调用位置）
let call = Span::call_site();

// 定义点 span（宏定义位置，Rust 1.45+）
let def = Span::def_site();

// 混合 span（Rust 1.45+）
let mixed = Span::mixed_site();

// 解析 span（从字符串解析时使用，Rust 1.45+）
// let resolved = Span::resolved_at(call);
```

**卫生性规则**:

- `call_site()` - 最卫生，标识符来自调用点作用域
- `def_site()` - 最不卫生，标识符来自定义点作用域
- `mixed_site()` - 折中，适合大多数情况

---

### 4.3 Span 操作

```rust
use proc_macro::{Span, Ident};

let span = Span::call_site();

// 获取源文件信息（需要 proc_macro_span 特性）
// let source_file = span.source_file();
// let line = span.start().line;
// let column = span.start().column;

// 合并 span
let span1 = Span::call_site();
let span2 = Span::call_site();
let joined = span1.join(span2);

// 应用 span 到标识符
let ident = Ident::new("my_var", span);
```

---

### 4.4 错误报告

```rust
use proc_macro::{Span, TokenStream};

#[proc_macro]
pub fn error_example(input: TokenStream) -> TokenStream {
    let span = Span::call_site();

    // 编译错误
    let error = quote::quote_spanned! {span=>
        compile_error!("Custom error message");
    };

    error.into()
}
```

**使用 Diagnostic API** (nightly):

```rust
#![feature(proc_macro_diagnostic)]

use proc_macro::{Diagnostic, Level};

span.error("This is an error message")
    .note("Additional note")
    .help("Try this instead")
    .emit();
```

---

## 5. Ident

### 5.1 创建标识符

```rust
use proc_macro::{Ident, Span};

// 创建新标识符
let ident = Ident::new("my_ident", Span::call_site());

// ⚠️ 关键字会 panic
// let bad = Ident::new("fn", Span::call_site()); // panic!

// 安全检查
let name = "fn";
if syn::parse_str::<syn::Ident>(name).is_err() {
    eprintln!("{} is a keyword!", name);
}
```

---

### 5.2 标识符操作

```rust
use proc_macro::Ident;

let ident = Ident::new("my_var", Span::call_site());

// 获取名称
let name: String = ident.to_string();

// 获取 span
let span = ident.span();

// 设置新 span
let new_ident = Ident::new(&name, new_span);

// 比较（忽略 span）
if ident.to_string() == "my_var" {
    println!("Match!");
}
```

---

### 5.3 原始标识符

```rust
use proc_macro::Ident;

// 创建原始标识符 (r#ident)
// proc_macro 不直接支持，需要通过字符串

// 使用 syn
let raw_ident = syn::Ident::new_raw("fn", Span::call_site());
// 结果: r#fn
```

---

## 6. Literal

### 6.1 字面量类型

```rust
use proc_macro::Literal;

// 整数
let int = Literal::i32_unsuffixed(42);
let int_typed = Literal::i32_suffixed(42);  // 42i32

// 浮点数
let float = Literal::f64_unsuffixed(3.14);
let float_typed = Literal::f64_suffixed(3.14);  // 3.14f64

// 字符串
let string = Literal::string("hello");

// 字符
let char_lit = Literal::character('x');

// 字节串
let byte_string = Literal::byte_string(b"hello");
```

---

### 6.2 创建字面量

```rust
use proc_macro::Literal;

#[proc_macro]
pub fn create_literals(_input: TokenStream) -> TokenStream {
    let literals = vec![
        Literal::u8_suffixed(255),
        Literal::i64_unsuffixed(-123),
        Literal::string("Hello, World!"),
        Literal::character('🦀'),
        Literal::f32_suffixed(2.5),
    ];

    let stream = TokenStream::from_iter(
        literals.into_iter().map(TokenTree::Literal)
    );

    quote::quote! {
        (#stream)
    }.into()
}
```

---

### 6.3 字面量操作

```rust
use proc_macro::Literal;

let lit = Literal::string("hello");

// 转换为字符串表示
let s = lit.to_string();  // "\"hello\""

// 获取 span
let span = lit.span();

// 设置 span
lit.set_span(new_span);
```

---

## 7. Punct

### 7.1 标点符号

```rust
use proc_macro::{Punct, Spacing};

// 单字符标点
let plus = Punct::new('+', Spacing::Alone);
let minus = Punct::new('-', Spacing::Alone);

// 多字符标点（需要多个 Punct）
let arrow = vec![
    Punct::new('-', Spacing::Joint),  // -
    Punct::new('>', Spacing::Alone),  // >
];
// 结果: ->
```

---

### 7.2 间距规则

```rust
pub enum Spacing {
    Alone,  // 后面有空格
    Joint,  // 后面紧邻下一个字符
}
```

**示例**:

```rust
use proc_macro::{Punct, Spacing, TokenStream, TokenTree};

// 创建 "->="
let tokens = vec![
    TokenTree::Punct(Punct::new('-', Spacing::Joint)),
    TokenTree::Punct(Punct::new('>', Spacing::Joint)),
    TokenTree::Punct(Punct::new('=', Spacing::Alone)),
];

let stream = TokenStream::from_iter(tokens);
// 结果: ->=
```

---

## 8. Group

### 8.1 分组类型

```rust
pub enum Delimiter {
    Parenthesis,  // ( )
    Brace,        // { }
    Bracket,      // [ ]
    None,         // 隐式分组
}
```

---

### 8.2 创建分组

```rust
use proc_macro::{Group, Delimiter, TokenStream};

// 创建 (1 + 2)
let inner = "1 + 2".parse::<TokenStream>().unwrap();
let group = Group::new(Delimiter::Parenthesis, inner);

// 获取分隔符
let delim = group.delimiter();

// 获取内部流
let stream = group.stream();

// 获取 span
let span = group.span();
let span_open = group.span_open();
let span_close = group.span_close();
```

---

## 9. Diagnostic API

### 9.1 基本诊断

```rust
#![feature(proc_macro_diagnostic)]

use proc_macro::{Span, Diagnostic, Level};

#[proc_macro]
pub fn diagnostic_demo(input: TokenStream) -> TokenStream {
    let span = Span::call_site();

    // 错误
    span.error("This is an error").emit();

    // 警告
    span.warning("This is a warning").emit();

    // 注释
    span.note("This is a note").emit();

    // 帮助
    span.help("Try this instead").emit();

    TokenStream::new()
}
```

---

### 9.2 多 Span 诊断

```rust
use proc_macro::{Span, Diagnostic, Level};

let span1 = Span::call_site();
let span2 = Span::call_site();

Diagnostic::spanned(vec![span1, span2], Level::Error, "Multiple locations")
    .note("First location")
    .note("Second location")
    .emit();
```

---

### 9.3 诊断级别

```rust
pub enum Level {
    Error,
    Warning,
    Note,
    Help,
}
```

---

## 10. proc_macro2

### 10.1 区别与优势

| 特性     | proc_macro | proc_macro2 |
| :--- | :--- | :--- || 使用位置 | 仅过程宏   | 任意代码    |
| 单元测试 | ❌         | ✅          |
| 可移植性 | 编译器绑定 | 独立实现    |
| 功能     | 基础       | 增强        |

**推荐用法**:

```rust
// 使用 proc_macro2 + syn + quote 组合
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::parse_macro_input;

#[proc_macro_derive(MyTrait)]
pub fn my_trait(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as syn::DeriveInput);

    // 内部使用 TokenStream2
    let expanded = my_trait_impl(&input);

    TokenStream::from(expanded)
}

fn my_trait_impl(input: &syn::DeriveInput) -> TokenStream2 {
    // 可以单元测试这个函数！
    quote! {
        // ...
    }
}
```

---

### 10.2 互操作

```rust
use proc_macro::TokenStream as TokenStream1;
use proc_macro2::TokenStream as TokenStream2;

// TokenStream1 -> TokenStream2
let ts1: TokenStream1 = /* ... */;
let ts2: TokenStream2 = ts1.into();

// TokenStream2 -> TokenStream1
let ts2: TokenStream2 = /* ... */;
let ts1: TokenStream1 = ts2.into();

// 双向转换无损
```

---

**相关文档**:

- [声明宏完整参考](./01_声明宏完整参考.md)
- [syn-quote参考](./03_syn-quote参考.md)
- [宏卫生性参考](./04_宏卫生性参考.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
