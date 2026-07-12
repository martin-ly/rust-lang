> **EN**: syn and quote Reference
> **Summary**: Authoritative concept page for `syn & quote 完整参考`. Content migrated from `crates/c11_macro_system_proc/docs/tier_03_references/03_syn_quote_reference.md`.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [专家]
> **内容分级**: [参考级]
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **S+P** — Structure + Procedure
> **双维定位**: S×App — 应用 syn/quote API
> **前置依赖**: [过程宏（Procedural Macro）](02_proc_macro.md) · [宏术语表](06_macro_glossary.md)
> **后置概念**: [生产级宏（Macro）开发](05_production_grade_macro_development.md) · [宏卫生性](09_macro_hygiene.md)
> **定理链**: Parse Input ⟹ Transform AST ⟹ Emit Tokens
>
> **权威来源**: 本页为 `syn and quote Reference` 的权威概念页；crate 文档仅保留导航 stub。

# syn & quote 完整参考

**最后更新**: 2025-12-11
**适用版本**: syn 2.0, quote 1.0

本文档提供 `syn` 和 `quote` 库的完整使用参考，这是过程宏（Procedural Macro）开发的核心工具。

---

## 📋 目录

- [syn \& quote 完整参考](#syn--quote-完整参考)
  - [📋 目录](#-目录)
  - [1. syn 库概述](#1-syn-库概述)
    - [1.1 核心功能](#11-核心功能)
    - [1.2 features 配置](#12-features-配置)
    - [1.3 基本使用](#13-基本使用)
  - [2. syn 解析 API](#2-syn-解析-api)
    - [2.1 parse\_macro\_input](#21-parse_macro_input)
    - [2.2 DeriveInput](#22-deriveinput)
    - [2.3 ItemFn](#23-itemfn)
    - [2.4 自定义解析](#24-自定义解析)
  - [3. syn 数据结构](#3-syn-数据结构)
    - [3.1 类型 (Type)](#31-类型-type)
    - [3.2 表达式 (Expr)](#32-表达式-expr)
    - [3.3 模式 (Pat)](#33-模式-pat)
    - [3.4 路径 (Path)](#34-路径-path)
  - [4. syn 属性处理](#4-syn-属性处理)
    - [4.1 解析属性](#41-解析属性)
    - [4.2 NestedMeta](#42-nestedmeta)
    - [4.3 自定义属性参数](#43-自定义属性参数)
  - [5. quote 库概述](#5-quote-库概述)
    - [5.1 核心功能](#51-核心功能)
    - [5.2 基本语法](#52-基本语法)
  - [6. quote! 宏详解](#6-quote-宏详解)
    - [6.1 插值 (#var)](#61-插值-var)
    - [6.2 重复 (#(...)\*)](#62-重复-)
    - [6.3 条件生成](#63-条件生成)
  - [7. quote\_spanned](#7-quote_spanned)
    - [7.1 Span 控制](#71-span-控制)
    - [7.2 错误位置](#72-错误位置)
  - [8. ToTokens trait](#8-totokens-trait)
    - [8.1 实现 ToTokens](#81-实现-totokens)
    - [8.2 自定义类型转换](#82-自定义类型转换)
  - [9. 常见模式](#9-常见模式)
    - [9.1 Derive 宏模式](#91-derive-宏模式)
    - [9.2 属性宏模式](#92-属性宏模式)
    - [9.3 函数宏模式](#93-函数宏模式)
  - [10. 最佳实践](#10-最佳实践)
    - [10.1 错误处理 (Error Handling)](#101-错误处理-error-handling)
    - [10.2 性能优化](#102-性能优化)
    - [10.3 可测试性](#103-可测试性)
  - [认知路径](#认知路径)
  - [定理链](#定理链)
  - [反命题](#反命题)
  - [反向推理](#反向推理)
  - [9. 实测示例：derive 宏的最小可用骨架（2026-07-12 回填）](#9-实测示例derive-宏的最小可用骨架2026-07-12-回填)
  - [过渡段](#过渡段)
  - [国际权威参考 / International Authority References（P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp1-学术--p2-生态)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：`quote!` 与 `quote_spanned!` 的分工（🟢 基础）](#测验-1quote-与-quote_spanned-的分工-基础)
    - [测验 2：`ToTokens` trait 的角色（🟡 进阶）](#测验-2totokens-trait-的角色-进阶)
    - [测验 3：syn/quote 的边界与卫生性（🔴 专家，联动「反命题」节）](#测验-3synquote-的边界与卫生性-专家联动反命题节)
  - [⚠️ 反例与陷阱](#️-反例与陷阱)
    - [反例：声明宏中拼接标识符（rustc 1.97.0 实测）](#反例声明宏中拼接标识符rustc-1970-实测)
    - [✅ 修正：显式传完整名称，或用 `paste`  crate / 过程宏](#-修正显式传完整名称或用-paste--crate--过程宏)

---

## 1. syn 库概述

`syn` 是「把 `TokenStream` 解析为类型化 Rust AST」的事实标准库，三个使用要点：

- **核心功能**：syn 为 Rust 语法定义了完整的 AST 类型树（`DeriveInput`、`ItemFn`、`Expr`、`Type`、`Pat` 等百余种节点），并提供「`TokenStream → AST 节点」的`Parse` trait 实现。它的定位是「解析器即库」——过程宏作者无需手写 token 级解析，直接获得「字段列表是什么、属性写了什么」的结构化答案。
- **features 配置**：syn 体积大、编译慢（完整构建常占宏 crate 编译时间的 70%+），按需开启 feature 是工程惯例——`default-features = false` 后只开 `derive`（derive 宏）、`parsing`/`printing`（解析与输出）、`full`（解析完整 Rust 文件，属性宏/函数宏需要）、`extra-traits`（AST 节点的 `Debug`/`Eq`，测试需要）。裁剪后编译时间可降一半以上。
- **基本使用**：入口模式固定为两步——`let input = parse_macro_input!(tokens as DeriveInput);`（失败自动生成编译错误并提前返回）→ 读 `input.ident`/`input.generics`/`input.data` 驱动代码生成。`parse_macro_input!` 的「错误即编译错误」语义是 syn  ergonomics 的核心：宏内的 `Result` 一律可用 `?` 传播，最终经 `to_compile_error()` 落到用户代码的 span 上。

判定 syn 的引入范围：derive 宏用 `derive + parsing + printing` 三 feature 起步；需要解析函数体/表达式时加 `full`；只在「确知性能瓶颈」时才考虑手写 token 解析替代 syn（极少正当）。

### 1.1 核心功能

`syn` 是 Rust 语法解析库，提供：

- 完整的 Rust 语法 AST
- 灵活的解析 API
- 精确的错误位置
- 零成本抽象（Zero-Cost Abstraction）

---

### 1.2 features 配置

```toml
[dependencies]
syn = { version = "2.0", features = ["full", "extra-traits"] }

# 常用 features:
# - "full": 完整 Rust 语法支持
# - "derive": 仅 DeriveInput
# - "parsing": 解析 trait
# - "printing": 打印 trait
# - "extra-traits": Debug/Eq/PartialEq
```

---

### 1.3 基本使用

```rust
use syn::{parse_macro_input, DeriveInput};
use proc_macro::TokenStream;

#[proc_macro_derive(MyTrait)]
pub fn my_trait(input: TokenStream) -> TokenStream {
    // 解析输入
    let input = parse_macro_input!(input as DeriveInput);

    // 提取信息
    let name = &input.ident;
    let generics = &input.generics;

    // 生成代码
    quote::quote! {
        impl #generics MyTrait for #name #generics {
            // ...
        }
    }.into()
}
```

---

## 2. syn 解析 API

syn 的解析 API 按「输入语法类别」分层，四个常用入口：

- **`parse_macro_input!`**：过程宏入口的标准宏——`parse_macro_input!(tokens as T)` 等价于「`T::parse(tokens)` 失败时 `return err.to_compile_error().into()`」。它强制了「解析错误 = 编译错误」的正确流向，避免新手把解析失败写成 panic（宏 panic 会显示为「proc macro panicked」的无信息错误）。
- **`DeriveInput`**：derive 宏的输入类型——三字段覆盖全部信息：`ident`（类型名）、`generics`（泛型参数 + where 子句，生成 impl 时用 `split_for_impl()` 拆成 `impl_generics`/`ty_generics`/`where_clause` 三件套）、`data`（`Data::Struct`/`Enum`/`Union` 的字段/变体详情）。derive 宏 80% 的逻辑是「遍历 `data` 的字段，为每个字段生成一段代码」。
- **`ItemFn`**：属性宏标注函数时的输入——`sig`（签名：`fn` 名、参数、返回类型）、`block`（函数体）、`attrs`/`vis`（外层属性与可见性）。典型改写模式：保留 `sig`，把 `block` 包进「前置逻辑 + 原调用 + 后置逻辑」（`#[instrument]` 的 tracing 注入即此模式）。
- **自定义解析**：DSL 式属性参数（`#[my(key = "val", list(a, b))]`）需实现 `Parse` trait——`ParseStream` 提供 `parse::<Ident>()`、`peek`/`lookahead1()` 前瞻、`parse_terminated` 列表解析等组合子，错误经 `lookahead.error()` 生成带 span 的诊断。

选型判定：derive → `DeriveInput`；标注函数/结构 → `ItemFn`/`ItemStruct`；属性带参数 → 自定义 `Parse`；只需标识符/字面量 → `parse_macro_input!(tokens as Ident/LitStr)` 直接到位。

### 2.1 parse_macro_input

```rust
use syn::{parse_macro_input, DeriveInput, ItemFn, Expr};
use proc_macro::TokenStream;

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    // 解析为 DeriveInput
    let input = parse_macro_input!(input as DeriveInput);
    // ...
}

#[proc_macro_attribute]
pub fn my_attr(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // 解析为函数
    let item = parse_macro_input!(item as ItemFn);
    // ...
}

#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // 解析为表达式
    let expr = parse_macro_input!(input as Expr);
    // ...
}
```

---

### 2.2 DeriveInput

```rust
pub struct DeriveInput {
    pub attrs: Vec<Attribute>,
    pub vis: Visibility,
    pub ident: Ident,
    pub generics: Generics,
    pub data: Data,
}

pub enum Data {
    Struct(DataStruct),
    Enum(DataEnum),
    Union(DataUnion),
}
```

**示例**:

```rust
use syn::{parse_macro_input, DeriveInput, Data, Fields};

#[proc_macro_derive(MyTrait)]
pub fn my_trait(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = &input.ident;

    match &input.data {
        Data::Struct(data_struct) => {
            match &data_struct.fields {
                Fields::Named(fields) => {
                    for field in &fields.named {
                        let field_name = &field.ident;
                        let field_type = &field.ty;
                        println!("{}: {}",
                                 quote::quote!(#field_name),
                                 quote::quote!(#field_type));
                    }
                }
                Fields::Unnamed(fields) => {
                    println!("Tuple struct with {} fields", fields.unnamed.len());
                }
                Fields::Unit => {
                    println!("Unit struct");
                }
            }
        }
        Data::Enum(data_enum) => {
            for variant in &data_enum.variants {
                let variant_name = &variant.ident;
                println!("Variant: {}", variant_name);
            }
        }
        Data::Union(_) => {
            panic!("Unions not supported");
        }
    }

    TokenStream::new()
}
```

---

### 2.3 ItemFn

```rust
pub struct ItemFn {
    pub attrs: Vec<Attribute>,
    pub vis: Visibility,
    pub sig: Signature,
    pub block: Box<Block>,
}

pub struct Signature {
    pub ident: Ident,
    pub inputs: Punctuated<FnArg, Token![,]>,
    pub output: ReturnType,
    // ...
}
```

**示例**:

```rust
use syn::{parse_macro_input, ItemFn};

#[proc_macro_attribute]
pub fn log_calls(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut func = parse_macro_input!(item as ItemFn);

    let func_name = &func.sig.ident;
    let block = &func.block;

    // 添加日志
    func.block = syn::parse_quote! {
        {
            println!("Calling {}", stringify!(#func_name));
            let result = #block;
            println!("Returning from {}", stringify!(#func_name));
            result
        }
    };

    quote::quote!(#func).into()
}
```

---

### 2.4 自定义解析

实现 `Parse` trait：

```rust
use syn::{parse::{Parse, ParseStream}, Result, Ident, Token};

struct MyInput {
    name: Ident,
    value: i32,
}

impl Parse for MyInput {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Ident = input.parse()?;
        input.parse::<Token![=]>()?;
        let value: syn::LitInt = input.parse()?;

        Ok(MyInput {
            name,
            value: value.base10_parse()?,
        })
    }
}

#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as MyInput);
    let name = &input.name;
    let value = input.value;

    quote::quote! {
        const #name: i32 = #value;
    }.into()
}

// 使用: my_macro!(FOO = 42);
```

---

## 3. syn 数据结构

「syn 数据结构」部分按类型 (Type)、表达式 (Expr)、模式 (Pat)与路径 (Path)的顺序逐层展开。

### 3.1 类型 (Type)

```rust
pub enum Type {
    Path(TypePath),           // std::vec::Vec
    Reference(TypeReference), // &T, &mut T
    Tuple(TypeTuple),        // (i32, String)
    Array(TypeArray),        // [T; N]
    Slice(TypeSlice),        // [T]
    // ... 更多
}
```

**示例**:

```rust
use syn::{Type, TypePath};

fn get_inner_type(ty: &Type) -> Option<&Type> {
    if let Type::Path(TypePath { path, .. }) = ty {
        if path.segments.last()?.ident == "Vec" {
            // 提取 Vec<T> 中的 T
            if let syn::PathArguments::AngleBracketed(args) =
                &path.segments.last()?.arguments
            {
                if let Some(syn::GenericArgument::Type(inner)) = args.args.first() {
                    return Some(inner);
                }
            }
        }
    }
    None
}
```

---

### 3.2 表达式 (Expr)

```rust
pub enum Expr {
    Binary(ExprBinary),    // a + b
    Call(ExprCall),        // f(x)
    If(ExprIf),           // if cond { }
    Match(ExprMatch),     // match x { }
    // ... 更多
}
```

---

### 3.3 模式 (Pat)

```rust
pub enum Pat {
    Ident(PatIdent),      // x
    Tuple(PatTuple),      // (x, y)
    Struct(PatStruct),    // Point { x, y }
    // ... 更多
}
```

---

### 3.4 路径 (Path)

```rust
pub struct Path {
    pub segments: Punctuated<PathSegment, Token![::]>,
}

pub struct PathSegment {
    pub ident: Ident,
    pub arguments: PathArguments,
}
```

**示例**:

```rust
use syn::{Path, PathSegment};

// 创建 std::vec::Vec
let path: Path = syn::parse_quote!(std::vec::Vec);

// 提取最后一段
let last_segment = path.segments.last().unwrap();
assert_eq!(last_segment.ident, "Vec");
```

---

## 4. syn 属性处理

本节将「syn 属性处理」分解为若干主题：解析属性、NestedMeta与自定义属性参数。

### 4.1 解析属性

```rust
use syn::{Attribute, Meta, MetaList, MetaNameValue};

fn parse_attributes(attrs: &[Attribute]) {
    for attr in attrs {
        match &attr.meta {
            Meta::Path(path) => {
                // #[my_attr]
                println!("Path: {}", quote::quote!(#path));
            }
            Meta::List(MetaList { path, tokens, .. }) => {
                // #[my_attr(arg1, arg2)]
                println!("List: {} with {}",
                         quote::quote!(#path),
                         quote::quote!(#tokens));
            }
            Meta::NameValue(MetaNameValue { path, value, .. }) => {
                // #[my_attr = "value"]
                println!("NameValue: {} = {}",
                         quote::quote!(#path),
                         quote::quote!(#value));
            }
        }
    }
}
```

---

### 4.2 NestedMeta

```rust
use syn::{Attribute, Meta, MetaList};

fn parse_derive_helper(attr: &Attribute) -> syn::Result<()> {
    let meta = &attr.meta;

    if let Meta::List(MetaList { tokens, .. }) = meta {
        let nested: syn::punctuated::Punctuated<syn::Meta, syn::Token![,]> =
            syn::parse2(tokens.clone())?;

        for meta in nested {
            match meta {
                Meta::Path(path) => {
                    println!("Flag: {}", quote::quote!(#path));
                }
                Meta::NameValue(nv) => {
                    println!("{} = {}",
                             quote::quote!(#nv.path),
                             quote::quote!(#nv.value));
                }
                _ => {}
            }
        }
    }

    Ok(())
}
```

---

### 4.3 自定义属性参数

```rust
use syn::{parse::{Parse, ParseStream}, Result, Ident, LitStr, Token};

struct MyAttrArgs {
    name: Ident,
    value: LitStr,
}

impl Parse for MyAttrArgs {
    fn parse(input: ParseStream) -> Result<Self> {
        let name: Ident = input.parse()?;
        input.parse::<Token![=]>()?;
        let value: LitStr = input.parse()?;

        Ok(MyAttrArgs { name, value })
    }
}

#[proc_macro_attribute]
pub fn my_attr(attr: TokenStream, item: TokenStream) -> TokenStream {
    let args = parse_macro_input!(attr as MyAttrArgs);
    // 使用 args.name 和 args.value
    item
}

// 使用: #[my_attr(name = "value")]
```

---

## 5. quote 库概述

本节围绕「quote 库概述」展开，覆盖核心功能 与 基本语法 两个方面。

### 5.1 核心功能

`quote` 提供类 Rust 语法生成代码：

- 自然的代码生成语法
- 类型安全的插值
- 自动 Span 传播

---

### 5.2 基本语法

```rust
use quote::quote;

let name = syn::Ident::new("MyStruct", proc_macro2::Span::call_site());

let expanded = quote! {
    impl Debug for #name {
        fn fmt(&self, f: &mut Formatter) -> Result {
            write!(f, stringify!(#name))
        }
    }
};

// expanded 是 proc_macro2::TokenStream
```

---

## 6. quote! 宏详解

`quote!` 是「用 Rust 语法写代码模板」的宏——参数是「像 Rust 代码的模板」，输出是 `proc_macro2::TokenStream`。三个核心机制：

- **插值（`#var`）**：`#` 后接实现 `ToTokens` 的变量，把该值「展开为 token」嵌入模板。`syn` 的全部 AST 节点、基础类型（`String` → 字符串字面量、`usize` → 数字字面量、`Ident` → 标识符）都实现了 `ToTokens`。构造标识符用 `quote::format_ident!("{}_impl", name)`（拼接用户类型名生成新标识符，带 span 控制）。
- **重复（`#(...)*`）**：模板段内出现「重复变量」（`Vec`/`Iterator` 的 `ToTokens` 项）时，`#( ... ),*` 按「每项一次、`,` 分隔」展开——`#(#fields),*` 生成字段列表，分隔符可为 `,`/`;`/省略。多变量同步重复要求长度一致（`#(#names: #types),*`）；`#(...)?` 处理 `Option`（有值展开一次）。
- **条件生成**：quote 本身无 `if`——条件逻辑写在 quote 外面：先 `let extra = if cond { quote!(...) } else { quote!() };`（空 `quote!()` 是零 token 的单位元），再 `#extra` 插入。这是「模板保持声明式、逻辑保持命令式」的分工惯例。

组合范式：`let methods = fields.iter().map(|f| { let name = &f.ident; quote!( pub fn #name(&self) -> &#ty { &self.#name } ) });` 然后 `quote!( impl #ident { #(#methods)* } )`——「map 生成片段列表 + 外层一次性组装」是 quote 的标准结构，覆盖绝大多数 derive 宏场景。

### 6.1 插值 (#var)

```rust
use quote::quote;

let name = quote!(MyType);
let field = quote!(value);
let ty = quote!(i32);

let output = quote! {
    struct #name {
        #field: #ty,
    }
};

// 结果:
// struct MyType {
//     value: i32,
// }
```

---

### 6.2 重复 (#(...)\*)

```rust
use quote::quote;

let fields = vec![
    quote!(field1: i32),
    quote!(field2: String),
    quote!(field3: bool),
];

let output = quote! {
    struct MyStruct {
        #(#fields),*
    }
};

// 结果:
// struct MyStruct {
//     field1: i32,
//     field2: String,
//     field3: bool
// }
```

**更复杂的重复**:

```rust
let names = vec![quote!(x), quote!(y), quote!(z)];
let types = vec![quote!(i32), quote!(f64), quote!(String)];

let output = quote! {
    (#(let #names: #types),*)
};

// 结果: (let x: i32, let y: f64, let z: String)
```

---

### 6.3 条件生成

```rust
use quote::quote;

let is_public = true;
let vis = if is_public {
    quote!(pub)
} else {
    quote!()
};

let output = quote! {
    #vis struct MyStruct {
        field: i32,
    }
};

// 结果: pub struct MyStruct { field: i32, }
```

---

## 7. quote_spanned

本节从 Span 控制 与 错误位置 两个层面剖析「quote_spanned」。

### 7.1 Span 控制

```rust
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;

let field = /* syn::Field */;
let field_span = field.span();

// 使用 field 的 span
let expanded = quote_spanned! {field_span=>
    compile_error!("Invalid field");
};

// 错误将指向原始 field 位置
```

---

### 7.2 错误位置

```rust
use quote::quote_spanned;
use syn::spanned::Spanned;

fn generate_impl(input: &syn::DeriveInput) -> proc_macro2::TokenStream {
    for field in get_fields(input) {
        let field_span = field.span();

        // 检查字段类型
        if !is_valid_type(&field.ty) {
            return quote_spanned! {field_span=>
                compile_error!("Field type not supported");
            };
        }
    }

    quote! {
        // 正常生成代码
    }
}
```

---

## 8. ToTokens trait

本节围绕「ToTokens trait」展开，覆盖实现 ToTokens 与 自定义类型转换 两个方面。

### 8.1 实现 ToTokens

```rust
use quote::{ToTokens, TokenStreamExt};

struct MyType {
    name: syn::Ident,
    value: i32,
}

impl ToTokens for MyType {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let name = &self.name;
        let value = self.value;

        tokens.append_all(quote! {
            const #name: i32 = #value;
        });
    }
}

// 使用
let my_type = MyType { /* ... */ };
let output = quote! {
    #my_type
};
```

---

### 8.2 自定义类型转换

```rust
use quote::ToTokens;

#[derive(Clone)]
struct Config {
    debug: bool,
    optimize: bool,
}

impl ToTokens for Config {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        let debug = self.debug;
        let optimize = self.optimize;

        tokens.extend(quote! {
            ConfigStruct {
                debug: #debug,
                optimize: #optimize,
            }
        });
    }
}
```

---

## 9. 常见模式

「常见模式」部分按 Derive 宏模式、属性宏模式与函数宏模式的顺序逐层展开。

### 9.1 Derive 宏模式

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyTrait)]
pub fn derive_my_trait(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let expanded = quote! {
        impl #impl_generics MyTrait for #name #ty_generics #where_clause {
            fn my_method(&self) {
                println!("MyTrait for {}", stringify!(#name));
            }
        }
    };

    TokenStream::from(expanded)
}
```

---

### 9.2 属性宏模式

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

#[proc_macro_attribute]
pub fn my_attribute(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);

    let name = &input.sig.ident;
    let block = &input.block;
    let sig = &input.sig;

    let expanded = quote! {
        #sig {
            println!("Before {}", stringify!(#name));
            let result = #block;
            println!("After {}", stringify!(#name));
            result
        }
    };

    TokenStream::from(expanded)
}
```

---

### 9.3 函数宏模式

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Ident};

#[proc_macro]
pub fn create_struct(input: TokenStream) -> TokenStream {
    let name = parse_macro_input!(input as Ident);

    let expanded = quote! {
        #[derive(Debug, Clone)]
        pub struct #name {
            pub value: i32,
        }

        impl #name {
            pub fn new(value: i32) -> Self {
                Self { value }
            }
        }
    };

    TokenStream::from(expanded)
}
```

---

## 10. 最佳实践

过程宏工程的三条最佳实践，分别针对「用户面对的错误」「编译性能」「回归防护」：

- **错误处理（Error Handling）**：宏内一切可失败操作返回 `syn::Result`，用 `?` 传播；错误构造用 `syn::Error::new_spanned(node, "消息")`——`node` 的 span 决定 rustc 报错的红线画在用户代码哪个 token 下（指向 `DeriveInput.ident` 即指向类型名，指向某字段即指向该字段）。多个错误用 `Error::combine` 聚合一次报出。反模式：`.unwrap()`（宏 panic = 无定位的「proc macro panicked」）、`Span::call_site()` 笼统定位（用户不知道错在哪个字段）。
- **性能优化**：syn 按需开 feature（见 §1）；生成逻辑避免「`quote!` 结果 `to_string()` 再 `parse`」的往返（每次往返是一次完整解析，应直接构造 `TokenStream`）；大宏（如 serde）采用「预分配 + `extend` 追加」而非反复 `quote!` 嵌套。宏的编译成本 = 「宏 crate 自身编译」+「每次调用的解析/生成」，前者由 feature 裁剪控制，后者由避免重解析控制。
- **可测试性**：生成逻辑写成「`proc_macro2::TokenStream → TokenStream`」的纯函数，单元测试直接断言输出（`prettyplease` 格式化后快照对比）；集成测试用 `trybuild` 锁定「应通过/应失败 + stderr」；复杂宏用「测试 crate」模拟真实调用（含泛型、where 子句、生命周期等边界输入）。三层测试使「宏升级 syn 版本」从盲改变为可验证重构。

### 10.1 错误处理 (Error Handling)

```rust
use syn::{Error, Result};
use quote::quote;

fn validate_input(input: &syn::DeriveInput) -> Result<()> {
    if input.ident.to_string().starts_with('_') {
        return Err(Error::new_spanned(
            &input.ident,
            "Type name cannot start with underscore"
        ));
    }
    Ok(())
}

#[proc_macro_derive(MyTrait)]
pub fn my_trait(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    if let Err(e) = validate_input(&input) {
        return e.to_compile_error().into();
    }

    // 正常处理
    TokenStream::new()
}
```

---

### 10.2 性能优化

```rust
// ✅ 好：复用 TokenStream
let mut output = TokenStream::new();
for item in items {
    output.extend(quote! { #item });
}

// ❌ 差：多次分配
let output = items.iter()
    .map(|item| quote! { #item })
    .collect::<TokenStream>();
```

---

### 10.3 可测试性

```rust
use proc_macro2::TokenStream;
use quote::quote;

// 核心逻辑使用 proc_macro2
fn my_trait_impl(input: &syn::DeriveInput) -> TokenStream {
    let name = &input.ident;
    quote! {
        impl MyTrait for #name {
            // ...
        }
    }
}

// 入口函数仅做转换
#[proc_macro_derive(MyTrait)]
pub fn my_trait(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    my_trait_impl(&input).into()
}

// 单元测试
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_my_trait() {
        let input: syn::DeriveInput = syn::parse_quote! {
            struct MyStruct {
                field: i32,
            }
        };

        let output = my_trait_impl(&input);
        assert!(output.to_string().contains("impl MyTrait"));
    }
}
```

---

**相关文档**:

- [声明宏（Declarative Macro）完整参考](/crates/c11_macro_system_proc/docs/tier_03_references/01_declarative_macros_complete_reference.md)
- [过程宏API参考](/crates/c11_macro_system_proc/docs/tier_03_references/02_procedural_macro_api_reference.md)
- [宏卫生性参考](/crates/c11_macro_system_proc/docs/tier_03_references/04_macro_hygiene_reference.md)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

> **向下引用（Reference）**: 参见 [17_macro_patterns](../../02_intermediate/06_macros_and_metaprogramming/03_macro_patterns.md)

## 认知路径

1. **问题识别**: 识别 syn/quote 是 Rust 过程宏开发的核心工具链。
2. **概念建立**: 掌握 `parse_macro_input!`、`DeriveInput`、`quote!` 等关键 API 的使用与限制。
3. **机制推理**: 通过解析输入 ⟹ 转换 AST ⟹ 生成 token 的定理链组织宏实现。
4. **边界辨析**: 辨析“syn/quote 是必须的”等反命题，理解直接操作 TokenStream 的场景。
5. **迁移应用**: 将 syn/quote 参考与生产级开发、卫生性主题链接。

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 精确解析 ⟹ 健壮宏 | 使用 syn 的类型化 AST 解析输入 | 宏在错误输入下给出清晰诊断 |
| AST 转换 ⟹ 代码生成灵活 | 在解析后的数据结构上进行变换 | 可以实现复杂的 derive/attribute 逻辑 |
| quote 生成 ⟹ 保留可读性 | 使用 `quote!` 以类 Rust 语法生成 token | 生成的代码更易审查与调试 |

## 反命题

> **反命题 1**: "syn 和 quote 是过程宏必须的" ⟹ 不成立。简单宏可以直接操作 `proc_macro::TokenStream`。
>
> **反命题 2**: "解析越宽松越好" ⟹ 不成立。过度宽松的解析会隐藏用户错误，导致难以诊断的生成代码。
>
> **反命题 3**: "quote! 中的变量会自动 hygiene" ⟹ 不成立。仍需关注 span 来源与标识符捕获。
>
## 反向推理

> **反向推理 1**: 宏在有效输入下 panic 或生成错误代码 ⟸ 说明 syn 解析或 AST 转换分支未覆盖该输入形状。
>
> **反向推理 2**: 生成代码报错位置混乱 ⟸ 说明 quote! 中未正确传递 span。
>
## 9. 实测示例：derive 宏的最小可用骨架（2026-07-12 回填）

> **来源**: [docs.rs — syn](https://docs.rs/syn/latest/syn/) · [docs.rs — quote](https://docs.rs/quote/latest/quote/) · [Rust Reference — Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)

下列骨架演示 syn/quote 的核心工作流：**`parse_macro_input!` 解析 → 提取 AST 节点 → `quote!` 插值生成**。已在临时 proc-macro crate（`syn = "2"` + `quote = "1"`，`edition = "2024"`）经 `cargo build --offline` 实测编译通过：

```rust,ignore
// proc-macro crate: Cargo.toml 需 [lib] proc-macro = true
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

/// 为结构体生成 `fn type_name() -> &'static str`，返回类型名字符串。
#[proc_macro_derive(TypeName)]
pub fn derive_type_name(input: TokenStream) -> TokenStream {
    // ① 解析：TokenStream → DeriveInput AST（含 ident / generics / data）
    let ast = parse_macro_input!(input as DeriveInput);
    // ② 提取：取类型标识符（宏卫生：def-site 生成 impl 块）
    let name = &ast.ident;
    let name_str = name.to_string();
    // ③ 生成：quote! 插值 #name / #name_str → 输出 TokenStream
    quote! {
        impl #name {
            pub fn type_name() -> &'static str { #name_str }
        }
    }
    .into()
}
```

工程要点（与 §1–§6 API 参照）：

- `parse_macro_input!` 在解析失败时自动生成 `compile_error!` 输出，是过程宏错误处理的标准入口；
- `quote!` 的 `#ident` 插值自动处理 `ToTokens`；重复插值用 `#(...)*` 配合分隔符；
- 生产级 derive 应处理 `ast.generics`（用 `split_for_impl()` 拆出 `impl_generics/ty_generics/where_clause`），本骨架为最小形式；
- 错误诊断建议配合 `syn::Error::new_spanned` 定位到具体 token（参见 [生产级宏开发](05_production_grade_macro_development.md) 与 [宏调试与诊断](04_macro_debugging_and_diagnostics.md)）。

> **权威来源**: [docs.rs — syn](https://docs.rs/syn/latest/syn/) · [docs.rs — quote](https://docs.rs/quote/latest/quote/) · [Rust Reference — Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)（链接 2026-07-12 curl 实测 200；代码 `cargo build --offline` 实测，syn 2.x + quote 1.x）

---

## 过渡段

> **过渡**: 从解析 API 过渡到 AST 数据结构，可以理解 syn 将无结构 token 转为可操作模型的价值。
>
> **过渡**: 从 AST 转换过渡到 quote 生成，可以建立“先解析、再变换、最后输出”的宏实现模式。
>
> **过渡**: 从 quote 生成过渡到卫生性，可以理解生成代码与调用方上下文之间的边界控制。
>

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/async-trait — 生态权威 API 文档](https://docs.rs/async-trait) · [docs.rs/syn — 生态权威 API 文档](https://docs.rs/syn)
- **P1 学术/形式化**: [Kohlbecker et al.: Hygienic Macro Expansion (LFP 1986, 卫生宏奠基)](https://dl.acm.org/doi/10.1145/319838.319859)

---

## 嵌入式测验（Embedded Quiz）

> W3-b 补充（2026-07-13）：本页原无嵌入式测验，按四级题型规范补 3 题（🟢🟡🔴 各 1 题，`<details>` 折叠答案），内容与本页正文严格一致；测验 3 与本页「反命题」节直接联动。

### 测验 1：`quote!` 与 `quote_spanned!` 的分工（🟢 基础）

生成 `compile_error!` 并希望错误信息指向用户输入的某个字段位置，应使用？

- A. `quote!`——它自动追踪所有输入 span
- B. `quote_spanned! {field_span=> compile_error!("...")}`——显式指定生成 token 的 span，错误定位到原始字段
- C. `format!` 拼接字符串再 parse
- D. `panic!`——过程宏的错误只能用 panic 报告

<details>
<summary>✅ 答案</summary>

**B 正确**。按本页 §7：`quote_spanned!` 用 `field.span()`（经 `syn::spanned::Spanned`）为生成的 token 指定 span，使 `compile_error!` 的错误指向用户的原始字段位置；`quote!` 生成的 token 默认 span 不绑定到具体输入节点，错误位置会落在宏调用处或生成代码内部。D 错：panic 会导致宏崩溃而非结构化诊断（见 §7.2 的模式）。

</details>

---

### 测验 2：`ToTokens` trait 的角色（🟡 进阶）

以下代码中 `impl ToTokens for MyType` 的收益是？

```rust,ignore
use quote::{ToTokens, quote};
struct MyType { /* ... */ }
impl ToTokens for MyType {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) { /* ... */ }
}
// 之后可在 quote! 中直接插值：quote! { #my_value }
```

- A. 让 `MyType` 可在 `quote!` 的 `#var` 插值中直接展开为 token，无需手动拼接
- B. 让 `MyType` 可被 serde 序列化
- C. 让 `MyType` 成为合法的过程宏入口类型
- D. 没有任何作用，`quote!` 不需要该 trait

<details>
<summary>✅ 答案</summary>

**A 正确**。按本页 §8：`ToTokens` 是 quote 的扩展点——为自定义 AST/中间类型实现 `to_tokens` 后，即可在 `quote! { #var }` 插值中直接展开（syn 的 `DeriveInput`、`Field` 等都实现了它）。B/C 与该 trait 无关；D 与插值机制矛盾。

</details>

---

### 测验 3：syn/quote 的边界与卫生性（🔴 专家，联动「反命题」节）

按本页「反命题」节，下列说法正确的有？（选出所有正确项）

- A. "syn 和 quote 是过程宏必须的"不成立：简单宏可直接操作 `proc_macro::TokenStream`
- B. "解析越宽松越好"不成立：过度宽松的解析会隐藏用户错误，导致难以诊断的生成代码
- C. "`quote!` 中的变量会自动 hygiene"不成立：仍需关注 span 来源与标识符捕获
- D. 只要用了 syn 解析，生成代码的报错位置就自动正确

<details>
<summary>✅ 答案</summary>

**A、B、C 正确**。按本页「反命题」节三条。D 错——报错位置取决于 span 传递：需用 `quote_spanned!` 或正确传播输入 span（本页「反向推理 2」：生成代码报错位置混乱 ⟸ 说明 `quote!` 中未正确传递 span）。卫生性（hygiene）在 quote 插值中不是自动的，标识符捕获与 span 来源必须显式管理。

</details>

## ⚠️ 反例与陷阱

本节以 `macro_rules!` 标识符拼接为反例，展示声明宏无法直接 paste 标识符、需 `paste` crate 或过程宏的边界。

### 反例：声明宏中拼接标识符（rustc 1.97.0 实测）

```rust,compile_fail
macro_rules! make_getter {
    ($field:ident) => {
        fn $field_name() {} // ❌ 声明宏不能拼接标识符
    };
}
fn main() { make_getter!(age); }
```

**错误**：`error: expected identifier`——`macro_rules!` 的片段替换是 token 级粘贴，不做标识符融合。

### ✅ 修正：显式传完整名称，或用 `paste`  crate / 过程宏

```rust
macro_rules! make_getter {
    ($name:ident) => {
        fn $name() -> u32 { 1 }
    };
}
make_getter!(age_name);
fn main() { println!("{}", age_name()); }
```
