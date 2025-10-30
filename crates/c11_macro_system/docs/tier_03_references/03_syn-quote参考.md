# syn & quote 完整参考

**最后更新**: 2025-10-24
**适用版本**: syn 2.0, quote 1.0

本文档提供 `syn` 和 `quote` 库的完整使用参考，这是过程宏开发的核心工具。

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
    - [10.1 错误处理](#101-错误处理)
    - [10.2 性能优化](#102-性能优化)
    - [10.3 可测试性](#103-可测试性)

---

## 1. syn 库概述

### 1.1 核心功能

`syn` 是 Rust 语法解析库，提供：

- 完整的 Rust 语法 AST
- 灵活的解析 API
- 精确的错误位置
- 零成本抽象

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

### 10.1 错误处理

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

- [声明宏完整参考](./01_声明宏完整参考.md)
- [过程宏API参考](./02_过程宏API参考.md)
- [宏卫生性参考](./04_宏卫生性参考.md)
