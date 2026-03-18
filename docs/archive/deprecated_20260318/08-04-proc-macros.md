# 过程宏开发深度指南

> **权威来源**: The Little Book of Rust Macros, proc-macro2 documentation, syn documentation
>
> **更新**: Rust 1.94 proc_macro_span API 稳定 ⚡

## 目录

- [过程宏开发深度指南](#过程宏开发深度指南)
  - [目录](#目录)
  - [1. 宏系统概述](#1-宏系统概述)
    - [过程宏类型](#过程宏类型)
  - [2. 声明宏（macro\_rules!）](#2-声明宏macro_rules)
    - [2.1 基础语法](#21-基础语法)
    - [2.2 重复模式](#22-重复模式)
    - [2.3 高级模式匹配](#23-高级模式匹配)
    - [2.4 递归宏](#24-递归宏)
    - [2.5 卫生性与 hygiene](#25-卫生性与-hygiene)
  - [3. 过程宏基础](#3-过程宏基础)
    - [3.1 项目设置](#31-项目设置)
    - [3.2 TokenStream 操作](#32-tokenstream-操作)
    - [3.3 使用 syn 解析](#33-使用-syn-解析)
  - [4. 派生宏（Derive Macros）](#4-派生宏derive-macros)
    - [4.1 基础派生宏](#41-基础派生宏)
    - [4.2 带辅助属性的派生宏](#42-带辅助属性的派生宏)
    - [4.3 复杂派生：序列化框架](#43-复杂派生序列化框架)
  - [5. 属性宏（Attribute Macros）](#5-属性宏attribute-macros)
    - [5.1 基础属性宏](#51-基础属性宏)
    - [5.2 路由宏示例](#52-路由宏示例)
    - [5.3 结构体转换宏](#53-结构体转换宏)
  - [6. 函数式宏（Function-like Macros）](#6-函数式宏function-like-macros)
    - [6.1 基础函数式宏](#61-基础函数式宏)
    - [6.2 SQL 查询宏](#62-sql-查询宏)
    - [6.3 HTML 模板宏](#63-html-模板宏)
  - [7. 高级技巧与模式](#7-高级技巧与模式)
    - [7.1 错误处理](#71-错误处理)
    - [7.2 泛型处理](#72-泛型处理)
    - [7.3 代码生成优化](#73-代码生成优化)
  - [8. Rust 1.94 过程宏新特性](#8-rust-194-过程宏新特性)
    - [8.1 proc\_macro\_span 稳定](#81-proc_macro_span-稳定)
    - [8.2 改进的诊断信息](#82-改进的诊断信息)
    - [8.3 性能优化](#83-性能优化)
    - [8.4 Cargo.toml 格式支持](#84-cargotoml-格式支持)
  - [9. 测试与调试](#9-测试与调试)
    - [9.1 单元测试](#91-单元测试)
    - [9.2 宏展开查看](#92-宏展开查看)
    - [9.3 调试技巧](#93-调试技巧)
  - [10. 实际案例](#10-实际案例)
    - [10.1 完整的 Builder 宏](#101-完整的-builder-宏)
    - [10.2 序列化/反序列化宏](#102-序列化反序列化宏)
    - [10.3 模拟框架宏](#103-模拟框架宏)
  - [总结](#总结)
  - [参考资源](#参考资源)

---

## 1. 宏系统概述

Rust 的宏系统提供了一种元编程能力，允许在编译时生成代码。Rust 提供两种宏系统：

1. **声明宏（Declarative Macros）**：使用 `macro_rules!` 定义，基于模式匹配
2. **过程宏（Procedural Macros）**：使用 Rust 代码操作 TokenStream

```rust
// 声明宏示例
macro_rules! vec_str {
    ($($x:expr),*) => {
        {
            let mut temp_vec = Vec::new();
            $(temp_vec.push($x.to_string());)*
            temp_vec
        }
    };
}

// 使用
let v = vec_str!["hello", "world"];
```

### 过程宏类型

| 类型 | 使用方式 | 典型用途 |
|------|----------|----------|
| 派生宏 | `#[derive(MyMacro)]` | 自动实现 trait |
| 属性宏 | `#[my_macro]` | 代码转换、装饰器 |
| 函数式宏 | `my_macro!(...)` | 自定义 DSL |

---

## 2. 声明宏（macro_rules!）

### 2.1 基础语法

```rust
macro_rules! say_hello {
    () => {
        println!("Hello!");
    };
}

macro_rules! create_function {
    // 匹配标识符
    ($func_name:ident) => {
        fn $func_name() {
            println!("You called {:?}()", stringify!($func_name));
        }
    };
}

create_function!(foo);
create_function!(bar);

fn main() {
    foo();  // 输出: You called "foo"()
    bar();  // 输出: You called "bar"()
}
```

### 2.2 重复模式

```rust
macro_rules! vector {
    // 空向量
    () => {
        Vec::new()
    };

    // 单个元素
    ($elem:expr) => {{
        let mut v = Vec::new();
        v.push($elem);
        v
    }};

    // 多个元素
    ($($elem:expr),+ $(,)?) => {{
        let mut v = Vec::new();
        $(v.push($elem);)*
        v
    }};
}

// 使用
let v1 = vector![];           // 空
let v2 = vector![1];          // 单个
let v3 = vector![1, 2, 3];    // 多个
let v4 = vector![1, 2, 3,];   // 带尾随逗号
```

### 2.3 高级模式匹配

```rust
macro_rules! complex_match {
    // 匹配表达式并赋值给变量
    (let $var:ident = $value:expr) => {
        let $var = $value;
    };

    // 匹配类型
    (type $name:ident = $ty:ty) => {
        type $name = $ty;
    };

    // 匹配代码块
    (fn $name:ident $block:block) => {
        fn $name() $block
    };

    // 匹配路径
    (use $path:path) => {
        use $path;
    };

    // 匹配元组模式
    (($($pat:pat),*)) => {
        ($($pat,)*)
    };
}

// 使用
complex_match!(let x = 42);
complex_match!(type MyInt = i32);
complex_match!(fn hello { println!("Hello"); });
complex_match!(use std::collections::HashMap);
```

### 2.4 递归宏

```rust
macro_rules! count_tts {
    () => (0usize);
    ($odd:tt $($a:tt $b:tt)*) => (count_tts!($($a)*) << 1 | 1usize);
    ($($a:tt $even:tt)*) => (count_tts!($($a)*) << 1);
}

// 计算参数数量
const N: usize = count_tts!(a b c d e f g);  // N = 7

// 递归生成嵌套结构
macro_rules! nested_struct {
    // 基础情况
    ($name:ident { $($field:ident: $ty:ty),* }) => {
        struct $name {
            $(pub $field: $ty,)*
        }
    };

    // 递归情况：嵌套结构
    ($outer:ident { $($field:ident: $inner:ident { $($inner_field:tt)* }),* }) => {
        $(nested_struct!($inner { $($inner_field)* });)*
        struct $outer {
            $(pub $field: $inner,)*
        }
    };
}

nested_struct!(Person {
    name: String,
    address: Address {
        street: String,
        city: String
    }
});
```

### 2.5 卫生性与 hygiene

```rust
macro_rules! hygienic_macro {
    ($val:expr) => {{
        // 这个 x 是宏内部的，不会与外部的 x 冲突
        let x = $val;
        x * 2
    }};
}

fn main() {
    let x = 5;
    let result = hygienic_macro!(10);  // result = 20
    println!("x is still {}", x);      // x is still 5
}

// 故意打破 hygiene（不推荐）
macro_rules! unhygienic {
    ($val:expr) => {{
        // 使用外部作用域的变量
        extern_variable = $val;
    }};
}
```

---

## 3. 过程宏基础

### 3.1 项目设置

```toml
# Cargo.toml
[package]
name = "my-proc-macro"
version = "0.1.0"
edition = "2021"
rust-version = "1.94"

[lib]
proc-macro = true

[dependencies]
proc-macro2 = "1.0"
quote = "1.0"
syn = { version = "2.0", features = ["full"] }
```

```rust
// lib.rs
use proc_macro::TokenStream;

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    // 实现...
    TokenStream::new()
}

#[proc_macro_attribute]
pub fn my_attribute(args: TokenStream, input: TokenStream) -> TokenStream {
    // 实现...
    input
}

#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // 实现...
    TokenStream::new()
}
```

### 3.2 TokenStream 操作

```rust
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};

fn basic_tokenstream() {
    // 创建 TokenStream
    let tokens: TokenStream = quote! {
        fn hello() {
            println!("Hello, World!");
        }
    };

    // 拼接 TokenStream
    let part1 = quote! { fn };
    let part2 = quote! { my_function() {} };
    let combined = quote! { #part1 #part2 };

    // 插值
    let name = quote::format_ident!("my_var");
    let ty = quote! { i32 };
    let value = 42;

    let declaration = quote! {
        let #name: #ty = #value;
    };
    // 生成: let my_var: i32 = 42;

    // 重复插值
    let fields = vec!["a", "b", "c"];
    let struct_def = quote! {
        struct MyStruct {
            #(pub #fields: i32,)*
        }
    };
    // 生成:
    // struct MyStruct {
    //     pub a: i32,
    //     pub b: i32,
    //     pub c: i32,
    // }
}
```

### 3.3 使用 syn 解析

```rust
use syn::{parse_macro_input, DeriveInput, Data, Fields, Attribute};
use quote::quote;

#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    // 解析输入
    let input = parse_macro_input!(input as DeriveInput);

    // 提取信息
    let name = input.ident;
    let builder_name = quote::format_ident!("{}Builder", name);

    // 获取结构体字段
    let fields = match input.data {
        Data::Struct(data) => match data.fields {
            Fields::Named(fields) => fields.named,
            _ => panic!("Only named fields supported"),
        },
        _ => panic!("Only structs supported"),
    };

    // 提取字段名和类型
    let field_names: Vec<_> = fields.iter()
        .map(|f| &f.ident)
        .collect();

    let field_types: Vec<_> = fields.iter()
        .map(|f| &f.ty)
        .collect();

    // 生成 Builder 实现
    let expanded = quote! {
        pub struct #builder_name {
            #( #field_names: Option<#field_types>, )*
        }

        impl #builder_name {
            pub fn new() -> Self {
                Self {
                    #( #field_names: None, )*
                }
            }

            #(
                pub fn #field_names(mut self, value: #field_types) -> Self {
                    self.#field_names = Some(value);
                    self
                }
            )*

            pub fn build(self) -> #name {
                #name {
                    #( #field_names: self.#field_names.unwrap(), )*
                }
            }
        }
    };

    expanded.into()
}
```

---

## 4. 派生宏（Derive Macros）

### 4.1 基础派生宏

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(HelloMacro)]
pub fn derive_hello_macro(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = input.ident;

    let expanded = quote! {
        impl HelloMacro for #name {
            fn hello_macro() {
                println!("Hello, Macro! My name is {}", stringify!(#name));
            }
        }
    };

    expanded.into()
}

// 使用
// #[derive(HelloMacro)]
// struct Pancakes;
//
// Pancakes::hello_macro();
```

### 4.2 带辅助属性的派生宏

```rust
use syn::{Attribute, Meta, Lit, NestedMeta};

#[proc_macro_derive(CustomDebug, attributes(debug))]
pub fn derive_custom_debug(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let fields_debug = match &input.data {
        syn::Data::Struct(data) => {
            match &data.fields {
                syn::Fields::Named(fields) => {
                    let field_fmts = fields.named.iter().map(|f| {
                        let field_name = &f.ident;
                        let field_ty = &f.ty;

                        // 检查 #[debug(skip)] 属性
                        let skip = f.attrs.iter().any(|attr| {
                            attr.path().is_ident("debug") &&
                            attr.parse_args::<syn::Ident>()
                                .map(|i| i == "skip")
                                .unwrap_or(false)
                        });

                        // 检查 #[debug(format = "...")] 属性
                        let format = f.attrs.iter().find_map(|attr| {
                            if !attr.path().is_ident("debug") {
                                return None;
                            }
                            // 解析属性...
                            None
                        });

                        if skip {
                            quote! {}
                        } else if let Some(fmt) = format {
                            quote! {
                                .field(stringify!(#field_name), &format_args!(#fmt, &self.#field_name))
                            }
                        } else {
                            quote! {
                                .field(stringify!(#field_name), &self.#field_name)
                            }
                        }
                    });

                    quote! {
                        f.debug_struct(stringify!(#name))
                            #(#field_fmts)*
                            .finish()
                    }
                }
                _ => panic!("Only named fields supported"),
            }
        }
        _ => panic!("Only structs supported"),
    };

    let expanded = quote! {
        impl std::fmt::Debug for #name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                #fields_debug
            }
        }
    };

    expanded.into()
}

// 使用
// #[derive(CustomDebug)]
// struct MyStruct {
//     #[debug(skip)]
//     internal_id: u64,
//     name: String,
//     #[debug(format = "{:.2}")]
//     value: f64,
// }
```

### 4.3 复杂派生：序列化框架

```rust
#[proc_macro_derive(Serialize, attributes(serialize))]
pub fn derive_serialize(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let serialize_impl = match &input.data {
        syn::Data::Struct(data) => {
            let field_serializations = serialize_struct_fields(&data.fields);
            quote! {
                fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                    let mut state = serializer.serialize_struct(stringify!(#name), #field_count)?;
                    #field_serializations
                    state.end()
                }
            }
        }
        syn::Data::Enum(data) => {
            let variant_serializations = data.variants.iter().map(|v| {
                let variant_name = &v.ident;
                // 处理每种变体类型
                match &v.fields {
                    syn::Fields::Unit => {
                        quote! {
                            Self::#variant_name => serializer.serialize_unit_variant(
                                stringify!(#name),
                                #variant_index,
                                stringify!(#variant_name)
                            )
                        }
                    }
                    syn::Fields::Unnamed(fields) => {
                        let field_count = fields.unnamed.len();
                        quote! {
                            Self::#variant_name(ref __field0 #(, ref __field #field_indices)*) => {
                                let mut __serde_state = serializer.serialize_tuple_variant(
                                    stringify!(#name),
                                    #variant_index,
                                    stringify!(#variant_name),
                                    #field_count
                                )?;
                                __serde_state.serialize_field(__field0)?;
                                #(__serde_state.serialize_field(__field #field_indices)?;)*
                                __serde_state.end()
                            }
                        }
                    }
                    syn::Fields::Named(fields) => {
                        // 类似处理...
                        quote! {}
                    }
                }
            });

            quote! {
                fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
                    match *self {
                        #(#variant_serializations),*
                    }
                }
            }
        }
        syn::Data::Union(_) => panic!("Unions not supported"),
    };

    let expanded = quote! {
        impl #impl_generics Serialize for #name #ty_generics #where_clause {
            #serialize_impl
        }
    };

    expanded.into()
}
```

---

## 5. 属性宏（Attribute Macros）

### 5.1 基础属性宏

```rust
#[proc_macro_attribute]
pub fn trace(args: TokenStream, input: TokenStream) -> TokenStream {
    let args = parse_macro_input!(args as AttributeArgs);
    let input = parse_macro_input!(input as ItemFn);

    let fn_name = &input.sig.ident;
    let fn_body = &input.block;
    let fn_vis = &input.vis;
    let fn_sig = &input.sig;

    // 解析参数
    let log_level = parse_log_level(&args);

    let expanded = quote! {
        #fn_vis #fn_sig {
            log::#log_level!("Entering function: {}", stringify!(#fn_name));
            let __start = std::time::Instant::now();

            let __result = (|| #fn_body)();

            log::#log_level!(
                "Exiting function: {} (took {:?})",
                stringify!(#fn_name),
                __start.elapsed()
            );

            __result
        }
    };

    expanded.into()
}

// 使用
// #[trace(level = "info")]
// fn process_data(data: &[u8]) -> Vec<u8> {
//     // ...
// }
```

### 5.2 路由宏示例

```rust
use syn::{FnArg, Pat, Type};

#[proc_macro_attribute]
pub fn route(args: TokenStream, input: TokenStream) -> TokenStream {
    let args = parse_macro_input!(args as AttributeArgs);
    let input = parse_macro_input!(input as ItemFn);

    // 解析路由参数
    let mut method = "GET".to_string();
    let mut path = String::new();

    for arg in args {
        match arg {
            NestedMeta::Meta(Meta::NameValue(nv)) => {
                if nv.path.is_ident("method") {
                    if let Lit::Str(s) = nv.lit {
                        method = s.value();
                    }
                } else if nv.path.is_ident("path") {
                    if let Lit::Str(s) = nv.lit {
                        path = s.value();
                    }
                }
            }
            _ => {}
        }
    }

    let fn_name = &input.sig.ident;
    let fn_vis = &input.vis;
    let fn_sig = &input.sig;
    let fn_body = &input.block;

    // 提取路径参数
    let path_params = extract_path_params(&path);

    // 生成处理函数
    let handler_impl = generate_handler(&input, &path_params);

    let expanded = quote! {
        #fn_vis fn #fn_name() -> Route {
            Route::new(
                Method::from_bytes(#method.as_bytes()).unwrap(),
                #path,
                #handler_impl
            )
        }
    };

    expanded.into()
}

// 使用
// #[route(method = "POST", path = "/users/{id}")]
// async fn get_user(id: u64) -> Json<User> {
//     // ...
// }
```

### 5.3 结构体转换宏

```rust
#[proc_macro_attribute]
pub fn api_response(args: TokenStream, input: TokenStream) -> TokenStream {
    let _args = parse_macro_input!(args as AttributeArgs);
    let input = parse_macro_input!(input as DeriveInput);

    let name = &input.ident;
    let response_name = quote::format_ident!("{}Response", name);

    let fields = match &input.data {
        syn::Data::Struct(data) => match &data.fields {
            syn::Fields::Named(fields) => &fields.named,
            _ => panic!("Only named fields supported"),
        },
        _ => panic!("Only structs supported"),
    };

    // 生成 API 响应结构体
    let response_fields = fields.iter().map(|f| {
        let name = &f.ident;
        let ty = &f.ty;
        let attrs = &f.attrs;

        // 检查是否有 #[api(skip)] 属性
        let skip = attrs.iter().any(|a| a.path().is_ident("api"));

        if skip {
            quote! {}
        } else {
            quote! {
                #[serde(rename = stringify!(#name))]
                pub #name: #ty,
            }
        }
    });

    let from_impl = fields.iter().filter_map(|f| {
        let name = &f.ident;
        let skip = f.attrs.iter().any(|a| a.path().is_ident("api"));

        if skip {
            None
        } else {
            Some(quote! { #name: value.#name })
        }
    });

    let expanded = quote! {
        #input

        #[derive(Serialize)]
        pub struct #response_name {
            #(#response_fields)*
        }

        impl From<#name> for #response_name {
            fn from(value: #name) -> Self {
                Self {
                    #(#from_impl,)*
                }
            }
        }
    };

    expanded.into()
}

// 使用
// #[api_response]
// struct User {
//     id: u64,
//     name: String,
//     #[api(skip)]
//     internal_token: String,
// }
//
// // 自动生成 UserResponse，不包含 internal_token
```

---

## 6. 函数式宏（Function-like Macros）

### 6.1 基础函数式宏

```rust
#[proc_macro]
pub fn make_answer(input: TokenStream) -> TokenStream {
    let _ = parse_macro_input!(input as parse::Nothing);

    quote! {
        fn answer() -> u32 {
            42
        }
    }.into()
}

// 使用
// make_answer!();
// fn main() {
//     println!("{}", answer());  // 42
// }
```

### 6.2 SQL 查询宏

```rust
use syn::{parse::Parse, parse::ParseStream, Expr, LitStr};

struct SqlQuery {
    query: LitStr,
    args: Vec<Expr>,
}

impl Parse for SqlQuery {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let query: LitStr = input.parse()?;

        let mut args = Vec::new();
        while !input.is_empty() {
            input.parse::<syn::Token![,]>()?;
            args.push(input.parse()?);
        }

        Ok(Self { query, args })
    }
}

#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    let SqlQuery { query, args } = parse_macro_input!(input as SqlQuery);

    // 解析 SQL 查询以提取参数
    let query_str = query.value();
    let param_count = query_str.matches('?').count();

    if param_count != args.len() {
        return syn::Error::new_spanned(
            query,
            format!("Expected {} parameters, found {}", param_count, args.len())
        ).to_compile_error().into();
    }

    let arg_bindings = args.iter().enumerate().map(|(i, arg)| {
        quote! { .bind(#arg) }
    });

    let expanded = quote! {
        {
            use sqlx::query::Query;
            sqlx::query(#query)
                #(#arg_bindings)*
        }
    };

    expanded.into()
}

// 使用
// let rows = sql!("SELECT * FROM users WHERE age > ? AND name = ?", min_age, user_name)
//     .fetch_all(&pool)
//     .await?;
```

### 6.3 HTML 模板宏

```rust
struct HtmlTemplate {
    parts: Vec<TemplatePart>,
}

enum TemplatePart {
    Literal(String),
    Expression(Expr),
    If { cond: Expr, then_branch: Vec<TemplatePart>, else_branch: Option<Vec<TemplatePart>> },
    For { pat: Pat, expr: Expr, body: Vec<TemplatePart> },
}

#[proc_macro]
pub fn html(input: TokenStream) -> TokenStream {
    let template = parse_macro_input!(input as HtmlTemplate);

    let expanded = generate_html_render(&template.parts);

    quote! {{
        let mut __html_output = String::new();
        #expanded
        __html_output
    }}.into()
}

fn generate_html_render(parts: &[TemplatePart]) -> TokenStream {
    let renders = parts.iter().map(|part| match part {
        TemplatePart::Literal(text) => {
            quote! { __html_output.push_str(#text); }
        }
        TemplatePart::Expression(expr) => {
            quote! {
                __html_output.push_str(&::std::fmt::Display::to_string(&(#expr)));
            }
        }
        TemplatePart::If { cond, then_branch, else_branch } => {
            let then_render = generate_html_render(then_branch);
            let else_render = else_branch.as_ref()
                .map(|b| generate_html_render(b))
                .unwrap_or_default();

            quote! {
                if #cond {
                    #then_render
                } else {
                    #else_render
                }
            }
        }
        TemplatePart::For { pat, expr, body } => {
            let body_render = generate_html_render(body);
            quote! {
                for #pat in #expr {
                    #body_render
                }
            }
        }
    });

    quote! { #(#renders)* }
}

// 使用
// let name = "World";
// let items = vec!["a", "b", "c"];
//
// let html_string = html!(
//     <h1>Hello, {name}!</h1>
//     <ul>
//         for item in items {
//             <li>{item}</li>
//         }
//     </ul>
// );
```

---

## 7. 高级技巧与模式

### 7.1 错误处理

```rust
use proc_macro2::Span;
use syn::spanned::Spanned;

// 生成用户友好的编译错误
fn generate_error<T: Spanned>(item: &T, message: &str) -> TokenStream {
    syn::Error::new(item.span(), message)
        .to_compile_error()
        .into()
}

// 使用示例
#[proc_macro_derive(MyDerive)]
pub fn derive_with_error(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    // 验证
    if !input.generics.params.is_empty() {
        return generate_error(
            &input.generics,
            "MyDerive does not support generic types yet"
        );
    }

    match &input.data {
        syn::Data::Struct(_) => {}
        _ => {
            return generate_error(&input, "Only structs are supported");
        }
    }

    // 正常实现...
    quote! {}.into()
}

// 使用 syn::Error 组合多个错误
fn validate_derive(input: &DeriveInput) -> syn::Result<()> {
    let mut errors = Vec::new();

    // 验证1
    if !input.generics.params.is_empty() {
        errors.push(syn::Error::new(
            input.generics.span(),
            "Generics not supported"
        ));
    }

    // 验证2
    if let syn::Data::Struct(data) = &input.data {
        if matches!(data.fields, syn::Fields::Unit) {
            errors.push(syn::Error::new(
                input.ident.span(),
                "Unit structs not supported"
            ));
        }
    }

    // 组合错误
    if let Some(first) = errors.pop() {
        return Err(errors.into_iter().fold(first, |mut acc, e| {
            acc.combine(e);
            acc
        }));
    }

    Ok(())
}
```

### 7.2 泛型处理

```rust
use syn::{GenericParam, LifetimeDef, TypeParam, ConstParam};

fn process_generics(generics: &syn::Generics) -> TokenStream {
    let params = &generics.params;

    // 分离不同类型的参数
    let lifetimes: Vec<_> = params.iter().filter_map(|p| {
        match p {
            GenericParam::Lifetime(l) => Some(&l.lifetime),
            _ => None,
        }
    }).collect();

    let type_params: Vec<_> = params.iter().filter_map(|p| {
        match p {
            GenericParam::Type(t) => Some(&t.ident),
            _ => None,
        }
    }).collect();

    let const_params: Vec<_> = params.iter().filter_map(|p| {
        match p {
            GenericParam::Const(c) => Some(&c.ident),
            _ => None,
        }
    }).collect();

    // 生成 where 子句约束
    let where_clause = &generics.where_clause;

    // 为每个类型参数添加约束
    let bounds = type_params.iter().map(|tp| {
        quote! { #tp: Serialize }
    });

    quote! {
        where
            #(#bounds,)*
            #where_clause
    }
}

// 处理带约束的泛型
fn split_generics(generics: &syn::Generics) -> (TokenStream, TokenStream, TokenStream) {
    let impl_generics = quote! { #generics };
    let ty_generics = {
        let args = generics.params.iter().map(|p| match p {
            GenericParam::Type(t) => {
                let ident = &t.ident;
                quote! { #ident }
            }
            GenericParam::Lifetime(l) => {
                let lifetime = &l.lifetime;
                quote! { #lifetime }
            }
            GenericParam::Const(c) => {
                let ident = &c.ident;
                quote! { #ident }
            }
        });
        quote! { <#(#args,)*> }
    };
    let where_clause = &generics.where_clause;

    (impl_generics, ty_generics, quote! { #where_clause })
}
```

### 7.3 代码生成优化

```rust
// 使用 lazy_static 缓存解析结果
use std::collections::HashMap;
use std::sync::Mutex;

lazy_static::lazy_static! {
    static ref TYPE_CACHE: Mutex<HashMap<String, syn::Type>> = Mutex::new(HashMap::new());
}

// 避免重复生成相同代码
fn cached_type_parse(type_str: &str) -> syn::Type {
    let mut cache = TYPE_CACHE.lock().unwrap();

    cache.entry(type_str.to_string()).or_insert_with(|| {
        syn::parse_str(type_str).expect("Invalid type string")
    }).clone()
}

// 代码去重
use std::collections::HashSet;

fn deduplicate_generated_code(tokens: TokenStream) -> TokenStream {
    let mut seen = HashSet::new();
    let mut result = TokenStream::new();

    for token in tokens {
        let key = token.to_string();
        if seen.insert(key) {
            result.extend(std::iter::once(token));
        }
    }

    result
}
```

---

## 8. Rust 1.94 过程宏新特性

### 8.1 proc_macro_span 稳定

Rust 1.94 稳定了 `proc_macro_span` API，允许过程宏获取更精确的源代码位置信息：

```rust
use proc_macro::Span;

#[proc_macro_derive(Debuggable)]
pub fn derive_debuggable(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    // 🎉 Rust 1.94: 使用 proc_macro_span 获取精确位置
    let span = Span::call_site();
    let source_file = span.source_file();
    let line = span.start().line;
    let column = span.start().column;

    // 可以用于生成更有用的诊断信息
    eprintln!("Macro invoked at {}:{}:{}",
        source_file.path().display(),
        line,
        column
    );

    // 生成代码...
}

// 更精确的跨宏错误定位
#[proc_macro_attribute]
pub fn tracked(args: TokenStream, input: TokenStream) -> TokenStream {
    let item = parse_macro_input!(input as ItemFn);

    // 获取函数定义的位置
    let fn_span = item.sig.ident.span();
    let location = format!(
        "{}:{}:{}",
        fn_span.source_file().path().display(),
        fn_span.start().line,
        fn_span.start().column
    );

    let fn_name = &item.sig.ident;

    let expanded = quote! {
        // 注入位置信息
        const #fn_name: &str = #location;

        #item
    };

    expanded.into()
}
```

### 8.2 改进的诊断信息

Rust 1.94 改进了过程宏的诊断信息输出：

```rust
use proc_macro::Diagnostic;
use proc_macro::Level;

#[proc_macro_derive(Validated)]
pub fn derive_validated(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    // 🎉 Rust 1.94: 使用新的 Diagnostic API
    if has_deprecated_field(&input) {
        // 发出警告而不是编译错误
        Diagnostic::spanned(
            input.span().unwrap(),
            Level::Warning,
            "This struct uses deprecated fields"
        )
        .help("Consider migrating to the new field types")
        .emit();
    }

    // 生成代码
    quote! {}.into()
}

// 生成更详细的错误信息
fn emit_detailed_error(span: Span, message: &str, help: Option<&str>) {
    let mut diag = Diagnostic::spanned(span, Level::Error, message);

    if let Some(help_msg) = help {
        diag = diag.help(help_msg);
    }

    // 🎉 Rust 1.94: 支持附加注释
    diag = diag.note("This error occurred in a procedural macro");

    diag.emit();
}
```

### 8.3 性能优化

Rust 1.94 对过程宏的性能进行了多项优化：

```rust
// 🎉 Rust 1.94: TokenStream 的延迟解析
use proc_macro::TokenStream;

#[proc_macro]
pub fn optimized_macro(input: TokenStream) -> TokenStream {
    // 只有在需要时才解析 TokenStream
    if should_fast_path(&input) {
        // 快速路径：直接操作原始 token
        return fast_path_transform(input);
    }

    // 慢速路径：完整解析
    let parsed = parse_macro_input!(input as MyInput);
    slow_path_transform(parsed)
}

// 🎉 Rust 1.94: 更高效的 Token 缓存
use std::cell::RefCell;

thread_local! {
    static TOKEN_CACHE: RefCell<TokenCache> = RefCell::new(TokenCache::new());
}

fn cached_token_clone(token: &TokenTree) -> TokenTree {
    TOKEN_CACHE.with(|cache| {
        cache.borrow_mut().get_or_clone(token)
    })
}

// 🎉 Rust 1.94: 改进的 TokenStream 拼接
fn efficient_combine(streams: Vec<TokenStream>) -> TokenStream {
    // 使用更高效的内部表示
    streams.into_iter()
        .fold(TokenStream::new(), |acc, stream| {
            // 优化的拼接操作
            acc.extend(stream)
        })
}
```

### 8.4 Cargo.toml 格式支持

Rust 1.94 的 Cargo 支持 TOML v1.1.0：

```toml
# Cargo.toml - Rust 1.94 格式
[package]
name = "my-proc-macro"
version = "0.1.0"
edition = "2021"
rust-version = "1.94"

[lib]
proc-macro = true

[dependencies]
# 🎉 Rust 1.94: 支持新的依赖语法
proc-macro2 = { version = "1.0", features = ["span-locations"] }
quote = "1.0"
syn = { version = "2.0", features = ["full", "parsing"] }

# 🎉 Rust 1.94: 改进的 workspace 继承
[lints]
workspace = true

[features]
default = ["std"]
std = []
nightly = ["proc-macro2/nightly"]
```

---

## 9. 测试与调试

### 9.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::TokenStream;
    use quote::quote;

    fn parse_derive_input(tokens: TokenStream) -> syn::DeriveInput {
        syn::parse2(tokens).unwrap()
    }

    #[test]
    fn test_builder_generation() {
        let input = quote! {
            struct User {
                name: String,
                age: u32,
            }
        };

        let parsed = parse_derive_input(input);
        let output = derive_builder_inner(parsed);

        // 验证输出包含预期的代码
        let output_str = output.to_string();
        assert!(output_str.contains("UserBuilder"));
        assert!(output_str.contains("fn name"));
        assert!(output_str.contains("fn age"));
    }

    #[test]
    fn test_error_for_unit_struct() {
        let input = quote! {
            struct Empty;
        };

        let parsed = parse_derive_input(input);
        let result = std::panic::catch_unwind(|| {
            derive_builder_inner(parsed)
        });

        assert!(result.is_err());
    }
}
```

### 9.2 宏展开查看

```bash
# 查看宏展开
cargo expand

# 查看特定模块
cargo expand path::to::module

# 保存到文件
cargo expand > expanded.rs

# 使用 nightly 的 rustc 展开
rustc +nightly -Zunpretty=expanded src/main.rs

# 🎉 Rust 1.94: 改进的展开格式
cargo expand --theme=none > expanded.rs
```

### 9.3 调试技巧

```rust
// 使用 eprintln 输出调试信息
#[proc_macro_derive(Debuggable)]
pub fn derive_debuggable(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    // 打印解析后的结构
    eprintln!("Input: {:#?}", input);

    let expanded = quote! { /* ... */ };

    // 打印生成的代码
    eprintln!("Generated: {}", expanded.to_string());

    expanded.into()
}

// 使用 cargo-expand 输出
// 在测试中使用 trybuild 验证编译错误
// [dev-dependencies]
// trybuild = "1.0"

#[test]
fn ui_tests() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/*.rs");
    t.pass("tests/ui/pass/*.rs");
}

// 🎉 Rust 1.94: 使用新的调试 API
#[proc_macro]
pub fn debuggable_macro(input: TokenStream) -> TokenStream {
    // 设置调试级别
    if cfg!(proc_macro_debug) {
        eprintln!("Debug: Input tokens = {}", input);
    }

    // 使用 tracing 进行结构化日志
    #[cfg(feature = "tracing")]
    tracing::debug!("Processing macro input");

    input
}
```

---

## 10. 实际案例

### 10.1 完整的 Builder 宏

```rust
// 使用
// #[derive(Builder)]
// #[builder(prefix = "with")]
// struct User {
//     name: String,
//     age: u32,
//     #[builder(default = "admin")]
//     role: String,
//     #[builder(skip)]
//     internal_id: u64,
// }

#[proc_macro_derive(Builder, attributes(builder))]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let struct_name = &input.ident;
    let builder_name = quote::format_ident!("{}Builder", struct_name);

    // 解析结构体属性
    let struct_attrs = parse_struct_attributes(&input.attrs);
    let prefix = struct_attrs.prefix.unwrap_or_else(|| "set".to_string());

    let fields = match &input.data {
        syn::Data::Struct(data) => match &data.fields {
            syn::Fields::Named(fields) => &fields.named,
            _ => panic!("Only named fields supported"),
        },
        _ => panic!("Only structs supported"),
    };

    // 处理每个字段
    let builder_fields = fields.iter().filter_map(|f| {
        if should_skip(f) {
            return None;
        }

        let name = &f.ident;
        let ty = &f.ty;

        // 将 T 转换为 Option<T>
        let option_ty = quote! { Option<#ty> };

        Some(quote! { #name: #option_ty })
    });

    let builder_methods = fields.iter().filter_map(|f| {
        if should_skip(f) {
            return None;
        }

        let name = f.ident.as_ref().unwrap();
        let ty = &f.ty;
        let method_name = quote::format_ident!("{}_{}", prefix, name);

        Some(quote! {
            pub fn #method_name(mut self, value: #ty) -> Self {
                self.#name = Some(value);
                self
            }
        })
    });

    let build_assignments = fields.iter().map(|f| {
        let name = f.ident.as_ref().unwrap();

        if should_skip(f) {
            quote! { #name: Default::default() }
        } else if let Some(default) = get_default(f) {
            quote! { #name: self.#name.unwrap_or_else(|| #default) }
        } else {
            quote! {
                #name: self.#name.ok_or_else(||
                    format!("Field '{}' is not set", stringify!(#name))
                )?
            }
        }
    });

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let expanded = quote! {
        pub struct #builder_name #impl_generics #where_clause {
            #(#builder_fields,)*
        }

        impl #impl_generics #builder_name #ty_generics #where_clause {
            pub fn new() -> Self {
                Self {
                    #(#builder_fields_init,)*
                }
            }

            #(#builder_methods)*

            pub fn build(self) -> Result<#struct_name #ty_generics, String> {
                Ok(#struct_name {
                    #(#build_assignments,)*
                })
            }
        }

        impl #impl_generics #struct_name #ty_generics #where_clause {
            pub fn builder() -> #builder_name #ty_generics {
                #builder_name::new()
            }
        }
    };

    expanded.into()
}

fn parse_struct_attributes(attrs: &[Attribute]) -> StructAttributes {
    // 解析 #[builder(...)] 属性
    // 实现略...
    StructAttributes { prefix: None }
}

fn should_skip(field: &syn::Field) -> bool {
    field.attrs.iter().any(|attr| {
        attr.path().is_ident("builder") &&
        attr.parse_args::<syn::Ident>()
            .map(|i| i == "skip")
            .unwrap_or(false)
    })
}

fn get_default(field: &syn::Field) -> Option<TokenStream> {
    // 解析 #[builder(default = "...")] 属性
    // 实现略...
    None
}

struct StructAttributes {
    prefix: Option<String>,
}
```

### 10.2 序列化/反序列化宏

```rust
#[proc_macro_derive(Json, attributes(json))]
pub fn derive_json(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let serialize_impl = generate_serialize(&input);
    let deserialize_impl = generate_deserialize(&input);

    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let expanded = quote! {
        impl #impl_generics serde::Serialize for #name #ty_generics #where_clause {
            fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
            where
                S: serde::Serializer,
            {
                #serialize_impl
            }
        }

        impl #impl_generics serde::Deserialize for #name #ty_generics #where_clause {
            fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
            where
                D: serde::Deserializer,
            {
                #deserialize_impl
            }
        }
    };

    expanded.into()
}
```

### 10.3 模拟框架宏

```rust
#[proc_macro_attribute]
pub fn mockable(_args: TokenStream, input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as ItemTrait);

    let trait_name = &input.ident;
    let mock_name = quote::format_ident!("Mock{}", trait_name);

    // 为每个方法生成模拟实现
    let mock_methods = input.items.iter().filter_map(|item| {
        match item {
            syn::TraitItem::Method(method) => {
                let method_name = &method.sig.ident;
                let return_type = &method.sig.output;

                Some(quote! {
                    pub fn #method_name(&self) -> MockCall #return_type {
                        MockCall::new(&self.#method_name)
                    }
                })
            }
            _ => None,
        }
    });

    let expanded = quote! {
        #input

        pub struct #mock_name {
            #(#mock_fields,)*
        }

        impl #mock_name {
            pub fn new() -> Self {
                Self {
                    #(#mock_field_inits,)*
                }
            }

            #(#mock_methods)*
        }

        impl #trait_name for #mock_name {
            #(#mock_trait_impls)*
        }
    };

    expanded.into()
}
```

---

## 总结

Rust 的宏系统是强大的元编程工具：

1. **声明宏**：使用 `macro_rules!` 进行基于模式匹配的代码生成
2. **过程宏**：使用 Rust 代码操作 TokenStream，更灵活但复杂
3. **工具链**：syn 用于解析，quote 用于生成，proc-macro2 用于开发
4. **测试**：使用 trybuild 进行 UI 测试，cargo-expand 查看展开结果
5. **最佳实践**：提供清晰的错误信息，避免代码膨胀，注意 hygiene
6. **🎉 Rust 1.94 新特性**：
   - `proc_macro_span` API 稳定，更好的源代码定位
   - 改进的诊断信息 API
   - TokenStream 性能优化
   - TOML v1.1.0 支持

---

## 参考资源

- [The Little Book of Rust Macros](https://danielkeep.github.io/tlborm/book/)
- [syn documentation](https://docs.rs/syn/)
- [quote documentation](https://docs.rs/quote/)
- [proc-macro-workshop](https://github.com/dtolnay/proc-macro-workshop)
- [Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)
- [Rust 1.94 Release Notes - Proc Macro](https://blog.rust-lang.org/)
