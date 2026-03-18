# 过程宏开发

过程宏（Procedural Macros）是 Rust 最强大的元编程工具，允许你在编译期操作 Rust 代码的抽象语法树（AST）。
本章节将深入讲解三种类型的过程宏：Derive 宏、属性宏和函数式宏。

## 目录

- [过程宏开发](#过程宏开发)
  - [目录](#目录)
  - [基础架构](#基础架构)
    - [项目结构](#项目结构)
    - [核心依赖解析](#核心依赖解析)
    - [基本模板](#基本模板)
  - [Derive 宏](#derive-宏)
    - [基础 Builder 模式 Derive](#基础-builder-模式-derive)
    - [高级 Derive 宏：自定义序列化](#高级-derive-宏自定义序列化)
    - [枚举处理](#枚举处理)
  - [属性宏](#属性宏)
    - [Web 框架路由宏](#web-框架路由宏)
    - [测试宏](#测试宏)
    - [日志记录宏](#日志记录宏)
  - [函数式宏](#函数式宏)
    - [SQL DSL 宏](#sql-dsl-宏)
    - [验证宏](#验证宏)
    - [JSON 字面量宏](#json-字面量宏)
  - [Token 操作](#token-操作)
    - [自定义解析器](#自定义解析器)
    - [Token 流转换](#token-流转换)
  - [错误处理和诊断](#错误处理和诊断)
    - [编译期错误报告](#编译期错误报告)
    - [使用 syn::Error](#使用-synerror)
  - [测试和调试](#测试和调试)
    - [单元测试过程宏](#单元测试过程宏)
    - [使用 trybuild 测试编译错误](#使用-trybuild-测试编译错误)
    - [调试技巧](#调试技巧)
    - [使用 cargo-expand](#使用-cargo-expand)

## 基础架构

### 项目结构

过程宏必须定义在特殊的 crate 类型中：

```toml
# Cargo.toml
[package]
name = "my-proc-macros"
version = "0.1.0"
edition = "2021"

[lib]
proc-macro = true

[dependencies]
proc-macro2 = "1.0"
quote = "1.0"
syn = { version = "2.0", features = ["full"] }
```

### 核心依赖解析

- **proc-macro2**: 提供 `TokenStream` 的包装，支持测试和调试
- **quote**: 用于生成 TokenStream 的宏
- **syn**: 解析 Rust 代码为 AST 结构

### 基本模板

```rust
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyTrait)]
pub fn derive_my_trait(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    let expanded = quote! {
        // 生成的代码
    };

    TokenStream::from(expanded)
}
```

## Derive 宏

### 基础 Builder 模式 Derive

创建一个为结构体生成 Builder 模式的 Derive 宏：

```rust
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::{quote, format_ident};
use syn::{parse_macro_input, Data, DeriveInput, Fields, Ident, Type};

#[proc_macro_derive(Builder, attributes(builder))]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let builder_name = format_ident!("{}Builder", name);

    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            _ => panic!("Builder derive only supports named fields"),
        },
        _ => panic!("Builder derive only supports structs"),
    };

    // 生成 Builder 结构体字段
    let builder_fields = fields.iter().map(|f| {
        let name = &f.ident;
        let ty = &f.ty;
        quote! { #name: std::option::Option<#ty> }
    });

    // 生成 setter 方法
    let setters = fields.iter().map(|f| {
        let name = &f.ident;
        let ty = &f.ty;
        let doc = format!("Set the {} field", name.as_ref().unwrap());

        quote! {
            #[doc = #doc]
            pub fn #name(mut self, value: #ty) -> Self {
                self.#name = Some(value);
                self
            }
        }
    });

    // 生成 build 方法
    let build_fields = fields.iter().map(|f| {
        let name = &f.ident;
        let field_name = name.as_ref().unwrap().to_string();

        quote! {
            #name: self.#name.ok_or_else(||
                format!("Field '{}' is required", #field_name)
            )?
        }
    });

    // 生成默认值初始化
    let default_inits = fields.iter().map(|f| {
        let name = &f.ident;
        quote! { #name: None }
    });

    let expanded = quote! {
        pub struct #builder_name {
            #(#builder_fields,)*
        }

        impl #builder_name {
            pub fn new() -> Self {
                Self {
                    #(#default_inits,)*
                }
            }

            #(#setters)*

            pub fn build(self) -> Result<#name, String> {
                Ok(#name {
                    #(#build_fields,)*
                })
            }
        }

        impl #name {
            pub fn builder() -> #builder_name {
                #builder_name::new()
            }
        }

        impl Default for #builder_name {
            fn default() -> Self {
                Self::new()
            }
        }
    };

    TokenStream::from(expanded)
}
```

**使用示例：**

```rust
use my_proc_macros::Builder;

#[derive(Builder)]
struct DatabaseConfig {
    host: String,
    port: u16,
    username: String,
    password: String,
    database: String,
    pool_size: u32,
}

fn main() {
    let config = DatabaseConfig::builder()
        .host("localhost".to_string())
        .port(5432)
        .username("admin".to_string())
        .password("secret".to_string())
        .database("myapp".to_string())
        .pool_size(10)
        .build()
        .unwrap();
}
```

### 高级 Derive 宏：自定义序列化

创建支持多种序列化格式的 Derive 宏：

```rust
use proc_macro::TokenStream;
use quote::{quote, format_ident};
use syn::{parse_macro_input, Data, DeriveInput, Fields, Meta, NestedMeta};

#[proc_macro_derive(CustomSerialize, attributes(serialize))]
pub fn derive_custom_serialize(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let fields = extract_fields(&input.data);

    // 生成 JSON 序列化
    let json_serialize = generate_json_serialize(&fields, name);
    let json_deserialize = generate_json_deserialize(&fields, name);

    // 生成二进制序列化
    let binary_serialize = generate_binary_serialize(&fields);
    let binary_deserialize = generate_binary_deserialize(&fields, name);

    let expanded = quote! {
        impl CustomSerialize for #name {
            #json_serialize
            #json_deserialize
            #binary_serialize
            #binary_deserialize
        }
    };

    TokenStream::from(expanded)
}

fn extract_fields(data: &Data) -> Vec<FieldInfo> {
    match data {
        Data::Struct(s) => match &s.fields {
            Fields::Named(fields) => fields.named.iter().map(|f| {
                let name = f.ident.clone().unwrap();
                let ty = f.ty.clone();

                // 解析属性
                let mut skip = false;
                let mut rename = None;

                for attr in &f.attrs {
                    if attr.path.is_ident("serialize") {
                        // 解析 #[serialize(skip)] 和 #[serialize(rename = "...")]
                        if let Ok(Meta::List(meta_list)) = attr.parse_meta() {
                            for nested in &meta_list.nested {
                                if let NestedMeta::Meta(Meta::Path(path)) = nested {
                                    if path.is_ident("skip") {
                                        skip = true;
                                    }
                                }
                                if let NestedMeta::Meta(Meta::NameValue(nv)) = nested {
                                    if nv.path.is_ident("rename") {
                                        if let syn::Lit::Str(s) = &nv.lit {
                                            rename = Some(s.value());
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                FieldInfo { name, ty, skip, rename }
            }).collect(),
            _ => vec![],
        },
        _ => vec![],
    }
}

struct FieldInfo {
    name: syn::Ident,
    ty: syn::Type,
    skip: bool,
    rename: Option<String>,
}

fn generate_json_serialize(fields: &[FieldInfo], _struct_name: &syn::Ident) -> proc_macro2::TokenStream {
    let field_serializations = fields.iter().filter(|f| !f.skip).map(|f| {
        let name = &f.name;
        let key = f.rename.clone().unwrap_or_else(|| name.to_string());

        quote! {
            map.insert(
                #key.to_string(),
                serde_json::json!(self.#name)
            );
        }
    });

    quote! {
        fn to_json(&self) -> serde_json::Value {
            let mut map = serde_json::Map::new();
            #(#field_serializations)*
            serde_json::Value::Object(map)
        }
    }
}

fn generate_json_deserialize(fields: &[FieldInfo], struct_name: &syn::Ident) -> proc_macro2::TokenStream {
    let field_deserializations = fields.iter().filter(|f| !f.skip).map(|f| {
        let name = &f.name;
        let key = f.rename.clone().unwrap_or_else(|| name.to_string());

        quote! {
            #name: json.get(#key)
                .and_then(|v| serde_json::from_value(v.clone()).ok())
                .ok_or_else(|| format!("Missing field: {}", #key))?,
        }
    });

    quote! {
        fn from_json(json: &serde_json::Value) -> Result<Self, String> {
            Ok(#struct_name {
                #(#field_deserializations)*
            })
        }
    }
}

fn generate_binary_serialize(fields: &[FieldInfo]) -> proc_macro2::TokenStream {
    let field_serializations = fields.iter().filter(|f| !f.skip).map(|f| {
        let name = &f.name;
        quote! {
            bytes.extend_from_slice(&self.#name.to_le_bytes());
        }
    });

    quote! {
        fn to_binary(&self) -> Vec<u8> {
            let mut bytes = Vec::new();
            #(#field_serializations)*
            bytes
        }
    }
}

fn generate_binary_deserialize(fields: &[FieldInfo], struct_name: &syn::Ident) -> proc_macro2::TokenStream {
    quote! {
        fn from_binary(bytes: &[u8]) -> Result<Self, String> {
            // 简化示例，实际实现需要处理字节偏移
            unimplemented!("Binary deserialization")
        }
    }
}
```

### 枚举处理

为枚举生成实用方法的 Derive 宏：

```rust
#[proc_macro_derive(EnumUtils, attributes(enum_utils))]
pub fn derive_enum_utils(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let variants = match &input.data {
        Data::Enum(e) => &e.variants,
        _ => panic!("EnumUtils only supports enums"),
    };

    // 生成 variant 名称列表
    let variant_names: Vec<_> = variants.iter().map(|v| {
        let name = &v.ident;
        quote! { stringify!(#name) }
    }).collect();

    // 生成 variant 数量
    let variant_count = variants.len();

    // 生成 from_str
    let from_str_arms = variants.iter().map(|v| {
        let name = &v.ident;
        let name_str = name.to_string();

        match &v.fields {
            Fields::Unit => {
                quote! {
                    #name_str => Some(#name::#name),
                }
            }
            _ => quote! {}, // 简化示例，只支持 Unit 变体
        }
    });

    let expanded = quote! {
        impl #name {
            pub fn all_variants() -> &'static [&'static str] {
                &[#(#variant_names),*]
            }

            pub fn variant_count() -> usize {
                #variant_count
            }

            pub fn from_str(s: &str) -> Option<Self> {
                match s {
                    #(#from_str_arms)*
                    _ => None,
                }
            }

            pub fn as_str(&self) -> &'static str {
                match self {
                    #(Self::#variant_names => stringify!(#variant_names),)*
                }
            }
        }
    };

    TokenStream::from(expanded)
}
```

## 属性宏

### Web 框架路由宏

创建类似 Actix-web 的路由属性宏：

```rust
use proc_macro::TokenStream;
use quote::{quote, format_ident};
use syn::{parse_macro_input, ItemFn, Lit, Meta, NestedMeta, ReturnType, Type};

#[proc_macro_attribute]
pub fn route(args: TokenStream, input: TokenStream) -> TokenStream {
    let args = parse_macro_input!(args as syn::AttributeArgs);
    let input_fn = parse_macro_input!(input as ItemFn);

    // 解析属性参数
    let mut path = String::from("/");
    let mut method = String::from("GET");

    for arg in args {
        match arg {
            NestedMeta::Lit(Lit::Str(s)) => {
                path = s.value();
            }
            NestedMeta::Meta(Meta::NameValue(nv)) => {
                if nv.path.is_ident("method") {
                    if let Lit::Str(s) = nv.lit {
                        method = s.value().to_uppercase();
                    }
                }
            }
            _ => {}
        }
    }

    let fn_name = &input_fn.sig.ident;
    let fn_vis = &input_fn.vis;
    let fn_block = &input_fn.block;
    let fn_inputs = &input_fn.sig.inputs;
    let fn_output = &input_fn.sig.output;

    // 生成路由注册代码
    let route_info_name = format_ident!("__ROUTE_INFO_{}", fn_name.to_string().to_uppercase());

    let expanded = quote! {
        #[allow(non_upper_case_globals)]
        pub static #route_info_name: RouteInfo = RouteInfo {
            path: #path,
            method: #method,
            handler: #fn_name,
        };

        inventory::submit! {
            #route_info_name
        }

        #fn_vis fn #fn_name(#fn_inputs) #fn_output {
            #fn_block
        }
    };

    TokenStream::from(expanded)
}

// 使用示例：
// #[route("/users/{id}", method = "GET")]
// async fn get_user(path: web::Path<(u32,)>) -> HttpResponse {
//     HttpResponse::Ok().body(format!("User: {}", path.0))
// }
```

### 测试宏

创建带有设置和清理的测试属性宏：

```rust
#[proc_macro_attribute]
pub fn integration_test(args: TokenStream, input: TokenStream) -> TokenStream {
    let args = parse_macro_input!(args as syn::AttributeArgs);
    let input_fn = parse_macro_input!(input as ItemFn);

    let fn_name = &input_fn.sig.ident;
    let fn_block = &input_fn.block;

    // 解析配置
    let mut timeout_secs = 30;
    let mut retry_count = 0;

    for arg in args {
        if let NestedMeta::Meta(Meta::NameValue(nv)) = arg {
            if nv.path.is_ident("timeout") {
                if let Lit::Int(i) = nv.lit {
                    timeout_secs = i.base10_parse().unwrap();
                }
            }
            if nv.path.is_ident("retry") {
                if let Lit::Int(i) = nv.lit {
                    retry_count = i.base10_parse().unwrap();
                }
            }
        }
    }

    let test_name = fn_name.to_string();

    let expanded = quote! {
        #[test]
        fn #fn_name() {
            let setup_result = std::panic::catch_unwind(|| {
                TestContext::setup(#test_name)
            });

            let ctx = match setup_result {
                Ok(ctx) => ctx,
                Err(_) => {
                    panic!("Test setup failed for {}", #test_name);
                }
            };

            let test_result = std::panic::catch_unwind(|| {
                #fn_block
            });

            ctx.cleanup();

            match test_result {
                Ok(result) => result,
                Err(e) => std::panic::resume_unwind(e),
            }
        }
    };

    TokenStream::from(expanded)
}
```

### 日志记录宏

创建自动记录函数入口和出口的属性宏：

```rust
#[proc_macro_attribute]
pub fn logged(_args: TokenStream, input: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(input as ItemFn);

    let fn_vis = &input_fn.vis;
    let fn_sig = &input_fn.sig;
    let fn_name = &fn_sig.ident;
    let fn_block = &input_fn.block;
    let fn_attrs = &input_fn.attrs;

    let name_str = fn_name.to_string();

    let expanded = quote! {
        #(#fn_attrs)*
        #fn_vis #fn_sig {
            let _span = tracing::span!(tracing::Level::INFO, #name_str);
            let _enter = _span.enter();

            tracing::info!("Entering function: {}", #name_str);

            let __start = std::time::Instant::now();
            let __result = #fn_block;
            let __elapsed = __start.elapsed();

            tracing::info!("Exiting function: {} (elapsed: {:?})", #name_str, __elapsed);

            __result
        }
    };

    TokenStream::from(expanded)
}
```

## 函数式宏

### SQL DSL 宏

创建类型安全的 SQL 查询宏：

```rust
use proc_macro::TokenStream;
use proc_macro2::TokenTree;
use quote::quote;

#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    let tokens: Vec<_> = input.into_iter().collect();

    if tokens.is_empty() {
        panic!("sql! macro requires a query string");
    }

    // 解析查询字符串
    let query = match &tokens[0] {
        proc_macro::TokenTree::Literal(lit) => {
            let s = lit.to_string();
            // 去除引号
            s.trim_matches('"').to_string()
        }
        _ => panic!("First argument must be a string literal"),
    };

    // 解析参数
    let params: Vec<_> = tokens.iter().skip(1).filter(|t| {
        !matches!(t, proc_macro::TokenTree::Punct(p) if p.as_char() == ',')
    }).collect();

    // 验证 SQL 语法（简化版本）
    validate_sql(&query);

    // 生成查询构建代码
    let param_count = params.len();
    let param_bindings = params.iter().enumerate().map(|(i, _)| {
        let idx = syn::Index::from(i);
        quote! { query.bind(&params.#idx) }
    });

    let expanded = quote! {
        {
            let params = (#(#params),*);
            let mut query = sqlx::query::<#param_count>(#query)
                #(.bind(&params.#param_bindings))*;
            query
        }
    };

    TokenStream::from(expanded)
}

fn validate_sql(query: &str) {
    // 基本安全检查
    let lower = query.to_lowercase();

    // 检查是否有明显的 SQL 注入风险
    if lower.contains("; drop ") || lower.contains("; delete ") {
        // 在实际实现中，这里应该发出警告或错误
    }
}

// 使用示例：
// let user = sql!("SELECT * FROM users WHERE id = ? AND active = ?", user_id, true).fetch_one(&pool).await?;
```

### 验证宏

创建运行时验证宏：

```rust
#[proc_macro]
pub fn validate(input: TokenStream) -> TokenStream {
    let tokens: Vec<_> = input.into_iter().collect();

    // 解析: validate!(value, rule1, rule2, ...)
    if tokens.len() < 3 {
        panic!("validate! requires at least a value and one rule");
    }

    let value = &tokens[0];

    // 收集验证规则
    let rules: Vec<_> = tokens.iter().skip(1)
        .filter(|t| !matches!(t, proc_macro::TokenTree::Punct(p) if p.as_char() == ','))
        .collect();

    let validations = rules.iter().map(|rule| {
        match rule {
            proc_macro::TokenTree::Ident(ident) => {
                let rule_name = ident.to_string();
                match rule_name.as_str() {
                    "not_empty" => quote! {
                        if #value.to_string().is_empty() {
                            return Err(ValidationError::Empty);
                        }
                    },
                    "email" => quote! {
                        if !#value.contains('@') {
                            return Err(ValidationError::InvalidEmail);
                        }
                    },
                    "positive" => quote! {
                        if #value <= 0 {
                            return Err(ValidationError::NotPositive);
                        }
                    },
                    _ => panic!("Unknown validation rule: {}", rule_name),
                }
            }
            proc_macro::TokenTree::Literal(lit) => {
                // 处理范围验证等
                quote! {}
            }
            _ => quote! {},
        }
    });

    let expanded = quote! {
        {
            #(#validations)*
            Ok(())
        }
    };

    TokenStream::from(expanded)
}
```

### JSON 字面量宏

```rust
#[proc_macro]
pub fn json(input: TokenStream) -> TokenStream {
    let input = proc_macro2::TokenStream::from(input);

    fn parse_json_value(tokens: &mut impl Iterator<Item = TokenTree>) -> proc_macro2::TokenStream {
        match tokens.next() {
            Some(TokenTree::Group(group)) if group.delimiter() == proc_macro2::Delimiter::Brace => {
                // 对象
                let inner = group.stream();
                let pairs = parse_object_pairs(inner);
                quote! { serde_json::json!(#pairs) }
            }
            Some(TokenTree::Group(group)) if group.delimiter() == proc_macro2::Delimiter::Bracket => {
                // 数组
                quote! { serde_json::json!(#group) }
            }
            Some(TokenTree::Literal(lit)) => {
                // 字符串或数字
                quote! { serde_json::json!(#lit) }
            }
            Some(TokenTree::Ident(ident)) => {
                // true, false, null 或变量
                match ident.to_string().as_str() {
                    "true" | "false" | "null" => quote! { serde_json::json!(#ident) },
                    _ => quote! { serde_json::json!(#ident) },
                }
            }
            _ => quote! {},
        }
    }

    let expanded = parse_json_value(&mut input.into_iter());
    TokenStream::from(expanded)
}
```

## Token 操作

### 自定义解析器

```rust
use syn::parse::{Parse, ParseStream};
use syn::{Ident, Token, Type, Expr};

struct RouteDefinition {
    method: Ident,
    path: syn::LitStr,
    handler: Ident,
    middlewares: Vec<Ident>,
}

impl Parse for RouteDefinition {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let method: Ident = input.parse()?;
        input.parse::<Token![=>]>()?;
        let path: syn::LitStr = input.parse()?;
        input.parse::<Token![=>]>()?;
        let handler: Ident = input.parse()?;

        let mut middlewares = Vec::new();
        while input.peek(Token![->]) {
            input.parse::<Token![->]>()?;
            let middleware: Ident = input.parse()?;
            middlewares.push(middleware);
        }

        Ok(RouteDefinition {
            method,
            path,
            handler,
            middlewares,
        })
    }
}

#[proc_macro]
pub fn define_route(input: TokenStream) -> TokenStream {
    let def = parse_macro_input!(input as RouteDefinition);

    let method = def.method;
    let path = def.path;
    let handler = def.handler;
    let middlewares = def.middlewares;

    let expanded = quote! {
        Route::new()
            .method(Method::#method)
            .path(#path)
            .handler(#handler)
            #(.middleware(#middlewares))*
    };

    TokenStream::from(expanded)
}

// 使用：define_route!(GET => "/users" => list_users -> auth -> rate_limit)
```

### Token 流转换

```rust
use proc_macro2::{TokenStream, TokenTree};

fn transform_async_trait(tokens: TokenStream) -> TokenStream {
    tokens.into_iter().map(|tt| {
        match tt {
            TokenTree::Ident(ref ident) if ident == "async_trait" => {
                // 替换为具体的展开
                quote::quote! {
                    #[async_trait::async_trait]
                }
            }
            TokenTree::Group(group) => {
                let new_stream = transform_async_trait(group.stream());
                let mut new_group = proc_macro2::Group::new(group.delimiter(), new_stream);
                new_group.set_span(group.span());
                TokenTree::Group(new_group)
            }
            _ => tt,
        }
    }).collect()
}
```

## 错误处理和诊断

### 编译期错误报告

```rust
use proc_macro::Diagnostic;
use proc_macro::Level;

fn emit_error(span: proc_macro2::Span, message: &str) {
    // 使用 proc_macro::Diagnostic（nightly 特性）
    #[cfg(nightly)]
    {
        Diagnostic::spanned(
            span.unwrap(),
            Level::Error,
            message
        ).emit();
    }

    // 稳定版使用 panic
    #[cfg(not(nightly))]
    {
        panic!("{}: {}", span, message);
    }
}

// 更好的错误处理
#[proc_macro_derive(Validate)]
pub fn derive_validate(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);

    // 收集所有错误
    let mut errors = Vec::new();

    if let Data::Struct(data) = &input.data {
        for field in &data.fields {
            if field.ident.is_none() {
                errors.push((
                    field.span(),
                    "Validate derive requires named fields"
                ));
            }
        }
    } else {
        errors.push((
            input.span(),
            "Validate derive only supports structs"
        ));
    }

    if !errors.is_empty() {
        // 报告所有错误
        for (span, msg) in errors {
            emit_error(span, msg);
        }
        return TokenStream::new();
    }

    // 正常生成代码
    quote! {}.into()
}
```

### 使用 syn::Error

```rust
use syn::Error;

fn parse_field_attrs(attrs: &[syn::Attribute]) -> Result<FieldConfig, Error> {
    let mut config = FieldConfig::default();

    for attr in attrs {
        if attr.path.is_ident("validate") {
            let meta = attr.parse_meta()?;

            if let Meta::List(list) = meta {
                for nested in &list.nested {
                    match nested {
                        NestedMeta::Meta(Meta::Path(path)) if path.is_ident("required") => {
                            config.required = true;
                        }
                        NestedMeta::Meta(Meta::NameValue(nv)) if nv.path.is_ident("min") => {
                            if let Lit::Int(i) = &nv.lit {
                                config.min = Some(i.base10_parse()?);
                            } else {
                                return Err(Error::new(
                                    nv.lit.span(),
                                    "min must be an integer"
                                ));
                            }
                        }
                        _ => {
                            return Err(Error::new(
                                nested.span(),
                                "Unknown validation attribute"
                            ));
                        }
                    }
                }
            }
        }
    }

    Ok(config)
}
```

## 测试和调试

### 单元测试过程宏

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use proc_macro2::TokenStream;
    use quote::quote;
    use syn::parse_quote;

    #[test]
    fn test_derive_builder() {
        let input: TokenStream = quote! {
            struct User {
                name: String,
                age: u32,
            }
        };

        let output = derive_builder(input.into());
        let output_str = output.to_string();

        assert!(output_str.contains("UserBuilder"));
        assert!(output_str.contains("fn name"));
        assert!(output_str.contains("fn age"));
    }

    #[test]
    fn test_parse_route_definition() {
        let input: syn::AttributeArgs = parse_quote! {
            GET, "/users", handler
        };

        // 测试解析逻辑
    }
}
```

### 使用 trybuild 测试编译错误

```toml
[dev-dependencies]
trybuild = { version = "1.0", features = ["diff"] }
```

```rust
#[test]
fn test_compile_errors() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/*.rs");
}
```

**tests/ui/invalid_builder.rs:**

```rust
use my_macros::Builder;

#[derive(Builder)]
struct Unit;  // 错误：Builder 不支持单元结构体

fn main() {}
```

**tests/ui/invalid_builder.stderr:**

```
error: Builder derive only supports named fields
 --> tests/ui/invalid_builder.rs:4:1
  |
4 | struct Unit;
  | ^^^^^^^^^^^^
```

### 调试技巧

```rust
use std::fs::File;
use std::io::Write;

#[proc_macro_derive(DebugPrint)]
pub fn derive_debug_print(input: TokenStream) -> TokenStream {
    // 写入文件以便检查
    let mut file = File::create("/tmp/proc_macro_debug.txt").unwrap();
    writeln!(file, "Input: {}", input.to_string()).unwrap();

    let input = parse_macro_input!(input as DeriveInput);

    // 打印解析后的结构
    writeln!(file, "Parsed: {:#?}", input).unwrap();

    let expanded = quote! {
        // 生成的代码
    };

    writeln!(file, "Output: {}", expanded.to_string()).unwrap();

    TokenStream::from(expanded)
}
```

### 使用 cargo-expand

```bash
# 安装 cargo-expand
cargo install cargo-expand

# 查看宏展开结果
cargo expand --test test_name
```

---

通过掌握这些过程宏技术，你可以极大地提升 Rust 代码的抽象能力和开发效率。过程宏虽然复杂，但它们是 Rust 元编程生态系统的核心组件。
