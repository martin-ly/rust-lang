# 派生宏详解

> **文档定位**: 深入理解和实现Rust派生宏  
> **难度级别**: ⭐⭐⭐ 高级  
> **预计时间**: 3.5小时  
> **最后更新**: 2025-10-20

---


## 📊 目录

- [📋 学习目标](#学习目标)
- [1. 派生宏基础](#1-派生宏基础)
  - [1.1 什么是派生宏](#11-什么是派生宏)
  - [1.2 派生宏的特点](#12-派生宏的特点)
  - [1.3 常见派生宏](#13-常见派生宏)
- [2. 实现第一个派生宏](#2-实现第一个派生宏)
  - [2.1 项目设置](#21-项目设置)
  - [2.2 实现HelloWorld派生宏](#22-实现helloworld派生宏)
  - [2.3 使用派生宏](#23-使用派生宏)
- [3. 处理结构体字段](#3-处理结构体字段)
  - [3.1 访问字段信息](#31-访问字段信息)
  - [3.2 命名字段 vs 元组字段](#32-命名字段-vs-元组字段)
- [4. 实现Builder模式](#4-实现builder模式)
  - [4.1 完整的Builder实现](#41-完整的builder实现)
  - [4.2 使用Builder](#42-使用builder)
- [5. 处理枚举](#5-处理枚举)
  - [5.1 访问枚举变体](#51-访问枚举变体)
  - [5.2 使用枚举派生宏](#52-使用枚举派生宏)
- [6. 使用宏属性](#6-使用宏属性)
  - [6.1 解析属性](#61-解析属性)
  - [6.2 带属性的Builder](#62-带属性的builder)
  - [6.3 使用属性](#63-使用属性)
- [7. 泛型支持](#7-泛型支持)
  - [7.1 处理泛型参数](#71-处理泛型参数)
  - [7.2 使用泛型](#72-使用泛型)
- [8. 复杂示例：FromRow派生宏](#8-复杂示例fromrow派生宏)
  - [8.1 实现FromRow](#81-实现fromrow)
  - [8.2 使用FromRow](#82-使用fromrow)
- [9. 错误处理最佳实践](#9-错误处理最佳实践)
  - [9.1 友好的错误消息](#91-友好的错误消息)
  - [9.2 多个错误](#92-多个错误)
- [10. 测试派生宏](#10-测试派生宏)
  - [10.1 单元测试](#101-单元测试)
  - [10.2 集成测试](#102-集成测试)
  - [10.3 编译失败测试](#103-编译失败测试)
- [11. 性能优化](#11-性能优化)
  - [11.1 避免重复解析](#111-避免重复解析)
  - [11.2 懒惰计算](#112-懒惰计算)
- [12. 实践项目：完整的Serialize派生宏](#12-实践项目完整的serialize派生宏)
  - [12.1 定义trait](#121-定义trait)
  - [12.2 实现派生宏](#122-实现派生宏)
  - [12.3 使用Serialize](#123-使用serialize)
- [📚 总结](#总结)
  - [关键概念](#关键概念)
  - [核心技能](#核心技能)
  - [下一步](#下一步)


## 📋 学习目标

完成本章后，你将能够：

- ✅ 理解派生宏的工作原理
- ✅ 实现自定义派生宏
- ✅ 处理结构体和枚举
- ✅ 使用宏属性参数
- ✅ 生成复杂的trait实现

---

## 1. 派生宏基础

### 1.1 什么是派生宏

**派生宏 (Derive Macros)** 允许为结构体和枚举自动生成trait实现。

```rust
// 使用内置派生宏
#[derive(Debug, Clone, PartialEq)]
struct Point {
    x: i32,
    y: i32,
}

// 使用自定义派生宏
#[derive(Builder)]
struct Config {
    host: String,
    port: u16,
}
```

### 1.2 派生宏的特点

| 特性 | 说明 |
|------|------|
| **输入** | 结构体或枚举定义 |
| **输出** | trait实现代码 |
| **位置** | `#[derive(...)]`属性 |
| **组合** | 可以同时使用多个派生宏 |

### 1.3 常见派生宏

```rust
// 标准库派生宏
#[derive(Debug)]        // 调试输出
#[derive(Clone)]        // 克隆
#[derive(Copy)]         // 复制
#[derive(PartialEq)]    // 部分相等
#[derive(Eq)]           // 完全相等
#[derive(PartialOrd)]   // 部分排序
#[derive(Ord)]          // 完全排序
#[derive(Hash)]         // 哈希

// 第三方派生宏
#[derive(Serialize, Deserialize)]  // Serde
#[derive(Builder)]                  // derive_builder
#[derive(FromStr)]                  // strum
```

---

## 2. 实现第一个派生宏

### 2.1 项目设置

```toml
# Cargo.toml
[package]
name = "my_derive"
version = "0.1.0"
edition = "2021"

[lib]
proc-macro = true

[dependencies]
syn = { version = "2.0", features = ["full", "extra-traits"] }
quote = "1.0"
proc-macro2 = "1.0"

[dev-dependencies]
trybuild = "1.0"
```

### 2.2 实现HelloWorld派生宏

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

/// HelloWorld trait
pub trait HelloWorld {
    fn hello_world();
}

/// 派生HelloWorld trait
#[proc_macro_derive(HelloWorld)]
pub fn derive_hello_world(input: TokenStream) -> TokenStream {
    // 解析输入
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    // 生成实现
    let expanded = quote! {
        impl HelloWorld for #name {
            fn hello_world() {
                println!("Hello, World! My name is {}!", stringify!(#name));
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

### 2.3 使用派生宏

```rust
use my_derive::HelloWorld;

#[derive(HelloWorld)]
struct MyStruct;

#[derive(HelloWorld)]
enum MyEnum {
    Variant1,
    Variant2,
}

fn main() {
    MyStruct::hello_world(); // Hello, World! My name is MyStruct!
    MyEnum::hello_world();   // Hello, World! My name is MyEnum!
}
```

---

## 3. 处理结构体字段

### 3.1 访问字段信息

```rust
use syn::{Data, Fields};

#[proc_macro_derive(FieldInfo)]
pub fn derive_field_info(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    // 提取字段
    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            Fields::Unnamed(fields) => &fields.unnamed,
            Fields::Unit => {
                return syn::Error::new_spanned(
                    name,
                    "不支持单元结构体"
                ).to_compile_error().into();
            }
        },
        Data::Enum(_) => {
            return syn::Error::new_spanned(
                name,
                "不支持枚举"
            ).to_compile_error().into();
        }
        Data::Union(_) => {
            return syn::Error::new_spanned(
                name,
                "不支持联合体"
            ).to_compile_error().into();
        }
    };
    
    // 生成字段信息
    let field_info: Vec<_> = fields.iter().map(|f| {
        let field_name = &f.ident;
        let field_type = &f.ty;
        quote! {
            println!("字段: {:?}, 类型: {}", stringify!(#field_name), stringify!(#field_type));
        }
    }).collect();
    
    let expanded = quote! {
        impl #name {
            pub fn print_field_info() {
                #(#field_info)*
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

### 3.2 命名字段 vs 元组字段

```rust
// 命名字段
#[derive(FieldInfo)]
struct Point {
    x: i32,  // Fields::Named
    y: i32,
}

// 元组字段
#[derive(FieldInfo)]
struct Pair(i32, i32);  // Fields::Unnamed

// 单元结构体
struct Unit;  // Fields::Unit
```

---

## 4. 实现Builder模式

### 4.1 完整的Builder实现

```rust
#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let builder_name = syn::Ident::new(
        &format!("{}Builder", name),
        name.span()
    );
    
    // 提取字段
    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            _ => panic!("Builder只支持命名字段结构体"),
        },
        _ => panic!("Builder只支持结构体"),
    };
    
    // 字段名和类型
    let field_names: Vec<_> = fields.iter()
        .map(|f| &f.ident)
        .collect();
    let field_types: Vec<_> = fields.iter()
        .map(|f| &f.ty)
        .collect();
    
    // 生成Builder结构体
    let builder_fields = quote! {
        #(
            #field_names: Option<#field_types>,
        )*
    };
    
    // 生成setter方法
    let setter_methods = field_names.iter().zip(field_types.iter()).map(|(name, ty)| {
        quote! {
            pub fn #name(mut self, #name: #ty) -> Self {
                self.#name = Some(#name);
                self
            }
        }
    });
    
    // 生成build方法
    let build_fields = field_names.iter().map(|name| {
        quote! {
            #name: self.#name.ok_or_else(|| {
                format!("字段 {} 未设置", stringify!(#name))
            })?,
        }
    });
    
    let expanded = quote! {
        pub struct #builder_name {
            #builder_fields
        }
        
        impl #builder_name {
            pub fn new() -> Self {
                Self {
                    #(
                        #field_names: None,
                    )*
                }
            }
            
            #(#setter_methods)*
            
            pub fn build(self) -> Result<#name, String> {
                Ok(#name {
                    #(#build_fields)*
                })
            }
        }
        
        impl #name {
            pub fn builder() -> #builder_name {
                #builder_name::new()
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

### 4.2 使用Builder

```rust
#[derive(Builder)]
struct Config {
    host: String,
    port: u16,
    timeout: u64,
}

fn main() {
    let config = Config::builder()
        .host("localhost".to_string())
        .port(8080)
        .timeout(30)
        .build()
        .unwrap();
    
    println!("Config: {}:{}", config.host, config.port);
}
```

---

## 5. 处理枚举

### 5.1 访问枚举变体

```rust
use syn::DataEnum;

#[proc_macro_derive(EnumInfo)]
pub fn derive_enum_info(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    // 提取枚举变体
    let variants = match &input.data {
        Data::Enum(DataEnum { variants, .. }) => variants,
        _ => {
            return syn::Error::new_spanned(
                name,
                "EnumInfo只支持枚举"
            ).to_compile_error().into();
        }
    };
    
    // 生成变体信息
    let variant_names: Vec<_> = variants.iter()
        .map(|v| &v.ident)
        .collect();
    
    let variant_count = variants.len();
    
    let expanded = quote! {
        impl #name {
            pub fn variant_count() -> usize {
                #variant_count
            }
            
            pub fn variant_names() -> &'static [&'static str] {
                &[#(stringify!(#variant_names)),*]
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

### 5.2 使用枚举派生宏

```rust
#[derive(EnumInfo)]
enum Color {
    Red,
    Green,
    Blue,
}

fn main() {
    println!("变体数量: {}", Color::variant_count()); // 3
    println!("变体名称: {:?}", Color::variant_names()); // ["Red", "Green", "Blue"]
}
```

---

## 6. 使用宏属性

### 6.1 解析属性

```rust
use syn::{Attribute, Meta, NestedMeta, Lit};

fn parse_builder_attribute(attr: &Attribute) -> Option<String> {
    if !attr.path.is_ident("builder") {
        return None;
    }
    
    match attr.parse_meta() {
        Ok(Meta::List(meta_list)) => {
            for nested in meta_list.nested {
                if let NestedMeta::Meta(Meta::NameValue(nv)) = nested {
                    if nv.path.is_ident("default") {
                        if let Lit::Str(lit_str) = &nv.lit {
                            return Some(lit_str.value());
                        }
                    }
                }
            }
        }
        _ => {}
    }
    
    None
}
```

### 6.2 带属性的Builder

```rust
#[proc_macro_derive(BuilderWithDefaults, attributes(builder))]
pub fn derive_builder_with_defaults(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            _ => panic!("只支持命名字段"),
        },
        _ => panic!("只支持结构体"),
    };
    
    // 处理每个字段
    let field_init: Vec<_> = fields.iter().map(|f| {
        let field_name = &f.ident;
        let field_type = &f.ty;
        
        // 检查是否有default属性
        let default_value = f.attrs.iter()
            .find_map(|attr| parse_builder_attribute(attr));
        
        if let Some(default) = default_value {
            let default_tokens: proc_macro2::TokenStream = default.parse().unwrap();
            quote! {
                #field_name: self.#field_name.unwrap_or_else(|| #default_tokens)
            }
        } else {
            quote! {
                #field_name: self.#field_name.ok_or_else(|| {
                    format!("字段 {} 未设置", stringify!(#field_name))
                })?
            }
        }
    }).collect();
    
    // 生成代码...
    let expanded = quote! {
        // Builder实现
        impl #name {
            pub fn build(self) -> Result<#name, String> {
                Ok(#name {
                    #(#field_init),*
                })
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

### 6.3 使用属性

```rust
#[derive(BuilderWithDefaults)]
struct ServerConfig {
    host: String,
    
    #[builder(default = "8080")]
    port: u16,
    
    #[builder(default = "30")]
    timeout: u64,
}

fn main() {
    let config = ServerConfig::builder()
        .host("localhost".to_string())
        .build() // port和timeout使用默认值
        .unwrap();
}
```

---

## 7. 泛型支持

### 7.1 处理泛型参数

```rust
use syn::{Generics, TypeParam};

#[proc_macro_derive(Display)]
pub fn derive_display(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let generics = &input.generics;
    
    // 分离泛型参数
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    
    let expanded = quote! {
        impl #impl_generics std::fmt::Display for #name #ty_generics #where_clause {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}", stringify!(#name))
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

### 7.2 使用泛型

```rust
#[derive(Display)]
struct Wrapper<T> {
    value: T,
}

#[derive(Display)]
struct Pair<T, U> 
where
    T: Clone,
    U: Clone,
{
    first: T,
    second: U,
}

fn main() {
    let w = Wrapper { value: 42 };
    println!("{}", w); // Wrapper
    
    let p = Pair { first: 1, second: "hello" };
    println!("{}", p); // Pair
}
```

---

## 8. 复杂示例：FromRow派生宏

### 8.1 实现FromRow

```rust
/// 从数据库行转换
pub trait FromRow {
    fn from_row(row: &[(&str, String)]) -> Result<Self, String>
    where
        Self: Sized;
}

#[proc_macro_derive(FromRow)]
pub fn derive_from_row(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            _ => panic!("FromRow只支持命名字段"),
        },
        _ => panic!("FromRow只支持结构体"),
    };
    
    // 为每个字段生成转换代码
    let field_conversions: Vec<_> = fields.iter().map(|f| {
        let field_name = &f.ident;
        let field_name_str = field_name.as_ref().unwrap().to_string();
        
        quote! {
            #field_name: row.iter()
                .find(|(col, _)| *col == #field_name_str)
                .ok_or_else(|| format!("缺少字段: {}", #field_name_str))?
                .1
                .parse()
                .map_err(|e| format!("解析字段 {} 失败: {}", #field_name_str, e))?
        }
    }).collect();
    
    let expanded = quote! {
        impl FromRow for #name {
            fn from_row(row: &[(&str, String)]) -> Result<Self, String> {
                Ok(Self {
                    #(#field_conversions),*
                })
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

### 8.2 使用FromRow

```rust
#[derive(FromRow)]
struct User {
    id: i32,
    name: String,
    email: String,
    age: u32,
}

fn main() {
    let row = [
        ("id", "1".to_string()),
        ("name", "Alice".to_string()),
        ("email", "alice@example.com".to_string()),
        ("age", "25".to_string()),
    ];
    
    let user = User::from_row(&row).unwrap();
    println!("User: {} ({})", user.name, user.email);
}
```

---

## 9. 错误处理最佳实践

### 9.1 友好的错误消息

```rust
use syn::Error;

#[proc_macro_derive(Validate)]
pub fn derive_validate(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    // 验证：只支持结构体
    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            Fields::Unnamed(_) => {
                return Error::new_spanned(
                    &input,
                    "Validate不支持元组结构体\n\
                     提示: 使用命名字段结构体"
                ).to_compile_error().into();
            }
            Fields::Unit => {
                return Error::new_spanned(
                    &input,
                    "Validate不支持单元结构体"
                ).to_compile_error().into();
            }
        },
        Data::Enum(_) => {
            return Error::new_spanned(
                &input,
                "Validate不支持枚举\n\
                 提示: 考虑为每个变体实现验证"
            ).to_compile_error().into();
        }
        Data::Union(_) => {
            return Error::new_spanned(
                &input,
                "Validate不支持联合体"
            ).to_compile_error().into();
        }
    };
    
    // 验证：至少有一个字段
    if fields.is_empty() {
        return Error::new_spanned(
            &input,
            "结构体必须至少有一个字段"
        ).to_compile_error().into();
    }
    
    // 生成代码...
    TokenStream::from(quote! {
        // 实现
    })
}
```

### 9.2 多个错误

```rust
use syn::Result;

fn validate_struct(input: &DeriveInput) -> Result<()> {
    let mut errors = Vec::new();
    
    // 收集所有错误
    match &input.data {
        Data::Struct(data) => {
            if data.fields.is_empty() {
                errors.push(Error::new_spanned(
                    input,
                    "结构体不能为空"
                ));
            }
            
            for field in data.fields.iter() {
                if field.ident.is_none() {
                    errors.push(Error::new_spanned(
                        field,
                        "字段必须有名称"
                    ));
                }
            }
        }
        _ => {
            errors.push(Error::new_spanned(
                input,
                "只支持结构体"
            ));
        }
    }
    
    // 合并所有错误
    if !errors.is_empty() {
        let mut combined = errors.into_iter().nth(0).unwrap();
        for err in errors.into_iter().skip(1) {
            combined.combine(err);
        }
        return Err(combined);
    }
    
    Ok(())
}
```

---

## 10. 测试派生宏

### 10.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_builder_basic() {
        let tokens = quote! {
            struct Config {
                host: String,
                port: u16,
            }
        };
        
        let output = derive_builder(tokens.into());
        
        // 验证输出包含Builder结构体
        assert!(output.to_string().contains("ConfigBuilder"));
    }
}
```

### 10.2 集成测试

```rust
// tests/derive.rs
use my_derive::Builder;

#[derive(Builder)]
struct TestStruct {
    field1: String,
    field2: i32,
}

#[test]
fn test_builder_works() {
    let result = TestStruct::builder()
        .field1("test".to_string())
        .field2(42)
        .build();
    
    assert!(result.is_ok());
    let s = result.unwrap();
    assert_eq!(s.field1, "test");
    assert_eq!(s.field2, 42);
}
```

### 10.3 编译失败测试

```rust
// tests/ui/builder_missing_field.rs
use my_derive::Builder;

#[derive(Builder)]
struct Config {
    host: String,
    port: u16,
}

fn main() {
    // 应该编译失败：缺少port字段
    let config = Config::builder()
        .host("localhost".to_string())
        .build();
}
```

```rust
// tests/compile_fail.rs
#[test]
fn ui() {
    let t = trybuild::TestCases::new();
    t.compile_fail("tests/ui/*.rs");
}
```

---

## 11. 性能优化

### 11.1 避免重复解析

```rust
// ❌ 低效
#[proc_macro_derive(Inefficient)]
pub fn inefficient(input: TokenStream) -> TokenStream {
    // 多次解析
    let input1 = syn::parse::<DeriveInput>(input.clone()).unwrap();
    let input2 = syn::parse::<DeriveInput>(input.clone()).unwrap();
    // ...
}

// ✅ 高效
#[proc_macro_derive(Efficient)]
pub fn efficient(input: TokenStream) -> TokenStream {
    // 只解析一次
    let input = parse_macro_input!(input as DeriveInput);
    // 重复使用input
}
```

### 11.2 懒惰计算

```rust
#[proc_macro_derive(Lazy)]
pub fn derive_lazy(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    // 只在需要时计算字段信息
    let fields = || {
        match &input.data {
            Data::Struct(data) => Some(&data.fields),
            _ => None,
        }
    };
    
    // 使用
    if let Some(f) = fields() {
        // 处理字段
    }
    
    TokenStream::new()
}
```

---

## 12. 实践项目：完整的Serialize派生宏

### 12.1 定义trait

```rust
pub trait Serialize {
    fn serialize(&self) -> String;
}
```

### 12.2 实现派生宏

```rust
#[proc_macro_derive(Serialize)]
pub fn derive_serialize(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    let serialize_body = match &input.data {
        Data::Struct(data) => {
            let field_serializations = match &data.fields {
                Fields::Named(fields) => {
                    let field_code: Vec<_> = fields.named.iter().map(|f| {
                        let field_name = &f.ident;
                        quote! {
                            format!(
                                "\"{}\": \"{}\"",
                                stringify!(#field_name),
                                self.#field_name
                            )
                        }
                    }).collect();
                    
                    quote! {
                        let fields = vec![
                            #(#field_code),*
                        ];
                        format!("{{{}}}", fields.join(", "))
                    }
                }
                _ => panic!("只支持命名字段"),
            };
            field_serializations
        }
        _ => panic!("只支持结构体"),
    };
    
    let expanded = quote! {
        impl Serialize for #name {
            fn serialize(&self) -> String {
                #serialize_body
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

### 12.3 使用Serialize

```rust
#[derive(Serialize)]
struct User {
    id: i32,
    name: String,
    email: String,
}

fn main() {
    let user = User {
        id: 1,
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
    };
    
    println!("{}", user.serialize());
    // {"id": "1", "name": "Alice", "email": "alice@example.com"}
}
```

---

## 📚 总结

### 关键概念

1. **DeriveInput** - 输入解析
2. **Fields** - 字段访问
3. **Generics** - 泛型处理
4. **Attributes** - 属性解析
5. **Error** - 错误处理

### 核心技能

- ✅ 实现自定义派生宏
- ✅ 处理结构体和枚举
- ✅ 使用宏属性
- ✅ 支持泛型
- ✅ 友好的错误处理

### 下一步

- 📖 学习 [属性宏教程](./03_attribute_macros.md)
- 📖 学习 [函数式宏教程](./04_function_macros.md)
- 📖 学习 [TokenStream详解](./05_token_streams.md)

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT
