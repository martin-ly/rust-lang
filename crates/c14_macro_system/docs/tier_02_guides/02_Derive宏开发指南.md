# C14 Macro System - Tier 2: Derive 宏开发指南

> **文档版本**: v1.0.0  
> **最后更新**: 2025-10-23  
> **Rust 版本**: 1.90+  
> **预计阅读**: 35 分钟

---

## 📊 目录

- [C14 Macro System - Tier 2: Derive 宏开发指南](#c14-macro-system---tier-2-derive-宏开发指南)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [1. Derive 宏概述](#1-derive-宏概述)
  - [2. 基础设置](#2-基础设置)
    - [2.1 项目结构](#21-项目结构)
    - [2.2 Cargo.toml 配置](#22-cargotoml-配置)
    - [2.3 基本框架](#23-基本框架)
  - [3. 解析结构体](#3-解析结构体)
    - [3.1 解析字段](#31-解析字段)
    - [3.2 解析属性](#32-解析属性)
  - [4. 生成代码](#4-生成代码)
    - [4.1 基础代码生成](#41-基础代码生成)
    - [4.2 泛型支持](#42-泛型支持)
  - [5. 错误处理](#5-错误处理)
    - [5.1 编译错误](#51-编译错误)
    - [5.2 字段错误](#52-字段错误)
  - [6. 实战案例](#6-实战案例)
    - [6.1 Builder 模式宏](#61-builder-模式宏)
    - [6.2 Debug 宏实现](#62-debug-宏实现)
    - [6.3 Serialize 宏](#63-serialize-宏)
  - [7. 总结](#7-总结)
    - [核心要点](#核心要点)
    - [最佳实践](#最佳实践)
  - [📚 参考资源](#-参考资源)

## 📋 目录

- [C14 Macro System - Tier 2: Derive 宏开发指南](#c14-macro-system---tier-2-derive-宏开发指南)
  - [📊 目录](#-目录)
  - [📋 目录](#-目录-1)
  - [1. Derive 宏概述](#1-derive-宏概述)
  - [2. 基础设置](#2-基础设置)
    - [2.1 项目结构](#21-项目结构)
    - [2.2 Cargo.toml 配置](#22-cargotoml-配置)
    - [2.3 基本框架](#23-基本框架)
  - [3. 解析结构体](#3-解析结构体)
    - [3.1 解析字段](#31-解析字段)
    - [3.2 解析属性](#32-解析属性)
  - [4. 生成代码](#4-生成代码)
    - [4.1 基础代码生成](#41-基础代码生成)
    - [4.2 泛型支持](#42-泛型支持)
  - [5. 错误处理](#5-错误处理)
    - [5.1 编译错误](#51-编译错误)
    - [5.2 字段错误](#52-字段错误)
  - [6. 实战案例](#6-实战案例)
    - [6.1 Builder 模式宏](#61-builder-模式宏)
    - [6.2 Debug 宏实现](#62-debug-宏实现)
    - [6.3 Serialize 宏](#63-serialize-宏)
  - [7. 总结](#7-总结)
    - [核心要点](#核心要点)
    - [最佳实践](#最佳实践)
  - [📚 参考资源](#-参考资源)

---

## 1. Derive 宏概述

**Derive 宏** 是过程宏的一种，为类型自动生成 trait 实现。

**特点**:

- ✅ 自动生成 trait 实现
- ✅ 作用于结构体和枚举
- ✅ 可组合使用 (`#[derive(Debug, Clone)]`)
- ✅ 支持属性配置

---

## 2. 基础设置

### 2.1 项目结构

```text
my_derive/
├── Cargo.toml
└── src/
    └── lib.rs
```

### 2.2 Cargo.toml 配置

```toml
[package]
name = "my_derive"
version = "0.1.0"
edition = "2021"

[lib]
proc-macro = true

[dependencies]
syn = { version = "2.0", features = ["full"] }
quote = "1.0"
proc-macro2 = "1.0"
```

### 2.3 基本框架

```rust
// src/lib.rs
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyTrait)]
pub fn derive_my_trait(input: TokenStream) -> TokenStream {
    // 1. 解析输入
    let input = parse_macro_input!(input as DeriveInput);
    
    // 2. 提取结构体名称
    let name = &input.ident;
    
    // 3. 生成代码
    let expanded = quote! {
        impl MyTrait for #name {
            fn my_method(&self) {
                println!("Hello from {}", stringify!(#name));
            }
        }
    };
    
    // 4. 返回生成的代码
    TokenStream::from(expanded)
}
```

---

## 3. 解析结构体

### 3.1 解析字段

```rust
use syn::{Data, Fields};

#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    // 提取字段
    let fields = match &input.data {
        Data::Struct(data_struct) => {
            match &data_struct.fields {
                Fields::Named(fields) => &fields.named,
                _ => panic!("Only named fields are supported"),
            }
        }
        _ => panic!("Only structs are supported"),
    };
    
    // 处理每个字段
    for field in fields {
        let field_name = &field.ident;
        let field_type = &field.ty;
        println!("Field: {:?} : {:?}", field_name, field_type);
    }
    
    TokenStream::new()
}
```

### 3.2 解析属性

```rust
use syn::{Attribute, Meta};

#[proc_macro_derive(MyTrait, attributes(my_attr))]
pub fn derive_with_attrs(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    // 解析类型级别属性
    for attr in &input.attrs {
        if attr.path().is_ident("my_attr") {
            println!("Found my_attr attribute");
        }
    }
    
    TokenStream::new()
}

// 使用：
// #[derive(MyTrait)]
// #[my_attr]
// struct MyStruct { ... }
```

---

## 4. 生成代码

### 4.1 基础代码生成

```rust
use quote::quote;

#[proc_macro_derive(Default)]
pub fn derive_default(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    let expanded = quote! {
        impl Default for #name {
            fn default() -> Self {
                Self {
                    // 这里需要为每个字段生成默认值
                }
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

### 4.2 泛型支持

```rust
use syn::{Generics, GenericParam};
use quote::quote;

#[proc_macro_derive(Clone)]
pub fn derive_clone(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let generics = &input.generics;
    
    // 分离泛型参数
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    
    let expanded = quote! {
        impl #impl_generics Clone for #name #ty_generics #where_clause {
            fn clone(&self) -> Self {
                Self {
                    // 克隆每个字段
                }
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

---

## 5. 错误处理

### 5.1 编译错误

```rust
use syn::Error;

#[proc_macro_derive(Validate)]
pub fn derive_validate(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    // 检查是否为结构体
    match input.data {
        Data::Struct(_) => {},
        _ => {
            return Error::new_spanned(
                input,
                "Validate can only be derived for structs"
            ).to_compile_error().into();
        }
    }
    
    TokenStream::new()
}
```

### 5.2 字段错误

```rust
#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    let fields = match &input.data {
        Data::Struct(data) => {
            match &data.fields {
                Fields::Named(fields) => &fields.named,
                Fields::Unnamed(_) => {
                    return Error::new_spanned(
                        data,
                        "Tuple structs are not supported"
                    ).to_compile_error().into();
                }
                Fields::Unit => {
                    return Error::new_spanned(
                        data,
                        "Unit structs are not supported"
                    ).to_compile_error().into();
                }
            }
        }
        _ => panic!("Not a struct"),
    };
    
    TokenStream::new()
}
```

---

## 6. 实战案例

### 6.1 Builder 模式宏

```rust
// my_derive/src/lib.rs
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, Data, DeriveInput, Fields};

#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let builder_name = format!("{}Builder", name);
    let builder_ident = syn::Ident::new(&builder_name, name.span());
    
    let fields = match &input.data {
        Data::Struct(data) => {
            match &data.fields {
                Fields::Named(fields) => &fields.named,
                _ => panic!("Only named fields supported"),
            }
        }
        _ => panic!("Only structs supported"),
    };
    
    // 生成 builder 字段
    let builder_fields = fields.iter().map(|f| {
        let name = &f.ident;
        let ty = &f.ty;
        quote! {
            #name: Option<#ty>
        }
    });
    
    // 生成 setter 方法
    let setters = fields.iter().map(|f| {
        let name = &f.ident;
        let ty = &f.ty;
        quote! {
            pub fn #name(mut self, value: #ty) -> Self {
                self.#name = Some(value);
                self
            }
        }
    });
    
    // 生成 build 方法
    let build_fields = fields.iter().map(|f| {
        let name = &f.ident;
        quote! {
            #name: self.#name.ok_or(concat!("Field '", stringify!(#name), "' not set"))?
        }
    });
    
    let expanded = quote! {
        pub struct #builder_ident {
            #(#builder_fields,)*
        }
        
        impl #builder_ident {
            #(#setters)*
            
            pub fn build(self) -> Result<#name, String> {
                Ok(#name {
                    #(#build_fields,)*
                })
            }
        }
        
        impl #name {
            pub fn builder() -> #builder_ident {
                #builder_ident {
                    #(#fields: None,)*
                }
            }
        }
    };
    
    TokenStream::from(expanded)
}

// 使用示例
#[derive(Builder)]
struct User {
    name: String,
    age: u32,
    email: String,
}

fn main() {
    let user = User::builder()
        .name("Alice".to_string())
        .age(30)
        .email("alice@example.com".to_string())
        .build()
        .unwrap();
}
```

### 6.2 Debug 宏实现

```rust
#[proc_macro_derive(Debug)]
pub fn derive_debug(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    let fields = match &input.data {
        Data::Struct(data) => {
            match &data.fields {
                Fields::Named(fields) => &fields.named,
                _ => panic!("Only named fields supported"),
            }
        }
        _ => panic!("Only structs supported"),
    };
    
    let debug_fields = fields.iter().map(|f| {
        let name = &f.ident;
        quote! {
            .field(stringify!(#name), &self.#name)
        }
    });
    
    let expanded = quote! {
        impl std::fmt::Debug for #name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_struct(stringify!(#name))
                    #(#debug_fields)*
                    .finish()
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

### 6.3 Serialize 宏

```rust
#[proc_macro_derive(Serialize)]
pub fn derive_serialize(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    let fields = match &input.data {
        Data::Struct(data) => {
            match &data.fields {
                Fields::Named(fields) => &fields.named,
                _ => panic!("Only named fields supported"),
            }
        }
        _ => panic!("Only structs supported"),
    };
    
    let serialize_fields = fields.iter().map(|f| {
        let name = &f.ident;
        let name_str = name.as_ref().unwrap().to_string();
        quote! {
            map.insert(#name_str, format!("{:?}", self.#name));
        }
    });
    
    let expanded = quote! {
        impl #name {
            pub fn serialize(&self) -> std::collections::HashMap<String, String> {
                let mut map = std::collections::HashMap::new();
                #(#serialize_fields)*
                map
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

---

## 7. 总结

### 核心要点

1. **项目配置**: `[lib] proc-macro = true`
2. **依赖**: `syn`, `quote`, `proc-macro2`
3. **解析**: 使用 `syn` 解析结构体
4. **生成**: 使用 `quote!` 生成代码
5. **错误**: 使用 `syn::Error` 报告错误

### 最佳实践

| 场景 | 推荐做法 |
|------|---------|
| **字段访问** | 使用 `Fields::Named` |
| **泛型** | 使用 `split_for_impl()` |
| **属性** | 使用 `attributes(my_attr)` |
| **错误** | 使用 `syn::Error::new_spanned()` |
| **测试** | 使用 `trybuild` |

**常见陷阱**:

- ❌ 不支持 tuple struct
- ❌ 忽略泛型约束
- ❌ 错误信息不清晰
- ❌ 缺少测试
- ✅ 检查字段类型
- ✅ 生成完整的泛型约束
- ✅ 提供清晰的错误信息
- ✅ 使用 `cargo expand` 调试

---

## 📚 参考资源

**文档**:

- [The Rust Reference - Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)
- [syn crate](https://docs.rs/syn/)
- [quote crate](https://docs.rs/quote/)

**工具**:

- `cargo expand` - 查看宏展开
- `trybuild` - 测试过程宏

**相关文档**:

- [Tier 2: 声明宏实践指南](./01_声明宏实践指南.md)
- [Tier 2: 属性宏开发指南](./03_属性宏开发指南.md)

---

**文档维护**: C14 Macro System Team  
**最后审核**: 2025-10-23  
**下次更新**: 2026-01-23
