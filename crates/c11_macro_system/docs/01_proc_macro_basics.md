# C11 过程宏基础

> **模块**: C11 宏系统
> **难度**: 中级 → 高级
> **Rust 版本**: 1.94.0+

---

## 📋 目录

- [C11 过程宏基础](#c11-过程宏基础)
  - [📋 目录](#-目录)
  - [过程宏概述](#过程宏概述)
  - [派生宏 (Derive Macro)](#派生宏-derive-macro)
  - [属性宏 (Attribute Macro)](#属性宏-attribute-macro)
  - [函数宏 (Function Macro)](#函数宏-function-macro)

---

## 过程宏概述

过程宏在编译时操作 Rust 代码的抽象语法树 (AST)。

```rust
// 三种过程宏类型
// 1. 派生宏: #[derive(Trait)]
// 2. 属性宏: #[attribute]
// 3. 函数宏: macro!(...)
```

---

## 派生宏 (Derive Macro)

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(CustomDebug)]
pub fn derive_custom_debug(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let expanded = quote! {
        impl std::fmt::Debug for #name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{} {{ ... }}", stringify!(#name))
            }
        }
    };

    expanded.into()
}
```

---

## 属性宏 (Attribute Macro)

```rust
#[proc_macro_attribute]
pub fn trace(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    let fn_name = &input_fn.sig.ident;
    let fn_body = &input_fn.block;

    let expanded = quote! {
        {
            println!("Entering: {}", stringify!(#fn_name));
            let result = #fn_body;
            println!("Exiting: {}", stringify!(#fn_name));
            result
        }
    };

    expanded.into()
}
```

---

## 函数宏 (Function Macro)

```rust
#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    let query = parse_macro_input!(input as LitStr);
    let query_str = query.value();

    // 在编译时解析 SQL 语法

    quote! {
        Query { sql: #query }
    }.into()
}
```

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
**状态**: ✅ 100% 完成
