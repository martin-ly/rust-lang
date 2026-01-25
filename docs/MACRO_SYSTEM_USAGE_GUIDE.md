# 宏系统使用指南

**模块**: C11 Macro System
**创建日期**: 2025-12-11
**最后更新**: 2026-01-26
**Rust 版本**: 1.93.0+
**Edition**: 2024

---

## 📋 目录

- [宏系统使用指南](#宏系统使用指南)
  - [📋 目录](#-目录)
  - [📋 概述](#-概述)
  - [🚀 快速开始](#-快速开始)
    - [声明宏](#声明宏)
    - [过程宏](#过程宏)
  - [📊 核心功能](#-核心功能)
    - [1. 声明宏](#1-声明宏)
      - [基本语法](#基本语法)
      - [重复模式](#重复模式)
      - [条件展开](#条件展开)
    - [2. 属性宏](#2-属性宏)
    - [3. 派生宏](#3-派生宏)
    - [4. 函数式宏](#4-函数式宏)
  - [🔧 实用宏示例](#-实用宏示例)
    - [1. 调试宏](#1-调试宏)
    - [2. 测试宏](#2-测试宏)
    - [3. 构建器宏](#3-构建器宏)
  - [⚡ 最佳实践](#-最佳实践)
    - [1. 宏命名](#1-宏命名)
    - [2. 文档](#2-文档)
    - [3. 错误处理](#3-错误处理)
  - [📚 相关文档](#-相关文档)

---

## 📋 概述

本指南介绍 Rust 宏系统的使用，包括声明宏、过程宏、属性宏、派生宏等。

---

## 🚀 快速开始

### 声明宏

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

// 使用
let v = vec![1, 2, 3];
```

### 过程宏

```rust
use proc_macro::TokenStream;

#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // 处理输入并生成代码
    input
}
```

---

## 📊 核心功能

### 1. 声明宏

#### 基本语法

```rust
macro_rules! my_macro {
    // 模式匹配
    (pattern) => {
        // 展开代码
    };
}
```

#### 重复模式

```rust
macro_rules! repeat {
    ($($item:expr),*) => {
        {
            let mut vec = Vec::new();
            $(
                vec.push($item);
            )*
            vec
        }
    };
}
```

#### 条件展开

```rust
macro_rules! conditional {
    ($condition:expr => $then:expr) => {
        if $condition {
            $then
        }
    };
    ($condition:expr => $then:expr else $else:expr) => {
        if $condition {
            $then
        } else {
            $else
        }
    };
}
```

### 2. 属性宏

```rust
use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn my_attribute(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // 处理属性并修改项
    item
}

// 使用
#[my_attribute]
fn my_function() {
    // ...
}
```

### 3. 派生宏

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyTrait)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let expanded = quote! {
        impl MyTrait for #name {
            fn method(&self) -> String {
                format!("{}", stringify!(#name))
            }
        }
    };

    TokenStream::from(expanded)
}

// 使用
#[derive(MyTrait)]
struct MyStruct;

let s = MyStruct;
println!("{}", s.method());  // "MyStruct"
```

### 4. 函数式宏

```rust
#[proc_macro]
pub fn my_function_macro(input: TokenStream) -> TokenStream {
    // 处理输入
    input
}

// 使用
my_function_macro!(some input);
```

---

## 🔧 实用宏示例

### 1. 调试宏

```rust
macro_rules! dbg_print {
    ($($arg:tt)*) => {
        #[cfg(debug_assertions)]
        println!($($arg)*);
    };
}
```

### 2. 测试宏

```rust
macro_rules! test_case {
    ($name:ident, $input:expr, $expected:expr) => {
        #[test]
        fn $name() {
            assert_eq!(process($input), $expected);
        }
    };
}

test_case!(test_1, 1, 2);
test_case!(test_2, 2, 4);
```

### 3. 构建器宏

```rust
macro_rules! builder {
    ($name:ident { $($field:ident: $type:ty),* }) => {
        struct $name {
            $($field: Option<$type>),*
        }

        impl $name {
            fn new() -> Self {
                Self {
                    $($field: None),*
                }
            }

            $(
                fn $field(mut self, value: $type) -> Self {
                    self.$field = Some(value);
                    self
                }
            )*
        }
    };
}

builder!(Config {
    host: String,
    port: u16,
});

// 使用
let config = Config::new()
    .host("localhost".to_string())
    .port(8080);
```

---

## ⚡ 最佳实践

### 1. 宏命名

- 使用 `snake_case`
- 使用描述性名称
- 避免与标准库宏冲突

### 2. 文档

```rust
/// 这是一个有用的宏
///
/// # Examples
///
/// ```
/// my_macro!(input);
/// ```
macro_rules! my_macro {
    // ...
}
```

### 3. 错误处理

```rust
macro_rules! safe_divide {
    ($a:expr, $b:expr) => {
        {
            if $b == 0 {
                return Err("Division by zero".into());
            }
            $a / $b
        }
    };
}
```

---

## 📚 相关文档

- [完整文档](../crates/c11_macro_system/README.md)
- [声明宏指南](../crates/c11_macro_system/docs/tier_02_guides/01_声明宏指南.md)
- [过程宏指南](../crates/c11_macro_system/docs/tier_02_guides/02_过程宏指南.md)

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 完整实现
**最后更新**: 2026-01-26
