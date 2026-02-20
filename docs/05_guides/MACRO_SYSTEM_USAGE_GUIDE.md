# 宏系统使用指南

**模块**: C11 Macro System
**创建日期**: 2025-12-11
**最后更新**: 2026-02-15
**Rust 版本**: 1.93.0+ (Edition 2024)
**状态**: ✅ 已完成

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
  - [🔬 声明宏完整示例](#-声明宏完整示例)
    - [示例 1: 模式匹配与重复](#示例-1-模式匹配与重复)
    - [示例 2: Token Tree 操作](#示例-2-token-tree-操作)
    - [示例 3: 条件编译宏](#示例-3-条件编译宏)
  - [🔧 过程宏完整示例](#-过程宏完整示例)
    - [示例 1: 自定义 Derive 宏](#示例-1-自定义-derive-宏)
    - [示例 2: 属性宏](#示例-2-属性宏)
    - [示例 3: 函数式宏](#示例-3-函数式宏)
  - [⚠️ 宏的常见陷阱与调试技巧](#️-宏的常见陷阱与调试技巧)
    - [陷阱 1: 卫生性问题 (Hygiene)](#陷阱-1-卫生性问题-hygiene)
    - [陷阱 2: 表达式 vs 语句](#陷阱-2-表达式-vs-语句)
    - [陷阱 3: 重复模式匹配问题](#陷阱-3-重复模式匹配问题)
    - [陷阱 4: 编译错误信息模糊](#陷阱-4-编译错误信息模糊)
    - [调试技巧 1: 展开宏查看](#调试技巧-1-展开宏查看)
    - [调试技巧 2: 使用 `trace_macros!`](#调试技巧-2-使用-trace_macros)
    - [调试技巧 3: 使用 `log_syntax!`](#调试技巧-3-使用-log_syntax)
    - [调试技巧 4: 编译时断言](#调试技巧-4-编译时断言)
    - [调试技巧 5: 过程宏调试](#调试技巧-5-过程宏调试)
  - [⚡ 最佳实践](#-最佳实践)
    - [1. 宏命名](#1-宏命名)
    - [2. 文档](#2-文档)
    - [3. 错误处理](#3-错误处理)
    - [4. 可见性控制](#4-可见性控制)
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

## 🔬 声明宏完整示例

### 示例 1: 模式匹配与重复

```rust
// 匹配不同数量的参数
macro_rules! calculate {
    // 单个值
    ($x:expr) => {
        $x
    };
    // 加法：两个值
    ($x:expr + $y:expr) => {
        $x + $y
    };
    // 复杂表达式
    ($x:expr, $y:expr, $op:tt) => {
        calculate!(@internal $x $op $y)
    };
    // 内部规则（私有）
    (@internal $x:expr + $y:expr) => { $x + $y };
    (@internal $x:expr - $y:expr) => { $x - $y };
    (@internal $x:expr * $y:expr) => { $x * $y };
    (@internal $x:expr / $y:expr) => { $x / $y };
}

// 递归处理重复
macro_rules! sum {
    () => { 0 };
    ($x:expr) => { $x };
    ($x:expr, $($rest:tt)*) => {
        $x + sum!($($rest)*)
    };
}
```

### 示例 2: Token Tree 操作

```rust
// 解析键值对
macro_rules! hashmap {
    // 空 map
    () => { {
        let mut _map = ::std::collections::HashMap::new();
        _map
    } };
    // 单个键值对
    ($key:expr => $value:expr $(,)?) => { {
        let mut _map = ::std::collections::HashMap::new();
        _map.insert($key, $value);
        _map
    } };
    // 多个键值对
    ($($key:expr => $value:expr),+ $(,)?) => { {
        let mut _map = ::std::collections::HashMap::new();
        $(
            _map.insert($key, $value);
        )+
        _map
    } };
}

// 使用
let map = hashmap! {
    "name" => "Alice",
    "age" => 30,
    "city" => "Beijing",
};
```

### 示例 3: 条件编译宏

```rust
macro_rules! platform_specific {
    // 根据平台选择代码
    (linux: $linux_code:block, windows: $windows_code:block, macos: $macos_code:block) => {
        #[cfg(target_os = "linux")]
        $linux_code
        #[cfg(target_os = "windows")]
        $windows_code
        #[cfg(target_os = "macos")]
        $macos_code
    };
}

// 使用
platform_specific! {
    linux: {
        println!("运行在 Linux");
    },
    windows: {
        println!("运行在 Windows");
    },
    macos: {
        println!("运行在 macOS");
    },
}
```

---

## 🔧 过程宏完整示例

### 示例 1: 自定义 Derive 宏

```rust
// lib.rs - 过程宏 crate
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Data, Fields};

#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let builder_name = quote::format_ident!("{}Builder", name);

    // 提取字段信息
    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            _ => panic!("只支持命名字段"),
        },
        _ => panic!("只支持 struct"),
    };

    // 生成 Builder 字段
    let builder_fields = fields.iter().map(|f| {
        let name = &f.ident;
        let ty = &f.ty;
        quote! { #name: Option<#ty> }
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
            #name: self.#name.ok_or(concat!(stringify!(#name), " 是必需的"))?
        }
    });

    let expanded = quote! {
        pub struct #builder_name {
            #(#builder_fields,)*
        }

        impl #builder_name {
            pub fn new() -> Self {
                Self {
                    #(#name: None,)*
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
    };

    TokenStream::from(expanded)
}
```

### 示例 2: 属性宏

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

// 计时属性宏
#[proc_macro_attribute]
pub fn timed(attr: TokenStream, item: TokenStream) -> TokenStream {
    let func = parse_macro_input!(item as ItemFn);
    let func_name = &func.sig.ident;
    let func_vis = &func.vis;
    let func_block = &func.block;
    let func_sig = &func.sig;

    // 解析属性参数
    let label = if attr.is_empty() {
        func_name.to_string()
    } else {
        attr.to_string().replace('"', "")
    };

    let expanded = quote! {
        #func_vis #func_sig {
            let _start = std::time::Instant::now();
            let _result = #func_block;
            let _elapsed = _start.elapsed();
            println!("[timed] {} 耗时: {:?}", #label, _elapsed);
            _result
        }
    };

    TokenStream::from(expanded)
}

// 使用
// #[timed("自定义标签")]
// fn heavy_computation() -> i32 { ... }
```

### 示例 3: 函数式宏

```rust
use proc_macro::TokenStream;
use proc_macro2::TokenTree;
use quote::quote;

// SQL 查询验证宏
#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    let tokens: Vec<_> = input.into_iter().collect();

    // 简单解析：检查是否是 SELECT/INSERT/UPDATE/DELETE
    if let Some(first) = tokens.first() {
        let sql_type = first.to_string().to_uppercase();
        let allowed = ["SELECT", "INSERT", "UPDATE", "DELETE"];

        if !allowed.contains(&sql_type.as_str()) {
            return syn::Error::new_spanned(
                first,
                "只支持 SELECT, INSERT, UPDATE, DELETE"
            )
            .to_compile_error()
            .into();
        }
    }

    // 转换回字符串
    let sql_string: String = tokens.iter()
        .map(|t| t.to_string())
        .collect::<Vec<_>>()
        .join(" ");

    let expanded = quote! {
        #sql_string
    };

    TokenStream::from(expanded)
}

// 使用
// let query = sql!(SELECT * FROM users WHERE id = 1);
```

---

## ⚠️ 宏的常见陷阱与调试技巧

### 陷阱 1: 卫生性问题 (Hygiene)

```rust
macro_rules! buggy_scope {
    () => {
        let x = 42;
        println!("{}", x);
    };
}

fn main() {
    let x = 10;
    buggy_scope!(); // 正常运行
    // 但如果宏内部变量与外部冲突...
}

// ✅ 解决方案：使用唯一标识符
macro_rules! safe_scope {
    () => {
        {
            let __macro_unique_x = 42;
            println!("{}", __macro_unique_x);
        }
    };
}
```

### 陷阱 2: 表达式 vs 语句

```rust
macro_rules! double {
    ($x:expr) => {
        $x * 2  // 如果 $x 是 match 表达式，可能出错
    };
}

// ❌ 问题
// let y = double!(match x { 0 => 1, _ => 2 });

// ✅ 解决方案：使用括号
macro_rules! double_safe {
    ($x:expr) => {{
        ($x) * 2
    }};
}
```

### 陷阱 3: 重复模式匹配问题

```rust
// ❌ 错误的重复匹配
macro_rules! wrong_repeat {
    ($($x:expr),*) => {
        $(
            println!("{}", $x);
            let y = $x + 1; // 可能产生多个 let 语句
        )*
    };
}

// ✅ 正确的重复匹配
macro_rules! correct_repeat {
    ($($x:expr),*) => {{
        $(
            println!("{}", $x);
        )*
    }};
}
```

### 陷阱 4: 编译错误信息模糊

```rust
// ❌ 错误信息不清晰
macro_rules! bad_assert {
    ($x:expr) => {
        if !$x {
            panic!("断言失败");
        }
    };
}

// ✅ 提供有用的错误信息
macro_rules! good_assert {
    ($x:expr) => {
        if !$x {
            panic!(
                "断言失败: {} at {}:{}",
                stringify!($x),
                file!(),
                line!()
            );
        }
    };
}
```

### 调试技巧 1: 展开宏查看

```bash
# 查看宏展开结果
cargo expand --lib

# 查看特定模块的展开
cargo expand --lib my_module

# 查看测试中的宏展开
cargo expand --test my_test
```

### 调试技巧 2: 使用 `trace_macros!`

```rust
#![feature(trace_macros)]

trace_macros!(true);

// 这行会打印宏展开过程
vec![1, 2, 3];

trace_macros!(false);
```

### 调试技巧 3: 使用 `log_syntax!`

```rust
#![feature(log_syntax)]

macro_rules! debug_macro {
    ($($tokens:tt)*) => {{
        log_syntax!("宏输入:", $($tokens)*);
        // ... 宏逻辑
    }};
}
```

### 调试技巧 4: 编译时断言

```rust
macro_rules! const_assert {
    ($x:expr $(,)?) => {
        const _: [(); 0 - !{ const ASSERT: bool = $x; ASSERT } as usize] = [];
    };
}

// 使用
const_assert!(std::mem::size_of::<usize>() == 8);
// const_assert!(1 == 2); // 编译错误！
```

### 调试技巧 5: 过程宏调试

```rust
// 在过程宏中使用 eprintln!
#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    eprintln!("输入: {}", input.to_string());

    let result = /* ... */;
    eprintln!("输出: {}", result.to_string());

    result
}
```

---

## ⚡ 最佳实践

### 1. 宏命名

- 使用 `snake_case`
- 使用描述性名称
- 避免与标准库宏冲突
- 过程宏 crate 名通常以 `_derive` 或 `_macros` 结尾

### 2. 文档

````rust
/// 创建一个 Vec，支持多种初始化语法
///
/// # Examples
///
/// ```
/// let v = my_vec![1, 2, 3];
/// assert_eq!(v.len(), 3);
/// ```
///
/// ```
/// let v = my_vec![0; 10]; // 10 个 0
/// assert_eq!(v.len(), 10);
/// ```
#[macro_export]
macro_rules! my_vec {
    // ...
}
````

### 3. 错误处理

```rust
macro_rules! safe_divide {
    ($a:expr, $b:expr) => {
        {
            let a = $a;
            let b = $b;
            if b == 0 {
                return Err("Division by zero".into());
            }
            a / b
        }
    };
}

// 先绑定再使用，避免重复计算
macro_rules! min {
    ($x:expr, $y:expr) => {{
        let x = $x;
        let y = $y;
        if x < y { x } else { y }
    }};
}
```

### 4. 可见性控制

```rust
// 使用内部规则隐藏实现细节
macro_rules! public_macro {
    // 公共接口
    ($x:expr) => {
        public_macro!(@internal $x)
    };
    // 私有实现
    (@internal $x:expr) => {
        $x + 1
    };
}
```

---

## 📚 相关文档

- [完整文档](../../crates/c11_macro_system/README.md)
- [声明宏指南](../../crates/c11_macro_system/docs/tier_02_guides/01_声明宏实践指南.md)
- [过程宏指南](../../crates/c11_macro_system/docs/tier_02_guides/02_Derive宏开发指南.md)
- [宏扩展形式化](../research_notes/formal_methods/macro_expansion_formalization.md) - 宏扩展过程的形式化分析

---

**维护者**: Rust 学习项目团队
**状态**: ✅ 完整实现
**最后更新**: 2026-02-20
