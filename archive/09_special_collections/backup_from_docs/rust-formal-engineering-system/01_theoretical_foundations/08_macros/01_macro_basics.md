# 宏系统基础（Macro System Basics）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [宏系统基础](#宏系统基础macro-system-basics)
  - [概述](#概述)
  - [声明式宏](#声明式宏)
  - [过程宏](#过程宏)
  - [属性宏](#属性宏)
  - [实践示例](#实践示例)
  - [最佳实践](#最佳实践)
  - [参考资料](#参考资料)

---

## 概述

Rust 的宏系统提供了强大的元编程能力，包括声明式宏（macro_rules!）和过程宏（procedural macros）。宏可以在编译时生成代码，减少重复并提高代码的可维护性。

## 声明式宏

### 基本语法

```rust
macro_rules! say_hello {
    () => {
        println!("Hello!");
    };
}

// 使用
say_hello!();
```

### 带参数的宏

```rust
macro_rules! greet {
    ($name:expr) => {
        println!("Hello, {}!", $name);
    };
}

// 使用
greet!("World");
greet!(format!("User {}", 123));
```

### 多个匹配模式

```rust
macro_rules! calculate {
    (add $a:expr, $b:expr) => {
        $a + $b
    };
    (multiply $a:expr, $b:expr) => {
        $a * $b
    };
    (subtract $a:expr, $b:expr) => {
        $a - $b
    };
}

// 使用
let sum = calculate!(add 5, 3);
let product = calculate!(multiply 4, 2);
```

### 重复模式

```rust
macro_rules! vec {
    ($($x:expr),*) => {
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
let v = vec![1, 2, 3, 4, 5];
```

## 过程宏

### 派生宏（Derive Macros）

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(HelloMacro)]
pub fn hello_macro_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let expanded = quote! {
        impl HelloMacro for #name {
            fn hello_macro() {
                println!("Hello, Macro! My name is {}!", stringify!(#name));
            }
        }
    };

    TokenStream::from(expanded)
}

// 使用
#[derive(HelloMacro)]
struct Pancakes;

// Pancakes::hello_macro() 会打印 "Hello, Macro! My name is Pancakes!"
```

### 函数式宏

```rust
#[proc_macro]
pub fn sql(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input);

    // 解析 SQL 查询
    // 生成类型安全的查询代码

    quote! {
        // 生成的代码
    }.into()
}

// 使用
let query = sql!(SELECT * FROM users WHERE id = 1);
```

## 属性宏

### 自定义属性

```rust
#[proc_macro_attribute]
pub fn route(attr: TokenStream, item: TokenStream) -> TokenStream {
    let attr = parse_macro_input!(attr);
    let item = parse_macro_input!(item);

    // 处理属性参数
    // 修改或包装函数

    quote! {
        // 生成的代码
    }.into()
}

// 使用
#[route(GET, "/users")]
fn get_users() {
    // 函数体
}
```

### 测试宏

```rust
#[proc_macro_attribute]
pub fn test_case(attr: TokenStream, item: TokenStream) -> TokenStream {
    let test_fn = parse_macro_input!(item as syn::ItemFn);
    let test_name = &test_fn.sig.ident;

    quote! {
        #[test]
        fn #test_name() {
            // 测试逻辑
        }
    }.into()
}
```

## 实践示例

### 示例 1：Builder 模式宏

```rust
macro_rules! builder {
    (
        $struct_name:ident {
            $(
                $field:ident: $field_type:ty
            ),* $(,)?
        }
    ) => {
        pub struct $struct_name {
            $(
                $field: Option<$field_type>,
            )*
        }

        impl $struct_name {
            pub fn new() -> Self {
                $struct_name {
                    $(
                        $field: None,
                    )*
                }
            }

            $(
                pub fn $field(mut self, value: $field_type) -> Self {
                    self.$field = Some(value);
                    self
                }
            )*

            pub fn build(self) -> Result<$struct_name, String> {
                Ok($struct_name {
                    $(
                        $field: self.$field.ok_or_else(|| {
                            format!("字段 {} 未设置", stringify!($field))
                        })?,
                    )*
                })
            }
        }
    };
}

// 使用
builder! {
    User {
        name: String,
        email: String,
        age: u32,
    }
}

let user = User::new()
    .name("Alice".to_string())
    .email("alice@example.com".to_string())
    .age(30)
    .build()?;
```

### 示例 2：日志宏

```rust
macro_rules! log {
    ($level:ident, $($arg:tt)*) => {
        println!("[{}] {}", stringify!($level), format!($($arg)*));
    };
}

macro_rules! info {
    ($($arg:tt)*) => {
        log!(INFO, $($arg)*);
    };
}

macro_rules! error {
    ($($arg:tt)*) => {
        log!(ERROR, $($arg)*);
    };
}

// 使用
info!("用户 {} 登录", user_id);
error!("处理失败: {}", error_message);
```

### 示例 3：类型安全的 SQL 构建器

```rust
macro_rules! select {
    ($($field:ident),* $(,)?) => {
        {
            let mut query = String::from("SELECT ");
            $(
                query.push_str(stringify!($field));
                query.push_str(", ");
            )*
            query.pop();
            query.pop();
            query
        }
    };
}

macro_rules! from {
    ($table:ident) => {
        format!(" FROM {}", stringify!($table))
    };
}

// 使用
let query = format!("{}{}", select!(id, name, email), from!(users));
```

## 最佳实践

### 1. 宏命名

```rust
// ✅ 正确：使用清晰的命名
macro_rules! create_user { ... }

// ❌ 错误：命名不清晰
macro_rules! cu { ... }
```

### 2. 文档注释

```rust
/// 创建一个新的用户
///
/// # 示例
///
/// ```
/// create_user!("Alice", "alice@example.com");
/// ```
macro_rules! create_user {
    // ...
}
```

### 3. 错误消息

```rust
macro_rules! require_field {
    ($field:expr, $name:expr) => {
        $field.ok_or_else(|| {
            format!("必需字段 {} 未设置", $name)
        })?
    };
}
```

## 参考资料

- [宏系统索引](./00_index.md)
- [理论基础索引](../00_index.md)
- [Rust 宏文档](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [proc-macro2 文档](https://docs.rs/proc-macro2/)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回理论基础: [`../00_index.md`](../00_index.md)
