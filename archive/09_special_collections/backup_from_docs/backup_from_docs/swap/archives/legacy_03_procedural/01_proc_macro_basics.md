# 过程宏基础

> **文档定位**: Rust过程宏的核心概念和基础用法  
> **难度级别**: ⭐⭐⭐ 高级  
> **预计时间**: 3小时  
> **最后更新**: 2025-10-20

---

## 📊 目录

- [过程宏基础](#过程宏基础)
  - [📊 目录](#-目录)
  - [📋 学习目标](#-学习目标)
  - [1. 什么是过程宏](#1-什么是过程宏)
    - [1.1 定义](#11-定义)
    - [1.2 与声明宏的区别](#12-与声明宏的区别)
    - [1.3 过程宏的类型](#13-过程宏的类型)
      - [派生宏 (Derive Macros)](#派生宏-derive-macros)
      - [属性宏 (Attribute Macros)](#属性宏-attribute-macros)
      - [函数式宏 (Function-like Macros)](#函数式宏-function-like-macros)
  - [2. TokenStream 基础](#2-tokenstream-基础)
    - [2.1 什么是TokenStream](#21-什么是tokenstream)
    - [2.2 Token类型](#22-token类型)
    - [2.3 TokenStream操作](#23-tokenstream操作)
  - [3. AST (抽象语法树)](#3-ast-抽象语法树)
    - [3.1 什么是AST](#31-什么是ast)
    - [3.2 使用syn解析AST](#32-使用syn解析ast)
    - [3.3 常见AST节点](#33-常见ast节点)
  - [4. 编译时执行](#4-编译时执行)
    - [4.1 过程宏的执行时机](#41-过程宏的执行时机)
    - [4.2 编译时限制](#42-编译时限制)
    - [4.3 错误处理](#43-错误处理)
  - [5. 第一个过程宏](#5-第一个过程宏)
    - [5.1 创建crate](#51-创建crate)
    - [5.2 实现Hello宏](#52-实现hello宏)
    - [5.3 使用宏](#53-使用宏)
  - [6. 调试过程宏](#6-调试过程宏)
    - [6.1 使用eprintln](#61-使用eprintln)
    - [6.2 使用cargo-expand](#62-使用cargo-expand)
    - [6.3 使用trybuild测试](#63-使用trybuild测试)
  - [7. 性能考虑](#7-性能考虑)
    - [7.1 编译时间](#71-编译时间)
    - [7.2 缓存优化](#72-缓存优化)
  - [8. 最佳实践](#8-最佳实践)
    - [8.1 错误处理](#81-错误处理)
    - [8.2 文档和测试](#82-文档和测试)
    - [8.3 版本兼容性](#83-版本兼容性)
  - [9. 常见问题](#9-常见问题)
    - [9.1 编译错误](#91-编译错误)
    - [9.2 运行时错误](#92-运行时错误)
    - [9.3 调试困难](#93-调试困难)
  - [10. 实践练习](#10-实践练习)
    - [练习1: 简单属性宏](#练习1-简单属性宏)
    - [练习2: 派生宏](#练习2-派生宏)
    - [练习3: 函数式宏](#练习3-函数式宏)
  - [📚 总结](#-总结)
    - [关键概念](#关键概念)
    - [核心技能](#核心技能)
    - [下一步](#下一步)

## 📋 学习目标

完成本章后，你将能够：

- ✅ 理解过程宏的基本概念
- ✅ 掌握TokenStream的使用
- ✅ 了解AST和编译时执行
- ✅ 实现简单的过程宏
- ✅ 理解过程宏与声明宏的区别

---

## 1. 什么是过程宏

### 1.1 定义

**过程宏 (Procedural Macros)** 是Rust中最强大的元编程工具，允许在编译时执行Rust代码来生成或转换其他Rust代码。

### 1.2 与声明宏的区别

| 特性 | 声明宏 (macro_rules!) | 过程宏 (proc_macro) |
|------|----------------------|---------------------|
| **复杂度** | 简单模式匹配 | 完整的Rust代码 |
| **输入** | Token树 | TokenStream |
| **处理** | 模式替换 | AST操作 |
| **编译** | 宏展开器 | 独立crate |
| **调试** | 困难 | 相对容易 |
| **性能** | 快 | 较慢 |

### 1.3 过程宏的类型

#### 派生宏 (Derive Macros)

```rust
#[derive(Builder)]
struct Config {
    host: String,
    port: u16,
}
```

#### 属性宏 (Attribute Macros)

```rust
#[debug_print]
fn my_function() {
    println!("Hello!");
}
```

#### 函数式宏 (Function-like Macros)

```rust
let result = my_macro!(some input);
```

---

## 2. TokenStream 基础

### 2.1 什么是TokenStream

`TokenStream` 是过程宏的输入和输出类型，表示一系列Rust tokens。

```rust
use proc_macro::TokenStream;

// TokenStream包含tokens，如：
// ident: "my_function"
// punct: "("
// literal: "42"
// punct: ")"
// punct: ";"
```

### 2.2 Token类型

```rust
// 标识符
let ident = syn::Ident::new("my_function", proc_macro2::Span::call_site());

// 字面量
let literal = syn::LitInt::new("42", proc_macro2::Span::call_site());

// 标点符号
let punct = syn::Punct::new('+', proc_macro2::Spacing::Alone);

// 分隔符
let delimiter = syn::MacroDelimiter::Paren(syn::token::Paren::default());
```

### 2.3 TokenStream操作

```rust
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;

// 创建TokenStream
let tokens = quote! {
    fn hello() {
        println!("Hello, world!");
    }
};

// 转换为proc_macro::TokenStream
let proc_tokens = proc_macro::TokenStream::from(tokens);
```

---

## 3. AST (抽象语法树)

### 3.1 什么是AST

**AST (Abstract Syntax Tree)** 是源代码的树状表示，每个节点代表代码的一个语法元素。

### 3.2 使用syn解析AST

```rust
use syn::{parse_macro_input, DeriveInput, ItemFn};

// 解析结构体
let input = parse_macro_input!(input as DeriveInput);
let struct_name = &input.ident;
let fields = match &input.data {
    syn::Data::Struct(data) => &data.fields,
    _ => panic!("只支持结构体"),
};

// 解析函数
let input_fn = parse_macro_input!(item as ItemFn);
let fn_name = &input_fn.sig.ident;
let fn_body = &input_fn.block;
```

### 3.3 常见AST节点

```rust
// 结构体字段
struct Field {
    vis: Visibility,      // 可见性
    ident: Option<Ident>,  // 字段名
    ty: Type,             // 字段类型
    attrs: Vec<Attribute>, // 属性
}

// 函数签名
struct Signature {
    constness: Option<Token![const]>,
    asyncness: Option<Token![async]>,
    unsafety: Option<Token![unsafe]>,
    abi: Option<Abi>,
    fn_token: Token![fn],
    ident: Ident,
    generics: Generics,
    paren_token: token::Paren,
    inputs: Punctuated<FnArg, Token![,]>,
    variadic: Option<ArgCaptured>,
    output: ReturnType,
}
```

---

## 4. 编译时执行

### 4.1 过程宏的执行时机

过程宏在**编译时**执行，具体时机：

1. **词法分析** 完成后
2. **语法分析** 进行中
3. **语义分析** 之前

### 4.2 编译时限制

```rust
// ❌ 不能做的事情
fn proc_macro_example() {
    // 不能访问文件系统
    std::fs::read_to_string("file.txt"); // 编译错误
    
    // 不能进行网络请求
    reqwest::get("https://api.example.com"); // 编译错误
    
    // 不能使用std::thread
    std::thread::spawn(|| {}); // 编译错误
}

// ✅ 可以做的事情
fn proc_macro_example() {
    // 可以解析和生成代码
    let ast = syn::parse_str::<DeriveInput>("struct MyStruct {}");
    
    // 可以进行字符串操作
    let name = "MyStruct".to_string();
    
    // 可以使用数学运算
    let result = 1 + 2;
}
```

### 4.3 错误处理

```rust
use proc_macro::TokenStream;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyMacro)]
pub fn my_macro(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    // 检查输入
    match &input.data {
        syn::Data::Struct(_) => {
            // 处理结构体
        }
        syn::Data::Enum(_) => {
            return syn::Error::new_spanned(
                &input,
                "MyMacro只支持结构体，不支持枚举"
            ).to_compile_error().into();
        }
        syn::Data::Union(_) => {
            return syn::Error::new_spanned(
                &input,
                "MyMacro只支持结构体，不支持联合体"
            ).to_compile_error().into();
        }
    }
    
    // 生成代码
    TokenStream::from(quote! {
        // 生成的代码
    })
}
```

---

## 5. 第一个过程宏

### 5.1 创建crate

```toml
# Cargo.toml
[package]
name = "my_proc_macro"
version = "0.1.0"
edition = "2021"

[lib]
proc-macro = true

[dependencies]
syn = { version = "2.0", features = ["full"] }
quote = "1.0"
proc-macro2 = "1.0"
```

### 5.2 实现Hello宏

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

/// 简单的Hello宏
#[proc_macro_attribute]
pub fn hello(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    let fn_name = &input_fn.sig.ident;
    
    let expanded = quote! {
        fn #fn_name() {
            println!("Hello from macro!");
            println!("Function: {}", stringify!(#fn_name));
        }
    };
    
    TokenStream::from(expanded)
}
```

### 5.3 使用宏

```rust
use my_proc_macro::hello;

#[hello]
fn greet() {
    // 这个函数会被宏替换
}

fn main() {
    greet(); // 输出: Hello from macro!
             //       Function: greet
}
```

---

## 6. 调试过程宏

### 6.1 使用eprintln

```rust
#[proc_macro_derive(DebugMacro)]
pub fn debug_macro(input: TokenStream) -> TokenStream {
    eprintln!("输入: {}", input);
    
    let input = parse_macro_input!(input as DeriveInput);
    eprintln!("解析后的结构体: {}", input.ident);
    
    let output = quote! {
        impl std::fmt::Debug for #input {
            // 实现
        }
    };
    
    eprintln!("输出: {}", output);
    TokenStream::from(output)
}
```

### 6.2 使用cargo-expand

```bash
# 安装cargo-expand
cargo install cargo-expand

# 查看宏展开结果
cargo expand --bin my_binary
```

### 6.3 使用trybuild测试

```rust
// tests/ui/compile-fail.rs
use trybuild::TestCases;

#[test]
fn ui() {
    let t = TestCases::new();
    t.compile_fail("tests/ui/*.rs");
}
```

---

## 7. 性能考虑

### 7.1 编译时间

过程宏会增加编译时间：

```rust
// ❌ 低效：每次都重新解析
#[proc_macro_derive(Inefficient)]
pub fn inefficient(input: TokenStream) -> TokenStream {
    let input_str = input.to_string();
    let parsed = syn::parse_str::<DeriveInput>(&input_str).unwrap();
    // 处理...
}

// ✅ 高效：直接解析TokenStream
#[proc_macro_derive(Efficient)]
pub fn efficient(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    // 处理...
}
```

### 7.2 缓存优化

```rust
use std::collections::HashMap;
use std::sync::Mutex;

lazy_static::lazy_static! {
    static ref CACHE: Mutex<HashMap<String, String>> = Mutex::new(HashMap::new());
}

#[proc_macro_derive(CachedMacro)]
pub fn cached_macro(input: TokenStream) -> TokenStream {
    let input_str = input.to_string();
    
    // 检查缓存
    if let Ok(mut cache) = CACHE.lock() {
        if let Some(cached) = cache.get(&input_str) {
            return cached.parse().unwrap();
        }
    }
    
    // 处理并缓存结果
    let result = process_input(input);
    
    if let Ok(mut cache) = CACHE.lock() {
        cache.insert(input_str, result.to_string());
    }
    
    result
}
```

---

## 8. 最佳实践

### 8.1 错误处理

```rust
use syn::{Error, Result};

fn process_struct(input: &DeriveInput) -> Result<TokenStream> {
    // 验证输入
    if !input.generics.params.is_empty() {
        return Err(Error::new_spanned(
            &input.generics,
            "不支持泛型参数"
        ));
    }
    
    // 处理逻辑
    Ok(quote! {
        // 生成的代码
    })
}

#[proc_macro_derive(MyMacro)]
pub fn my_macro(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    match process_struct(&input) {
        Ok(output) => TokenStream::from(output),
        Err(err) => err.to_compile_error().into(),
    }
}
```

### 8.2 文档和测试

```rust
/// 自动生成Builder模式的派生宏
///
/// # 示例
///
/// ```rust
/// use my_crate::Builder;
///
/// #[derive(Builder)]
/// struct Config {
///     host: String,
///     port: u16,
/// }
///
/// let config = Config::builder()
///     .host("localhost".to_string())
///     .port(8080)
///     .build();
/// ```
#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    // 实现...
}
```

### 8.3 版本兼容性

```rust
// 检查syn版本
const MIN_SYN_VERSION: &str = "2.0";

#[proc_macro_derive(VersionAware)]
pub fn version_aware(input: TokenStream) -> TokenStream {
    // 根据syn版本调整行为
    #[cfg(feature = "syn-2")]
    {
        // syn 2.x 的实现
    }
    
    #[cfg(not(feature = "syn-2"))]
    {
        // 旧版本的实现
    }
}
```

---

## 9. 常见问题

### 9.1 编译错误

**问题**: `proc_macro crate not found`

**解决方案**:

```toml
# Cargo.toml
[lib]
proc-macro = true  # 必须设置
```

**问题**: `syn::parse_str` 失败

**解决方案**:

```rust
// 使用parse_macro_input而不是parse_str
let input = parse_macro_input!(input as DeriveInput);
```

### 9.2 运行时错误

**问题**: 宏生成的代码有语法错误

**解决方案**:

```rust
// 使用quote!确保语法正确
let expanded = quote! {
    impl MyTrait for #name {
        fn method(&self) -> String {
            format!("Hello from {}", stringify!(#name))
        }
    }
};
```

### 9.3 调试困难

**问题**: 不知道宏生成了什么代码

**解决方案**:

```rust
// 使用cargo-expand查看展开结果
cargo expand --bin my_binary

// 或者在宏中使用eprintln!
eprintln!("生成的代码: {}", quote! { /* 代码 */ });
```

---

## 10. 实践练习

### 练习1: 简单属性宏

实现一个`#[count_calls]`属性宏，统计函数调用次数：

```rust
#[count_calls]
fn my_function() {
    println!("Hello!");
}

// 期望输出:
// 调用次数: 1
// Hello!
// 调用次数: 2
// Hello!
```

### 练习2: 派生宏

实现一个`#[Default]`派生宏，为结构体生成默认值：

```rust
#[derive(Default)]
struct Point {
    x: i32,
    y: i32,
}

let point = Point::default(); // Point { x: 0, y: 0 }
```

### 练习3: 函数式宏

实现一个`measure_time!`宏，测量代码块执行时间：

```rust
let result = measure_time!({
    std::thread::sleep(std::time::Duration::from_millis(100));
    42
});
// 输出: 执行时间: 100ms
```

---

## 📚 总结

### 关键概念

1. **TokenStream** - 过程宏的输入输出
2. **AST** - 抽象语法树表示
3. **编译时执行** - 在编译阶段运行代码
4. **三种类型** - 派生、属性、函数式宏

### 核心技能

- ✅ 理解TokenStream操作
- ✅ 使用syn解析AST
- ✅ 使用quote生成代码
- ✅ 处理编译时错误
- ✅ 调试过程宏

### 下一步

- 📖 学习 [派生宏教程](./02_derive_macros.md)
- 📖 学习 [属性宏教程](./03_attribute_macros.md)
- 📖 学习 [函数式宏教程](./04_function_macros.md)
- 📖 学习 [TokenStream详解](./05_token_streams.md)

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT
