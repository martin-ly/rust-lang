# Rust 1.90 宏系统特性指南

> **文档定位**: Rust 1.90版本中宏系统的完整特性  
> **难度级别**: ⭐⭐⭐⭐ 专家  
> **适用版本**: Rust 1.90+  
> **最后更新**: 2025-10-20

---

## 📋 目录

- [1. Rust 1.90宏系统概述](#1-rust-190宏系统概述)
- [2. 声明宏 (macro_rules!) 1.90特性](#2-声明宏-macro_rules-190特性)
- [3. 过程宏 1.90特性](#3-过程宏-190特性)
- [4. 宏卫生性增强](#4-宏卫生性增强)
- [5. TokenStream改进](#5-tokenstream改进)
- [6. 诊断与错误报告](#6-诊断与错误报告)
- [7. 性能优化](#7-性能优化)
- [8. 新的宏模式](#8-新的宏模式)
- [9. 工具链支持](#9-工具链支持)
- [10. 最佳实践](#10-最佳实践)

---

## 1. Rust 1.90宏系统概述

### 1.1 宏系统架构

Rust 1.90的宏系统包含三个层次：

```text
┌─────────────────────────────────────┐
│     Declarative Macros              │
│     (macro_rules!)                  │
│     - Pattern Matching              │
│     - Token Tree Munching           │
├─────────────────────────────────────┤
│     Procedural Macros               │
│     - Derive Macros                 │
│     - Attribute Macros              │
│     - Function-like Macros          │
├─────────────────────────────────────┤
│     Compiler Integration            │
│     - syn/quote ecosystem           │
│     - proc-macro2                   │
│     - TokenStream processing        │
└─────────────────────────────────────┘
```

### 1.2 版本特性总览

| 特性类别 | Rust 1.90支持 | 说明 |
|----------|--------------|------|
| 声明宏 2.0 | ⚠️ 部分 | 实验性特性 |
| 过程宏稳定化 | ✅ 完全 | 所有类型均稳定 |
| 宏诊断 | ✅ 增强 | 更好的错误消息 |
| TokenStream | ✅ 优化 | 性能改进 |
| syn 2.0 | ✅ 支持 | 生态系统更新 |

---

## 2. 声明宏 (macro_rules!) 1.90特性

### 2.1 稳定的片段说明符

Rust 1.90支持13种片段说明符：

```rust
macro_rules! demo_fragments {
    // 1. item - 项（函数、结构体等）
    ($i:item) => { $i };
    
    // 2. block - 块表达式
    ($b:block) => { $b };
    
    // 3. stmt - 语句
    ($s:stmt) => { $s };
    
    // 4. expr - 表达式
    ($e:expr) => { $e };
    
    // 5. pat - 模式
    ($p:pat) => { $p };
    
    // 6. ty - 类型
    ($t:ty) => { $t };
    
    // 7. ident - 标识符
    ($id:ident) => { $id };
    
    // 8. path - 路径
    ($path:path) => { $path };
    
    // 9. tt - Token Tree
    ($tt:tt) => { $tt };
    
    // 10. meta - 元信息
    ($m:meta) => { $m };
    
    // 11. lifetime - 生命周期
    ($l:lifetime) => { $l };
    
    // 12. vis - 可见性
    ($v:vis) => { $v };
    
    // 13. literal - 字面量 (Rust 1.32+)
    ($lit:literal) => { $lit };
}
```

### 2.2 重复模式增强

```rust
// Rust 1.90支持更复杂的重复模式

macro_rules! multi_repeat {
    // 嵌套重复
    ($($($x:expr),+);+) => {
        vec![$(vec![$($x),+]),+]
    };
    
    // 可选重复
    ($($x:expr),* $(,)?) => {
        vec![$($x),*]
    };
}

// 使用
let nested = multi_repeat!(1, 2; 3, 4; 5);
let trailing = multi_repeat!(1, 2, 3,); // 支持尾随逗号
```

### 2.3 宏导出改进

```rust
// Rust 1.90支持更精确的导出控制

#[macro_export]
macro_rules! exported_macro {
    () => { println!("Exported!"); };
}

// 文档化导出
/// 这个宏在所有crate中可用
#[macro_export]
#[doc(alias = "log")]
macro_rules! debug_log {
    ($($arg:tt)*) => {
        #[cfg(debug_assertions)]
        eprintln!("[DEBUG] {}", format!($($arg)*));
    };
}
```

---

## 3. 过程宏 1.90特性

### 3.1 派生宏稳定化

```rust
// Rust 1.90中所有派生宏特性均稳定

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyDerive, attributes(my_attr))]
pub fn derive_my_trait(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    
    // 使用 syn 2.0 的完整特性
    let expanded = quote! {
        impl MyTrait for #name {
            fn method(&self) -> String {
                format!("MyTrait for {}", stringify!(#name))
            }
        }
    };
    
    TokenStream::from(expanded)
}
```

### 3.2 属性宏增强

```rust
// Rust 1.90支持在更多位置使用属性宏

#[proc_macro_attribute]
pub fn my_attribute(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let fn_name = &input.sig.ident;
    
    // 改进的错误报告
    if input.sig.inputs.is_empty() {
        return syn::Error::new_spanned(
            &input.sig,
            "This attribute requires at least one parameter"
        ).to_compile_error().into();
    }
    
    // 生成代码...
    TokenStream::from(quote! {
        #input
    })
}
```

### 3.3 函数式宏改进

```rust
#[proc_macro]
pub fn my_function_like(input: TokenStream) -> TokenStream {
    // Rust 1.90支持更好的span信息
    let input_span = proc_macro2::Span::call_site();
    
    // 使用 syn 2.0 的解析器
    let input_str = input.to_string();
    
    // 生成带有准确span的代码
    let output = quote_spanned! {input_span=>
        println!("Generated code with proper span");
    };
    
    TokenStream::from(output)
}
```

---

## 4. 宏卫生性增强

### 4.1 改进的作用域解析

```rust
// Rust 1.90中宏卫生性更加严格

macro_rules! hygienic_macro {
    () => {
        // 使用 $crate 确保正确的路径解析
        $crate::internal_function();
        
        // 局部变量不会泄露
        let temp = 42;
        temp
    };
}

// 在其他模块使用时，$crate 会正确解析
```

### 4.2 Span信息保留

```rust
use proc_macro2::{Span, TokenStream};
use quote::quote;

// Rust 1.90更好地保留了span信息
fn generate_with_span(original: &syn::Ident) -> TokenStream {
    let span = original.span();
    
    // 生成的代码保留原始位置信息
    quote_spanned! {span=>
        fn generated_function() {
            println!("Generated at {:?}", #original);
        }
    }
}
```

---

## 5. TokenStream改进

### 5.1 性能优化

```rust
// Rust 1.90中TokenStream操作更高效

use proc_macro2::TokenStream;

// ✅ 高效的TokenStream构建
fn efficient_build() -> TokenStream {
    let mut tokens = TokenStream::new();
    tokens.extend(quote! { fn foo() {} });
    tokens.extend(quote! { fn bar() {} });
    tokens
}

// ❌ 低效的方式（避免）
fn inefficient_build() -> TokenStream {
    let mut result = quote! { fn foo() {} };
    result = quote! { #result fn bar() {} }; // 重复解析
    result
}
```

### 5.2 TokenTree操作

```rust
use proc_macro2::{TokenTree, TokenStream};

// Rust 1.90支持更灵活的token操作
fn process_tokens(input: TokenStream) -> TokenStream {
    input.into_iter()
        .filter_map(|tt| match tt {
            TokenTree::Ident(ident) if ident == "old" => {
                Some(TokenTree::Ident(
                    proc_macro2::Ident::new("new", ident.span())
                ))
            }
            other => Some(other),
        })
        .collect()
}
```

---

## 6. 诊断与错误报告

### 6.1 改进的错误消息

```rust
use syn::{Error, Result};

// Rust 1.90支持更详细的错误报告
fn validate_input(input: &DeriveInput) -> Result<()> {
    // 多个错误合并
    let mut errors = Vec::new();
    
    if input.generics.params.is_empty() {
        errors.push(Error::new_spanned(
            &input.generics,
            "Expected at least one generic parameter"
        ));
    }
    
    for field in get_fields(input) {
        if field.ident.is_none() {
            errors.push(Error::new_spanned(
                field,
                "Unnamed fields are not supported"
            ));
        }
    }
    
    // 合并所有错误
    if !errors.is_empty() {
        let mut combined = errors.into_iter().next().unwrap();
        for error in errors.into_iter().skip(1) {
            combined.combine(error);
        }
        return Err(combined);
    }
    
    Ok(())
}
```

### 6.2 诊断属性

```rust
// Rust 1.90支持自定义诊断
#[proc_macro_attribute]
pub fn diagnose(attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    
    // 生成包含诊断信息的代码
    let expanded = quote! {
        #[allow(dead_code)]
        #[doc = "This function was generated by the diagnose macro"]
        #input
    };
    
    TokenStream::from(expanded)
}
```

---

## 7. 性能优化

### 7.1 编译时间优化

```rust
// Rust 1.90宏编译性能改进

// ✅ 推荐：最小化token操作
#[proc_macro_derive(Fast)]
pub fn derive_fast(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    
    // 只解析需要的部分
    let name = &input.ident;
    
    // 简单的代码生成
    TokenStream::from(quote! {
        impl Fast for #name {}
    })
}

// ❌ 避免：复杂的递归解析
#[proc_macro_derive(Slow)]
pub fn derive_slow(input: TokenStream) -> TokenStream {
    // 多次解析整个输入
    let parsed1 = syn::parse::<DeriveInput>(input.clone()).unwrap();
    let parsed2 = syn::parse::<DeriveInput>(input).unwrap();
    // ...
}
```

### 7.2 增量编译支持

```rust
// Rust 1.90改进了宏的增量编译

// 使用稳定的哈希
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

fn stable_hash(input: &TokenStream) -> u64 {
    let mut hasher = DefaultHasher::new();
    input.to_string().hash(&mut hasher);
    hasher.finish()
}
```

---

## 8. 新的宏模式

### 8.1 可变参数宏

```rust
// Rust 1.90支持更灵活的可变参数模式

macro_rules! variadic {
    // 至少一个参数
    ($first:expr $(, $rest:expr)*) => {
        {
            let mut result = vec![$first];
            $(result.push($rest);)*
            result
        }
    };
    
    // 零个或多个参数
    ($($arg:expr),*) => {
        vec![$($arg),*]
    };
}

// 使用
let v1 = variadic!(1, 2, 3);
let v2 = variadic!();
```

### 8.2 条件宏展开

```rust
// Rust 1.90支持更复杂的条件展开

macro_rules! conditional {
    (@internal debug $($arg:tt)*) => {
        #[cfg(debug_assertions)]
        {
            println!($($arg)*);
        }
    };
    
    (@internal release $($arg:tt)*) => {
        #[cfg(not(debug_assertions))]
        {
            // 优化版本
        }
    };
    
    (debug $($arg:tt)*) => {
        conditional!(@internal debug $($arg)*);
    };
    
    (release $($arg:tt)*) => {
        conditional!(@internal release $($arg)*);
    };
}
```

---

## 9. 工具链支持

### 9.1 cargo-expand

```bash
# Rust 1.90完全支持 cargo-expand

# 查看宏展开
cargo expand

# 查看特定模块的展开
cargo expand module_name

# 查看特定函数的展开
cargo expand::function_name

# 查看所有宏展开（包括标准库）
cargo expand --lib
```

### 9.2 rust-analyzer集成

```rust
// Rust 1.90中rust-analyzer对宏的支持更好

// 悬停提示会显示宏展开结果
macro_rules! hover_demo {
    () => {
        println!("This will be shown in hover tooltip");
    };
}

// 代码补全支持宏参数
macro_rules! completion_demo {
    ($ident:ident, $ty:ty) => {
        let $ident: $ty;  // 补全会建议类型
    };
}
```

### 9.3 调试支持

```rust
// Rust 1.90改进了宏调试

#[proc_macro]
pub fn debug_macro(input: TokenStream) -> TokenStream {
    // 使用 eprintln! 输出调试信息
    eprintln!("Macro input: {}", input);
    
    // 使用 dbg! 调试中间状态
    let parsed = dbg!(syn::parse::<MyStruct>(input).unwrap());
    
    // 输出会在 cargo build 时显示
    TokenStream::new()
}
```

---

## 10. 最佳实践

### 10.1 宏设计原则

```rust
// ✅ 好的宏设计

// 1. 清晰的命名
#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    // 名称明确表达意图
}

// 2. 友好的错误消息
fn validate(input: &DeriveInput) -> Result<()> {
    if !is_struct(input) {
        return Err(Error::new_spanned(
            input,
            "Builder can only be derived for structs.\n\
             Hint: Use a struct instead of an enum."
        ));
    }
    Ok(())
}

// 3. 文档齐全
/// Derives a builder pattern for the struct.
///
/// # Example
///
/// ```rust
/// #[derive(Builder)]
/// struct Config {
///     host: String,
///     port: u16,
/// }
/// ```
#[proc_macro_derive(Builder)]
pub fn derive_builder_documented(input: TokenStream) -> TokenStream {
    // ...
}
```

### 10.2 性能考虑

```rust
// ✅ 性能最佳实践

// 1. 避免不必要的克隆
fn process(input: &DeriveInput) -> TokenStream {
    let name = &input.ident;  // 借用而非克隆
    quote! { impl MyTrait for #name {} }.into()
}

// 2. 使用缓存
use once_cell::sync::Lazy;
use std::collections::HashMap;

static CACHE: Lazy<HashMap<String, TokenStream>> = Lazy::new(HashMap::new);

// 3. 最小化 TokenStream 操作
fn efficient_quote() -> TokenStream {
    quote! {
        fn f1() {}
        fn f2() {}
        fn f3() {}
    }.into()
}
```

### 10.3 测试策略

```rust
// Rust 1.90推荐的宏测试方法

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_macro_expansion() {
        let input = quote! {
            struct MyStruct {
                field: i32,
            }
        };
        
        let output = my_macro(input.into());
        let expected = quote! {
            impl MyTrait for MyStruct {}
        };
        
        assert_eq!(output.to_string(), expected.to_string());
    }
}

// 使用 trybuild 进行编译测试
#[test]
fn ui() {
    let t = trybuild::TestCases::new();
    t.pass("tests/01-parse.rs");
    t.compile_fail("tests/02-missing-attr.rs");
}
```

---

## 📚 相关资源

### 官方文档

- [The Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)
- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)
- [Proc Macro Workshop](https://github.com/dtolnay/proc-macro-workshop)

### 工具生态

- `syn` 2.0+ - AST解析
- `quote` 1.0+ - 代码生成
- `proc-macro2` 1.0+ - 测试支持
- `cargo-expand` - 宏展开查看
- `trybuild` - 编译测试

### 学习路径

1. **基础**: 掌握 `macro_rules!` 和基本模式
2. **进阶**: 学习派生宏和属性宏
3. **高级**: 掌握 TokenStream 和 syn/quote
4. **专家**: 构建复杂DSL和代码生成工具

---

**文档版本**: v1.0  
**适用版本**: Rust 1.90+  
**最后更新**: 2025-10-20  
**维护状态**: 活跃

---

## 返回导航

- [返回主索引](../00_MASTER_INDEX.md)
- [宏系统README](../../README.md)
- [理论基础](../01_theory/)
- [声明宏教程](../02_declarative/)
- [过程宏教程](../03_procedural/)
