# TokenStream深度解析

> **文档定位**: 深入理解TokenStream和token处理  
> **难度级别**: ⭐⭐⭐⭐ 专家  
> **预计时间**: 2.5小时  
> **最后更新**: 2025-10-20

---


## 📊 目录

- [📋 学习目标](#学习目标)
- [1. TokenStream概述](#1-tokenstream概述)
  - [1.1 什么是Token Stream](#11-什么是token-stream)
  - [1.2 Token类型](#12-token类型)
- [2. proc_macro vs proc_macro2](#2-proc_macro-vs-proc_macro2)
  - [2.1 两个crate](#21-两个crate)
  - [2.2 转换](#22-转换)
  - [2.3 为什么需要proc_macro2](#23-为什么需要proc_macro2)
- [3. 手动操作Token](#3-手动操作token)
  - [3.1 创建Token](#31-创建token)
  - [3.2 创建Group](#32-创建group)
  - [3.3 组合Token](#33-组合token)
- [4. 解析TokenStream](#4-解析tokenstream)
  - [4.1 迭代Token](#41-迭代token)
  - [4.2 Peekable迭代](#42-peekable迭代)
  - [4.3 使用syn::parse](#43-使用synparse)
- [5. Span和位置信息](#5-span和位置信息)
  - [5.1 什么是Span](#51-什么是span)
  - [5.2 错误报告](#52-错误报告)
  - [5.3 Span操作](#53-span操作)
- [6. 高级Token操作](#6-高级token操作)
  - [6.1 TokenTree转换](#61-tokentree转换)
  - [6.2 修改TokenStream](#62-修改tokenstream)
  - [6.3 过滤Token](#63-过滤token)
- [7. 性能优化](#7-性能优化)
  - [7.1 避免不必要的克隆](#71-避免不必要的克隆)
  - [7.2 使用引用](#72-使用引用)
  - [7.3 延迟求值](#73-延迟求值)
- [8. 调试技巧](#8-调试技巧)
  - [8.1 打印TokenStream](#81-打印tokenstream)
  - [8.2 使用cargo-expand](#82-使用cargo-expand)
  - [8.3 断点调试](#83-断点调试)
- [9. 实战案例](#9-实战案例)
  - [9.1 自定义序列化](#91-自定义序列化)
  - [9.2 条件编译生成](#92-条件编译生成)
- [10. 最佳实践](#10-最佳实践)
  - [10.1 Token处理原则](#101-token处理原则)
  - [10.2 代码组织](#102-代码组织)
  - [10.3 测试策略](#103-测试策略)
- [📚 总结](#总结)
  - [关键概念](#关键概念)
  - [核心技能](#核心技能)
  - [下一步](#下一步)


## 📋 学习目标

完成本章后，你将能够：

- ✅ 理解TokenStream的内部结构
- ✅ 手动操作Token
- ✅ 实现复杂的token解析
- ✅ 优化宏性能
- ✅ 调试token流

---

## 1. TokenStream概述

### 1.1 什么是Token Stream

**TokenStream** 是token的序列，代表Rust代码的词法结构。

```rust
// 代码
fn hello() { println!("Hello"); }

// TokenStream (简化)
[
    Ident("fn"),
    Ident("hello"),
    Group(Parenthesis, []),
    Group(Brace, [
        Ident("println"),
        Punct('!'),
        Group(Parenthesis, [Literal("Hello")]),
        Punct(';'),
    ]),
]
```

### 1.2 Token类型

```rust
use proc_macro2::{TokenTree, Ident, Literal, Punct, Group, Delimiter};

match token_tree {
    TokenTree::Ident(ident) => {
        // 标识符: fn, my_var, MyStruct
    }
    TokenTree::Literal(lit) => {
        // 字面量: 42, "hello", 3.14
    }
    TokenTree::Punct(punct) => {
        // 标点: +, -, =, ;, ::
    }
    TokenTree::Group(group) => {
        // 分组: (), {}, []
    }
}
```

---

## 2. proc_macro vs proc_macro2

### 2.1 两个crate

```rust
// proc_macro - 编译器提供
use proc_macro::TokenStream;

// proc_macro2 - 独立库
use proc_macro2::TokenStream as TokenStream2;
```

### 2.2 转换

```rust
// proc_macro -> proc_macro2
let ts2: TokenStream2 = ts.into();

// proc_macro2 -> proc_macro
let ts: TokenStream = ts2.into();
```

### 2.3 为什么需要proc_macro2

| 特性 | proc_macro | proc_macro2 |
|------|------------|-------------|
| **单元测试** | ❌ 不支持 | ✅ 支持 |
| **独立使用** | ❌ 只在过程宏 | ✅ 任何地方 |
| **功能** | 基础 | 完整 |

---

## 3. 手动操作Token

### 3.1 创建Token

```rust
use proc_macro2::{Span, Ident, Literal, Punct, Spacing};

// 标识符
let ident = Ident::new("my_function", Span::call_site());

// 字面量
let num = Literal::i32_unsuffixed(42);
let string = Literal::string("Hello");
let float = Literal::f64_unsuffixed(3.14);

// 标点
let plus = Punct::new('+', Spacing::Alone);
let colon = Punct::new(':', Spacing::Joint); // ::中的第一个:
```

### 3.2 创建Group

```rust
use proc_macro2::{Group, Delimiter, TokenStream};

// ()
let paren_group = Group::new(
    Delimiter::Parenthesis,
    TokenStream::new()
);

// {}
let brace_group = Group::new(
    Delimiter::Brace,
    quote! { println!("Hello"); }
);

// []
let bracket_group = Group::new(
    Delimiter::Bracket,
    quote! { 1, 2, 3 }
);
```

### 3.3 组合Token

```rust
use quote::quote;

let name = Ident::new("my_fn", Span::call_site());
let value = Literal::i32_unsuffixed(42);

let tokens = quote! {
    fn #name() -> i32 {
        #value
    }
};
```

---

## 4. 解析TokenStream

### 4.1 迭代Token

```rust
use proc_macro2::TokenStream;

fn process_tokens(input: TokenStream) {
    for token in input {
        match token {
            TokenTree::Ident(ident) => {
                println!("标识符: {}", ident);
            }
            TokenTree::Literal(lit) => {
                println!("字面量: {}", lit);
            }
            TokenTree::Punct(punct) => {
                println!("标点: {}", punct.as_char());
            }
            TokenTree::Group(group) => {
                println!("分组: {:?}", group.delimiter());
                process_tokens(group.stream());
            }
        }
    }
}
```

### 4.2 Peekable迭代

```rust
use proc_macro2::token_stream::IntoIter;

fn parse_custom(input: TokenStream) -> syn::Result<MyStruct> {
    let mut iter = input.into_iter().peekable();
    
    // 查看下一个token
    if let Some(TokenTree::Ident(ident)) = iter.peek() {
        if ident == "struct" {
            iter.next(); // 消费token
            // 继续解析...
        }
    }
    
    Ok(MyStruct {})
}
```

### 4.3 使用syn::parse

```rust
use syn::{parse::Parse, parse::ParseStream};

impl Parse for MyStruct {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        // 消费标识符
        let name: Ident = input.parse()?;
        
        // 消费标点
        input.parse::<Token![:]>()?;
        
        // 消费字面量
        let value: LitInt = input.parse()?;
        
        Ok(MyStruct { name, value })
    }
}
```

---

## 5. Span和位置信息

### 5.1 什么是Span

**Span** 代表token在源代码中的位置。

```rust
use proc_macro2::Span;

// 宏调用位置
let call_site = Span::call_site();

// 混合span
let mixed = Span::mixed_site();

// 自定义位置
let ident = Ident::new("my_var", call_site);
```

### 5.2 错误报告

```rust
use syn::Error;

fn validate_token(ident: &Ident) -> syn::Result<()> {
    if ident.to_string().starts_with("__") {
        return Err(Error::new(
            ident.span(),
            "标识符不应以双下划线开头"
        ));
    }
    Ok(())
}
```

### 5.3 Span操作

```rust
// 获取span信息
let span = ident.span();
let start = span.start();
let end = span.end();

// 合并span
let combined = span1.join(span2).unwrap_or(span1);

// 设置span
let new_ident = Ident::new("name", custom_span);
```

---

## 6. 高级Token操作

### 6.1 TokenTree转换

```rust
fn ident_to_string(tree: TokenTree) -> Option<String> {
    match tree {
        TokenTree::Ident(ident) => Some(ident.to_string()),
        _ => None,
    }
}

fn literal_to_int(tree: TokenTree) -> Option<i64> {
    match tree {
        TokenTree::Literal(lit) => {
            lit.to_string().parse().ok()
        }
        _ => None,
    }
}
```

### 6.2 修改TokenStream

```rust
fn rename_idents(input: TokenStream, old: &str, new: &str) -> TokenStream {
    input.into_iter().map(|tt| match tt {
        TokenTree::Ident(ident) if ident == old => {
            TokenTree::Ident(Ident::new(new, ident.span()))
        }
        TokenTree::Group(group) => {
            let new_stream = rename_idents(group.stream(), old, new);
            TokenTree::Group(Group::new(group.delimiter(), new_stream))
        }
        other => other,
    }).collect()
}
```

### 6.3 过滤Token

```rust
fn remove_comments(input: TokenStream) -> TokenStream {
    input.into_iter()
        .filter(|tt| !is_comment(tt))
        .collect()
}

fn is_comment(tt: &TokenTree) -> bool {
    match tt {
        TokenTree::Punct(p) if p.as_char() == '/' => {
            // 检查是否是注释开始
            true
        }
        _ => false,
    }
}
```

---

## 7. 性能优化

### 7.1 避免不必要的克隆

```rust
// ❌ 低效
fn bad_process(input: TokenStream) -> TokenStream {
    let cloned = input.clone(); // 不必要的克隆
    process(cloned)
}

// ✅ 高效
fn good_process(input: TokenStream) -> TokenStream {
    process(input) // 直接使用
}
```

### 7.2 使用引用

```rust
// ❌ 低效
fn process_each(tokens: Vec<TokenTree>) {
    for token in tokens { // 移动所有token
        handle(token);
    }
}

// ✅ 高效
fn process_each(tokens: &[TokenTree]) {
    for token in tokens { // 只借用
        handle(token);
    }
}
```

### 7.3 延迟求值

```rust
fn lazy_expand(input: TokenStream) -> TokenStream {
    // 只在需要时展开
    if should_expand(&input) {
        expand(input)
    } else {
        input
    }
}
```

---

## 8. 调试技巧

### 8.1 打印TokenStream

```rust
#[proc_macro]
pub fn debug_tokens(input: TokenStream) -> TokenStream {
    eprintln!("Input tokens:");
    eprintln!("{}", input);
    eprintln!("Tree structure:");
    debug_print_tree(&input.into(), 0);
    input
}

fn debug_print_tree(stream: &TokenStream2, indent: usize) {
    for tt in stream.clone() {
        let prefix = "  ".repeat(indent);
        match tt {
            TokenTree::Group(g) => {
                eprintln!("{}Group {:?}", prefix, g.delimiter());
                debug_print_tree(&g.stream(), indent + 1);
            }
            TokenTree::Ident(i) => eprintln!("{}Ident: {}", prefix, i),
            TokenTree::Punct(p) => eprintln!("{}Punct: {}", prefix, p.as_char()),
            TokenTree::Literal(l) => eprintln!("{}Literal: {}", prefix, l),
        }
    }
}
```

### 8.2 使用cargo-expand

```bash
# 查看完整展开
cargo expand

# 查看特定模块
cargo expand module_name

# 查看特定函数
cargo expand::function_name
```

### 8.3 断点调试

```rust
#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    // 在这里设置断点
    let parsed = syn::parse_macro_input!(input as DeriveInput);
    
    // 检查parsed的内容
    dbg!(&parsed);
    
    // 生成输出
    let output = quote! { /* ... */ };
    
    // 检查输出
    dbg!(output.to_string());
    
    output.into()
}
```

---

## 9. 实战案例

### 9.1 自定义序列化

```rust
#[proc_macro]
pub fn custom_serialize(input: TokenStream) -> TokenStream {
    let input: TokenStream2 = input.into();
    
    let mut fields = Vec::new();
    let mut iter = input.into_iter();
    
    while let Some(tt) = iter.next() {
        if let TokenTree::Ident(ident) = tt {
            // 提取字段名
            fields.push(ident);
            
            // 跳过类型信息
            iter.next(); // :
            iter.next(); // 类型
            iter.next(); // ,
        }
    }
    
    let ser_code = fields.iter().map(|f| {
        quote! {
            output.push(format!("{}={}", stringify!(#f), self.#f));
        }
    });
    
    quote! {
        {
            let mut output = Vec::new();
            #(#ser_code)*
            output.join("&")
        }
    }.into()
}
```

### 9.2 条件编译生成

```rust
#[proc_macro]
pub fn conditional_code(input: TokenStream) -> TokenStream {
    let input: TokenStream2 = input.into();
    
    // 检测debug模式
    #[cfg(debug_assertions)]
    let expanded = quote! {
        {
            println!("[DEBUG] Executing code");
            #input
        }
    };
    
    #[cfg(not(debug_assertions))]
    let expanded = quote! {
        #input
    };
    
    expanded.into()
}
```

---

## 10. 最佳实践

### 10.1 Token处理原则

1. **最小化克隆** - 使用引用
2. **保留Span** - 保持错误位置准确
3. **验证输入** - 提前检查格式
4. **友好错误** - 清晰的错误消息
5. **性能优化** - 避免重复解析

### 10.2 代码组织

```rust
// 分离解析和生成
fn parse_input(input: TokenStream) -> syn::Result<MyStruct> {
    // 解析逻辑
}

fn generate_output(data: &MyStruct) -> TokenStream2 {
    // 生成逻辑
}

#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    let data = match parse_input(input) {
        Ok(d) => d,
        Err(e) => return e.to_compile_error().into(),
    };
    
    generate_output(&data).into()
}
```

### 10.3 测试策略

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use quote::quote;
    
    #[test]
    fn test_token_parsing() {
        let input = quote! {
            fn test() {}
        };
        
        let result = parse_input(input.into());
        assert!(result.is_ok());
    }
    
    #[test]
    fn test_token_generation() {
        let data = MyStruct { /* ... */ };
        let output = generate_output(&data);
        
        assert!(output.to_string().contains("impl"));
    }
}
```

---

## 📚 总结

### 关键概念

1. **TokenStream** - Token序列
2. **TokenTree** - 4种Token类型
3. **Span** - 位置信息
4. **proc_macro2** - 可测试版本
5. **优化** - 性能考虑

### 核心技能

- ✅ 理解Token结构
- ✅ 手动操作Token
- ✅ 解析复杂输入
- ✅ 保留位置信息
- ✅ 调试Token流

### 下一步

- 📖 回顾 [过程宏基础](./01_proc_macro_basics.md)
- 📖 实践 复杂宏项目
- 📖 研究 标准库实现

---

**作者**: Rust学习社区  
**最后更新**: 2025-10-20  
**许可**: MIT
