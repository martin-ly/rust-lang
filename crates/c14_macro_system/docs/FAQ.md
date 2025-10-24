# ❓ C14宏系统 - 常见问题

> **文档定位**: 宏学习中的常见问题和解答  
> **最后更新**: 2025-10-20

---


## 📊 目录

- [基础问题](#基础问题)
  - [1. 宏和函数有什么区别？](#1-宏和函数有什么区别)
  - [2. 什么时候应该使用宏？](#2-什么时候应该使用宏)
  - [3. `macro_rules!`中的`$`符号是什么意思？](#3-macro_rules中的符号是什么意思)
  - [4. 宏卫生(Hygiene)是什么？](#4-宏卫生hygiene是什么)
- [声明宏问题](#声明宏问题)
  - [5. 如何在宏中接受可变数量的参数？](#5-如何在宏中接受可变数量的参数)
  - [6. 如何实现递归宏？](#6-如何实现递归宏)
  - [7. 宏中的`tt`、`expr`、`ident`等是什么？](#7-宏中的ttexprident等是什么)
  - [8. 如何导出宏让其他crate使用？](#8-如何导出宏让其他crate使用)
- [过程宏问题](#过程宏问题)
  - [9. 派生宏、属性宏、函数式宏有什么区别？](#9-派生宏属性宏函数式宏有什么区别)
  - [10. 如何创建过程宏crate？](#10-如何创建过程宏crate)
  - [11. `syn`和`quote`是什么？](#11-syn和quote是什么)
- [调试问题](#调试问题)
  - [12. 如何查看宏展开后的代码？](#12-如何查看宏展开后的代码)
  - [13. 宏编译错误如何调试？](#13-宏编译错误如何调试)
  - [14. 过程宏如何调试？](#14-过程宏如何调试)
- [高级问题](#高级问题)
  - [15. 如何在宏中实现条件编译？](#15-如何在宏中实现条件编译)
  - [16. 宏可以访问环境变量吗？](#16-宏可以访问环境变量吗)
  - [17. 如何测试宏？](#17-如何测试宏)
  - [18. 宏有性能影响吗？](#18-宏有性能影响吗)
  - [19. 宏能生成宏吗？](#19-宏能生成宏吗)
  - [20. 如何构建DSL？](#20-如何构建dsl)
- [获取帮助](#获取帮助)
  - [找不到答案？](#找不到答案)


## 基础问题

### 1. 宏和函数有什么区别？

**主要区别**:

| 特性 | 宏 | 函数 |
|------|-----|------|
| 执行时机 | 编译期展开 | 运行时调用 |
| 参数类型 | 可接受任意语法 | 必须类型匹配 |
| 返回值 | 展开为代码 | 返回具体值 |
| 性能 | 零开销（内联） | 可能有调用开销 |
| 调试难度 | 较难 | 较易 |

**示例对比**:

```rust
// 函数 - 运行时
fn double(x: i32) -> i32 { x * 2 }

// 宏 - 编译期
macro_rules! double {
    ($x:expr) => { $x * 2 };
}
```

---

### 2. 什么时候应该使用宏？

**适合使用宏的场景**:

- ✅ 需要生成重复的样板代码
- ✅ 需要元编程能力
- ✅ 需要自定义语法
- ✅ 需要编译期计算

**不适合使用宏的场景**:

- ❌ 简单的代码封装（用函数）
- ❌ 运行时逻辑（用函数）
- ❌ 需要经常调试的代码
- ❌ 类型系统可以解决的问题

---

### 3. `macro_rules!`中的`$`符号是什么意思？

`$`符号用于：

1. **变量绑定**: `$name:type`
2. **重复匹配**: `$(...)*`
3. **变量展开**: `$name`

**示例**:

```rust
macro_rules! example {
    ($x:expr) => {  // $x 是变量名，expr 是类型
        println!("{}", $x);  // $x 展开为实际表达式
    };
}
```

---

### 4. 宏卫生(Hygiene)是什么？

**宏卫生**确保宏内部的标识符不会与外部冲突。

**示例**:

```rust
macro_rules! define_x {
    () => {
        let x = 42;  // 这个x不会影响外部
    };
}

let x = 1;
define_x!();
println!("{}", x);  // 输出: 1，不是42
```

---

## 声明宏问题

### 5. 如何在宏中接受可变数量的参数？

使用重复语法 `$(...)*` 或 `$(...)+`:

```rust
macro_rules! print_all {
    ($($arg:expr),*) => {
        $(println!("{}", $arg);)*
    };
}

print_all!(1, 2, 3);  // 接受任意数量参数
```

---

### 6. 如何实现递归宏？

通过在宏内部调用自己：

```rust
macro_rules! count {
    () => { 0 };
    ($x:expr) => { 1 };
    ($x:expr, $($rest:expr),+) => {
        1 + count!($($rest),+)  // 递归调用
    };
}
```

---

### 7. 宏中的`tt`、`expr`、`ident`等是什么？

这些是**片段指定符**(Fragment Specifiers):

| 指定符 | 匹配内容 | 示例 |
|--------|---------|------|
| `expr` | 表达式 | `1 + 2` |
| `ident` | 标识符 | `foo` |
| `ty` | 类型 | `i32` |
| `pat` | 模式 | `Some(x)` |
| `stmt` | 语句 | `let x = 1;` |
| `tt` | Token树 | 任意token |
| `item` | 项 | `fn foo() {}` |
| `block` | 代码块 | `{ ... }` |

---

### 8. 如何导出宏让其他crate使用？

使用`#[macro_export]`:

```rust
#[macro_export]
macro_rules! my_macro {
    () => { ... };
}

// 其他crate中
use my_crate::my_macro;
```

---

## 过程宏问题

### 9. 派生宏、属性宏、函数式宏有什么区别？

| 类型 | 语法 | 用途 | 示例 |
|------|------|------|------|
| 派生宏 | `#[derive(Trait)]` | 自动实现trait | `#[derive(Debug)]` |
| 属性宏 | `#[attr]` | 修改项 | `#[route(GET)]` |
| 函数式宏 | `macro!()` | 函数式调用 | `sql!()` |

---

### 10. 如何创建过程宏crate？

```toml
# Cargo.toml
[lib]
proc-macro = true

[dependencies]
syn = "2.0"
quote = "1.0"
proc-macro2 = "1.0"
```

```rust
// lib.rs
use proc_macro::TokenStream;

#[proc_macro_derive(MyTrait)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    // 实现逻辑
}
```

---

### 11. `syn`和`quote`是什么？

- **syn**: 解析Rust语法为AST
- **quote**: 生成Rust代码

**示例**:

```rust
use syn::{parse_macro_input, DeriveInput};
use quote::quote;

#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let ast = parse_macro_input!(input as DeriveInput);
    let name = &ast.ident;
    
    let expanded = quote! {
        impl #name {
            fn builder() -> Builder { ... }
        }
    };
    
    TokenStream::from(expanded)
}
```

---

## 调试问题

### 12. 如何查看宏展开后的代码？

**方法1**: 使用`cargo-expand`

```bash
cargo install cargo-expand
cargo expand --example my_example
```

**方法2**: 使用`trace_macros`

```rust
#![feature(trace_macros)]
trace_macros!(true);
my_macro!();
trace_macros!(false);
```

---

### 13. 宏编译错误如何调试？

**技巧**:

1. 使用`cargo expand`查看展开
2. 简化宏测试用例
3. 添加`println!`或`compile_error!`
4. 使用IDE的宏展开功能

**示例**:

```rust
macro_rules! debug_macro {
    ($($arg:tt)*) => {
        compile_error!(stringify!($($arg)*));
    };
}
```

---

### 14. 过程宏如何调试？

```rust
// 使用eprintln!输出调试信息
#[proc_macro]
pub fn my_macro(input: TokenStream) -> TokenStream {
    eprintln!("Input: {}", input);  // 编译时打印
    // ...
}
```

---

## 高级问题

### 15. 如何在宏中实现条件编译？

```rust
macro_rules! platform_specific {
    () => {
        #[cfg(target_os = "windows")]
        fn impl_windows() { }
        
        #[cfg(target_os = "linux")]
        fn impl_linux() { }
    };
}
```

---

### 16. 宏可以访问环境变量吗？

在`macro_rules!`中不能，但在过程宏中可以：

```rust
#[proc_macro]
pub fn env_macro(_input: TokenStream) -> TokenStream {
    let value = std::env::var("MY_VAR").unwrap();
    // 使用环境变量生成代码
}
```

---

### 17. 如何测试宏？

**声明宏测试**:

```rust
#[test]
fn test_my_macro() {
    let result = my_macro!(1 + 1);
    assert_eq!(result, 2);
}
```

**过程宏测试** (使用trybuild):

```rust
#[test]
fn test_proc_macro() {
    let t = trybuild::TestCases::new();
    t.pass("tests/pass/*.rs");
    t.compile_fail("tests/fail/*.rs");
}
```

---

### 18. 宏有性能影响吗？

**编译期**:

- ❌ 增加编译时间
- ❌ 复杂宏会显著增加

**运行时**:

- ✅ 零开销（宏展开为代码）
- ✅ 可能比函数更快（内联）

---

### 19. 宏能生成宏吗？

可以！

```rust
macro_rules! make_macro {
    ($name:ident) => {
        macro_rules! $name {
            () => { println!("Hello"); };
        }
    };
}

make_macro!(greet);
greet!();  // 输出: Hello
```

---

### 20. 如何构建DSL？

**步骤**:

1. 设计DSL语法
2. 使用宏解析语法
3. 生成对应代码

**示例**:

```rust
macro_rules! html {
    ($tag:ident { $($content:tt)* }) => {
        format!("<{}>{}</{}>", 
            stringify!($tag),
            html!($($content)*),
            stringify!($tag))
    };
    ($text:expr) => { $text };
}

// 使用
let page = html! {
    html {
        body {
            "Hello World"
        }
    }
};
```

---

## 获取帮助

### 找不到答案？

1. 查看[术语表](./Glossary.md)
2. 阅读[官方文档](https://doc.rust-lang.org/reference/macros.html)
3. 查看[示例代码](../examples/)
4. 提交Issue

---

**最后更新**: 2025-10-20  
**维护者**: Rust学习社区

有新问题？欢迎提交！
