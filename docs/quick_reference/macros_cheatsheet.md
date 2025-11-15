# 🔧 Rust 宏系统速查卡

> **快速参考** | [完整文档](../../crates/c11_macro_system/docs/) | [代码示例](../../crates/c11_macro_system/examples/)
> **最后更新**: 2025-11-15 | **Rust 版本**: 1.91.1+ | **Edition**: 2024

---

## 🎯 核心概念

### 声明宏 (macro_rules!)

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
```

### 过程宏

```rust
// 派生宏
#[derive(Debug, Clone)]
struct MyStruct;

// 属性宏
#[route(GET, "/")]
fn handler() {}

// 函数式宏
println!("Hello, {}!", name);
```

---

## 📐 声明宏模式

### 基本模式

```rust
macro_rules! my_macro {
    // 匹配单个表达式
    ($x:expr) => { $x };

    // 匹配多个表达式
    ($($x:expr),*) => {
        vec![$($x),*]
    };

    // 匹配标识符
    ($name:ident) => {
        let $name = 42;
    };
}
```

### 片段类型

```rust
// expr: 表达式
// ident: 标识符
// ty: 类型
// path: 路径
// pat: 模式
// stmt: 语句
// block: 代码块
// item: 项
// meta: 元数据
// tt: 标记树
```

---

## 🔧 过程宏实现

### 派生宏

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let expanded = quote! {
        impl #name {
            fn hello() {
                println!("Hello from {}", stringify!(#name));
            }
        }
    };

    TokenStream::from(expanded)
}
```

### 属性宏

```rust
#[proc_macro_attribute]
pub fn my_attr(_attr: TokenStream, item: TokenStream) -> TokenStream {
    // 处理属性宏
    item
}
```

---

## 🎯 常见模式

### 模式 1: 重复

```rust
macro_rules! repeat {
    ($($item:expr),+ $(,)?) => {
        {
            let mut v = Vec::new();
            $(
                v.push($item);
            )+
            v
        }
    };
}
```

### 模式 2: 条件编译

```rust
#[cfg(target_os = "windows")]
macro_rules! platform_specific {
    () => { "Windows" };
}

#[cfg(target_os = "linux")]
macro_rules! platform_specific {
    () => { "Linux" };
}
```

---

## 🔗 相关资源

- [宏系统完整文档](../../crates/c11_macro_system/docs/)
- [Rust 官方文档 - 宏](https://doc.rust-lang.org/book/ch19-06-macros.html)

---

---

## 🆕 Rust 1.91.1 宏系统改进

### 编译优化

**改进**: 宏展开性能优化，更好的错误诊断

```rust
// Rust 1.91.1 优化后的宏展开
macro_rules! my_macro {
    ($x:expr) => {
        // ✅ 更快的宏展开
        // ✅ 更好的错误定位
        println!("{}", $x);
    };
}
```

**影响**:

- 宏展开性能提升
- 更好的错误诊断
- 编译时间优化

---

**最后更新**: 2025-11-15
**Rust 版本**: 1.91.1+ (Edition 2024)
