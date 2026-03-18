# Rust 过程宏 (Procedural Macros)

> 🦀 深入理解 Rust 最强大的元编程工具——过程宏，掌握自定义 derive、attribute 和 function-like 宏的开发技巧。
>
> ⏱️ **预计学习时间**: 90-120 分钟 | 🎯 **难度**: 高级

---

## 🎯 学习目标

- 理解过程宏与声明宏的本质区别
- 掌握三种过程宏：derive、attribute、function-like
- 熟练使用 `syn` 和 `quote` crate
- 编写实用的 derive 和 attribute 宏
- 理解过程宏的编译时限制和最佳实践

---

## 📋 先决条件

1. **Rust 基础语法**：所有权、生命周期、trait、泛型
2. **宏基础**：了解 `macro_rules!` 的基本用法
3. **Cargo 工作区**：理解多 crate 项目的组织结构
4. **Rust 编译流程**：了解编译时与运行时的区别

---

## 🧠 核心概念

### 什么是过程宏？

过程宏是 Rust 在**编译时运行**的 Rust 函数，接收 Rust 代码作为输入，产生新的 Rust 代码作为输出：

```rust
// 声明宏 - 基于模式匹配
macro_rules! say_hello {
    () => { println!("Hello!"); };
}

// 过程宏 - 基于代码转换
#[derive(CustomDebug)]
struct Point { x: i32, y: i32 }
```

与声明宏相比，过程宏：

- **直接操作 Token**：接收 `TokenStream`，输出 `TokenStream`
- **编译时执行**：在编译阶段运行，不增加运行时开销
- **类型安全**：可以解析输入代码的语义结构

### 三种过程宏类型

| 类型 | 用途 | 示例 |
|------|------|------|
| **Derive** | 为结构体/枚举自动生成 trait 实现 | `#[derive(Debug)]` |
| **Attribute** | 修改被装饰的代码 | `#[route("/users")]` |
| **Function-like** | 类函数调用，任意表达式位置 | `sql!("SELECT ...")` |

### proc-macro crate 结构

```toml
# Cargo.toml
[package]
name = "my-derive"
version = "0.1.0"
edition = "2021"

[lib]
proc-macro = true

[dependencies]
syn = { version = "2.0", features = ["full"] }
quote = "1.0"
proc-macro2 = "1.0"
```

```rust
use proc_macro::TokenStream;

#[proc_macro_derive(MyDerive)]
pub fn my_derive(input: TokenStream) -> TokenStream {
    TokenStream::new()
}
```

### syn 和 quote 使用

**syn** 解析 Rust 代码，**quote** 生成代码：

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Data, Fields};

#[proc_macro_derive(CustomDebug)]
pub fn derive_debug(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            _ => panic!("Only named fields supported"),
        },
        _ => panic!("Only structs supported"),
    };

    let field_names: Vec<_> = fields.iter().map(|f| &f.ident).collect();

    let expanded = quote! {
        impl std::fmt::Debug for #name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                f.debug_struct(stringify!(#name))
                    #(.field(stringify!(#field_names), &self.#field_names))*
                    .finish()
            }
        }
    };
    TokenStream::from(expanded)
}
```

#### 常用 syn 类型

| 类型 | 用途 |
|------|------|
| `DeriveInput` | 解析 derive 宏的输入 |
| `Attribute` | 表示 `#[...]` 属性 |
| `Meta` | 属性的内部结构 |
| `Lit` | 字面值（字符串、数字等）|
| `Expr` | 表达式 |

#### quote! 宏技巧

```rust
use quote::{quote, format_ident};

let name = format_ident!("MyStruct");
let fields = vec!["x", "y"];

let output = quote! {
    struct #name {
        #(#fields: i32),*  // 重复模式
    }
};
```

### Derive Macro 实例：Builder 模式

```rust
use proc_macro::TokenStream;
use quote::{quote, format_ident};
use syn::{parse_macro_input, DeriveInput, Data, Fields, Field};

#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let builder_name = format_ident!("{}Builder", name);

    let fields = match &input.data {
        Data::Struct(data) => match &data.fields {
            Fields::Named(fields) => &fields.named,
            _ => panic!("Only named fields supported"),
        },
        _ => panic!("Only structs supported"),
    };

    let builder_fields = fields.iter().map(|f: &Field| {
        let name = &f.ident;
        let ty = &f.ty;
        quote! { #name: Option<#ty> }
    });

    let setters = fields.iter().map(|f: &Field| {
        let name = &f.ident;
        let ty = &f.ty;
        quote! {
            pub fn #name(mut self, value: #ty) -> Self {
                self.#name = Some(value);
                self
            }
        }
    });

    let build_fields = fields.iter().map(|f: &Field| {
        let name = &f.ident;
        let name_str = format!("{}", quote!(#name));
        quote! {
            #name: self.#name.ok_or(concat!(#name_str, " is required"))?
        }
    });

    let init_fields = fields.iter().map(|f: &Field| {
        let name = &f.ident;
        quote! { #name: None }
    });

    let expanded = quote! {
        pub struct #builder_name {
            #(#builder_fields,)*
        }
        impl #name {
            pub fn builder() -> #builder_name {
                #builder_name { #(#init_fields,)* }
            }
        }
        impl #builder_name {
            #(#setters)*
            pub fn build(self) -> Result<#name, &'static str> {
                Ok(#name { #(#build_fields,)* })
            }
        }
    };
    TokenStream::from(expanded)
}
```

使用示例：

```rust
use my_derive::Builder;

#[derive(Builder)]
struct User {
    name: String,
    age: u32,
}

fn main() {
    let user = User::builder()
        .name("Alice".to_string())
        .age(30)
        .build()
        .unwrap();
}
```

### Attribute Macro 实例

自动计时属性宏：

```rust
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

#[proc_macro_attribute]
pub fn timed(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    let vis = &input_fn.vis;
    let sig = &input_fn.sig;
    let block = &input_fn.block;
    let fn_name = &sig.ident;

    let expanded = quote! {
        #vis #sig {
            let __start = std::time::Instant::now();
            let __result = #block;
            let __elapsed = __start.elapsed();
            println!("{} took {:?}", stringify!(#fn_name), __elapsed);
            __result
        }
    };
    TokenStream::from(expanded)
}
```

使用：

```rust
#[timed]
fn slow_operation() {
    std::thread::sleep(std::time::Duration::from_millis(100));
}
```

### 带参数的属性宏

```rust
#[proc_macro_attribute]
pub fn retry(attr: TokenStream, item: TokenStream) -> TokenStream {
    let retries: syn::LitInt = syn::parse(attr).expect("Expected integer");
    let max_retries: usize = retries.base10_parse().unwrap();
    let input_fn = parse_macro_input!(item as ItemFn);
    let vis = &input_fn.vis;
    let sig = &input_fn.sig;
    let block = &input_fn.block;

    let expanded = quote! {
        #vis #sig {
            let mut __attempts = 0;
            loop {
                let __result = (|| #block)();
                match __result {
                    Ok(v) => break Ok(v),
                    Err(e) if __attempts < #max_retries => {
                        __attempts += 1;
                        eprintln!("Retry {}: {:?}", __attempts, e);
                    }
                    Err(e) => break Err(e),
                }
            }
        }
    };
    TokenStream::from(expanded)
}
// 使用：#[retry(3)]
```

---

## 💡 最佳实践

### 1. 错误处理

```rust
fn derive_macro(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    match generate_code(&input) {
        Ok(tokens) => tokens.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

fn validate_field(field: &Field) -> syn::Result<()> {
    if field.attrs.is_empty() {
        return Err(syn::Error::new(
            field.span(),
            "Field must have at least one attribute"
        ));
    }
    Ok(())
}
```

### 2. 辅助属性解析

```rust
#[derive(Builder)]
#[builder(default)]
struct Config {
    #[builder(skip)]
    internal: bool,
    name: String,
}

fn parse_builder_attrs(attrs: &[Attribute]) -> BuilderOptions {
    let mut options = BuilderOptions::default();
    for attr in attrs {
        if attr.path().is_ident("builder") {
            attr.parse_nested_meta(|meta| {
                if meta.path.is_ident("default") {
                    options.has_default = true;
                }
                Ok(())
            }).unwrap();
        }
    }
    options
}
```

### 3. 可测试的代码生成

```rust
fn generate_builder(input: &DeriveInput) -> syn::Result<proc_macro2::TokenStream> {
    // 可测试的纯逻辑
}

#[proc_macro_derive(Builder)]
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    generate_builder(&input)
        .unwrap_or_else(|e| e.to_compile_error())
        .into()
}
```

---

## ⚠️ 常见陷阱

| 问题 | 解决方案 |
|------|----------|
| 递归限制 | `#![recursion_limit = "256"]` |
| 名称冲突 | 使用双下划线前缀 `__result` |
| Hygiene | 使用完整路径 `::std::vec::Vec::new()` |
| Span 丢失 | 使用 `quote_spanned!` |
| 编译循环 | proc-macro crate 不能依赖使用它的 crate |

Span 保留示例：

```rust
use quote::quote_spanned;

// ❌ 丢失位置信息
quote! { #field: Default::default() }

// ✅ 保留 span
quote_spanned!(field.span()=> #field: Default::default())
```

---

## 🎮 动手练习

### 练习 1: Compact Debug

实现单行输出的 `#[derive(CompactDebug)]` 宏。

### 练习 2: Route 宏

实现 `#[route("/path")]` 为 HTTP handler 生成路由。

### 练习 3: SQL 验证

实现 `sql!("SELECT ...")` 在编译时验证 SQL 语法。

### 练习 4: Config 系统

结合知识实现：

```rust
#[derive(Config)]
#[config(file = "app.toml")]
struct AppConfig {
    #[config(default = 8080)]
    port: u16,
}
```

---

## 📖 延伸阅读

- 📚 [The Rust Reference - Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)
- 📚 [syn 文档](https://docs.rs/syn/) | [quote 文档](https://docs.rs/quote/)
- 🎓 [proc-macro-workshop](https://github.com/dtolnay/proc-macro-workshop)
- 🎓 [调试过程宏技巧](https://blog.turbo.fish/proc-macro-debugging/)
- 🛠️ [serde](https://github.com/serde-rs/serde) | [clap](https://github.com/clap-rs/clap) | [thiserror](https://github.com/dtolnay/thiserror)

---

> 💡 **总结**：过程宏是 Rust 最强大的元编程工具。掌握 `syn` 和 `quote`，从简单开始，始终提供清晰的错误信息。

*最后更新: 2026年3月*
