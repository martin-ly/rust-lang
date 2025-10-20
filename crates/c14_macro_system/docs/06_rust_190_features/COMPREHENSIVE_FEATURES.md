# Rust 1.90 宏系统完整特性清单

> **文档定位**: Rust 1.90宏系统的详尽特性列表  
> **难度级别**: ⭐⭐⭐⭐ 专家  
> **最后更新**: 2025-10-20

---

## 📋 目录

- [Rust 1.90 宏系统完整特性清单](#rust-190-宏系统完整特性清单)
  - [📋 目录](#-目录)
  - [1. 稳定特性](#1-稳定特性)
    - [1.1 声明宏特性](#11-声明宏特性)
      - [完全稳定 (Stable)](#完全稳定-stable)
      - [示例：完整特性演示](#示例完整特性演示)
    - [1.2 过程宏特性](#12-过程宏特性)
      - [派生宏 (Derive Macros)](#派生宏-derive-macros)
      - [属性宏 (Attribute Macros)](#属性宏-attribute-macros)
      - [函数式宏 (Function-like Macros)](#函数式宏-function-like-macros)
    - [1.3 TokenStream API](#13-tokenstream-api)
  - [2. 实验性特性](#2-实验性特性)
    - [2.1 声明宏 2.0 (Unstable)](#21-声明宏-20-unstable)
    - [2.2 过程宏诊断 API (Unstable)](#22-过程宏诊断-api-unstable)
    - [2.3 内联宏 (Unstable)](#23-内联宏-unstable)
  - [3. 废弃特性](#3-废弃特性)
    - [3.1 已废弃的宏特性](#31-已废弃的宏特性)
  - [4. 生态系统支持](#4-生态系统支持)
    - [4.1 核心库](#41-核心库)
    - [4.2 工具链](#42-工具链)
  - [5. 性能基准](#5-性能基准)
    - [5.1 编译时间对比](#51-编译时间对比)
    - [5.2 优化建议](#52-优化建议)
  - [📚 版本兼容性矩阵](#-版本兼容性矩阵)
  - [返回导航](#返回导航)

---

## 1. 稳定特性

### 1.1 声明宏特性

#### 完全稳定 (Stable)

| 特性 | 版本 | 说明 |
|------|------|------|
| `macro_rules!` | 1.0 | 基础声明宏 |
| 13种片段说明符 | 1.32+ | 包括 `literal` |
| 重复模式 `$()*` | 1.0 | 基本重复 |
| 可选尾随分隔符 | 1.32+ | `$(,)?` 语法 |
| `#[macro_export]` | 1.0 | 导出宏 |
| `$crate` 元变量 | 1.30+ | 卫生性路径 |
| 嵌套宏调用 | 1.0 | 宏中调用宏 |

#### 示例：完整特性演示

```rust
/// 展示Rust 1.90所有稳定的声明宏特性
#[macro_export]
macro_rules! comprehensive_macro {
    // 1. 基础模式匹配
    () => {
        println!("No arguments");
    };
    
    // 2. 所有片段说明符
    (item: $i:item) => { $i };
    (block: $b:block) => { $b };
    (stmt: $s:stmt) => { $s };
    (expr: $e:expr) => { $e };
    (pat: $p:pat) => { let $p = 42; };
    (ty: $t:ty) => { let _: $t; };
    (ident: $id:ident) => { let $id = "ident"; };
    (path: $path:path) => { use $path; };
    (tt: $tt:tt) => { $tt };
    (meta: $m:meta) => { #[$m] };
    (lifetime: $l:lifetime) => { fn foo<$l>() {} };
    (vis: $v:vis) => { $v fn bar() {} };
    (literal: $lit:literal) => { $lit };
    
    // 3. 重复模式
    (repeat: $($x:expr),*) => {
        vec![$($x),*]
    };
    
    // 4. 嵌套重复
    (nested: $($($x:expr),+);+) => {
        vec![$(vec![$($x),+]),+]
    };
    
    // 5. 可选尾随分隔符
    (trailing: $($x:expr),+ $(,)?) => {
        vec![$($x),+]
    };
    
    // 6. 使用 $crate 确保卫生性
    (hygienic: $func:ident) => {
        $crate::internal::$func()
    };
    
    // 7. 内部规则
    (@internal $x:expr) => {
        $x * 2
    };
    
    // 8. 递归调用
    (recursive: $x:expr, $($rest:expr),+) => {
        $x + comprehensive_macro!(recursive: $($rest),+)
    };
    (recursive: $x:expr) => {
        $x
    };
}
```

### 1.2 过程宏特性

#### 派生宏 (Derive Macros)

| 特性 | 版本 | 说明 |
|------|------|------|
| 基础派生宏 | 1.15+ | `#[proc_macro_derive]` |
| 辅助属性 | 1.30+ | `attributes(attr)` |
| 泛型支持 | 1.15+ | 完整泛型处理 |
| 生命周期处理 | 1.15+ | 完整生命周期支持 |

```rust
// Rust 1.90派生宏完整示例
use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, Data, Fields};

#[proc_macro_derive(CompleteDerive, attributes(complete))]
pub fn derive_complete(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;
    let generics = &input.generics;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();
    
    // 处理所有数据类型
    let implementation = match &input.data {
        Data::Struct(data) => {
            match &data.fields {
                Fields::Named(fields) => {
                    let field_names: Vec<_> = fields.named.iter()
                        .map(|f| &f.ident)
                        .collect();
                    
                    quote! {
                        impl #impl_generics CompleteTrait for #name #ty_generics #where_clause {
                            fn process(&self) -> String {
                                format!("{:?}", (#(self.#field_names),*))
                            }
                        }
                    }
                }
                Fields::Unnamed(fields) => {
                    let indices = (0..fields.unnamed.len()).map(syn::Index::from);
                    quote! {
                        impl #impl_generics CompleteTrait for #name #ty_generics #where_clause {
                            fn process(&self) -> String {
                                format!("{:?}", (#(self.#indices),*))
                            }
                        }
                    }
                }
                Fields::Unit => {
                    quote! {
                        impl #impl_generics CompleteTrait for #name #ty_generics #where_clause {
                            fn process(&self) -> String {
                                stringify!(#name).to_string()
                            }
                        }
                    }
                }
            }
        }
        Data::Enum(data) => {
            let variants = data.variants.iter().map(|v| {
                let variant_name = &v.ident;
                quote! { #name::#variant_name => stringify!(#variant_name).to_string() }
            });
            
            quote! {
                impl #impl_generics CompleteTrait for #name #ty_generics #where_clause {
                    fn process(&self) -> String {
                        match self {
                            #(#variants),*
                        }
                    }
                }
            }
        }
        Data::Union(_) => {
            return syn::Error::new_spanned(
                &input,
                "CompleteDerive does not support unions"
            ).to_compile_error().into();
        }
    };
    
    TokenStream::from(implementation)
}
```

#### 属性宏 (Attribute Macros)

| 特性 | 版本 | 说明 |
|------|------|------|
| 基础属性宏 | 1.30+ | `#[proc_macro_attribute]` |
| 函数属性 | 1.30+ | 装饰函数 |
| 结构体属性 | 1.30+ | 装饰类型 |
| 模块属性 | 1.30+ | 装饰模块 |
| 表达式属性 | 1.45+ | 装饰表达式 |

```rust
// Rust 1.90属性宏完整示例
#[proc_macro_attribute]
pub fn complete_attribute(attr: TokenStream, item: TokenStream) -> TokenStream {
    // 解析属性参数
    let attr_args = parse_macro_input!(attr as AttributeArgs);
    
    // 解析被装饰的项
    let item_enum: syn::Item = parse_macro_input!(item);
    
    match item_enum {
        syn::Item::Fn(mut item_fn) => {
            // 处理函数
            let fn_name = &item_fn.sig.ident;
            let original_block = &item_fn.block;
            
            // 修改函数体
            let new_block = syn::parse2(quote! {
                {
                    println!("Entering {}", stringify!(#fn_name));
                    let result = #original_block;
                    println!("Exiting {}", stringify!(#fn_name));
                    result
                }
            }).unwrap();
            
            item_fn.block = Box::new(new_block);
            TokenStream::from(quote! { #item_fn })
        }
        syn::Item::Struct(item_struct) => {
            // 处理结构体
            let struct_name = &item_struct.ident;
            TokenStream::from(quote! {
                #[derive(Debug, Clone)]
                #item_struct
                
                impl #struct_name {
                    pub fn new() -> Self {
                        Default::default()
                    }
                }
            })
        }
        syn::Item::Mod(item_mod) => {
            // 处理模块
            TokenStream::from(quote! {
                #[allow(dead_code)]
                #item_mod
            })
        }
        other => {
            TokenStream::from(quote! { #other })
        }
    }
}
```

#### 函数式宏 (Function-like Macros)

| 特性 | 版本 | 说明 |
|------|------|------|
| 基础函数式宏 | 1.30+ | `#[proc_macro]` |
| 自定义语法 | 1.30+ | 完全自定义 |
| 编译时检查 | 1.30+ | SQL/HTML等DSL |

```rust
// Rust 1.90函数式宏完整示例
use syn::parse::{Parse, ParseStream};
use syn::{Ident, Token, LitStr, braced};

// 自定义DSL语法
struct ConfigDsl {
    items: Vec<ConfigItem>,
}

struct ConfigItem {
    key: Ident,
    _colon: Token![:],
    value: LitStr,
}

impl Parse for ConfigDsl {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let content;
        braced!(content in input);
        
        let mut items = Vec::new();
        while !content.is_empty() {
            items.push(content.parse()?);
            if content.peek(Token![,]) {
                content.parse::<Token![,]>()?;
            }
        }
        
        Ok(ConfigDsl { items })
    }
}

impl Parse for ConfigItem {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(ConfigItem {
            key: input.parse()?,
            _colon: input.parse()?,
            value: input.parse()?,
        })
    }
}

#[proc_macro]
pub fn config(input: TokenStream) -> TokenStream {
    let config = parse_macro_input!(input as ConfigDsl);
    
    let items = config.items.iter().map(|item| {
        let key = &item.key;
        let value = &item.value;
        quote! {
            (#key, #value)
        }
    });
    
    TokenStream::from(quote! {
        {
            use std::collections::HashMap;
            let mut config = HashMap::new();
            #(config.insert(stringify!(#items.0), #items.1);)*
            config
        }
    })
}

// 使用:
// let cfg = config! {
//     host: "localhost",
//     port: "8080",
//     db: "mydb"
// };
```

### 1.3 TokenStream API

| API | 版本 | 说明 |
|-----|------|------|
| `TokenStream::new()` | 1.15+ | 创建空流 |
| `TokenStream::from()` | 1.15+ | 转换 |
| `.into_iter()` | 1.15+ | 迭代 |
| `TokenTree` | 1.15+ | Token树 |
| `Span` | 1.15+ | 位置信息 |
| `proc_macro2` | 外部 | 测试支持 |

```rust
// Rust 1.90 TokenStream完整操作示例
use proc_macro2::{TokenStream, TokenTree, Ident, Literal, Punct, Group, Delimiter, Spacing, Span};

fn token_operations() -> TokenStream {
    let mut stream = TokenStream::new();
    
    // 1. 添加标识符
    let ident = Ident::new("my_function", Span::call_site());
    stream.extend(quote! { #ident });
    
    // 2. 添加标点
    let punct = Punct::new(':', Spacing::Joint);
    stream.extend(std::iter::once(TokenTree::Punct(punct)));
    
    // 3. 添加字面量
    let lit = Literal::i32_unsuffixed(42);
    stream.extend(std::iter::once(TokenTree::Literal(lit)));
    
    // 4. 添加分组
    let group = Group::new(
        Delimiter::Brace,
        quote! { println!("Hello"); }
    );
    stream.extend(std::iter::once(TokenTree::Group(group)));
    
    // 5. 过滤和转换
    stream.into_iter()
        .filter(|tt| !matches!(tt, TokenTree::Punct(_)))
        .collect()
}
```

---

## 2. 实验性特性

### 2.1 声明宏 2.0 (Unstable)

```rust
// 需要 #![feature(decl_macro)]

// 新语法
pub macro my_macro_2_0($e:expr) {
    $e * 2
}

// 使用
let result = my_macro_2_0!(21); // 42
```

**状态**: 不稳定  
**追踪**: [rust-lang/rust#39412](https://github.com/rust-lang/rust/issues/39412)

### 2.2 过程宏诊断 API (Unstable)

```rust
// 需要 #![feature(proc_macro_diagnostic)]

use proc_macro::Diagnostic;

#[proc_macro]
pub fn diagnostic_demo(input: TokenStream) -> TokenStream {
    let span = input.into_iter().next().unwrap().span();
    
    // 发出警告
    span.warning("This is a warning").emit();
    
    // 发出错误
    span.error("This is an error").emit();
    
    // 发出提示
    span.note("This is a note").emit();
    
    TokenStream::new()
}
```

**状态**: 不稳定  
**追踪**: [rust-lang/rust#54140](https://github.com/rust-lang/rust/issues/54140)

### 2.3 内联宏 (Unstable)

```rust
// 需要 #![feature(proc_macro_hygiene)]

// 在表达式位置使用函数式宏
let value = my_macro!();
```

**状态**: 部分稳定  
**追踪**: [rust-lang/rust#54727](https://github.com/rust-lang/rust/issues/54727)

---

## 3. 废弃特性

### 3.1 已废弃的宏特性

| 特性 | 废弃版本 | 替代方案 |
|------|----------|----------|
| `macro_reexport` | 1.30 | 使用 `pub use` |
| 旧版宏导出语法 | 1.30 | `#[macro_export]` |

---

## 4. 生态系统支持

### 4.1 核心库

| 库 | 版本 | Rust 1.90兼容性 |
|------|------|-----------------|
| `syn` | 2.0+ | ✅ 完全支持 |
| `quote` | 1.0+ | ✅ 完全支持 |
| `proc-macro2` | 1.0+ | ✅ 完全支持 |
| `proc-macro-error` | 1.0+ | ✅ 完全支持 |

### 4.2 工具链

| 工具 | Rust 1.90支持 |
|------|--------------|
| `cargo-expand` | ✅ |
| `rust-analyzer` | ✅ |
| `rustfmt` | ✅ |
| `clippy` | ✅ |

---

## 5. 性能基准

### 5.1 编译时间对比

```rust
// 简单派生宏
#[derive(Simple)]  // ~0.5ms

// 复杂派生宏
#[derive(Complex)] // ~5ms

// 函数式宏
complex_macro!()   // ~10ms
```

### 5.2 优化建议

1. **最小化syn解析**: 只解析需要的部分
2. **避免字符串操作**: 直接操作TokenStream
3. **缓存结果**: 使用静态缓存
4. **并行处理**: 对独立操作使用并行

---

## 📚 版本兼容性矩阵

| Rust版本 | 声明宏 | 派生宏 | 属性宏 | 函数式宏 | syn 2.0 |
|----------|--------|--------|--------|----------|---------|
| 1.15 | ✅ | ✅ | ❌ | ❌ | ❌ |
| 1.30 | ✅ | ✅ | ✅ | ✅ | ❌ |
| 1.45 | ✅ | ✅ | ✅ | ✅ | ❌ |
| 1.56 | ✅ | ✅ | ✅ | ✅ | ✅ |
| 1.70 | ✅ | ✅ | ✅ | ✅ | ✅ |
| 1.90 | ✅ | ✅ | ✅ | ✅ | ✅ |

---

**文档版本**: v1.0  
**适用版本**: Rust 1.90+  
**最后更新**: 2025-10-20

---

## 返回导航

- [返回特性目录](README.md)
- [返回主索引](../00_MASTER_INDEX.md)
