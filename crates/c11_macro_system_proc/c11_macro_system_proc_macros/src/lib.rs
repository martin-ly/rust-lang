//! # C11: Rust 过程宏系统
//!
//! 本 crate 演示 Rust 过程宏（Procedural Macros）的核心类型与用法，包括：
//!
//! - **派生宏（Derive Macros）**：为结构体或枚举自动实现 trait。
//! - **属性宏（Attribute Macros）**：装饰函数、结构体、模块等。
//! - **函数式宏（Function-like Macros）**：类似 `macro_rules!`，但使用 Rust 代码解析 TokenStream。
//!
//! ## 核心概念
//!
//! - **TokenStream**：宏接收和返回的标记流。
//! - **AST**：抽象语法树表示，通常通过 `syn` crate 解析得到。
//! - **编译时执行**：过程宏在编译阶段运行并生成代码。
//!
//! ## 示例
//!
//! ```rust
//! use c11_macro_system_proc_macros::*;
//!
//! #[derive(Builder)]
//! struct Config {
//!     host: String,
//!     port: u16,
//! }
//!
//! #[debug_print]
//! fn my_function() {
//!     println!("Hello from macro!");
//! }
//! ```
mod rust_195_features;
mod rust_196_features;
mod rust_197_features;

use proc_macro::TokenStream;
use quote::quote;
use syn::{DeriveInput, ItemFn, parse_macro_input};

/// # 示例
/// # example
/// ```rust
/// use c11_macro_system_proc_macros::Builder;
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
    let input = parse_macro_input!(input as DeriveInput);

    let name = &input.ident;
    let builder_name = syn::Ident::new(&format!("{}Builder", name), name.span());

    // 提取字段信息
    let fields = match &input.data {
        syn::Data::Struct(syn::DataStruct { fields, .. }) => fields,
        _ => panic!("Builder宏只支持结构体"),
    };

    let field_names: Vec<_> = fields.iter().map(|f| &f.ident).collect();
    let field_types: Vec<_> = fields.iter().map(|f| &f.ty).collect();

    // 生成Builder结构体
    let builder_struct = quote! {
        pub struct #builder_name {
            #(
                #field_names: Option<#field_types>,
            )*
        }
    };

    // 生成Builder实现
    let builder_impl = quote! {
        impl #builder_name {
            pub fn new() -> Self {
                Self {
                    #(
                        #field_names: None,
                    )*
                }
            }

            #(
                pub fn #field_names(mut self, #field_names: #field_types) -> Self {
                    self.#field_names = Some(#field_names);
                    self
                }
            )*

            pub fn build(self) -> Result<#name, String> {
                Ok(#name {
                    #(
                        #field_names: self.#field_names.ok_or_else(|| format!("字段 {} 未设置", stringify!(#field_names)))?,
                    )*
                })
            }
        }
    };

    // 生成原结构体的builder方法
    let original_impl = quote! {
        impl #name {
            pub fn builder() -> #builder_name {
                #builder_name::new()
            }
        }
    };

    let expanded = quote! {
        #builder_struct
        #builder_impl
        #original_impl
    };

    TokenStream::from(expanded)
}

/// 调试打印属性宏
/// attribute
/// 调试Printattribute macro
/// # 示例
/// # example
/// ```rust
/// use c11_macro_system_proc_macros::debug_print;
///
/// #[debug_print]
/// fn my_function() {
///     println!("Hello!");
/// }
/// ```
#[proc_macro_attribute]
pub fn debug_print(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut input_fn = parse_macro_input!(item as ItemFn);
    let fn_name = &input_fn.sig.ident;
    let fn_block = &input_fn.block;

    let wrapped_block = quote! {
        {
            println!("[DEBUG] 调用函数: {}", stringify!(#fn_name));
            let __debug_result = #fn_block;
            println!("[DEBUG] 函数 {} 执行完成", stringify!(#fn_name));
            __debug_result
        }
    };

    input_fn.block = syn::parse2(wrapped_block).expect("generated block should be valid syntax");
    TokenStream::from(quote! { #input_fn })
}

/// 计时器属性宏
/// attribute
/// 计时器attribute macro
/// # 示例
/// # example
/// ```rust
/// use c11_macro_system_proc_macros::timed;
///
/// #[timed]
/// fn slow_function() {
///     std::thread::sleep(std::time::Duration::from_millis(100));
/// }
/// ```
#[proc_macro_attribute]
pub fn timed(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let mut input_fn = parse_macro_input!(item as ItemFn);
    let fn_name = &input_fn.sig.ident;
    let fn_block = &input_fn.block;

    // 包装函数体
    let wrapped_block = quote! {
        {
            let start = std::time::Instant::now();
            let result = #fn_block;
            let duration = start.elapsed();
            println!("[TIMED] 函数 {} 执行时间: {:?}", stringify!(#fn_name), duration);
            result
        }
    };

    input_fn.block = syn::parse2(wrapped_block).expect("generated block should be valid syntax");

    TokenStream::from(quote! { #input_fn })
}

/// 条件编译宏
/// condition
/// # 示例
/// # example
/// ```rust
/// use c11_macro_system_proc_macros::conditional;
///
/// conditional! {
///     #[cfg(debug_assertions)]
///     println!("调试模式");
///     println!("");
///     println!("发布模式");
///     println!("");
/// }
/// ```
#[proc_macro]
pub fn conditional(input: TokenStream) -> TokenStream {
    // 解析条件编译块：conditional! { #[cfg(cond)] { expr } #[cfg(not(cond))] { expr } }
    let input = proc_macro2::TokenStream::from(input);
    let mut iter = input.into_iter().peekable();
    let mut current_cfg: Option<String> = None;
    let mut branches: Vec<(Option<String>, proc_macro2::TokenStream)> = Vec::new();
    let mut current_tokens = proc_macro2::TokenStream::new();

    while let Some(token) = iter.next() {
        match &token {
            proc_macro2::TokenTree::Punct(p) if p.as_char() == '#' => {
                // 检查是否是 #[cfg(...)]
                #[allow(clippy::collapsible_if)]
                if let Some(proc_macro2::TokenTree::Group(g)) = iter.peek() {
                    if g.delimiter() == proc_macro2::Delimiter::Bracket {
                        let inner = g.stream().to_string();
                        if inner.starts_with("cfg") {
                            // 保存之前的分支
                            if !current_tokens.is_empty() {
                                branches.push((current_cfg.take(), current_tokens));
                                current_tokens = proc_macro2::TokenStream::new();
                            }
                            current_cfg = Some(inner.to_string());
                            iter.next(); // consume group
                            continue;
                        }
                    }
                    current_tokens.extend(std::iter::once(token));
                }
            }
            proc_macro2::TokenTree::Group(g) if g.delimiter() == proc_macro2::Delimiter::Brace => {
                if current_cfg.is_some() {
                    branches.push((current_cfg.take(), g.stream()));
                    current_tokens = proc_macro2::TokenStream::new();
                } else {
                    current_tokens
                        .extend(std::iter::once(proc_macro2::TokenTree::Group(g.clone())));
                }
            }
            _ => {
                current_tokens.extend(std::iter::once(token));
            }
        }
    }

    if !current_tokens.is_empty() {
        branches.push((current_cfg.take(), current_tokens));
    }

    // 选择一个匹配的分支（简化：检查 debug_assertions）
    let selected = branches
        .iter()
        .find_map(|(cfg, tokens)| match cfg.as_deref() {
            Some(c) if c.contains("debug_assertions") && !c.contains("not") => Some(tokens.clone()),
            Some(c) if c.contains("not(debug_assertions)") => {
                if cfg!(not(debug_assertions)) {
                    Some(tokens.clone())
                } else {
                    None
                }
            }
            None => Some(tokens.clone()),
            _ => None,
        });

    selected.map_or_else(TokenStream::new, TokenStream::from)
}

/// # 示例
/// # example
/// ```rust
/// use c11_macro_system_proc_macros::AutoClone;
///
/// #[derive(AutoClone)]
/// struct MyStruct {
///     name: String,
///     value: i32,
/// }
/// ```
#[proc_macro_derive(AutoClone)]
pub fn derive_auto_clone(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let fields = match &input.data {
        syn::Data::Struct(syn::DataStruct { fields, .. }) => fields,
        _ => panic!("AutoClone宏只支持结构体"),
    };

    let field_clones: Vec<_> = fields
        .iter()
        .map(|f| {
            let field_name = &f.ident;
            quote! { #field_name: self.#field_name.clone() }
        })
        .collect();

    let expanded = quote! {
        impl Clone for #name {
            fn clone(&self) -> Self {
                Self {
                    #(#field_clones),*
                }
            }
        }
    };

    TokenStream::from(expanded)
}

/// 序列化辅助宏
/// sequence
/// # 示例
/// # example
/// ```rust
/// use c11_macro_system_proc_macros::serializable;
///
/// serializable! {
///     struct User {
///         id: u32,
///         name: String,
///         email: String,
///     }
/// }
/// ```
#[proc_macro]
pub fn serializable(input: TokenStream) -> TokenStream {
    // 解析结构体定义，生成 Debug + 自定义 to_json / from_json 方法
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let fields = match &input.data {
        syn::Data::Struct(syn::DataStruct { fields, .. }) => fields,
        _ => panic!("serializable! 只支持结构体"),
    };

    let field_names: Vec<_> = fields.iter().map(|f| &f.ident).collect();
    let field_names_str: Vec<String> = field_names
        .iter()
        .map(|n| n.as_ref().unwrap().to_string())
        .collect();

    let expanded = quote! {
        #[derive(Debug)]
        #input

        impl #name {
            pub fn to_json(&self) -> String {
                let mut parts = Vec::new();
                #(
                    parts.push(format!("\"{}\": {:?}", #field_names_str, self.#field_names));
                )*
                format!("{{ {} }}", parts.join(", "))
            }
        }
    };

    TokenStream::from(expanded)
}
