//! # C11: Rust 过程宏系统
//!
//! 这个crate提供了Rust过程宏的完整实现和示例。
//! 过程宏是Rust中最强大的元编程工具，允许在编译时生成和转换代码。
//!
//! ## 宏类型
//!
//! - **派生宏 (Derive Macros)**: 自动为结构体和枚举实现trait
//! - **属性宏 (Attribute Macros)**: 装饰函数、结构体等
//! - **函数式宏 (Function-like Macros)**: 类似macro_rules!但更强大
//!
//! ## 核心概念
//!
//! - **TokenStream**: 宏的输入和输出
//! - **AST**: 抽象语法树表示
//! - **编译时执行**: 在编译阶段运行代码
//!
//! ## 示例
//!
//! ```rust
//! use c11_macro_system_proc::*;
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

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput, ItemFn};

/// 自动生成Builder模式的派生宏
///
/// # 示例
///
/// ```rust
/// use c11_macro_system_proc::Builder;
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
///
/// # 示例
///
/// ```rust
/// use c11_macro_system_proc::debug_print;
///
/// #[debug_print]
/// fn my_function() {
///     println!("Hello!");
/// }
/// ```
#[proc_macro_attribute]
pub fn debug_print(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input_fn = parse_macro_input!(item as ItemFn);
    let fn_name = &input_fn.sig.ident;
    let fn_block = &input_fn.block;
    
    let expanded = quote! {
        fn #fn_name() {
            println!("[DEBUG] 调用函数: {}", stringify!(#fn_name));
            #fn_block
            println!("[DEBUG] 函数 {} 执行完成", stringify!(#fn_name));
        }
    };
    
    TokenStream::from(expanded)
}

/// 计时器属性宏
///
/// # 示例
///
/// ```rust
/// use c11_macro_system_proc::timed;
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
    
    input_fn.block = syn::parse2(wrapped_block).unwrap();
    
    TokenStream::from(quote! { #input_fn })
}

/// 条件编译宏
///
/// # 示例
///
/// ```rust
/// use c11_macro_system_proc::conditional;
///
/// conditional! {
///     #[cfg(debug_assertions)]
///     println!("调试模式");
///     
///     #[cfg(not(debug_assertions))]
///     println!("发布模式");
/// }
/// ```
#[proc_macro]
pub fn conditional(input: TokenStream) -> TokenStream {
    let input_str = input.to_string();
    
    // 简单的条件编译实现
    let expanded = quote! {
        {
            #input
        }
    };
    
    TokenStream::from(expanded)
}

/// 自动实现Clone trait的派生宏
///
/// # 示例
///
/// ```rust
/// use c11_macro_system_proc::AutoClone;
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
    
    let field_clones: Vec<_> = fields.iter().map(|f| {
        let field_name = &f.ident;
        quote! { #field_name: self.#field_name.clone() }
    }).collect();
    
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
///
/// # 示例
///
/// ```rust
/// use c11_macro_system_proc::serializable;
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
    let input_str = input.to_string();
    
    // 这里可以实现更复杂的序列化逻辑
    let expanded = quote! {
        // 序列化实现
        #input
    };
    
    TokenStream::from(expanded)
}
