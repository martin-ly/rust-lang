//! 最小过程宏示例：自定义 derive 宏
//! 
//! 本 crate 演示如何创建自定义 derive 宏，为结构体自动生成方法。

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, DeriveInput};

/// 为结构体自动生成 `display` 方法
#[proc_macro_derive(Display)]
pub fn derive_display(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let expanded = quote! {
        impl #name {
            pub fn display(&self) -> String {
                format!("{}", stringify!(#name))
            }
        }
    };

    TokenStream::from(expanded)
}

/// 为结构体自动生成 `id` 方法（假设有 id 字段）
#[proc_macro_derive(WithId)]
pub fn derive_with_id(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let name = &input.ident;

    let expanded = quote! {
        impl #name {
            pub fn id(&self) -> u64 {
                // 简化实现：返回结构体名称的哈希值
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                
                let mut hasher = DefaultHasher::new();
                stringify!(#name).hash(&mut hasher);
                hasher.finish()
            }
        }
    };

    TokenStream::from(expanded)
}
