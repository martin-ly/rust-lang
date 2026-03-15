//! 自定义派生宏示例
//! 
//! 展示如何实现自定义派生宏

use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse2, DeriveInput};

/// 生成 CustomDebug 派生实现
pub fn derive_custom_debug(input: TokenStream) -> TokenStream {
    let input: DeriveInput = parse2(input).expect("Failed to parse input");
    let name = &input.ident;
    
    let expanded = quote! {
        impl std::fmt::Debug for #name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{} {{ ... }}", stringify!(#name))
            }
        }
    };
    
    expanded
}

/// 生成 Builder 模式派生实现
pub fn derive_builder(input: TokenStream) -> TokenStream {
    let input: DeriveInput = parse2(input as TokenStream).expect("Failed to parse input");
    let name = &input.ident;
    let builder_name = quote::format_ident!("{}Builder", name);
    
    let expanded = quote! {
        pub struct #builder_name {
            // Builder 字段
        }
        
        impl #builder_name {
            pub fn new() -> Self {
                Self {}
            }
            
            pub fn build(self) -> Result<#name, String> {
                Ok(#name {})
            }
        }
    };
    
    expanded
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_custom_debug_generation() {
        let input = quote! {
            struct MyStruct {
                field: i32,
            }
        };
        
        let output = derive_custom_debug(input);
        let output_str = output.to_string();
        
        assert!(output_str.contains("impl std :: fmt :: Debug for MyStruct"));
    }
}
