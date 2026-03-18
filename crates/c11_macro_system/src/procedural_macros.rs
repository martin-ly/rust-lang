//! 过程宏（Procedural Macros）
//!
//! 过程宏允许在编译期运行Rust代码来操作Token流。

// 过程宏需要在单独的crate中定义
// 这里展示的是概念性代码

/// Derive宏示例说明
/// 
/// 实际实现需要在proc-macro crate中：
/// ```ignore
/// use proc_macro::TokenStream;
/// use quote::quote;
/// use syn::{parse_macro_input, DeriveInput};
/// 
/// #[proc_macro_derive(MyDebug)]
/// pub fn my_debug_derive(input: TokenStream) -> TokenStream {
///     let input = parse_macro_input!(input as DeriveInput);
///     let name = input.ident;
///     
///     let expanded = quote! {
///         impl std::fmt::Debug for #name {
///             fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
///                 write!(f, "{} {{ ... }}", stringify!(#name))
///             }
///         }
///     };
///     
///     TokenStream::from(expanded)
/// }
/// ```
pub struct DeriveMacroExample;

/// 属性宏示例说明
///
/// 属性宏可以应用于任何Item：
/// ```ignore
/// use proc_macro::TokenStream;
/// 
/// #[proc_macro_attribute]
/// pub fn log_entry(attr: TokenStream, item: TokenStream) -> TokenStream {
///     // attr: 属性参数
///     // item: 被修饰的项
///     // 返回修改后的TokenStream
/// }
/// ```
pub struct AttributeMacroExample;

/// 函数式宏示例说明
///
/// 函数式宏类似于macro_rules!，但更灵活：
/// ```ignore
/// use proc_macro::TokenStream;
/// use syn::{parse_macro_input, Expr};
/// 
/// #[proc_macro]
/// pub fn sql(input: TokenStream) -> TokenStream {
///     let expr = parse_macro_input!(input as Expr);
///     // 解析SQL并生成代码
///     TokenStream::new()
/// }
/// ```
pub struct FunctionLikeMacroExample;

/// 过程宏最佳实践
pub mod best_practices {
    /// 1. 使用syn crate解析输入
    pub fn use_syn() {}
    
    /// 2. 使用quote crate生成代码
    pub fn use_quote() {}
    
    /// 3. 提供有意义的错误消息
    pub fn meaningful_errors() {}
    
    /// 4. 避免生成过长的代码
    pub fn avoid_code_bloat() {}
    
    /// 5. 使用Span保持错误位置信息
    pub fn use_span() {}
}

/// 常用proc-macro crate介绍
pub mod crates {
    /// syn: 解析Rust代码为AST
    pub const SYN: &str = "syn";
    
    /// quote: 将AST转换回代码
    pub const QUOTE: &str = "quote";
    
    /// proc-macro2: proc_macro的封装
    pub const PROC_MACRO2: &str = "proc-macro2";
    
    /// trybuild: 测试宏编译错误
    pub const TRYBUILD: &str = "trybuild";
}
