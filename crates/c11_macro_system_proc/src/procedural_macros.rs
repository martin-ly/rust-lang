//! Procedural Macros

// [来源: Rust Reference / RFC 1566]
//! 过程宏（Procedural Macros）

// 过程宏需要在单独的crate中定义
// 这里展示的是概念性代码

/// ```text
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
///     };
///     
///     TokenStream::from(expanded)
/// }
/// ```text
pub struct DeriveMacroExample;

/// 属性宏示例说明
/// attribute example explain
/// 属性宏可以应用于任何Item：
/// attribute can application Item：
///
/// #\[proc_macro_attribute\]
/// pub fn log_entry(attr: TokenStream, item: TokenStream) -> TokenStream {
///     // attr: 属性参数
///     // attr: attribute parameter
///     // item: is修饰项
///     // item: is
pub struct AttributeMacroExample;

/// 函数式宏示例说明
/// functional example explain
/// 函数式宏类似于macro_rules!，但更灵活：
/// functional similar to macro_rules!，but ：
/// use syn::{parse_macro_input, Expr};
///
/// #\[proc_macro\]
/// pub fn sql(input: TokenStream) -> TokenStream {
///     let expr = parse_macro_input!(input as Expr);
///     // 解析SQL并生成代码
///     // SQLand
/// ```text
pub struct FunctionLikeMacroExample;

/// 过程宏最佳实践
/// best practice
pub mod best_practices {
    /// 使用 syn crate 解析 Rust 语法
    /// use syn crate to parse Rust syntax
    pub fn use_syn() {}

    /// 使用 quote crate 生成代码
    /// use quote crate to generate code
    pub fn use_quote() {}

    /// 3. 提供有意义的错误消息
    /// 3. message
    /// 3.
    pub fn meaningful_errors() {}

    /// 4. 避免生成过长的代码
    /// 4.
    pub fn avoid_code_bloat() {}

    /// 使用 span 进行错误定位
    /// use span for error location
    pub fn use_span() {}
}

/// 过程宏常用 crate 列表
/// list of commonly used procedural macro crates
pub mod crates {
    /// syn crate 名称
    /// syn crate name
    pub const SYN: &str = "syn";

    /// quote crate 名称
    /// quote crate name
    pub const QUOTE: &str = "quote";

    /// proc-macro2 crate 名称
    /// proc-macro2 crate name
    pub const PROC_MACRO2: &str = "proc-macro2";

    /// trybuild: 测试宏编译错误
    /// trybuild:
    pub const TRYBUILD: &str = "trybuild";
}
