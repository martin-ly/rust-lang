//! 属性宏详解
//! attribute
//! 属性宏允许自定义#[...]和#![...]属性的行为。
//! attribute definition #[...]and #![...]attribute as 。

/// 属性宏基础概念
/// attribute foundation concept
/// 属性宏可以应用于：
/// attribute can application ：
/// - 结构体和枚举
/// - struct and enum
/// - 函数
/// - function
/// - 模块
/// - module
/// - 语句
/// -
/// 示例定义：
/// example definition ：
/// #[proc_macro_attribute]
/// pub fn trace(attr: TokenStream, item: TokenStream) -> TokenStream {
///     // attr: attributeparameter，如 #[trace(level = "debug")] in level = "debug"
///
/// 常用的属性宏示例
/// attribute example
/// 1. 序列化/反序列化
/// 1. sequence /sequence
/// #[derive(Serialize, Deserialize)]
/// struct User {
///     name: String,
/// }
/// ```
pub struct DeriveExample;

/// 2. 测试属性
/// 2. attribute
/// #[test]
/// fn my_test() {}
///
/// #[should_panic]
/// fn panicking_test() {}
/// ```
pub struct TestAttributes;

/// 3. 条件编译
/// 3. condition
/// fn linux_only() {}
///
/// #[cfg_attr(feature = "serde", derive(Serialize))]
/// struct MyStruct;
/// ```
pub struct CfgAttributes;

/// 4. 文档属性
/// 4. attribute
/// 4. 文档attribute
/// /// 这是一个文档注释
/// ///
/// /// 等同于 #[doc = "这是一个文档注释"]
/// /// etc. #[doc = ""]
/// #![allow(dead_code)]  // 模块级属性
pub struct DocAttributes;

/// 5. 内联和优化提示
/// 5. inside and optimization hint
/// fn small_function() {}
///
/// #[inline(always)]
/// fn must_inline() {}
///
/// #[cold]
/// fn rare_path() {}
/// ```
pub struct InlineAttributes;

/// 自定义属性宏的设计模式
/// definition attribute design
pub mod patterns {
    /// 参数解析模式
    /// parameter
    /// #[my_macro(key = value, flag)]
    /// fn item() {}
    /// ```
    pub fn parse_key_value_args() {}

    /// 条件修改模式
    /// condition
    /// 根据属性参数决定是否修改代码
    /// according to attribute parameter
    pub fn conditional_modification() {}

    /// 代码注入模式
    /// 在函数开始或结束处注入代码
    /// in function or
    pub fn code_injection() {}

    /// 包装器模式
    /// 将被装饰的项包装在另一个结构中
    /// will is in structure in
    pub fn wrapper_pattern() {}
}

/// 属性宏调试技巧
/// attribute tip
pub mod debugging {
    pub fn use_cargo_expand() {
        // cargo install cargo-expand
        // cargo expand --lib
    }

    /// 使用compile_error!在编译期报错
    /// compile_error!in
    /// Usecompile_error!in编译期报错
    pub fn use_compile_error() {
        // compile_error!("This should fail with a helpful message");
    }

    pub fn print_token_stream() {
        // eprintln!("Tokens: {}", tokens);
    }
}
