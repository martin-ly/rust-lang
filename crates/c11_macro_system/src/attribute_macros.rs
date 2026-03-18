//! 属性宏详解
//!
//! 属性宏允许自定义#[...]和#![...]属性的行为。

/// 属性宏基础概念
///
/// 属性宏可以应用于：
/// - 结构体和枚举
/// - 函数
/// - trait和impl块
/// - 模块
/// - 语句
///
/// 示例定义：
/// ```ignore
/// #[proc_macro_attribute]
/// pub fn trace(attr: TokenStream, item: TokenStream) -> TokenStream {
///     // attr: 属性参数，如 #[trace(level = "debug")] 中的 level = "debug"
///     // item: 被装饰的项的TokenStream
///     // 返回修改后的TokenStream
/// }
/// ```

/// 常用的属性宏示例

/// 1. 序列化/反序列化
/// ```ignore
/// #[derive(Serialize, Deserialize)]
/// struct User {
///     name: String,
/// }
/// ```
pub struct DeriveExample;

/// 2. 测试属性
/// ```ignore
/// #[test]
/// fn my_test() {}
///
/// #[should_panic]
/// fn panicking_test() {}
/// ```
pub struct TestAttributes;

/// 3. 条件编译
/// ```ignore
/// #[cfg(target_os = "linux")]
/// fn linux_only() {}
///
/// #[cfg_attr(feature = "serde", derive(Serialize))]
/// struct MyStruct;
/// ```
pub struct CfgAttributes;

/// 4. 文档属性
/// ```ignore
/// /// 这是一个文档注释
/// /// 等同于 #[doc = "这是一个文档注释"]
/// fn documented() {}
///
/// #![allow(dead_code)]  // 模块级属性
/// ```
pub struct DocAttributes;

/// 5. 内联和优化提示
/// ```ignore
/// #[inline]
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
pub mod patterns {
    /// 参数解析模式
    ///
    /// ```ignore
    /// #[my_macro(key = value, flag)]
    /// fn item() {}
    /// ```
    pub fn parse_key_value_args() {}

    /// 条件修改模式
    ///
    /// 根据属性参数决定是否修改代码
    pub fn conditional_modification() {}

    /// 代码注入模式
    ///
    /// 在函数开始或结束处注入代码
    pub fn code_injection() {}

    /// 包装器模式
    ///
    /// 将被装饰的项包装在另一个结构中
    pub fn wrapper_pattern() {}
}

/// 属性宏调试技巧
pub mod debugging {
    /// 使用cargo expand查看宏展开结果
    pub fn use_cargo_expand() {
        // cargo install cargo-expand
        // cargo expand --lib
    }

    /// 使用compile_error!在编译期报错
    pub fn use_compile_error() {
        // compile_error!("This should fail with a helpful message");
    }

    /// 打印TokenStream进行调试
    pub fn print_token_stream() {
        // eprintln!("Tokens: {}", tokens);
    }
}
