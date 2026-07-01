//! 过程宏实现模块
//! module
//! 允许在编译时生成和转换代码。
//! allow in compile-time and conversion 。
//! in compile-time and conversion 。
//! ## 宏类型
//! ## type
//! ## 宏type
//! - **属性宏 (Attribute Macros)**: 装饰函数、结构体等
//! - **attribute (Attribute Macros)**: function 、struct etc.
//! - **attribute macro (Attribute Macros)**: 装饰function、structetc.
//! - **函数式宏 (Function-like Macros)**: 类似 `macro_rules!` 但更强大
//! ## 实际实现
//! ## actual
//! ## 可用宏
//! ##
//! - `Builder` - 自动Generate Builder 模式derive macro
//! - `debug_print` - 调试打印属性宏
//! - `debug_print` - attribute
//! - `debug_print` - 调试Printattribute macro
//! - `timed` - 计时器属性宏
//! - `timed` - attribute
//! - `timed` - 计时器attribute macro
//! - `conditional` - 条件编译宏
//! - `serializable` - 序列化辅助宏
//! - `serializable` - sequence
//! ## 使用示例
//! ## example
//! ```ignore
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

pub mod custom_derive;

// 重新导出 proc crate 中的宏，方便用户通过 c11_macro_system_proc 使用
pub use c11_macro_system_proc_macros::*;
