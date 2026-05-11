//! 过程宏实现模块
//!
//! 过程宏（Procedural Macros）是 Rust 中最强大的元编程工具，
//! 允许在编译时生成和转换代码。
//!
//! ## 宏类型
//!
//! - **派生宏 (Derive Macros)**: 自动为结构体和枚举实现 trait
//! - **属性宏 (Attribute Macros)**: 装饰函数、结构体等
//! - **函数式宏 (Function-like Macros)**: 类似 `macro_rules!` 但更强大
//!
//! ## 实际实现
//!
//! 本 crate 中的真正过程宏实现在独立的 proc-macro crate 中：
//! `crates/c11_macro_system_proc`
//!
//! 这是因为 Rust 要求过程宏必须位于标记为 `proc-macro = true` 的独立 crate 中。
//!
//! ## 可用宏
//!
//! - `Builder` - 自动生成 Builder 模式的派生宏
//! - `AutoClone` - 自动实现 Clone trait
//! - `debug_print` - 调试打印属性宏
//! - `timed` - 计时器属性宏
//! - `conditional` - 条件编译宏
//! - `serializable` - 序列化辅助宏
//!
//! ## 使用示例
//!
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

// 重新导出 proc crate 中的宏，方便用户通过 c11_macro_system 使用
pub use c11_macro_system_proc::*;
