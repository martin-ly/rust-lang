//! # c11_macro_system_proc - Rust 宏系统学习库
//!
//! 本 crate 提供 Rust 声明宏（`macro_rules!`）与过程宏的学习资源，
//! 涵盖宏卫生、宏模式、属性宏、编译期元编程与宏调试工具。
//!
//! ## 模块结构
//!
//! - `declarative` - 声明宏实现与示例
//! - `procedural_macros` - 过程宏示例
//! - `attribute_macros` - 属性宏
//! - `macro_hygiene` - 宏卫生
//! - `macro_patterns` - 常见宏模式
//! - `compile_time_metaprogramming` - 编译期元编程
//! - `utils` - 宏开发辅助工具
//!
//! ## 快速开始
//!
//! ```rust
//! use c11_macro_system_proc::*;
//!
//! // 使用声明宏示例，详见 examples/ 目录
//! ```
//!
//! ## 学习路径
//!
//! 1. 查看 `docs/00_MASTER_INDEX.md` 获取完整学习导航。
//! 2. 阅读理论文档了解宏的基础概念。
//! 3. 运行示例代码进行实践。
//! 4. 完成练习巩固知识。
//!
//! ## 相关资源
//!
//! - [The Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)

// [来源: Rust Reference / The Little Book of Rust Macros]
#![allow(clippy::type_complexity)]
#![allow(clippy::assertions_on_constants)]
#![warn(missing_docs)]
#![warn(clippy::all)]

// 公共模块导出
pub mod declarative;
pub mod error;
pub mod utils;

/// 过程宏实现模块（文档与示例）。
pub mod proc;

// Rust 1.91 新特性模块
pub mod archive;

// Rust 1.92 新特性模块
pub use archive::rust_192_features;
pub mod rust_186_features;
pub mod rust_187_features;
pub mod rust_188_features;
pub mod rust_189_features;
pub mod rust_193_features;
pub mod rust_194_features;
pub mod rust_195_features; // Rust 1.95 特性 (cfg_select!)
pub mod rust_196_features;

// 重新导出常用项
pub use declarative::*;

// 重新导出 Rust 1.92 特性
pub use archive::rust_192_features::{
    MacroExpansionItem,
    // 性能监控
    MacroExpansionPerformanceMonitor,
    // 宏展开队列
    MacroExpansionQueue,
    MacroMemoryAllocator,
    // 宏缓存计算
    calculate_macro_cache_size,
    check_macro_expansion_states,
    // 宏列表比较
    compare_macro_lists,
    // 主要功能函数
    demonstrate_rust_192_macro_features,
};

/// 模块版本号。
///
/// ```
/// use c11_macro_system_proc::VERSION;
///
/// assert!(!VERSION.is_empty());
/// ```
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// 模块名称。
///
/// ```
/// use c11_macro_system_proc::MODULE_NAME;
///
/// assert_eq!(MODULE_NAME, "C11: Macro System");
/// ```
pub const MODULE_NAME: &str = "C11: Macro System";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version() {
        assert!(!VERSION.is_empty());
    }

    #[test]
    fn test_module_name() {
        assert_eq!(MODULE_NAME, "C11: Macro System");
    }
}

// 新增模块
pub mod attribute_macros;
pub mod compile_time_metaprogramming;
pub mod declarative_macros;
pub mod macro_hygiene;
pub mod macro_patterns;
pub mod procedural_macros;
pub mod rust_197_features;
