//! Lib

// [来源: Rust Reference / The Little Book of Rust Macros]
//! Declarative macros (macro_rules!) and macro hygiene.
#![allow(clippy::type_complexity)]
#![allow(clippy::assertions_on_constants)]

//! ## 模块结构
//! ## module structure
//! - `declarative` - 声明宏实现和示例
//! - `declarative` - and example
//! - `utils` - 宏开发辅助工具
//! - `utils` - tool
//! - `utils` - 宏开发辅助tool
//! - `utils` - tool
//! ## 快速开始
//! ## fast
//! use c11_macro_system::*;
//!
//! // 使用声明宏示例
//! // example
//! // 查看 examples/ 目录获取更多示例
//! // examples/ example
//! // 查看 examples/ 目录Get更多Example of
//! ## 学习路径
//! ## learn
//! 1. 查看 `docs/00_MASTER_INDEX.md` 获取完整学习导航
//! 1. `docs/00_MASTER_INDEX.md` complete learn
//! 2. 阅读理论文档了解宏的基础概念
//! 2. theory foundation concept
//! 3. 运行示例代码进行实践
//! 3. Run example
//! 4. 完成练习巩固知识
//! 4. complete
//! 4.
//! ## 相关资源
//! ##
//! - [The Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)
#![warn(missing_docs)]
#![warn(clippy::all)]

// 公共模块导出
pub mod declarative;
pub mod error;
pub mod utils;

/// 过程宏实现模块（文档和示例）
/// module （and example ）
pub mod proc;

// Rust 1.91 新特性模块
pub mod archive;
pub use archive::rust_191_features;

// Rust 1.92 新特性模块
pub use archive::rust_192_features;
pub mod rust_186_features;
pub mod rust_187_features;
pub mod rust_188_features;
pub mod rust_189_features;
pub mod rust_190_features;
pub mod rust_193_features;
pub mod rust_194_features;
pub mod rust_195_features; // Rust 1.95 特性 (cfg_select!)
pub mod rust_196_features;

// 重新导出常用项
pub use declarative::*;

// 重新导出 Rust 1.91 特性
pub use archive::rust_191_features::{
    demonstrate_all_rust_191_macro_features,
    // 主要功能函数
    demonstrate_rust_191_macro_features,
    // 改进的错误消息
    improved_macro_errors,
    // 宏展开缓存
    macro_expansion_cache,
    // 过程宏编译优化
    proc_macro_compilation_optimization,
};

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

/// 模块版本信息
/// module this
///
/// ```
/// use c11_macro_system::VERSION;
///
/// assert!(!VERSION.is_empty());
/// ```
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// 模块名称
/// module
///
/// ```
/// use c11_macro_system::MODULE_NAME;
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
