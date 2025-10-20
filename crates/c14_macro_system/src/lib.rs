//! # C14: Rust宏系统 (Macro System)
//!
//! 本模块提供Rust宏系统的系统化学习内容，包括声明宏和过程宏。
//!
//! ## 模块结构
//!
//! - `declarative` - 声明宏实现和示例
//! - `utils` - 宏开发辅助工具
//!
//! ## 快速开始
//!
//! ```rust
//! use c14_macro_system::*;
//!
//! // 使用声明宏示例
//! // 查看 examples/ 目录获取更多示例
//! ```
//!
//! ## 学习路径
//!
//! 1. 查看 `docs/00_MASTER_INDEX.md` 获取完整学习导航
//! 2. 阅读理论文档了解宏的基础概念
//! 3. 运行示例代码进行实践
//! 4. 完成练习巩固知识
//!
//! ## 相关资源
//!
//! - [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)
//! - [The Rust Reference - Macros](https://doc.rust-lang.org/reference/macros.html)

#![warn(missing_docs)]
#![warn(clippy::all)]

// 公共模块导出
pub mod declarative;
pub mod utils;

// 重新导出常用项
pub use declarative::*;

/// 模块版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// 模块名称
pub const MODULE_NAME: &str = "C14: Macro System";

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_version() {
        assert!(!VERSION.is_empty());
    }

    #[test]
    fn test_module_name() {
        assert_eq!(MODULE_NAME, "C14: Macro System");
    }
}

