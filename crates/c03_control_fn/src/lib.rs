//! # c03_control_fn - Rust 控制流与函数学习模块
//!
//! 本 crate 聚焦 Rust 控制流、函数、闭包与错误处理模式的理论与实践，
//! 涵盖 `if let` guards、异步控制流、生成器（gen blocks，nightly-only）、
//! 函数组合、状态机等主题，并按 Rust 版本特性组织历史演进示例。
//!
//! ## 模块组织
//!
//! - 控制流模式 [`control_flow_patterns`]
//! - 闭包与函数 [`closure`]
//! - 异步控制流 [`async_control_flow`]
//! - 错误处理 [`error_handling`]
//! - `if let` guards 深度解析 [`if_let_guards_deep_dive`]
//! - Rust 1.94–1.97 特性演进模块
//!
//! ## 版本信息
//!
//! - **当前版本**: 与 workspace 一致
//! - **目标 Rust 版本**: 1.95.0+
//! - **Edition**: 2024

// [来源: Rust Reference / TRPL]
#![allow(clippy::type_complexity)]
#![allow(clippy::assertions_on_constants)]
// 导出核心模块
pub mod async_control_flow;
pub mod control_flow_patterns;
pub mod error;
pub mod if_let_guards_deep_dive;
pub mod rust_186_features;
pub mod rust_187_features;
pub mod rust_188_features;
pub mod rust_189_features;
pub mod rust_192_features;
pub mod rust_193_features;
pub mod rust_194_features; // Rust 1.94 特性
pub mod rust_195_features; // Rust 1.95.0 特性 (if let guards, bool TryFrom)
pub mod rust_196_features; // Rust 2024 Edition let chains
pub mod rust_197_features;

pub mod rust_196_gen_examples; // gen blocks 前瞻 (nightly-only, 非 1.96 stable) // if let guards 深度解析 (Rust 1.95.0 stable)

// 重新导出Rust 1.94.0新特性
pub use rust_194_features::{
    // 闭包和控制流
    ClosureCaptureAnalyzer,
    // LazyCell 控制流
    ConditionalLazyController,
    ControlFlowLazyCache,
    // 数学常量控制流
    ConvergenceController,
    DataFilterProcessor,
    Edition2024,
    // Edition 2024
    Edition2024ControlFlow,
    EnhancedMatcher,
    EventStreamProcessor,
    // 函数指针优化
    FunctionPtrWrapper,
    GenericParser,
    // Match增强
    MatchResult,
    ParseResult,
    // Peekable新方法
    SimpleLexer,
    // array_windows 相关
    StateMachineParser,
    Token,
    TokenIterator,
    branch_predictor_friendly,
    branchless_computation,
    compose_functions,
    conditional_execute,
    controlled_harmonic_sum,
    create_precise_closure,
    // 演示函数
    demonstrate_rust_194_control_flow,
    get_rust_194_control_flow_info,
    golden_section_search,
    math_consts,
    // 性能优化
    optimized_loop,
    process_match_result,
    vectorizable_loop,
};

// 重新导出 gen blocks 前瞻示例 (nightly-only, 非 1.96 stable)
pub use rust_196_gen_examples::{
    advanced_gen, async_gen, basic_gen, demonstrate_rust_196_gen_features, gen_pin,
    get_rust_196_gen_info,
};

// 导出基础语法模块
pub mod basic_syntax;

// 导出子模块
pub mod closure;
pub mod control_struct;
pub mod error_handling;
pub mod expressions;
pub mod items;
pub mod pattern_matching;
pub mod statements;

// 重新导出主要功能
pub use async_control_flow::*;

// 重新导出基础语法模块
pub use basic_syntax::*;

// 版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const RUST_VERSION: &str = "1.95.0";

/// 项目元信息。
pub struct ProjectInfo;

impl ProjectInfo {
    /// 返回项目版本号。
    pub fn version() -> &'static str {
        VERSION
    }

    /// 返回目标 Rust 版本号。
    pub fn rust_version() -> &'static str {
        RUST_VERSION
    }

    /// 返回项目描述。
    pub fn description() -> &'static str {
        "Rust 控制流与函数特性研究项目"
    }
}

/// 初始化控制流与函数模块，设置日志系统并打印项目信息。
///
/// ```
/// use c03_control_fn::init;
///
/// init();
/// ```
///
/// # Note
///
/// 此函数会初始化日志系统，多次调用是安全的。
pub fn init() {
    // 设置日志
    tracing_subscriber::fmt::init();

    println!(
        "🚀 {} v{} 初始化完成",
        ProjectInfo::description(),
        ProjectInfo::version()
    );
    println!("📦 支持 Rust {}", ProjectInfo::rust_version());
}

#[cfg(test)]
pub mod miri_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_project_info() {
        assert_eq!(ProjectInfo::version(), VERSION);
        assert_eq!(ProjectInfo::rust_version(), RUST_VERSION);
        assert!(!ProjectInfo::description().is_empty());
    }

    #[test]
    fn test_init() {
        // 测试初始化函数不会panic
        init();
    }
}
