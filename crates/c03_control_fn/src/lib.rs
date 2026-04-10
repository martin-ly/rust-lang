#![allow(clippy::type_complexity)]
#![allow(clippy::empty_line_after_doc_comments)]
#![allow(clippy::duplicated_attributes)]
#![allow(clippy::assertions_on_constants)]

//! Rust 1.92.0 控制流与函数特性研究项目
//!
//! 本项目专注于控制流与函数系统的深度分析和实践应用，
//! 涵盖了异步编程增强、类型系统增强、性能优化特性等核心新特性。
//!
//! **当前版本**: Rust 1.92.0+
//!
//! ## Rust 1.92.0 新特性
//!
//! - **异步Drop**: 异步资源清理支持
//! - **异步生成器**: 原生异步迭代器支持
//! - **Polonius借用检查器**: 更精确的借用分析
//! - **下一代特质求解器**: 更快的编译和更好的错误消息
//! - **并行前端**: 并行编译支持
// 导出核心模块
pub mod async_control_flow;
pub mod error;
pub mod rust_194_features; // Rust 1.94 特性
pub mod rust_196_gen_examples; // Rust 1.96 gen 关键字

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

// 重新导出Rust 1.96.0 gen关键字特性
pub use rust_196_gen_examples::{
    advanced_gen, async_gen, basic_gen, demonstrate_rust_196_gen_features, gen_pin,
    get_rust_196_gen_info,
};

// 导出基础语法模块
pub mod basic_syntax;

// 导出子模块
pub mod closure;
pub mod control_struct;
pub mod coroutine;
pub mod error_handling;
pub mod expressions;
pub mod generator;
pub mod items;
pub mod pattern_matching;
pub mod statements;

// 重新导出主要功能
pub use async_control_flow::*;

// 重新导出基础语法模块
pub use basic_syntax::*;

// 版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const RUST_VERSION: &str = "1.94.0";

/// 项目信息
pub struct ProjectInfo;

impl ProjectInfo {
    /// 获取项目版本
    pub fn version() -> &'static str {
        VERSION
    }

    /// 获取支持的Rust版本
    pub fn rust_version() -> &'static str {
        RUST_VERSION
    }

    /// 获取项目描述
    pub fn description() -> &'static str {
        "Rust 1.92 控制流与函数特性研究项目"
    }
}

/// 初始化项目
///
/// 初始化控制流与函数模块，设置日志系统并打印项目信息。
///
/// # Examples
///
/// ```
/// use c03_control_fn::init;
///
/// // 初始化项目
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
