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
pub mod async_control_flow_189;
pub mod performance_optimization_189;
pub mod rust_189_enhanced_features;
pub mod rust_189_features;

// 导出Rust 1.90新特性模块
pub mod rust_190_features;
pub mod rust_190_real_implementation;  // 真正的Rust 1.90特性实现
pub mod rust_190_complete_features;    // Rust 1.90完整特性实现
pub mod advanced_async_control_flow_190; // 高级异步控制流
pub mod performance_benchmarks_190;    // 性能基准测试
pub mod async_control_flow_190;
pub mod performance_optimization_190;
pub mod formal_verification_190;

// 导出Rust 1.91新特性模块
pub mod rust_191_features;

// 导出Rust 1.92.0新特性模块
pub mod rust_192_features;
pub mod rust_194_features;

// 重新导出Rust 1.92.0新特性
pub use rust_192_features::{
    control_flow_check, control_flow_branch, control_flow_loop, control_flow_match,
    control_flow_with_never, LocatedError, ErrorContext,
    ControlFlowAnalyzer, ControlFlowOptimizer,
    ControlFlowMatcher, ControlFlowCombinator, ControlFlowProfiler, ControlFlowValidator,
    ControlFlowStateMachine, ControlFlowState,
    IteratorControlFlow,
    ControlFlowVisualization,
    ControlFlowUtils, ControlFlowDecorator,
    get_rust_192_control_flow_info, demonstrate_rust_192_control_flow,
};

// 注意：async_control_flow 和 parallel_control_flow 是模块，已在 rust_192_features 中定义
// 可以通过 rust_192_features::async_control_flow 和 rust_192_features::parallel_control_flow 访问

// 重新导出Rust 1.91新特性
pub use rust_191_features::{
    const_control_flow,
    improved_control_flow,
    function_performance,
    error_handling as rust_191_error_handling,
    optimized_conditionals,
    optimized_loops,
    function_call_optimization,
    closure_optimization,
    comprehensive_examples,
    demonstrate_rust_191_control_flow,
    get_rust_191_control_flow_info,
};

// 导出基础语法模块
pub mod basic_syntax;
pub mod rust_189_basic_syntax;

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

// 重新导出主要功能（避免重复）
pub use async_control_flow::*;
pub use async_control_flow_189::*;
pub use performance_optimization_189::*;
pub use rust_189_enhanced_features::*;

// 重新导出Rust 1.90新特性
pub use rust_190_features::*;
pub use rust_190_real_implementation::*;  // 真正的Rust 1.90特性实现

// 选择性导出rust_190_complete_features以避免名称冲突
pub use rust_190_complete_features::{
    AsyncClosureDemo, TupleCollectionDemo, AsyncProcessor, DataProcessor,
    CompleteAdvancedDataProcessor, AdvancedDataProcessor, AsyncProcessorManager,
    ProcessorWrapper, CompleteAsyncResource, CompleteAsyncResourceManager,
    CompleteAsyncResourceManagerType, CompleteAsyncResourceType,
    DatabaseConnection, FileResource, demonstrate_rust_190_complete_features
};

pub use advanced_async_control_flow_190::*; // 高级异步控制流
pub use performance_benchmarks_190::*;    // 性能基准测试
pub use async_control_flow_190::*;
pub use performance_optimization_190::*;
pub use formal_verification_190::*;

// 重新导出基础语法模块
pub use basic_syntax::*;
pub use rust_189_basic_syntax::*;

// 版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const RUST_VERSION: &str = "1.92.0";

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
