//! Rust 1.89 控制流与函数特性研究项目
//! 
//! 本项目专注于控制流与函数系统的深度分析和实践应用，
//! 涵盖了异步编程增强、类型系统增强、性能优化特性等核心新特性。

// 导出核心模块
pub mod rust_189_features;
pub mod async_control_flow;
pub mod async_control_flow_189;
pub mod performance_optimization_189;

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

// 版本信息
pub const VERSION: &str = env!("CARGO_PKG_VERSION");
pub const RUST_VERSION: &str = "1.89.0";

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
        "Rust 1.89 控制流与函数特性研究项目"
    }
}

/// 初始化项目
pub fn init() {
    // 设置日志
    tracing_subscriber::fmt::init();
    
    println!("🚀 {} v{} 初始化完成", ProjectInfo::description(), ProjectInfo::version());
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
