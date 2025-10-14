// 导出所有主要模块
pub mod initial_object;
pub mod performance;
pub mod primitive_types;
pub mod terminal_object;
pub mod type_class;
pub mod type_composition;
pub mod type_decomposition;
pub mod type_operation;
pub mod type_transformation;
pub mod type_variance;
pub mod r#unsafe;

// 导出 Rust 1.89 基础语法模块
pub mod rust_189_simple_demo;
// pub mod rust_189_basic_syntax; // 暂时注释掉，因为有编译错误
// pub mod rust_189_basic_syntax_simple; // 暂时注释掉，因为有编译错误

// 重新导出Rust 1.89增强特性
pub use performance::*;
pub use type_composition::rust_189_enhancements;
pub use rust_189_simple_demo::*;
pub use primitive_types::scalar_types::number::enhanced_integer_fixed::*;

// 导出 Rust 1.90 最新特性演示
pub mod rust_190_latest_features {
    // 这里可以添加 Rust 1.90 最新特性的模块导出
    // 目前通过 examples 目录中的文件进行演示
}

// 导出 Rust 1.90 高级特性模块
pub mod rust_190_advanced_features;

// 导出 WebAssembly 支持模块
pub mod wasm_support;

// 导出高级模式匹配模块
pub mod advanced_pattern_matching;

// 导出高级错误处理模块
pub mod advanced_error_handling;

// 导出类型系统验证工具模块
pub mod type_system_validator;

// 导出性能优化技巧模块
pub mod performance_optimization;

// 导出并发和异步高级特性模块
pub mod concurrent_async_advanced;

// 导出内存安全高级演示模块
pub mod memory_safety_advanced;

// 导出高级宏系统模块
pub mod advanced_macros;

// 导出示例模块
pub mod examples;
