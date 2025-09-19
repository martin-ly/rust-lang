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
