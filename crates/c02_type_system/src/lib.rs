// 导出所有主要模块
pub mod primitive_types;
pub mod type_composition;
pub mod type_decomposition;
pub mod type_class;
pub mod type_operation;
pub mod type_transformation;
pub mod type_variance;
pub mod r#unsafe;
pub mod terminal_object;
pub mod initial_object;
pub mod performance;

// 重新导出Rust 1.89增强特性
pub use type_composition::rust_189_enhancements;
pub use performance::*;
