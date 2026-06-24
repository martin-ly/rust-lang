//! 类型操作（type operation）：定义、转换、组合、等价、子类型化等。
//!
//! 本模块把 Rust 类型系统中的常见“操作”实现为可运行代码与测试，
//! 与 [`crate::type_composition`] / [`crate::type_decomposition`] /
//! [`crate::type_transformation`] 等模块一起覆盖类型系统的完整生命周期。

pub mod newtype;
pub mod subtype_relation;
pub mod type_aliases;
pub mod type_composition;
pub mod type_conversion;
pub mod type_definition;
pub mod type_equality;
pub mod type_equivalence;
