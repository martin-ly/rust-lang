//! Field Projections 预览 — Rust Nightly 实验性特性
//!
//! **编译要求**: 需要 nightly Rust + `#![feature(field_projections)]`。
//! 当前 nightly (1.98.0) 中 `field_of!` 内置宏尚未可用，因此本模块仅保留
//! 概念文档与 API 占位，待编译器支持后再恢复完整实现。
//!
//! **来源**: [Rust Project Goals 2026 — Field Projections](https://rust-lang.github.io/rust-project-goals/2026/field-projections.html)
//! · [rust-lang/rust#152730](https://github.com/rust-lang/rust/pull/152730)
//!
//! **核心洞察**:
//! Field Projections 允许通过类型系统安全地投影结构体字段，无需 `unsafe` 或
//! `pin-project` 等外部 crate。这是 Rust 向“安全自引用结构”迈出的关键一步。

use std::pin::Pin;

/// 演示结构体：三维点。
pub struct Point3D {
    /// x 坐标
    pub x: f64,
    /// y 坐标
    pub y: f64,
    /// z 坐标
    pub z: f64,
}

/// 演示：使用 `field_of!` 获取字段的类型级表示。
///
/// 完整实现需要在 nightly 启用 `#![feature(field_projections)]` 后恢复：
///
/// ```ignore
/// #![feature(field_projections)]
/// use std::field::{Field, field_of};
///
/// fn project_ref<'a, T, F: Field<Base = T>>(r: &'a T) -> &'a F::Type {
///     unsafe { &*std::ptr::from_ref(r).byte_add(F::OFFSET).cast() }
/// }
///
/// let p = Point3D { x: 1.0, y: 2.0, z: 3.0 };
/// let x_ref = project_ref::<Point3D, field_of!(Point3D, x)>(&p);
/// ```
pub fn demo_basic_projection() {
    // 占位：等待 `field_of!` 在 nightly 可用后恢复。
    unimplemented!("field_of! 尚未在当前 nightly 可用")
}

/// 演示：字段信息 introspection。
pub fn demo_field_introspection() {
    unimplemented!("field_of! 尚未在当前 nightly 可用")
}

/// 自引用结构体示例。
pub struct SelfReferential {
    /// 数据缓冲区
    pub buffer: Vec<u8>,
    /// 指向 `buffer` 内部的指针
    pub ptr: *const u8,
}

/// 演示：安全的 Pin 字段投影。
pub fn demo_pinnable_field() {
    unimplemented!("field_of! 尚未在当前 nightly 可用")
}

/// 安全的 Pin 字段投影入口（占位签名）。
pub fn project_pinned(_r: Pin<&mut SelfReferential>) {
    unimplemented!("field_of! 尚未在当前 nightly 可用")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "field_of! 尚未在当前 nightly 可用"]
    fn test_basic_projection() {
        demo_basic_projection();
    }

    #[test]
    #[ignore = "field_of! 尚未在当前 nightly 可用"]
    fn test_field_introspection() {
        demo_field_introspection();
    }

    #[test]
    #[ignore = "field_of! 尚未在当前 nightly 可用"]
    fn test_pinnable_field() {
        demo_pinnable_field();
    }
}
