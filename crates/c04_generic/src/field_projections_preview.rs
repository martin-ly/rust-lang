//! Field Projections 预览 — Rust Nightly 实验性特性
//! **编译要求**: 需要 nightly Rust + `#![feature(field_projections)]`
//! **来源**: [Rust Project Goals 2026 — Field Projections](https://rust-lang.github.io/rust-project-goals/2026/field-projections.html)
//! · [rust-lang/rust#152730](https://github.com/rust-lang/rust/pull/152730)
//! · [来源: Rust Official Docs]
//!
//! **状态**: 🧪 Nightly 实验性（2026-02 `field_of!` 宏已合并，2026-04 t-lang 设计会议反馈极为正面）
//! **关联**: Pin Ergonomics, Reborrow Traits, Smart Pointer ergonomics
//!
//! **核心洞察**:
//! Field Projections 允许通过类型系统安全地投影结构体字段，无需 `unsafe` 或 `pin-project` 等外部 crate。
//! 这是 Rust 向"安全自引用结构"迈出的关键一步。

#![allow(incomplete_features)]
#![feature(field_projections)]

use std::field::{Field, field_of};
use std::pin::Pin;
use std::ptr;

// ============================================================================
// 1. 基础 Field Projection：通过类型系统访问字段
// ============================================================================

/// 安全地投影任意字段引用
///
/// `F: Field<Base = T>` 保证了 `F` 是 `T` 的合法字段，且 `F::OFFSET` 和 `F::Type` 由编译器提供。
fn project_ref<'a, T, F: Field<Base = T>>(r: &'a T) -> &'a F::Type {
    // SAFETY: `Field` trait 由编译器实现，保证 OFFSET 和 Type 的正确性。
    unsafe { &*ptr::from_ref(r).byte_add(F::OFFSET).cast() }
}

/// 安全地投影任意字段可变引用
fn project_mut<'a, T, F: Field<Base = T>>(r: &'a mut T) -> &'a mut F::Type {
    // SAFETY: 同上
    unsafe { &mut *ptr::from_mut(r).byte_add(F::OFFSET).cast() }
}

struct Point3D {
    x: f64,
    y: f64,
    z: f64,
}

/// 演示：使用 `field_of!` 获取字段的类型级表示
pub fn demo_basic_projection() {
    let mut p = Point3D { x: 1.0, y: 2.0, z: 3.0 };

    // `field_of!(Point3D, x)` 是一个零大小类型，代表 Point3D 的 x 字段
    let x_ref: &f64 = project_ref::<Point3D, field_of!(Point3D, x)>(&p);
    let y_ref: &f64 = project_ref::<Point3D, field_of!(Point3D, y)>(&p);
    let z_mut: &mut f64 = project_mut::<Point3D, field_of!(Point3D, z)>(&mut p);

    println!("x = {x_ref}, y = {y_ref}, z = {z_mut}");
    *z_mut = 42.0;
    println!("updated z = {}", p.z);
}

// ============================================================================
// 2. 泛型字段操作：编写对任意字段生效的函数
// ============================================================================

/// 泛型地获取字段的偏移量和类型大小信息
fn field_info<T, F: Field<Base = T>>(_field: F) -> (usize, usize) {
    (F::OFFSET, std::mem::size_of::<F::Type>())
}

/// 演示：字段信息 introspection
pub fn demo_field_introspection() {
    let (offset_x, size_x) = field_info(field_of!(Point3D, x));
    let (offset_y, size_y) = field_info(field_of!(Point3D, y));
    println!("Point3D.x: offset={offset_x}, size={size_x}");
    println!("Point3D.y: offset={offset_y}, size={size_y}");
}

// ============================================================================
// 3. PinnableField：安全的 Pin 投影（Pin Ergonomics 关键基础设施）
// ============================================================================

/// 标记一个字段为"结构性固定"（structurally pinned）
///
/// 这是 Pin Ergonomics 的核心模式：通过 trait 系统区分哪些字段在 Pin 投影后
/// 仍然是 `Pin<&mut>`，哪些可以退化为普通 `&mut`。
unsafe trait PinnableField: Field {
    type StructuralRefMut<'a>
    where
        Self::Type: 'a,
        Self::Base: 'a;

    fn project_mut<'a>(base: Pin<&'a mut Self::Base>) -> Self::StructuralRefMut<'a>
    where
        Self::Type: 'a,
        Self::Base: 'a;
}

struct SelfReferential {
    buffer: Vec<u8>,
    // `ptr` 指向 `buffer` 内部，因此当结构被 Pin 时，`ptr` 的投影必须是 Pin
    ptr: *const u8,
}

// `buffer` 字段不是结构固定的 —— 可以直接获取 &mut Vec<u8>
unsafe impl PinnableField for field_of!(SelfReferential, buffer) {
    type StructuralRefMut<'a> = &'a mut Vec<u8>
    where
        Self::Type: 'a,
        Self::Base: 'a;

    fn project_mut<'a>(base: Pin<&'a mut Self::Base>) -> Self::StructuralRefMut<'a>
    where
        Self::Type: 'a,
        Self::Base: 'a,
    {
        let base = unsafe { Pin::into_inner_unchecked(base) };
        &mut base.buffer
    }
}

// `ptr` 字段是结构固定的 —— 必须保持 Pin 不变性
unsafe impl PinnableField for field_of!(SelfReferential, ptr) {
    type StructuralRefMut<'a> = Pin<&'a mut *const u8>
    where
        Self::Type: 'a,
        Self::Base: 'a;

    fn project_mut<'a>(base: Pin<&'a mut Self::Base>) -> Self::StructuralRefMut<'a>
    where
        Self::Type: 'a,
        Self::Base: 'a,
    {
        let base = unsafe { Pin::into_inner_unchecked(base) };
        // ptr 字段本身是一个裸指针，但由于它是自引用的，我们将其视为固定
        unsafe { Pin::new_unchecked(&mut base.ptr) }
    }
}

/// 安全的 Pin 字段投影入口
fn project_pinned<'a, T, F>(r: Pin<&'a mut T>) -> <F as PinnableField>::StructuralRefMut<'a>
where
    F: PinnableField<Base = T>,
{
    F::project_mut(r)
}

pub fn demo_pinnable_field() {
    let mut data = SelfReferential {
        buffer: vec![1, 2, 3, 4, 5],
        ptr: ptr::null(),
    };
    data.ptr = data.buffer.as_ptr();

    let pin = Pin::new(&mut data);

    // buffer 可以直接获取普通可变引用（因为它不依赖自引用）
    let buf: &mut Vec<u8> = project_pinned::<SelfReferential, field_of!(SelfReferential, buffer)>(pin);
    buf.push(6);

    // 注意：ptr 的投影在此示例中简化了；实际使用中需确保 Pin 契约不被破坏
    println!("PinnableField demo: buffer len = {}", data.buffer.len());
}

// ============================================================================
// 4. 边界与限制
// ============================================================================

/// Field Projections 当前限制（截至 nightly 1.98.0）：
/// - 仅支持 `repr(Rust)` 且非 `repr(packed)` 的结构体
/// - 所有字段必须是 `Sized`
/// - `field_of!` 返回的 FRT（Field Representing Type）目前仅自动实现 `Field` trait
///   在上述条件下
/// - Union 支持有限
/// - Enum variant 字段支持正在开发中

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_projection() {
        demo_basic_projection();
    }

    #[test]
    fn test_field_introspection() {
        demo_field_introspection();
    }

    #[test]
    fn test_pinnable_field() {
        demo_pinnable_field();
    }
}
