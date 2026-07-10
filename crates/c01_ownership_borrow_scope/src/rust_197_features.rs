//! Rust 1.97.0 stable 特性 —— 所有权、借用与作用域
//!
//! 本模块演示 Rust 1.97.0 稳定化的所有权/指针相关 API。

use std::rc::Rc;
use std::sync::Arc;

/// Rust 1.97 所有权/借用特性演示
///
/// 涉及特性：
/// - `Option::as_slice` / `Option::as_mut_slice`
/// - `Box::as_ptr`（`Box::<T>::as_ptr` 在 1.97.0 仍为 unstable，此处保留稳定等效实现）
/// - `From<&mut [T]>` for `Box<[T]>`, `Rc<[T]>`, `Arc<[T]>`
/// - `const size_of_val` / `const align_of_val`
pub struct Rust197OwnershipFeatures;

impl Rust197OwnershipFeatures {
    /// 将 `Option<T>` 转为只读切片视图
    ///
    /// `Some(x)` → `&[x]`，`None` → `&[]`
    pub fn option_as_slice<T>(opt: &Option<T>) -> &[T] {
        opt.as_slice()
    }

    /// 将 `Option<T>` 转为可变切片视图
    pub fn option_as_mut_slice<T>(opt: &mut Option<T>) -> &mut [T] {
        opt.as_mut_slice()
    }

    /// 获取 `Box<T>` 中堆分配对象的裸指针
    ///
    /// `Box::<T>::as_ptr` 在 Rust 1.97.0 仍为 unstable，因此使用等效实现。
    #[allow(clippy::borrowed_box)]
    pub fn box_as_ptr<T>(b: &Box<T>) -> *const T {
        b.as_ref() as *const T
    }

    /// 将可变切片转换为 `Box<[T]>`
    pub fn box_from_mut_slice<T: Clone>(slice: &mut [T]) -> Box<[T]> {
        Box::from(slice)
    }

    /// 将可变切片转换为 `Rc<[T]>`
    pub fn rc_from_mut_slice<T: Clone>(slice: &mut [T]) -> Rc<[T]> {
        Rc::from(slice)
    }

    /// 将可变切片转换为 `Arc<[T]>`
    pub fn arc_from_mut_slice<T: Clone>(slice: &mut [T]) -> Arc<[T]> {
        Arc::from(slice)
    }

    /// 编译期计算值的大小（`Sized` 类型）
    pub const fn const_size_of_val<T: Sized>(value: &T) -> usize {
        std::mem::size_of_val(value)
    }

    /// 编译期计算值的对齐（`Sized` 类型）
    pub const fn const_align_of_val<T: Sized>(value: &T) -> usize {
        std::mem::align_of_val(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_option_as_slice_some() {
        let opt = Some(42);
        assert_eq!(Rust197OwnershipFeatures::option_as_slice(&opt), &[42]);
    }

    #[test]
    fn test_option_as_slice_none() {
        let opt: Option<i32> = None;
        assert!(Rust197OwnershipFeatures::option_as_slice(&opt).is_empty());
    }

    #[test]
    fn test_option_as_mut_slice() {
        let mut opt = Some(42);
        let slice = Rust197OwnershipFeatures::option_as_mut_slice(&mut opt);
        slice[0] = 100;
        assert_eq!(opt, Some(100));
    }

    #[test]
    fn test_box_as_ptr() {
        let b = Box::new(42);
        let p = Rust197OwnershipFeatures::box_as_ptr(&b);
        assert_eq!(unsafe { *p }, 42);
    }

    #[test]
    fn test_box_from_mut_slice() {
        let mut slice = [1, 2, 3];
        let boxed = Rust197OwnershipFeatures::box_from_mut_slice(&mut slice);
        assert_eq!(&*boxed, &[1, 2, 3]);
    }

    #[test]
    fn test_rc_from_mut_slice() {
        let mut slice = [1, 2, 3];
        let rc = Rust197OwnershipFeatures::rc_from_mut_slice(&mut slice);
        assert_eq!(&*rc, &[1, 2, 3]);
    }

    #[test]
    fn test_arc_from_mut_slice() {
        let mut slice = [1, 2, 3];
        let arc = Rust197OwnershipFeatures::arc_from_mut_slice(&mut slice);
        assert_eq!(&*arc, &[1, 2, 3]);
    }

    #[test]
    fn test_const_size_align_of_val() {
        const BUF: [u8; 10] = [0; 10];
        const SIZE: usize = Rust197OwnershipFeatures::const_size_of_val(&BUF);
        const ALIGN: usize = Rust197OwnershipFeatures::const_align_of_val(&BUF);
        assert_eq!(SIZE, 10);
        assert_eq!(ALIGN, 1);
    }
}
