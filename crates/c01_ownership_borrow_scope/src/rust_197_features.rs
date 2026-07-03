//! Rust 1.97 Nightly 前瞻/候选特性 —— 所有权、借用与作用域
//!
//! 本模块演示 Rust 1.97.0 候选/nightly 中的所有权/指针相关 API。
//! 由于当前工具链为 Rust 1.96.1，实际代码使用等价的 1.96.1 兼容实现；
//! 对应的 1.97 原生 API 调用以 `#[cfg(nightly)]` 分支保留，可通过
//! `RUSTFLAGS="--cfg nightly" cargo build` 启用。
#![allow(clippy::incompatible_msrv)]
#![allow(unexpected_cfgs)]
#![allow(clippy::borrowed_box)]

use std::rc::Rc;
use std::sync::Arc;

/// Rust 1.97 所有权/借用特性演示
///
/// 涉及特性：
/// - `Option::as_slice` / `Option::as_mut_slice`
/// - `Box::as_ptr`
/// - `From<&mut [T]>` for `Box<[T]>`, `Rc<[T]>`, `Arc<[T]>`
/// - `const size_of_val` / `const align_of_val`
pub struct Rust197OwnershipFeatures;

impl Rust197OwnershipFeatures {
    /// 将 `Option<T>` 转为只读切片视图
    ///
    /// `Some(x)` → `&[x]`，`None` → `&[]`
    #[cfg(nightly)]
    pub fn option_as_slice<T>(opt: &Option<T>) -> &[T] {
        opt.as_slice()
    }

    #[cfg(not(nightly))]
    pub fn option_as_slice<T>(opt: &Option<T>) -> &[T] {
        match opt {
            Some(x) => std::slice::from_ref(x),
            None => &[],
        }
    }

    /// 将 `Option<T>` 转为可变切片视图
    #[cfg(nightly)]
    pub fn option_as_mut_slice<T>(opt: &mut Option<T>) -> &mut [T] {
        opt.as_mut_slice()
    }

    #[cfg(not(nightly))]
    pub fn option_as_mut_slice<T>(opt: &mut Option<T>) -> &mut [T] {
        match opt {
            Some(x) => std::slice::from_mut(x),
            None => &mut [],
        }
    }

    /// 获取 `Box<T>` 中堆分配对象的裸指针
    #[allow(clippy::borrowed_box)]
    #[cfg(nightly)]
    pub fn box_as_ptr<T>(b: &Box<T>) -> *const T {
        Box::as_ptr(b)
    }

    #[allow(clippy::borrowed_box)]
    #[cfg(not(nightly))]
    pub fn box_as_ptr<T>(b: &Box<T>) -> *const T {
        b.as_ref() as *const T
    }

    /// 将可变切片转换为 `Box<[T]>`
    #[cfg(nightly)]
    pub fn box_from_mut_slice<T: Clone>(slice: &mut [T]) -> Box<[T]> {
        Box::from(slice)
    }

    #[cfg(not(nightly))]
    pub fn box_from_mut_slice<T: Clone>(slice: &mut [T]) -> Box<[T]> {
        slice.to_vec().into_boxed_slice()
    }

    /// 将可变切片转换为 `Rc<[T]>`
    #[cfg(nightly)]
    pub fn rc_from_mut_slice<T: Clone>(slice: &mut [T]) -> Rc<[T]> {
        Rc::from(slice)
    }

    #[cfg(not(nightly))]
    pub fn rc_from_mut_slice<T: Clone>(slice: &mut [T]) -> Rc<[T]> {
        slice.to_vec().into()
    }

    /// 将可变切片转换为 `Arc<[T]>`
    #[cfg(nightly)]
    pub fn arc_from_mut_slice<T: Clone>(slice: &mut [T]) -> Arc<[T]> {
        Arc::from(slice)
    }

    #[cfg(not(nightly))]
    pub fn arc_from_mut_slice<T: Clone>(slice: &mut [T]) -> Arc<[T]> {
        slice.to_vec().into()
    }

    /// 编译期计算值的大小（1.96 兼容版，仅支持 `Sized` 类型）
    #[cfg(nightly)]
    pub const fn const_size_of_val<T: Sized>(value: &T) -> usize {
        std::mem::size_of_val(value)
    }

    #[cfg(not(nightly))]
    pub const fn const_size_of_val<T: Sized>(_: &T) -> usize {
        std::mem::size_of::<T>()
    }

    /// 编译期计算值的对齐（1.96 兼容版，仅支持 `Sized` 类型）
    #[cfg(nightly)]
    pub const fn const_align_of_val<T: Sized>(value: &T) -> usize {
        std::mem::align_of_val(value)
    }

    #[cfg(not(nightly))]
    pub const fn const_align_of_val<T: Sized>(_: &T) -> usize {
        std::mem::align_of::<T>()
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
