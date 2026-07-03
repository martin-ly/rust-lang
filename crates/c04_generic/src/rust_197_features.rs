//! Rust 1.97 稳定特性 —— 泛型系统
//!
//! 本模块演示 Rust 1.97 中稳定化、且与泛型/常量上下文相关的 API。
//! 实际代码使用等价的 Rust 1.96 兼容实现；1.97 原生调用以 `#[cfg(nightly)]`
//! 分支保留，可通过 `RUSTFLAGS="--cfg nightly" cargo build` 启用。
#![allow(clippy::incompatible_msrv)]
#![allow(unexpected_cfgs)]
#![allow(clippy::borrowed_box)]

/// Rust 1.97 泛型特性演示
///
/// 涉及特性：
/// - `Option::as_slice` / `Option::as_mut_slice`（泛型包装）
/// - `const size_of_val` / `const align_of_val`
/// - `BuildHasherDefault::new` const 稳定
pub struct Rust197GenericFeatures;

impl Rust197GenericFeatures {
    /// 泛型地将 `Option<T>` 转为只读切片
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

    /// 泛型地将 `Option<T>` 转为可变切片
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

    /// 编译期计算 `Sized` 泛型值的大小
    #[cfg(nightly)]
    pub const fn const_size_of_val<T: Sized>(value: &T) -> usize {
        std::mem::size_of_val(value)
    }

    #[cfg(not(nightly))]
    pub const fn const_size_of_val<T: Sized>(_: &T) -> usize {
        std::mem::size_of::<T>()
    }

    /// 编译期计算 `Sized` 泛型值的对齐
    #[cfg(nightly)]
    pub const fn const_align_of_val<T: Sized>(value: &T) -> usize {
        std::mem::align_of_val(value)
    }

    #[cfg(not(nightly))]
    pub const fn const_align_of_val<T: Sized>(_: &T) -> usize {
        std::mem::align_of::<T>()
    }

    /// 构造默认哈希器
    #[cfg(nightly)]
    pub const fn const_build_hasher()
    -> std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher> {
        std::hash::BuildHasherDefault::new()
    }

    #[cfg(not(nightly))]
    pub fn const_build_hasher()
    -> std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher> {
        std::hash::BuildHasherDefault::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_option_as_slice() {
        let opt = Some(42);
        assert_eq!(Rust197GenericFeatures::option_as_slice(&opt), &[42]);
        let none: Option<i32> = None;
        assert!(Rust197GenericFeatures::option_as_slice(&none).is_empty());
    }

    #[test]
    fn test_option_as_mut_slice() {
        let mut opt = Some(String::from("hello"));
        let slice = Rust197GenericFeatures::option_as_mut_slice(&mut opt);
        slice[0].push_str(" world");
        assert_eq!(opt, Some(String::from("hello world")));
    }

    #[test]
    fn test_const_size_align_of_val() {
        let value = [0u64; 4];
        assert_eq!(Rust197GenericFeatures::const_size_of_val(&value), 32);
        assert_eq!(Rust197GenericFeatures::const_align_of_val(&value), 8);
    }

    #[test]
    fn test_const_build_hasher() {
        let _ = Rust197GenericFeatures::const_build_hasher();
    }
}
