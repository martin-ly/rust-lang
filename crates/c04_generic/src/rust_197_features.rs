//! Rust 1.97.0 stable 特性 —— 泛型系统
//!
//! 本模块演示 Rust 1.97.0 稳定化、且与泛型/常量上下文相关的 API。

/// Rust 1.97 泛型特性演示
///
/// 涉及特性：
/// - `Option::as_slice` / `Option::as_mut_slice`（泛型包装）
/// - `const size_of_val` / `const align_of_val`
/// - `BuildHasherDefault::new` const 稳定
pub struct Rust197GenericFeatures;

impl Rust197GenericFeatures {
    /// 泛型地将 `Option<T>` 转为只读切片
    pub fn option_as_slice<T>(opt: &Option<T>) -> &[T] {
        opt.as_slice()
    }

    /// 泛型地将 `Option<T>` 转为可变切片
    pub fn option_as_mut_slice<T>(opt: &mut Option<T>) -> &mut [T] {
        opt.as_mut_slice()
    }

    /// 编译期计算 `Sized` 泛型值的大小
    pub const fn const_size_of_val<T: Sized>(value: &T) -> usize {
        std::mem::size_of_val(value)
    }

    /// 编译期计算 `Sized` 泛型值的对齐
    pub const fn const_align_of_val<T: Sized>(value: &T) -> usize {
        std::mem::align_of_val(value)
    }

    /// 构造默认哈希器
    pub const fn const_build_hasher()
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
