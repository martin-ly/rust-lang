//! Rust 1.97 稳定特性 —— 所有权、借用与作用域
//!
//! 本模块演示 Rust 1.97 中稳定化的所有权/指针相关 API。
//! 由于当前工具链为 Rust 1.96，实际代码使用等价的 1.96 兼容实现；
//! 对应的 1.97 原生 API 调用以注释形式保留。
#![allow(clippy::incompatible_msrv)]

/// Rust 1.97 所有权/借用特性演示
///
/// 涉及特性：/// - `Option::as_slice` / `Option::as_mut_slice`
/// - `Box::as_ptr`
/// - `pointer::byte_add` / `pointer::wrapping_byte_add`
/// - `const size_of_val` / `const align_of_val`
pub struct Rust197OwnershipFeatures;

impl Rust197OwnershipFeatures {
    /// 将 `Option<T>` 转为只读切片视图
    ///
    /// `Some(x)` → `&[x]`，`None` → `&[]`
    pub fn option_as_slice<T>(opt: &Option<T>) -> &[T] {
        // 1.97+: opt.as_slice()
        match opt {
            Some(x) => std::slice::from_ref(x),
            None => &[],
        }
    }

    /// 将 `Option<T>` 转为可变切片视图
    pub fn option_as_mut_slice<T>(opt: &mut Option<T>) -> &mut [T] {
        // 1.97+: opt.as_mut_slice()
        match opt {
            Some(x) => std::slice::from_mut(x),
            None => &mut [],
        }
    }

    /// 获取 `Box<T>` 中堆分配对象的裸指针
    pub fn box_as_ptr<T>(b: &Box<T>) -> *const T {
        // 1.97+: Box::as_ptr(b)
        &**b as *const T
    }

    /// 按字节偏移裸指针
    ///
    /// # Safety
    /// 调用者必须确保偏移后的指针仍在有效分配范围内。
    pub unsafe fn byte_add<T>(ptr: *const T, offset: usize) -> *const T {
        // 1.97+: ptr.byte_add(offset)
        (ptr as *const u8).add(offset) as *const T
    }

    /// 按字节进行环绕偏移（不检查有效性）
    pub fn wrapping_byte_add<T>(ptr: *const T, offset: usize) -> *const T {
        // 1.97+: ptr.wrapping_byte_add(offset)
        (ptr as *const u8).wrapping_add(offset) as *const T
    }

    /// 编译期计算值的大小（1.96 兼容版，仅支持 `Sized` 类型）
    pub const fn const_size_of_val<T: Sized>(_: &T) -> usize {
        // 1.97+: std::mem::size_of_val(value)
        std::mem::size_of::<T>()
    }

    /// 编译期计算值的对齐（1.96 兼容版，仅支持 `Sized` 类型）
    pub const fn const_align_of_val<T: Sized>(_: &T) -> usize {
        // 1.97+: std::mem::align_of_val(value)
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
    fn test_byte_add() {
        let arr = [1u8, 2, 3, 4];
        let ptr = arr.as_ptr();
        let offset = unsafe { Rust197OwnershipFeatures::byte_add(ptr, 2) };
        assert_eq!(offset as usize, ptr as usize + 2);
    }

    #[test]
    fn test_wrapping_byte_add() {
        let arr = [0u8; 4];
        let ptr = arr.as_ptr();
        let wrapped = Rust197OwnershipFeatures::wrapping_byte_add(ptr, 1);
        assert_eq!(wrapped as usize, ptr as usize + 1);
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
