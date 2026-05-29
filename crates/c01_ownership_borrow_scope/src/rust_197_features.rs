//! Rust 1.97 特性跟踪模块 —— 所有权、借用与作用域
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 所有权/借用特性演示
///
/// Rust 1.97 稳定化的所有权与指针相关 API：
/// - `Option::as_slice` / `as_mut_slice` — Option 到切片视图
/// - `From<&mut [T]>` for `Box<[T]>`, `Rc<[T]>`, `Arc<[T]>`
/// - `pointer::byte_add` / `byte_offset` / `wrapping_byte_add` — 按字节偏移指针
pub struct Rust197OwnershipFeatures;

impl Rust197OwnershipFeatures {
    /// 使用 `Option::as_slice` 将 Option 转为切片视图
    ///
    /// `Some(x)` → `&[x]`，`None` → `&[]`
    pub fn option_as_slice<T>(opt: &Option<T>) -> &[T] {
        opt.as_slice()
    }

    /// 使用 `Option::as_mut_slice` 将 Option 转为可变切片视图
    pub fn option_as_mut_slice<T>(opt: &mut Option<T>) -> &mut [T] {
        opt.as_mut_slice()
    }

    /// 使用 `From<&mut [T]>` for `Box<[T]>` 转换可变切片
    pub fn mut_slice_to_boxed_slice<T: Clone>(slice: &mut [T]) -> Box<[T]> {
        Box::from(slice)
    }

    /// 使用 `From<&mut [T]>` for `Rc<[T]>` 转换可变切片
    pub fn mut_slice_to_rc_slice<T: Clone>(slice: &mut [T]) -> std::rc::Rc<[T]> {
        std::rc::Rc::from(slice)
    }

    /// 使用 `From<&mut [T]>` for `Arc<[T]>` 转换可变切片
    pub fn mut_slice_to_arc_slice<T: Clone>(slice: &mut [T]) -> std::sync::Arc<[T]> {
        std::sync::Arc::from(slice)
    }

    /// 使用 `pointer::byte_add` 按字节偏移指针
    ///
    /// 替代 `ptr.cast::<u8>().add(offset).cast::<T>()` 的繁琐写法。
    ///
    /// # Safety
    /// 调用者必须确保偏移后的指针仍在有效分配范围内。
    pub unsafe fn offset_by_bytes<T>(ptr: *const T, offset: usize) -> *const T {
        // SAFETY: caller ensures the offset is in-bounds
        unsafe { ptr.byte_add(offset) }
    }

    /// 使用 `pointer::wrapping_byte_add` 进行环绕字节偏移
    pub fn wrapping_offset_bytes<T>(ptr: *const T, offset: usize) -> *const T {
        // wrapping_byte_add is safe
        ptr.wrapping_byte_add(offset)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_option_as_slice_some() {
        let opt = Some(42);
        let slice = Rust197OwnershipFeatures::option_as_slice(&opt);
        assert_eq!(slice, &[42]);
    }

    #[test]
    fn test_option_as_slice_none() {
        let opt: Option<i32> = None;
        let slice = Rust197OwnershipFeatures::option_as_slice(&opt);
        assert!(slice.is_empty());
    }

    #[test]
    fn test_option_as_mut_slice() {
        let mut opt = Some(42);
        let slice = Rust197OwnershipFeatures::option_as_mut_slice(&mut opt);
        slice[0] = 100;
        assert_eq!(opt, Some(100));
    }

    #[test]
    fn test_mut_slice_to_boxed_slice() {
        let mut data = [1, 2, 3];
        let boxed = Rust197OwnershipFeatures::mut_slice_to_boxed_slice(&mut data);
        assert_eq!(&*boxed, &[1, 2, 3]);
    }

    #[test]
    fn test_mut_slice_to_rc_slice() {
        let mut data = [1, 2, 3];
        let rc = Rust197OwnershipFeatures::mut_slice_to_rc_slice(&mut data);
        assert_eq!(&*rc, &[1, 2, 3]);
    }

    #[test]
    fn test_mut_slice_to_arc_slice() {
        let mut data = [1, 2, 3];
        let arc = Rust197OwnershipFeatures::mut_slice_to_arc_slice(&mut data);
        assert_eq!(&*arc, &[1, 2, 3]);
    }

    #[test]
    fn test_offset_by_bytes() {
        let arr = [1u8, 2, 3, 4];
        let ptr = arr.as_ptr();
        let offset = unsafe { Rust197OwnershipFeatures::offset_by_bytes(ptr, 2) };
        assert_eq!(offset as usize, ptr as usize + 2);
    }

    #[test]
    fn test_wrapping_offset_bytes() {
        let arr = [0u8; 4];
        let ptr = arr.as_ptr();
        let wrapped = Rust197OwnershipFeatures::wrapping_offset_bytes(ptr, 1);
        assert_eq!(wrapped as usize, ptr as usize + 1);
    }
}
