//! Rust 1.93.0 泛型 特性模块
#![allow(clippy::incompatible_msrv)]

use std::mem::MaybeUninit;

/// 泛型函数：使用 `MaybeUninit` 初始化固定长度数组并返回
pub fn init_generic_array<T: Copy, const N: usize>(values: [T; N]) -> [T; N] {
    let mut buf = [MaybeUninit::uninit(); N];
    for (i, &v) in values.iter().enumerate() {
        buf[i].write(v);
    }
    // SAFETY: 所有 N 个元素均已通过 write 初始化
    unsafe { std::mem::transmute_copy(&buf) }
}

/// 泛型函数：尝试将切片转为定长数组引用
pub fn try_as_array<T, const N: usize>(slice: &[T]) -> Option<&[T; N]> {
    slice.as_array::<N>()
}

/// 泛型函数：使用 `Vec::into_raw_parts` 展示泛型内存布局
pub fn vec_layout_inspection<T>(v: Vec<T>) -> (usize, usize, usize) {
    let (ptr, len, cap) = v.into_raw_parts();
    let layout = (ptr as usize, len, cap);
    // SAFETY: 立即重建，不泄漏
    let _ = unsafe { Vec::from_raw_parts(ptr, len, cap) };
    layout
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_init_generic_array() {
        assert_eq!(init_generic_array([1, 2, 3]), [1, 2, 3]);
        assert_eq!(init_generic_array([10u8; 5]), [10u8; 5]);
    }

    #[test]
    fn test_try_as_array() {
        let data = ["a", "b", "c"];
        assert_eq!(try_as_array::<&str, 3>(&data), Some(&["a", "b", "c"]));
        assert_eq!(try_as_array::<&str, 5>(&data), None);
    }

    #[test]
    fn test_vec_layout_inspection() {
        let v = vec![1.0f64, 2.0, 3.0];
        let (_, len, cap) = vec_layout_inspection(v);
        assert_eq!(len, 3);
        assert!(cap >= 3);
    }
}
