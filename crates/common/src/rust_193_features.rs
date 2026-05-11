//! Rust 1.93.0 通用工具 特性模块
#![allow(clippy::incompatible_msrv)]

/// 使用 `String::into_raw_parts` 获取底层指针信息并安全重建
pub fn string_into_raw_parts_roundtrip(s: String) -> String {
    let (ptr, len, cap) = s.into_raw_parts();
    // SAFETY: ptr/len/cap 来自合法的 String
    unsafe { String::from_raw_parts(ptr, len, cap) }
}

/// 使用 `Vec::into_raw_parts` 获取底层指针信息并安全重建
pub fn vec_into_raw_parts_roundtrip<T>(v: Vec<T>) -> Vec<T> {
    let (ptr, len, cap) = v.into_raw_parts();
    // SAFETY: ptr/len/cap 来自合法的 Vec
    unsafe { Vec::from_raw_parts(ptr, len, cap) }
}

/// 使用 `slice::as_array` 将切片转为定长数组引用
pub fn slice_as_fixed_array<T, const N: usize>(slice: &[T]) -> Option<&[T; N]> {
    slice.as_array::<N>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_roundtrip() {
        let s = String::from("common utilities");
        assert_eq!(string_into_raw_parts_roundtrip(s), "common utilities");
    }

    #[test]
    fn test_vec_roundtrip() {
        let v = vec![1, 2, 3, 4, 5];
        assert_eq!(vec_into_raw_parts_roundtrip(v), vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_slice_as_fixed_array() {
        let data = [10, 20, 30];
        assert_eq!(slice_as_fixed_array::<i32, 3>(&data), Some(&[10, 20, 30]));
        assert_eq!(slice_as_fixed_array::<i32, 5>(&data), None);
    }
}
