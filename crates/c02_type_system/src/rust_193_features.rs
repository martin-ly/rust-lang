//! Rust 1.93.0 类型系统 特性模块
#![allow(clippy::incompatible_msrv)]

/// 演示 `char::MAX_LEN_UTF8` 和 `char::MAX_LEN_UTF16`
pub fn char_encoding_limits() -> (usize, usize) {
    (char::MAX_LEN_UTF8, char::MAX_LEN_UTF16)
}

/// 使用 `slice::as_array` 将定长切片转为数组引用
pub fn get_array_ref<const N: usize>(slice: &[i32]) -> Option<&[i32; N]> {
    slice.as_array::<N>()
}

/// 结合类型推断演示 `as_array` 与 `copied`
pub fn slice_to_owned_array(slice: &[i32]) -> Option<[i32; 3]> {
    slice.as_array::<3>().copied()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_char_encoding_limits() {
        let (utf8, utf16) = char_encoding_limits();
        assert_eq!(utf8, 4);
        assert_eq!(utf16, 2);
    }

    #[test]
    fn test_slice_as_array_some() {
        let data = [1, 2, 3, 4];
        assert_eq!(get_array_ref::<4>(&data), Some(&[1, 2, 3, 4]));
    }

    #[test]
    fn test_slice_as_array_none() {
        let data = [1, 2];
        assert_eq!(get_array_ref::<4>(&data), None);
    }

    #[test]
    fn test_slice_to_owned_array() {
        assert_eq!(slice_to_owned_array(&[7, 8, 9]), Some([7, 8, 9]));
        assert_eq!(slice_to_owned_array(&[7, 8]), None);
    }
}
