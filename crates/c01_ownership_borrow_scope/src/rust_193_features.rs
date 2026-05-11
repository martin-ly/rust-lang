//! Rust 1.93.0 所有权与内存 特性模块
#![allow(clippy::incompatible_msrv)]

use std::mem::MaybeUninit;

/// 演示 `String::into_raw_parts` 的往返不泄漏
pub fn string_raw_parts_roundtrip(s: String) -> String {
    let (ptr, len, cap) = s.into_raw_parts();
    // SAFETY: ptr/len/cap 来自刚刚 into_raw_parts 的合法 String
    unsafe { String::from_raw_parts(ptr, len, cap) }
}

/// 演示 `Vec::into_raw_parts` 的泛型往返
pub fn vec_raw_parts_roundtrip<T>(v: Vec<T>) -> Vec<T> {
    let (ptr, len, cap) = v.into_raw_parts();
    // SAFETY: ptr/len/cap 来自刚刚 into_raw_parts 的合法 Vec
    unsafe { Vec::from_raw_parts(ptr, len, cap) }
}

/// 使用 `MaybeUninit` 1.93 API 安全初始化并读取值
pub fn maybeuninit_init_and_read() -> i32 {
    let mut val = MaybeUninit::uninit();
    val.write(42);
    // SAFETY: 刚刚通过 write 完成初始化
    let r = unsafe { val.assume_init_ref() };
    *r
}

/// 使用 `MaybeUninit::assume_init_drop` 手动 drop
pub fn maybeuninit_manual_drop() {
    let mut val = MaybeUninit::new(String::from("drop me"));
    // SAFETY: val 确实包含已初始化的 String
    unsafe { val.assume_init_drop() };
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_roundtrip() {
        let s = String::from("hello rust 193");
        assert_eq!(string_raw_parts_roundtrip(s), "hello rust 193");
    }

    #[test]
    fn test_vec_roundtrip() {
        let v = vec![10, 20, 30];
        assert_eq!(vec_raw_parts_roundtrip(v), vec![10, 20, 30]);
    }

    #[test]
    fn test_maybeuninit_read() {
        assert_eq!(maybeuninit_init_and_read(), 42);
    }

    #[test]
    fn test_maybeuninit_drop() {
        maybeuninit_manual_drop();
    }
}
