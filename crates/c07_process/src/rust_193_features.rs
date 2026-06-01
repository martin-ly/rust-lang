//! Rust 1.93.0 进程与性能 特性模块
//! Rust 1.93.0 processperformance features module
#![allow(clippy::incompatible_msrv)]

/// 演示 `String::into_raw_parts` 用于进程间数据元信息提取
/// demonstration `String::into_raw_parts` process
pub fn string_raw_meta(s: String) -> (usize, usize, usize) {
    let (ptr, len, cap) = s.into_raw_parts();
    let meta = (ptr as usize, len, cap);
    // SAFETY: 立即重建，确保不泄漏
    let _ = unsafe { String::from_raw_parts(ptr, len, cap) };
    meta
}

/// 演示 `Vec::into_raw_parts` 用于缓冲区内存分析
/// `Vec::into_raw_parts` memory analysis
pub fn vec_raw_meta<T>(v: Vec<T>) -> (usize, usize, usize) {
    let (ptr, len, cap) = v.into_raw_parts();
    let meta = (ptr as usize, len, cap);
    // SAFETY: 立即重建，确保不泄漏
    let _ = unsafe { Vec::from_raw_parts(ptr, len, cap) };
    meta
}

/// 使用 `slice::as_array` 解析固定长度头部
pub fn parse_fixed_header(slice: &[u8]) -> Option<&[u8; 4]> {
    slice.as_array::<4>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_raw_meta() {
        let s = String::from("process data");
        let (_, len, _) = string_raw_meta(s.clone());
        assert_eq!(len, "process data".len());
    }

    #[test]
    fn test_vec_raw_meta() {
        let v = vec![0u8; 256];
        let (_, len, cap) = vec_raw_meta(v);
        assert_eq!(len, 256);
        assert!(cap >= 256);
    }

    #[test]
    fn test_parse_fixed_header() {
        let header = [0x01, 0x02, 0x03, 0x04];
        assert_eq!(parse_fixed_header(&header), Some(&[0x01, 0x02, 0x03, 0x04]));
        assert_eq!(parse_fixed_header(&[0x01, 0x02]), None);
    }
}
