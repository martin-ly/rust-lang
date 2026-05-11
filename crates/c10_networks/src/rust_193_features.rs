//! Rust 1.93.0 网络编程 特性模块
#![allow(clippy::incompatible_msrv)]

/// 使用 `String::into_raw_parts` 获取网络数据包的字符串元信息
pub fn string_packet_meta(s: String) -> (usize, usize, usize) {
    let (ptr, len, cap) = s.into_raw_parts();
    let meta = (ptr as usize, len, cap);
    // SAFETY: 立即重建以避免泄漏
    let _ = unsafe { String::from_raw_parts(ptr, len, cap) };
    meta
}

/// 使用 `char::MAX_LEN_UTF8` 预分配网络消息 UTF-8 编码缓冲区
pub fn utf8_encode_buffer_size() -> usize {
    char::MAX_LEN_UTF8
}

/// 使用 `char::MAX_LEN_UTF16` 预分配网络消息 UTF-16 编码缓冲区
pub fn utf16_encode_buffer_size() -> usize {
    char::MAX_LEN_UTF16
}

/// 使用 `slice::as_array` 解析 4 字节网络头部
pub fn parse_network_header(slice: &[u8]) -> Option<&[u8; 4]> {
    slice.as_array::<4>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_packet_meta() {
        let s = String::from("network payload");
        let (_, len, _) = string_packet_meta(s);
        assert_eq!(len, "network payload".len());
    }

    #[test]
    fn test_utf8_buffer_size() {
        assert_eq!(utf8_encode_buffer_size(), 4);
    }

    #[test]
    fn test_utf16_buffer_size() {
        assert_eq!(utf16_encode_buffer_size(), 2);
    }

    #[test]
    fn test_parse_network_header() {
        let header = [0x45, 0x00, 0x00, 0x3c];
        assert_eq!(parse_network_header(&header), Some(&[0x45, 0x00, 0x00, 0x3c]));
        assert_eq!(parse_network_header(&[0x45, 0x00]), None);
    }
}
