//! Rust 1.97 特性跟踪模块 —— 网络编程
#![allow(clippy::incompatible_msrv)]

use std::collections::VecDeque;
use std::io;

/// # Rust 1.97 特性演示
///
/// 展示 `io::Error::other` 和 `VecDeque::resize` 在网络编程中的应用。
pub struct Rust197Features;

impl Rust197Features {
    /// 使用 `io::Error::other` 快速创建网络错误
    pub fn network_error(reason: &str) -> io::Error {
        io::Error::other(reason)
    }

    /// 使用 `VecDeque::resize` 调整网络包缓冲区
    pub fn resize_packet_buffer(packets: VecDeque<u8>, frame_size: usize) -> VecDeque<u8> {
        let mut buf = packets;
        buf.resize(frame_size, 0);
        buf
    }

    /// 结合两者进行网络帧验证
    pub fn validate_frame(frame: VecDeque<u8>, min_size: usize) -> Result<VecDeque<u8>, io::Error> {
        if frame.len() < min_size {
            return Err(io::Error::other("帧长度不足"));
        }
        let mut buf = frame;
        buf.resize(min_size, 0);
        Ok(buf)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_network_error() {
        let err = Rust197Features::network_error("连接超时");
        assert_eq!(err.kind(), io::ErrorKind::Other);
    }

    #[test]
    fn test_resize_packet_buffer() {
        let buf = VecDeque::from(vec![0x01, 0x02]);
        let result = Rust197Features::resize_packet_buffer(buf, 4);
        assert_eq!(result.len(), 4);
        assert_eq!(Vec::from(result), vec![0x01, 0x02, 0x00, 0x00]);
    }

    #[test]
    fn test_validate_frame() {
        let frame = VecDeque::from(vec![0xFF; 10]);
        let result = Rust197Features::validate_frame(frame, 8).unwrap();
        assert_eq!(result.len(), 8);

        let small = VecDeque::from(vec![0x01]);
        assert!(Rust197Features::validate_frame(small, 8).is_err());
    }
}
