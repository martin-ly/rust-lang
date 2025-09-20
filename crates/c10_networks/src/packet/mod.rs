//! 数据包处理模块
//!
//! 本模块提供了基于 Rust 1.89 的数据包处理功能，
//! 包括数据包解析、序列化、缓冲管理等功能。

pub mod buffer;
pub mod parser;
pub mod serializer;

pub use buffer::{BufferError, PacketBuffer};
pub use parser::{PacketParser, ParseResult};
pub use serializer::{PacketSerializer, SerializeResult};

// use crate::error::{NetworkError, NetworkResult}; // 暂时注释掉未使用的导入
use bytes::{Bytes, BytesMut};
use serde::{Deserialize, Serialize};
use std::fmt;

/// 数据包类型
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PacketType {
    /// 原始字节数据包
    Raw,
    /// HTTP 数据包
    Http,
    /// WebSocket 数据包
    WebSocket,
    /// TCP 数据包
    Tcp,
    /// UDP 数据包
    Udp,
    /// 自定义数据包
    Custom(String),
}

/// 数据包头部
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PacketHeader {
    pub packet_type: PacketType,
    pub length: u32,
    pub timestamp: u64,
    pub sequence_number: Option<u64>,
    pub flags: u32,
}

impl PacketHeader {
    /// 创建新的数据包头部
    pub fn new(packet_type: PacketType, length: u32) -> Self {
        Self {
            packet_type,
            length,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap_or_default()
                .as_millis() as u64,
            sequence_number: None,
            flags: 0,
        }
    }

    /// 设置序列号
    pub fn with_sequence_number(mut self, seq: u64) -> Self {
        self.sequence_number = Some(seq);
        self
    }

    /// 设置标志位
    pub fn with_flags(mut self, flags: u32) -> Self {
        self.flags = flags;
        self
    }
}

/// 数据包
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Packet {
    pub header: PacketHeader,
    pub payload: Bytes,
}

impl Packet {
    /// 创建新的数据包
    pub fn new(packet_type: PacketType, payload: Bytes) -> Self {
        let length = payload.len() as u32;
        let header = PacketHeader::new(packet_type, length);
        Self { header, payload }
    }

    /// 创建带序列号的数据包
    pub fn with_sequence(packet_type: PacketType, payload: Bytes, seq: u64) -> Self {
        let length = payload.len() as u32;
        let header = PacketHeader::new(packet_type, length).with_sequence_number(seq);
        Self { header, payload }
    }

    /// 获取数据包总大小
    pub fn total_size(&self) -> usize {
        std::mem::size_of::<PacketHeader>() + self.payload.len()
    }

    /// 检查数据包是否为空
    pub fn is_empty(&self) -> bool {
        self.payload.is_empty()
    }

    /// 获取数据包类型
    pub fn packet_type(&self) -> &PacketType {
        &self.header.packet_type
    }

    /// 获取载荷长度
    pub fn payload_length(&self) -> usize {
        self.payload.len()
    }
}

impl fmt::Display for Packet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Packet {{ type: {:?}, length: {}, seq: {:?}, flags: 0x{:x} }}",
            self.header.packet_type,
            self.header.length,
            self.header.sequence_number,
            self.header.flags
        )
    }
}

/// 数据包构建器
pub struct PacketBuilder {
    packet_type: PacketType,
    payload: BytesMut,
    sequence_number: Option<u64>,
    flags: u32,
}

impl PacketBuilder {
    /// 创建新的数据包构建器
    pub fn new(packet_type: PacketType) -> Self {
        Self {
            packet_type,
            payload: BytesMut::new(),
            sequence_number: None,
            flags: 0,
        }
    }

    /// 添加数据到载荷
    pub fn add_data(&mut self, data: &[u8]) -> &mut Self {
        self.payload.extend_from_slice(data);
        self
    }

    /// 设置序列号
    pub fn sequence_number(&mut self, seq: u64) -> &mut Self {
        self.sequence_number = Some(seq);
        self
    }

    /// 设置标志位
    pub fn flags(&mut self, flags: u32) -> &mut Self {
        self.flags = flags;
        self
    }

    /// 构建数据包
    pub fn build(self) -> Packet {
        let length = self.payload.len() as u32;
        let mut header = PacketHeader::new(self.packet_type, length).with_flags(self.flags);

        if let Some(seq) = self.sequence_number {
            header.sequence_number = Some(seq);
        }

        Packet {
            header,
            payload: self.payload.freeze(),
        }
    }
}

/// 数据包统计信息
#[derive(Debug, Clone, Default)]
pub struct PacketStats {
    pub total_packets: u64,
    pub total_bytes: u64,
    pub packets_by_type: std::collections::HashMap<PacketType, u64>,
    pub bytes_by_type: std::collections::HashMap<PacketType, u64>,
    pub average_packet_size: f64,
    pub largest_packet_size: usize,
    pub smallest_packet_size: usize,
}

impl PacketStats {
    /// 创建新的统计信息
    pub fn new() -> Self {
        Self::default()
    }

    /// 添加数据包到统计
    pub fn add_packet(&mut self, packet: &Packet) {
        self.total_packets += 1;
        self.total_bytes += packet.payload.len() as u64;

        let packet_type = packet.packet_type().clone();
        *self.packets_by_type.entry(packet_type.clone()).or_insert(0) += 1;
        *self.bytes_by_type.entry(packet_type).or_insert(0) += packet.payload.len() as u64;

        let packet_size = packet.payload.len();
        if packet_size > self.largest_packet_size {
            self.largest_packet_size = packet_size;
        }
        if self.smallest_packet_size == 0 || packet_size < self.smallest_packet_size {
            self.smallest_packet_size = packet_size;
        }

        self.average_packet_size = self.total_bytes as f64 / self.total_packets as f64;
    }

    /// 重置统计信息
    pub fn reset(&mut self) {
        *self = Self::new();
    }

    /// 获取指定类型的数据包数量
    pub fn packets_of_type(&self, packet_type: &PacketType) -> u64 {
        self.packets_by_type.get(packet_type).copied().unwrap_or(0)
    }

    /// 获取指定类型的数据包字节数
    pub fn bytes_of_type(&self, packet_type: &PacketType) -> u64 {
        self.bytes_by_type.get(packet_type).copied().unwrap_or(0)
    }
}

/// 数据包过滤器
pub struct PacketFilter {
    allowed_types: std::collections::HashSet<PacketType>,
    min_size: Option<usize>,
    max_size: Option<usize>,
    sequence_range: Option<(u64, u64)>,
}

impl PacketFilter {
    /// 创建新的过滤器
    pub fn new() -> Self {
        Self {
            allowed_types: std::collections::HashSet::new(),
            min_size: None,
            max_size: None,
            sequence_range: None,
        }
    }

    /// 允许指定的数据包类型
    pub fn allow_type(mut self, packet_type: PacketType) -> Self {
        self.allowed_types.insert(packet_type);
        self
    }

    /// 设置最小数据包大小
    pub fn min_size(mut self, size: usize) -> Self {
        self.min_size = Some(size);
        self
    }

    /// 设置最大数据包大小
    pub fn max_size(mut self, size: usize) -> Self {
        self.max_size = Some(size);
        self
    }

    /// 设置序列号范围
    pub fn sequence_range(mut self, start: u64, end: u64) -> Self {
        self.sequence_range = Some((start, end));
        self
    }

    /// 检查数据包是否通过过滤器
    pub fn matches(&self, packet: &Packet) -> bool {
        // 检查类型
        if !self.allowed_types.is_empty() && !self.allowed_types.contains(packet.packet_type()) {
            return false;
        }

        // 检查大小
        let packet_size = packet.payload.len();
        if let Some(min_size) = self.min_size
            && packet_size < min_size {
                return false;
            }
        if let Some(max_size) = self.max_size
            && packet_size > max_size {
                return false;
            }

        // 检查序列号
        if let Some((start, end)) = self.sequence_range {
            if let Some(seq) = packet.header.sequence_number {
                if seq < start || seq > end {
                    return false;
                }
            } else {
                return false;
            }
        }

        true
    }
}

impl Default for PacketFilter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_packet_creation() {
        let payload = Bytes::copy_from_slice(b"test data");
        let packet = Packet::new(PacketType::Raw, payload.clone());

        assert_eq!(packet.packet_type(), &PacketType::Raw);
        assert_eq!(packet.payload_length(), payload.len());
        assert!(!packet.is_empty());
    }

    #[test]
    fn test_packet_builder() {
        let mut builder = PacketBuilder::new(PacketType::Http);
        builder.add_data(b"GET /");
        builder.add_data(b" HTTP/1.1");
        builder.sequence_number(123);
        builder.flags(0x01);
        let packet = builder.build();

        assert_eq!(packet.packet_type(), &PacketType::Http);
        assert_eq!(packet.payload, Bytes::copy_from_slice(b"GET / HTTP/1.1"));
        assert_eq!(packet.header.sequence_number, Some(123));
        assert_eq!(packet.header.flags, 0x01);
    }

    #[test]
    fn test_packet_stats() {
        let mut stats = PacketStats::new();

        let packet1 = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"data1"));
        let packet2 = Packet::new(PacketType::Http, Bytes::copy_from_slice(b"data2"));

        stats.add_packet(&packet1);
        stats.add_packet(&packet2);

        assert_eq!(stats.total_packets, 2);
        assert_eq!(stats.packets_of_type(&PacketType::Raw), 1);
        assert_eq!(stats.packets_of_type(&PacketType::Http), 1);
    }

    #[test]
    fn test_packet_filter() {
        let filter = PacketFilter::new()
            .allow_type(PacketType::Http)
            .min_size(5)
            .max_size(10);

        let packet1 = Packet::new(PacketType::Http, Bytes::copy_from_slice(b"GET /"));
        let packet2 = Packet::new(PacketType::Raw, Bytes::copy_from_slice(b"data"));
        let packet3 = Packet::new(PacketType::Http, Bytes::copy_from_slice(b"very long data"));

        assert!(filter.matches(&packet1));
        assert!(!filter.matches(&packet2)); // 类型不匹配
        assert!(!filter.matches(&packet3)); // 大小超出范围
    }
}
