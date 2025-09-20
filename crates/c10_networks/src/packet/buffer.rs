//! 数据包缓冲区管理

use crate::error::{NetworkError, NetworkResult};
#[cfg(test)]
use bytes::Bytes;
use std::collections::VecDeque;
use std::time::{Duration, Instant};

/// 缓冲区错误类型
#[derive(Debug, thiserror::Error)]
pub enum BufferError {
    #[error("Buffer is full")]
    Full,
    #[error("Buffer is empty")]
    Empty,
    #[error("Invalid buffer size: {0}")]
    InvalidSize(usize),
    #[error("Timeout while waiting for data")]
    Timeout,
    #[error("Buffer overflow")]
    Overflow,
}

impl From<BufferError> for NetworkError {
    fn from(err: BufferError) -> Self {
        NetworkError::Other(err.to_string())
    }
}

/// 数据包缓冲区配置
#[derive(Debug, Clone)]
pub struct BufferConfig {
    pub max_size: usize,
    pub max_packets: usize,
    pub timeout: Option<Duration>,
    pub auto_flush: bool,
    pub flush_interval: Duration,
}

impl Default for BufferConfig {
    fn default() -> Self {
        Self {
            max_size: 1024 * 1024, // 1MB
            max_packets: 1000,
            timeout: Some(Duration::from_secs(30)),
            auto_flush: true,
            flush_interval: Duration::from_millis(100),
        }
    }
}

/// 数据包缓冲区
pub struct PacketBuffer {
    config: BufferConfig,
    packets: VecDeque<super::Packet>,
    total_size: usize,
    last_flush: Instant,
    created_at: Instant,
}

impl PacketBuffer {
    /// 创建新的数据包缓冲区
    pub fn new(config: BufferConfig) -> Self {
        Self {
            config,
            packets: VecDeque::new(),
            total_size: 0,
            last_flush: Instant::now(),
            created_at: Instant::now(),
        }
    }

    /// 添加数据包到缓冲区
    pub fn push(&mut self, packet: super::Packet) -> Result<(), BufferError> {
        let packet_size = packet.total_size();

        // 检查缓冲区是否已满
        if self.packets.len() >= self.config.max_packets {
            return Err(BufferError::Full);
        }

        if self.total_size + packet_size > self.config.max_size {
            return Err(BufferError::Overflow);
        }

        self.total_size += packet_size;
        self.packets.push_back(packet);

        // 自动刷新检查
        if self.config.auto_flush && self.should_flush() {
            self.flush();
        }

        Ok(())
    }

    /// 从缓冲区取出数据包
    pub fn pop(&mut self) -> Option<super::Packet> {
        if let Some(packet) = self.packets.pop_front() {
            self.total_size -= packet.total_size();
            Some(packet)
        } else {
            None
        }
    }

    /// 查看下一个数据包但不移除
    pub fn peek(&self) -> Option<&super::Packet> {
        self.packets.front()
    }

    /// 检查缓冲区是否为空
    pub fn is_empty(&self) -> bool {
        self.packets.is_empty()
    }

    /// 检查缓冲区是否已满
    pub fn is_full(&self) -> bool {
        self.packets.len() >= self.config.max_packets || self.total_size >= self.config.max_size
    }

    /// 获取缓冲区中的数据包数量
    pub fn len(&self) -> usize {
        self.packets.len()
    }

    /// 获取缓冲区总大小
    pub fn total_size(&self) -> usize {
        self.total_size
    }

    /// 清空缓冲区
    pub fn clear(&mut self) {
        self.packets.clear();
        self.total_size = 0;
    }

    /// 检查是否应该刷新缓冲区
    fn should_flush(&self) -> bool {
        self.last_flush.elapsed() >= self.config.flush_interval
    }

    /// 刷新缓冲区（重置刷新时间）
    fn flush(&mut self) {
        self.last_flush = Instant::now();
    }

    /// 获取缓冲区统计信息
    pub fn stats(&self) -> BufferStats {
        BufferStats {
            packet_count: self.packets.len(),
            total_size: self.total_size,
            max_size: self.config.max_size,
            max_packets: self.config.max_packets,
            utilization: self.total_size as f64 / self.config.max_size as f64,
            age: self.created_at.elapsed(),
        }
    }

    /// 等待数据包到达
    pub async fn wait_for_packet(&mut self) -> NetworkResult<super::Packet> {
        let timeout_duration = self.config.timeout.unwrap_or(Duration::from_secs(30));
        let start = Instant::now();

        while self.is_empty() {
            if start.elapsed() > timeout_duration {
                return Err(BufferError::Timeout.into());
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }

        self.pop().ok_or_else(|| BufferError::Empty.into())
    }

    /// 批量获取数据包
    pub fn drain(&mut self, max_count: usize) -> Vec<super::Packet> {
        let mut result = Vec::new();
        let count = std::cmp::min(max_count, self.packets.len());

        for _ in 0..count {
            if let Some(packet) = self.pop() {
                result.push(packet);
            }
        }

        result
    }

    /// 按类型过滤数据包
    pub fn filter_by_type(&mut self, packet_type: &super::PacketType) -> Vec<super::Packet> {
        let mut result = Vec::new();
        let mut remaining = VecDeque::new();

        while let Some(packet) = self.packets.pop_front() {
            if packet.packet_type() == packet_type {
                result.push(packet);
            } else {
                remaining.push_back(packet);
            }
        }

        self.packets = remaining;
        self.recalculate_size();
        result
    }

    /// 重新计算缓冲区大小
    fn recalculate_size(&mut self) {
        self.total_size = self.packets.iter().map(|p| p.total_size()).sum();
    }
}

/// 缓冲区统计信息
#[derive(Debug, Clone)]
pub struct BufferStats {
    pub packet_count: usize,
    pub total_size: usize,
    pub max_size: usize,
    pub max_packets: usize,
    pub utilization: f64,
    pub age: Duration,
}

/// 环形缓冲区
pub struct RingBuffer {
    buffer: Vec<u8>,
    head: usize,
    tail: usize,
    size: usize,
    capacity: usize,
}

impl RingBuffer {
    /// 创建新的环形缓冲区
    pub fn new(capacity: usize) -> Self {
        Self {
            buffer: vec![0; capacity],
            head: 0,
            tail: 0,
            size: 0,
            capacity,
        }
    }

    /// 写入数据到缓冲区
    pub fn write(&mut self, data: &[u8]) -> Result<usize, BufferError> {
        if data.is_empty() {
            return Ok(0);
        }

        let available = self.capacity - self.size;
        let to_write = std::cmp::min(data.len(), available);

        if to_write == 0 {
            return Err(BufferError::Full);
        }

        for &byte in data.iter().take(to_write) {
            self.buffer[self.tail] = byte;
            self.tail = (self.tail + 1) % self.capacity;
        }

        self.size += to_write;
        Ok(to_write)
    }

    /// 从缓冲区读取数据
    pub fn read(&mut self, buffer: &mut [u8]) -> Result<usize, BufferError> {
        if buffer.is_empty() || self.size == 0 {
            return Ok(0);
        }

        let to_read = std::cmp::min(buffer.len(), self.size);

        for (i, &byte) in self.buffer.iter().skip(self.head).take(to_read).enumerate() {
            buffer[i] = byte;
            self.head = (self.head + 1) % self.capacity;
        }

        self.size -= to_read;
        Ok(to_read)
    }

    /// 检查缓冲区是否为空
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// 检查缓冲区是否已满
    pub fn is_full(&self) -> bool {
        self.size == self.capacity
    }

    /// 获取可用空间
    pub fn available(&self) -> usize {
        self.capacity - self.size
    }

    /// 获取已使用空间
    pub fn used(&self) -> usize {
        self.size
    }

    /// 清空缓冲区
    pub fn clear(&mut self) {
        self.head = 0;
        self.tail = 0;
        self.size = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_packet_buffer_basic() {
        let config = BufferConfig::default();
        let mut buffer = PacketBuffer::new(config);

        let packet = super::super::Packet::new(
            super::super::PacketType::Raw,
            Bytes::copy_from_slice(b"test data"),
        );

        assert!(buffer.push(packet.clone()).is_ok());
        assert!(!buffer.is_empty());
        assert_eq!(buffer.len(), 1);

        let popped = buffer.pop().unwrap();
        assert_eq!(popped.payload, packet.payload);
        assert!(buffer.is_empty());
    }

    #[test]
    fn test_packet_buffer_overflow() {
        let config = BufferConfig {
            max_size: 10_000,
            max_packets: 10,
            ..Default::default()
        };
        let mut buffer = PacketBuffer::new(config);

        // 添加大量数据包直到溢出
        for i in 0..20 {
            let packet = super::super::Packet::new(
                super::super::PacketType::Raw,
                Bytes::copy_from_slice(format!("data {}", i).as_bytes()),
            );

            if i < 10 {
                assert!(buffer.push(packet).is_ok());
            } else {
                assert!(buffer.push(packet).is_err());
            }
        }
    }

    #[test]
    fn test_ring_buffer() {
        let mut ring = RingBuffer::new(10);

        // 写入数据
        let data = b"hello";
        assert_eq!(ring.write(data).unwrap(), 5);
        assert_eq!(ring.used(), 5);
        assert_eq!(ring.available(), 5);

        // 读取数据
        let mut buffer = [0u8; 10];
        assert_eq!(ring.read(&mut buffer).unwrap(), 5);
        assert_eq!(&buffer[..5], b"hello");
        assert_eq!(ring.used(), 0);
        assert_eq!(ring.available(), 10);
    }

    #[test]
    fn test_ring_buffer_overflow() {
        let mut ring = RingBuffer::new(5);

        // 写入超过容量的数据
        let data = b"hello world";
        assert_eq!(ring.write(data).unwrap(), 5);
        assert!(ring.is_full());

        // 再次写入应该失败
        assert!(ring.write(b"x").is_err());
    }
}
