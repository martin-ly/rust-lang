//! 数据包序列化器

use crate::error::{NetworkError, NetworkResult};
use bytes::{Bytes, BytesMut};
// use std::fmt; // 暂时注释掉未使用的导入

/// 序列化结果
#[derive(Debug, Clone)]
pub struct SerializeResult {
    pub data: Bytes,
    pub size: usize,
}

/// 数据包序列化器
pub struct PacketSerializer {
    buffer: BytesMut,
    max_size: usize,
}

impl PacketSerializer {
    /// 创建新的数据包序列化器
    pub fn new(max_size: usize) -> Self {
        Self {
            buffer: BytesMut::new(),
            max_size,
        }
    }

    /// 序列化数据包
    pub fn serialize(&mut self, packet: &super::Packet) -> NetworkResult<SerializeResult> {
        self.buffer.clear();
        
        // 序列化头部
        self.serialize_header(&packet.header)?;
        
        // 序列化载荷
        self.buffer.extend_from_slice(&packet.payload);
        
        if self.buffer.len() > self.max_size {
            return Err(NetworkError::Other("Serialized data too large".to_string()));
        }
        
        let size = self.buffer.len();
        let data = self.buffer.split().freeze();
        
        Ok(SerializeResult { data, size })
    }

    /// 序列化数据包头部
    fn serialize_header(&mut self, header: &super::PacketHeader) -> NetworkResult<()> {
        // 序列化数据包类型
        let packet_type_raw = match &header.packet_type {
            super::PacketType::Raw => 0u32,
            super::PacketType::Http => 1u32,
            super::PacketType::WebSocket => 2u32,
            super::PacketType::Tcp => 3u32,
            super::PacketType::Udp => 4u32,
            super::PacketType::Custom(_) => 999u32, // 自定义类型
        };
        
        self.buffer.extend_from_slice(&packet_type_raw.to_be_bytes());
        self.buffer.extend_from_slice(&header.length.to_be_bytes());
        self.buffer.extend_from_slice(&header.timestamp.to_be_bytes());
        
        // 序列化序列号
        let sequence_number = header.sequence_number.unwrap_or(0);
        self.buffer.extend_from_slice(&sequence_number.to_be_bytes());
        
        // 序列化标志位
        self.buffer.extend_from_slice(&header.flags.to_be_bytes());
        
        Ok(())
    }

    /// 批量序列化数据包
    pub fn serialize_batch(&mut self, packets: &[super::Packet]) -> NetworkResult<Vec<SerializeResult>> {
        let mut results = Vec::new();
        
        for packet in packets {
            let result = self.serialize(packet)?;
            results.push(result);
        }
        
        Ok(results)
    }

    /// 清空序列化缓冲区
    pub fn clear(&mut self) {
        self.buffer.clear();
    }

    /// 获取缓冲区大小
    pub fn buffer_size(&self) -> usize {
        self.buffer.len()
    }
}

/// HTTP 请求序列化器
pub struct HttpRequestSerializer;

impl HttpRequestSerializer {
    /// 序列化 HTTP 请求
    pub fn serialize_request(
        method: &str,
        uri: &str,
        version: &str,
        headers: &std::collections::HashMap<String, String>,
        body: Option<&[u8]>,
    ) -> NetworkResult<SerializeResult> {
        let mut buffer = BytesMut::new();
        
        // 序列化请求行
        buffer.extend_from_slice(method.as_bytes());
        buffer.extend_from_slice(b" ");
        buffer.extend_from_slice(uri.as_bytes());
        buffer.extend_from_slice(b" ");
        buffer.extend_from_slice(version.as_bytes());
        buffer.extend_from_slice(b"\r\n");
        
        // 序列化头部
        for (name, value) in headers {
            buffer.extend_from_slice(name.as_bytes());
            buffer.extend_from_slice(b": ");
            buffer.extend_from_slice(value.as_bytes());
            buffer.extend_from_slice(b"\r\n");
        }
        
        // 空行
        buffer.extend_from_slice(b"\r\n");
        
        // 序列化主体
        if let Some(body_data) = body {
            buffer.extend_from_slice(body_data);
        }
        
        let size = buffer.len();
        let data = buffer.freeze();
        
        Ok(SerializeResult { data, size })
    }
}

/// HTTP 响应序列化器
pub struct HttpResponseSerializer;

impl HttpResponseSerializer {
    /// 序列化 HTTP 响应
    pub fn serialize_response(
        version: &str,
        status_code: u16,
        status_text: &str,
        headers: &std::collections::HashMap<String, String>,
        body: Option<&[u8]>,
    ) -> NetworkResult<SerializeResult> {
        let mut buffer = BytesMut::new();
        
        // 序列化状态行
        buffer.extend_from_slice(version.as_bytes());
        buffer.extend_from_slice(b" ");
        buffer.extend_from_slice(&status_code.to_string().as_bytes());
        buffer.extend_from_slice(b" ");
        buffer.extend_from_slice(status_text.as_bytes());
        buffer.extend_from_slice(b"\r\n");
        
        // 序列化头部
        for (name, value) in headers {
            buffer.extend_from_slice(name.as_bytes());
            buffer.extend_from_slice(b": ");
            buffer.extend_from_slice(value.as_bytes());
            buffer.extend_from_slice(b"\r\n");
        }
        
        // 空行
        buffer.extend_from_slice(b"\r\n");
        
        // 序列化主体
        if let Some(body_data) = body {
            buffer.extend_from_slice(body_data);
        }
        
        let size = buffer.len();
        let data = buffer.freeze();
        
        Ok(SerializeResult { data, size })
    }
}

/// WebSocket 帧序列化器
pub struct WebSocketFrameSerializer;

impl WebSocketFrameSerializer {
    /// 序列化 WebSocket 帧
    pub fn serialize_frame(frame: &crate::protocol::websocket::WebSocketFrame) -> NetworkResult<SerializeResult> {
        let mut buffer = BytesMut::new();
        
        // 第一个字节：FIN + RSV + Opcode
        let first_byte = if frame.fin { 0x80 } else { 0x00 };
        let first_byte = first_byte | (frame.opcode.clone() as u8);
        buffer.extend_from_slice(&[first_byte]);
        
        // 第二个字节：MASK + Payload length
        let second_byte = if frame.mask { 0x80 } else { 0x00 };
        
        if frame.payload_length <= 125 {
            buffer.extend_from_slice(&[second_byte | (frame.payload_length as u8)]);
        } else if frame.payload_length <= 65535 {
            buffer.extend_from_slice(&[second_byte | 126]);
            buffer.extend_from_slice(&(frame.payload_length as u16).to_be_bytes());
        } else {
            buffer.extend_from_slice(&[second_byte | 127]);
            buffer.extend_from_slice(&frame.payload_length.to_be_bytes());
        }
        
        // 掩码键
        if frame.mask {
            if let Some(key) = frame.masking_key {
                buffer.extend_from_slice(&key);
            }
        }
        
        // 载荷
        let payload = frame.payload.clone();
        
        // 应用掩码
        if frame.mask {
            if let Some(key) = frame.masking_key {
                let mut masked_payload = payload.to_vec();
                for (i, byte) in masked_payload.iter_mut().enumerate() {
                    *byte ^= key[i % 4];
                }
                buffer.extend_from_slice(&masked_payload);
            } else {
                buffer.extend_from_slice(&payload);
            }
        } else {
            buffer.extend_from_slice(&payload);
        }
        
        let size = buffer.len();
        let data = buffer.freeze();
        
        Ok(SerializeResult { data, size })
    }
}

/// 数据包序列化器工厂
pub struct SerializerFactory;

impl SerializerFactory {
    /// 创建数据包序列化器
    pub fn create_packet_serializer(max_size: usize) -> PacketSerializer {
        PacketSerializer::new(max_size)
    }

    /// 创建 HTTP 请求序列化器
    pub fn create_http_request_serializer() -> HttpRequestSerializer {
        HttpRequestSerializer
    }

    /// 创建 HTTP 响应序列化器
    pub fn create_http_response_serializer() -> HttpResponseSerializer {
        HttpResponseSerializer
    }

    /// 创建 WebSocket 帧序列化器
    pub fn create_websocket_frame_serializer() -> WebSocketFrameSerializer {
        WebSocketFrameSerializer
    }
}

/// 序列化器统计信息
#[derive(Debug, Clone, Default)]
pub struct SerializerStats {
    pub total_serialized: u64,
    pub total_bytes: u64,
    pub average_size: f64,
    pub largest_size: usize,
    pub smallest_size: usize,
    pub errors: u64,
}

impl SerializerStats {
    /// 添加序列化结果到统计
    pub fn add_result(&mut self, result: &SerializeResult) {
        self.total_serialized += 1;
        self.total_bytes += result.size as u64;
        
        if result.size > self.largest_size {
            self.largest_size = result.size;
        }
        
        if self.smallest_size == 0 || result.size < self.smallest_size {
            self.smallest_size = result.size;
        }
        
        self.average_size = self.total_bytes as f64 / self.total_serialized as f64;
    }

    /// 记录错误
    pub fn record_error(&mut self) {
        self.errors += 1;
    }

    /// 重置统计信息
    pub fn reset(&mut self) {
        *self = Self::default();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_packet_serializer() {
        let mut serializer = PacketSerializer::new(1024);
        
        let packet = super::super::Packet::new(
            super::super::PacketType::Raw,
            Bytes::copy_from_slice(b"test data")
        );
        
        let result = serializer.serialize(&packet).unwrap();
        assert!(result.size > 0);
        assert!(!result.data.is_empty());
    }

    #[test]
    fn test_http_request_serializer() {
        let mut headers = std::collections::HashMap::new();
        headers.insert("Host".to_string(), "example.com".to_string());
        headers.insert("Content-Type".to_string(), "application/json".to_string());
        
        let result = HttpRequestSerializer::serialize_request(
            "GET",
            "/api/test",
            "HTTP/1.1",
            &headers,
            Some(b"{\"test\": true}")
        ).unwrap();
        
        let request_str = String::from_utf8_lossy(&result.data);
        assert!(request_str.contains("GET /api/test HTTP/1.1"));
        assert!(request_str.contains("Host: example.com"));
        assert!(request_str.contains("{\"test\": true}"));
    }

    #[test]
    fn test_http_response_serializer() {
        let mut headers = std::collections::HashMap::new();
        headers.insert("Content-Type".to_string(), "application/json".to_string());
        headers.insert("Content-Length".to_string(), "17".to_string());
        
        let result = HttpResponseSerializer::serialize_response(
            "HTTP/1.1",
            200,
            "OK",
            &headers,
            Some(b"{\"status\": \"ok\"}")
        ).unwrap();
        
        let response_str = String::from_utf8_lossy(&result.data);
        assert!(response_str.contains("HTTP/1.1 200 OK"));
        assert!(response_str.contains("Content-Type: application/json"));
        assert!(response_str.contains("{\"status\": \"ok\"}"));
    }

    #[test]
    fn test_websocket_frame_serializer() {
        let frame = crate::protocol::websocket::WebSocketFrame::text("Hello, World!");
        
        let result = WebSocketFrameSerializer::serialize_frame(&frame).unwrap();
        assert!(result.size > 0);
        assert!(!result.data.is_empty());
    }

    #[test]
    fn test_serializer_stats() {
        let mut stats = SerializerStats::default();
        
        let result1 = SerializeResult {
            data: Bytes::copy_from_slice(b"data1"),
            size: 5,
        };
        
        let result2 = SerializeResult {
            data: Bytes::copy_from_slice(b"data2"),
            size: 5,
        };
        
        stats.add_result(&result1);
        stats.add_result(&result2);
        
        assert_eq!(stats.total_serialized, 2);
        assert_eq!(stats.total_bytes, 10);
        assert_eq!(stats.average_size, 5.0);
        assert_eq!(stats.largest_size, 5);
        assert_eq!(stats.smallest_size, 5);
    }
}
