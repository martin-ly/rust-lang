//! 数据包解析器

use crate::error::{NetworkError, NetworkResult};
use bytes::{Bytes, BytesMut};
use nom::{
    IResult, Parser,
    bytes::complete::{tag, take},
    combinator::map,
    number::complete::{be_u16, be_u32, be_u64},
};
// use std::fmt; // 暂时注释掉未使用的导入

/// 解析结果
#[derive(Debug, Clone)]
pub struct ParseResult {
    pub packet: super::Packet,
    pub remaining: Bytes,
}

/// 数据包解析器
pub struct PacketParser {
    buffer: BytesMut,
    max_packet_size: usize,
}

impl PacketParser {
    /// 创建新的数据包解析器
    pub fn new(max_packet_size: usize) -> Self {
        Self {
            buffer: BytesMut::new(),
            max_packet_size,
        }
    }

    /// 添加数据到解析缓冲区
    pub fn feed(&mut self, data: &[u8]) -> NetworkResult<()> {
        if self.buffer.len() + data.len() > self.max_packet_size {
            return Err(NetworkError::Other("Buffer overflow".to_string()));
        }

        self.buffer.extend_from_slice(data);
        Ok(())
    }

    /// 解析数据包
    pub fn parse(&mut self) -> NetworkResult<Option<ParseResult>> {
        if self.buffer.len() < 4 {
            return Ok(None); // 需要更多数据
        }

        let buffer_slice = &self.buffer[..];
        match self.parse_packet(buffer_slice) {
            Ok((remaining, packet)) => {
                let _consumed = self.buffer.len() - remaining.len();
                let remaining_data = Bytes::copy_from_slice(remaining);
                self.buffer = BytesMut::from(remaining);

                Ok(Some(ParseResult {
                    packet,
                    remaining: remaining_data,
                }))
            }
            Err(nom::Err::Incomplete(_)) => {
                Ok(None) // 需要更多数据
            }
            Err(e) => Err(NetworkError::Other(format!("Parse error: {:?}", e))),
        }
    }

    /// 解析单个数据包
    fn parse_packet<'a>(&self, input: &'a [u8]) -> IResult<&'a [u8], super::Packet> {
        let (input, (packet_type_raw, length, timestamp, sequence_number, flags)) = (
            be_u32, // packet_type (作为 u32)
            be_u32, // length
            be_u64, // timestamp
            be_u64, // sequence_number
            be_u32, // flags
        )
            .parse(input)?;

        let packet_type = match packet_type_raw {
            0 => super::PacketType::Raw,
            1 => super::PacketType::Http,
            2 => super::PacketType::WebSocket,
            3 => super::PacketType::Tcp,
            4 => super::PacketType::Udp,
            _ => super::PacketType::Custom(format!("Unknown_{}", packet_type_raw)),
        };

        let (input, payload) = take(length)(input)?;

        let header = super::PacketHeader {
            packet_type,
            length,
            timestamp,
            sequence_number: Some(sequence_number),
            flags,
        };

        Ok((
            input,
            super::Packet {
                header,
                payload: Bytes::copy_from_slice(payload),
            },
        ))
    }

    /// 清空解析缓冲区
    pub fn clear(&mut self) {
        self.buffer.clear();
    }

    /// 获取缓冲区大小
    pub fn buffer_size(&self) -> usize {
        self.buffer.len()
    }

    /// 检查是否有待解析的数据
    pub fn has_data(&self) -> bool {
        !self.buffer.is_empty()
    }
}

/// HTTP 请求解析器
pub struct HttpRequestParser;

impl HttpRequestParser {
    /// 解析 HTTP 请求行
    pub fn parse_request_line(input: &[u8]) -> IResult<&[u8], (String, String, String)> {
        let (input, method) = map(nom::bytes::complete::take_until(" "), |s: &[u8]| {
            String::from_utf8_lossy(s).to_string()
        })
        .parse(input)?;

        let (input, _) = tag(" ")(input)?;

        let (input, uri) = map(nom::bytes::complete::take_until(" "), |s: &[u8]| {
            String::from_utf8_lossy(s).to_string()
        })
        .parse(input)?;

        let (input, _) = tag(" ")(input)?;

        let (input, version) = map(nom::bytes::complete::take_until("\r\n"), |s: &[u8]| {
            String::from_utf8_lossy(s).to_string()
        })
        .parse(input)?;

        let (input, _) = tag("\r\n")(input)?;

        Ok((input, (method, uri, version)))
    }

    /// 解析 HTTP 头部
    pub fn parse_headers(
        input: &[u8],
    ) -> IResult<&[u8], std::collections::HashMap<String, String>> {
        let mut headers = std::collections::HashMap::new();
        let mut remaining = input;

        loop {
            if remaining.starts_with(b"\r\n") {
                remaining = &remaining[2..];
                break;
            }

            let (new_remaining, header_line) =
                map(nom::bytes::complete::take_until("\r\n"), |s: &[u8]| {
                    String::from_utf8_lossy(s).to_string()
                })
                .parse(remaining)?;

            let (new_remaining, _) = tag("\r\n")(new_remaining)?;

            if let Some(colon_pos) = header_line.find(':') {
                let name = header_line[..colon_pos].trim().to_string();
                let value = header_line[colon_pos + 1..].trim().to_string();
                headers.insert(name, value);
            }

            remaining = new_remaining;
        }

        Ok((remaining, headers))
    }
}

/// WebSocket 帧解析器
pub struct WebSocketFrameParser;

impl WebSocketFrameParser {
    /// 解析 WebSocket 帧
    pub fn parse_frame(input: &[u8]) -> IResult<&[u8], crate::protocol::websocket::WebSocketFrame> {
        if input.len() < 2 {
            return Err(nom::Err::Incomplete(nom::Needed::new(2)));
        }

        let (input, first_byte) = take(1usize)(input)?;
        let (input, second_byte) = take(1usize)(input)?;

        let fin = (first_byte[0] & 0x80) != 0;
        let opcode = first_byte[0] & 0x0F;
        let mask = (second_byte[0] & 0x80) != 0;
        let payload_length = second_byte[0] & 0x7F;

        let (input, actual_length) = if payload_length == 126 {
            let (input, length) = be_u16(input)?;
            (input, length as u64)
        } else if payload_length == 127 {
            let (input, length) = be_u64(input)?;
            (input, length)
        } else {
            (input, payload_length as u64)
        };

        let (input, masking_key) = if mask {
            let (input, key) = take(4usize)(input)?;
            (input, Some([key[0], key[1], key[2], key[3]]))
        } else {
            (input, None)
        };

        let (input, payload) = take(actual_length as usize)(input)?;

        let opcode =
            crate::protocol::websocket::WebSocketOpcode::from_u8(opcode).map_err(|_| {
                nom::Err::Error(nom::error::Error::new(input, nom::error::ErrorKind::Tag))
            })?;

        let mut payload_bytes = payload.to_vec();

        // 解掩码
        if mask {
            if let Some(key) = masking_key {
                for i in 0..payload_bytes.len() {
                    payload_bytes[i] ^= key[i % 4];
                }
            }
        }

        let frame = crate::protocol::websocket::WebSocketFrame {
            fin,
            opcode,
            mask,
            payload_length: actual_length,
            masking_key,
            payload: Bytes::copy_from_slice(&payload_bytes),
        };

        Ok((input, frame))
    }
}

/// 数据包解析器工厂
pub struct ParserFactory;

impl ParserFactory {
    /// 创建数据包解析器
    pub fn create_packet_parser(max_size: usize) -> PacketParser {
        PacketParser::new(max_size)
    }

    /// 创建 HTTP 请求解析器
    pub fn create_http_parser() -> HttpRequestParser {
        HttpRequestParser
    }

    /// 创建 WebSocket 帧解析器
    pub fn create_websocket_parser() -> WebSocketFrameParser {
        WebSocketFrameParser
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_packet_parser() {
        let mut parser = PacketParser::new(1024);

        // 创建测试数据包
        let packet = super::super::Packet::new(
            super::super::PacketType::Raw,
            Bytes::copy_from_slice(b"test data"),
        );

        // 序列化数据包（简化版本）
        let mut data = BytesMut::new();
        data.extend_from_slice(&0u32.to_be_bytes()); // packet_type
        data.extend_from_slice(&(packet.payload.len() as u32).to_be_bytes()); // length
        data.extend_from_slice(&packet.header.timestamp.to_be_bytes()); // timestamp
        data.extend_from_slice(&0u64.to_be_bytes()); // sequence_number
        data.extend_from_slice(&0u32.to_be_bytes()); // flags
        data.extend_from_slice(&packet.payload); // payload

        parser.feed(&data).unwrap();

        let result = parser.parse().unwrap().unwrap();
        assert_eq!(result.packet.packet_type(), &super::super::PacketType::Raw);
        assert_eq!(result.packet.payload, Bytes::copy_from_slice(b"test data"));
    }

    #[test]
    fn test_http_request_parser() {
        let request = b"GET /api/test HTTP/1.1\r\nHost: example.com\r\n\r\n";

        let (remaining, (method, uri, version)) =
            HttpRequestParser::parse_request_line(request).unwrap();
        assert_eq!(method, "GET");
        assert_eq!(uri, "/api/test");
        assert_eq!(version, "HTTP/1.1");

        let (remaining, headers) = HttpRequestParser::parse_headers(remaining).unwrap();
        assert_eq!(headers.get("Host"), Some(&"example.com".to_string()));
        assert!(remaining.is_empty());
    }

    #[test]
    fn test_websocket_frame_parser() {
        // 创建简单的 WebSocket 文本帧
        let mut frame_data = vec![0x81, 0x05]; // FIN=1, opcode=1 (text), mask=0, length=5
        frame_data.extend_from_slice(b"hello");

        let (remaining, frame) = WebSocketFrameParser::parse_frame(&frame_data).unwrap();
        assert!(frame.fin);
        assert_eq!(
            frame.opcode,
            crate::protocol::websocket::WebSocketOpcode::Text
        );
        assert_eq!(frame.payload, Bytes::copy_from_slice(b"hello"));
        assert!(remaining.is_empty());
    }
}
