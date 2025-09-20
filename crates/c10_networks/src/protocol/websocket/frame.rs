//! WebSocket 帧处理

use crate::error::NetworkError;
use bytes::Bytes;
use serde::{Deserialize, Serialize};

/// WebSocket 操作码
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum WebSocketOpcode {
    Continuation = 0x0,
    Text = 0x1,
    Binary = 0x2,
    Close = 0x8,
    Ping = 0x9,
    Pong = 0xA,
}

impl WebSocketOpcode {
    /// 从字节值创建操作码
    pub fn from_u8(value: u8) -> Result<Self, NetworkError> {
        match value {
            0x0 => Ok(WebSocketOpcode::Continuation),
            0x1 => Ok(WebSocketOpcode::Text),
            0x2 => Ok(WebSocketOpcode::Binary),
            0x8 => Ok(WebSocketOpcode::Close),
            0x9 => Ok(WebSocketOpcode::Ping),
            0xA => Ok(WebSocketOpcode::Pong),
            _ => Err(NetworkError::Protocol(format!(
                "Invalid WebSocket opcode: {}",
                value
            ))),
        }
    }

    /// 检查是否为控制帧
    pub fn is_control_frame(&self) -> bool {
        matches!(
            self,
            WebSocketOpcode::Close | WebSocketOpcode::Ping | WebSocketOpcode::Pong
        )
    }

    /// 检查是否为数据帧
    pub fn is_data_frame(&self) -> bool {
        matches!(
            self,
            WebSocketOpcode::Text | WebSocketOpcode::Binary | WebSocketOpcode::Continuation
        )
    }
}

/// WebSocket 帧
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WebSocketFrame {
    pub fin: bool,
    pub opcode: WebSocketOpcode,
    pub mask: bool,
    pub payload_length: u64,
    pub masking_key: Option<[u8; 4]>,
    pub payload: Bytes,
}

impl WebSocketFrame {
    /// 创建新的 WebSocket 帧
    pub fn new(opcode: WebSocketOpcode, payload: Bytes) -> Self {
        Self {
            fin: true,
            opcode,
            mask: false,
            payload_length: payload.len() as u64,
            masking_key: None,
            payload,
        }
    }

    /// 创建文本帧
    pub fn text(text: &str) -> Self {
        Self::new(
            WebSocketOpcode::Text,
            Bytes::copy_from_slice(text.as_bytes()),
        )
    }

    /// 创建二进制帧
    pub fn binary(data: &[u8]) -> Self {
        Self::new(WebSocketOpcode::Binary, Bytes::copy_from_slice(data))
    }

    /// 创建关闭帧
    pub fn close(code: Option<u16>, reason: Option<&str>) -> Self {
        let mut payload = Vec::new();

        if let Some(code) = code {
            payload.extend_from_slice(&code.to_be_bytes());
        }

        if let Some(reason) = reason {
            payload.extend_from_slice(reason.as_bytes());
        }

        Self::new(WebSocketOpcode::Close, payload.into())
    }

    /// 创建 Ping 帧
    pub fn ping(data: Option<&[u8]>) -> Self {
        let payload = data.map(Bytes::copy_from_slice).unwrap_or_default();
        Self::new(WebSocketOpcode::Ping, payload)
    }

    /// 创建 Pong 帧
    pub fn pong(data: Option<&[u8]>) -> Self {
        let payload = data.map(Bytes::copy_from_slice).unwrap_or_default();
        Self::new(WebSocketOpcode::Pong, payload)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_websocket_opcode() {
        assert_eq!(
            WebSocketOpcode::from_u8(0x1).unwrap(),
            WebSocketOpcode::Text
        );
        assert_eq!(
            WebSocketOpcode::from_u8(0x8).unwrap(),
            WebSocketOpcode::Close
        );
        assert!(WebSocketOpcode::from_u8(0xF).is_err());

        assert!(WebSocketOpcode::Close.is_control_frame());
        assert!(!WebSocketOpcode::Text.is_control_frame());

        assert!(WebSocketOpcode::Text.is_data_frame());
        assert!(!WebSocketOpcode::Close.is_data_frame());
    }

    #[test]
    fn test_websocket_frame_creation() {
        let text_frame = WebSocketFrame::text("Hello, World!");
        assert_eq!(text_frame.opcode, WebSocketOpcode::Text);
        assert_eq!(text_frame.payload, Bytes::from("Hello, World!"));
        assert!(text_frame.fin);

        let binary_frame = WebSocketFrame::binary(&[1, 2, 3, 4]);
        assert_eq!(binary_frame.opcode, WebSocketOpcode::Binary);
        assert_eq!(binary_frame.payload, Bytes::from(&[1, 2, 3, 4][..]));

        let close_frame = WebSocketFrame::close(Some(1000), Some("Normal closure"));
        assert_eq!(close_frame.opcode, WebSocketOpcode::Close);
    }
}
