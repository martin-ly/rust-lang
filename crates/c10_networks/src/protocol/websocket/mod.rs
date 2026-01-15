//! WebSocket 协议实现模块
//!
//! 本模块提供了基于 Rust 1.92.0 的 WebSocket 协议实现，
//! 包括握手、帧处理、消息传递等功能。

pub mod frame;
pub mod handshake;

pub use frame::{WebSocketFrame, WebSocketOpcode};
pub use handshake::{WebSocketClient, WebSocketHandshakeRequest, WebSocketHandshakeResponse};

// use crate::error::{NetworkError, NetworkResult}; // 暂时注释掉未使用的导入
use std::collections::HashMap;

/// WebSocket 连接状态
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WebSocketState {
    Connecting,
    Open,
    Closing,
    Closed,
}

/// WebSocket 连接
pub struct WebSocketConnection {
    pub state: WebSocketState,
    pub uri: String,
    pub headers: HashMap<String, String>,
}

impl WebSocketConnection {
    /// 创建新的 WebSocket 连接
    pub fn new(uri: &str) -> Self {
        Self {
            state: WebSocketState::Connecting,
            uri: uri.to_string(),
            headers: HashMap::new(),
        }
    }

    /// 添加自定义请求头
    pub fn add_header(&mut self, name: &str, value: &str) {
        self.headers.insert(name.to_string(), value.to_string());
    }

    /// 检查连接是否已打开
    pub fn is_open(&self) -> bool {
        self.state == WebSocketState::Open
    }

    /// 检查连接是否已关闭
    pub fn is_closed(&self) -> bool {
        self.state == WebSocketState::Closed
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_websocket_connection() {
        let mut connection = WebSocketConnection::new("ws://example.com/chat");
        assert_eq!(connection.state, WebSocketState::Connecting);
        assert!(!connection.is_open());
        assert!(!connection.is_closed());

        connection.add_header("User-Agent", "MyClient/1.0");
        assert_eq!(
            connection.headers.get("User-Agent"),
            Some(&"MyClient/1.0".to_string())
        );
    }
}
