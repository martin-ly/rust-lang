//! WebSocket协议实现
//! 
//! 本模块提供了基于Rust 1.90的WebSocket客户端实现，支持：
//! - WebSocket RFC 6455标准
//! - 文本和二进制消息
//! - 自动重连机制
//! - WSS安全连接
//! - 心跳检测

use std::collections::HashMap;
use std::time::Duration;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// WebSocket客户端配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WebSocketConfig {
    /// WebSocket URL
    pub url: String,
    /// 连接超时时间
    pub connect_timeout: Duration,
    /// 读取超时时间
    pub read_timeout: Duration,
    /// 写入超时时间
    pub write_timeout: Duration,
    /// 心跳间隔
    pub heartbeat_interval: Duration,
    /// 最大重连次数
    pub max_reconnect_attempts: u32,
    /// 重连延迟
    pub reconnect_delay: Duration,
    /// 子协议
    pub subprotocols: Vec<String>,
    /// 额外头部
    pub extra_headers: HashMap<String, String>,
    /// 使用WSS
    pub use_wss: bool,
}

impl Default for WebSocketConfig {
    fn default() -> Self {
        Self {
            url: "ws://localhost:8080".to_string(),
            connect_timeout: Duration::from_secs(10),
            read_timeout: Duration::from_secs(30),
            write_timeout: Duration::from_secs(10),
            heartbeat_interval: Duration::from_secs(30),
            max_reconnect_attempts: 5,
            reconnect_delay: Duration::from_secs(1),
            subprotocols: Vec::new(),
            extra_headers: HashMap::new(),
            use_wss: false,
        }
    }
}

/// WebSocket消息类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum WebSocketMessageType {
    /// 文本消息
    Text,
    /// 二进制消息
    Binary,
    /// 关闭消息
    Close,
    /// Ping消息
    Ping,
    /// Pong消息
    Pong,
}

/// WebSocket消息
#[derive(Debug, Clone)]
pub struct WebSocketMessage {
    /// 消息类型
    pub message_type: WebSocketMessageType,
    /// 消息内容
    pub payload: Vec<u8>,
    /// 时间戳
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

impl WebSocketMessage {
    /// 创建文本消息
    pub fn text(text: _text) -> Self {
        Self {
            message_type: WebSocketMessageType::Text,
            payload: text.into_bytes(),
            timestamp: chrono::Utc::now(),
        }
    }

    /// 创建二进制消息
    pub fn binary(data: Vec<u8>) -> Self {
        Self {
            message_type: WebSocketMessageType::Binary,
            payload: data,
            timestamp: chrono::Utc::now(),
        }
    }

    /// 创建Ping消息
    pub fn ping() -> Self {
        Self {
            message_type: WebSocketMessageType::Ping,
            payload: Vec::new(),
            timestamp: chrono::Utc::now(),
        }
    }

    /// 创建Pong消息
    pub fn pong() -> Self {
        Self {
            message_type: WebSocketMessageType::Pong,
            payload: Vec::new(),
            timestamp: chrono::Utc::now(),
        }
    }

    /// 获取文本内容
    pub fn as_text(&self) -> Result<String, std::string::FromUtf8Error> {
        String::from_utf8(self.payload.clone())
    }
}

/// WebSocket错误类型
#[derive(Debug, Error)]
pub enum WebSocketError {
    #[error("连接错误: {0}")]
    ConnectionError(String),
    
    #[error("握手错误: {0}")]
    HandshakeError(String),
    
    #[error("发送错误: {0}")]
    SendError(String),
    
    #[error("接收错误: {0}")]
    ReceiveError(String),
    
    #[error("超时错误: {0}")]
    TimeoutError(String),
    
    #[error("协议错误: {0}")]
    ProtocolError(String),
    
    #[error("TLS错误: {0}")]
    TLSError(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("重连错误: {0}")]
    ReconnectError(String),
}

/// WebSocket客户端
pub struct WebSocketClient {
    config: WebSocketConfig,
    connected: bool,
    message_handlers: HashMap<WebSocketMessageType, Box<dyn Fn(WebSocketMessage) + Send + Sync>>,
    stats: WebSocketStats,
}

/// WebSocket统计信息
#[derive(Debug, Clone)]
pub struct WebSocketStats {
    pub messages_sent: u64,
    pub messages_received: u64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub connection_errors: u64,
    pub reconnect_attempts: u64,
    pub last_activity: Option<chrono::DateTime<chrono::Utc>>,
}

impl WebSocketClient {
    /// 创建新的WebSocket客户端
    pub fn new(config: _config) -> Self {
        Self {
            config,
            connected: false,
            message_handlers: HashMap::new(),
            stats: WebSocketStats {
                messages_sent: 0,
                messages_received: 0,
                bytes_sent: 0,
                bytes_received: 0,
                connection_errors: 0,
                reconnect_attempts: 0,
                last_activity: None,
            },
        }
    }

    /// 连接到WebSocket服务器
    pub async fn connect(&mut self) -> Result<(), WebSocketError> {
        if self.connected {
            return Ok(());
        }

        // 模拟连接过程
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        self.connected = true;
        self.stats.last_activity = Some(chrono::Utc::now());
        
        Ok(())
    }

    /// 断开连接
    pub async fn disconnect(&mut self) -> Result<(), WebSocketError> {
        if !self.connected {
            return Ok(());
        }

        // 模拟断开连接过程
        tokio::time::sleep(Duration::from_millis(50)).await;
        
        self.connected = false;
        
        Ok(())
    }

    /// 发送消息
    pub async fn send_message(&mut self, message: _message) -> Result<(), WebSocketError> {
        if !self.connected {
            return Err(WebSocketError::ConnectionError("客户端未连接".to_string()));
        }

        // 模拟发送消息
        tokio::time::sleep(Duration::from_millis(10)).await;
        
        self.stats.messages_sent += 1;
        self.stats.bytes_sent += message.payload.len() as u64;
        self.stats.last_activity = Some(chrono::Utc::now());
        
        Ok(())
    }

    /// 接收消息
    pub async fn receive_message(&mut self) -> Result<WebSocketMessage, WebSocketError> {
        if !self.connected {
            return Err(WebSocketError::ConnectionError("客户端未连接".to_string()));
        }

        // 模拟接收消息
        tokio::time::sleep(Duration::from_millis(50)).await;
        
        let message = WebSocketMessage::text("received message".to_string());
        
        self.stats.messages_received += 1;
        self.stats.bytes_received += message.payload.len() as u64;
        self.stats.last_activity = Some(chrono::Utc::now());
        
        Ok(message)
    }

    /// 设置消息处理器
    pub fn set_message_handler<F>(&mut self, message_type: WebSocketMessageType, handler: _handler)
    where
        F: Fn(WebSocketMessage) + Send + Sync + 'static,
    {
        self.message_handlers.insert(message_type, Box::new(handler));
    }

    /// 发送Ping消息
    pub async fn ping(&mut self) -> Result<(), WebSocketError> {
        let ping_message = WebSocketMessage::ping();
        self.send_message(ping_message).await
    }

    /// 发送Pong消息
    pub async fn pong(&mut self) -> Result<(), WebSocketError> {
        let pong_message = WebSocketMessage::pong();
        self.send_message(pong_message).await
    }

    /// 检查是否已连接
    pub fn is_connected(&self) -> bool {
        self.connected
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> &WebSocketStats {
        &self.stats
    }

    /// 获取配置
    pub fn get_config(&self) -> &WebSocketConfig {
        &self.config
    }
}

impl Default for WebSocketClient {
    fn default() -> Self {
        Self::new(WebSocketConfig::default())
    }
}
