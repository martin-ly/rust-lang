//! WebSocket消息模块
//! 
//! 定义WebSocket消息类型和协议

use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// WebSocket消息类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum WebSocketMessageType {
    /// 文本消息
    Text,
    /// 二进制消息
    Binary,
    /// 心跳消息
    Ping,
    /// 心跳响应
    Pong,
    /// 关闭连接
    Close,
    /// 错误消息
    Error,
    /// 系统消息
    System,
    /// 用户消息
    User,
    /// 广播消息
    Broadcast,
}

/// WebSocket消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WebSocketMessage {
    pub id: Uuid,
    pub message_type: WebSocketMessageType,
    pub content: String,
    pub sender_id: Option<String>,
    pub recipient_id: Option<String>,
    pub room_id: Option<String>,
    pub metadata: Option<serde_json::Value>,
    pub created_at: DateTime<Utc>,
    pub expires_at: Option<DateTime<Utc>>,
}

impl WebSocketMessage {
    /// 创建新的WebSocket消息
    pub fn new(message_type: WebSocketMessageType, content: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            message_type,
            content,
            sender_id: None,
            recipient_id: None,
            room_id: None,
            metadata: None,
            created_at: Utc::now(),
            expires_at: None,
        }
    }

    /// 创建文本消息
    pub fn text(content: String) -> Self {
        Self::new(WebSocketMessageType::Text, content)
    }

    /// 创建系统消息
    pub fn system(content: String) -> Self {
        Self::new(WebSocketMessageType::System, content)
    }

    /// 创建心跳消息
    pub fn ping() -> Self {
        Self::new(WebSocketMessageType::Ping, "ping".to_string())
    }

    /// 创建心跳响应
    pub fn pong() -> Self {
        Self::new(WebSocketMessageType::Pong, "pong".to_string())
    }

    /// 设置发送者ID
    pub fn with_sender(mut self, sender_id: String) -> Self {
        self.sender_id = Some(sender_id);
        self
    }

    /// 设置接收者ID
    pub fn with_recipient(mut self, recipient_id: String) -> Self {
        self.recipient_id = Some(recipient_id);
        self
    }

    /// 设置房间ID
    pub fn with_room(mut self, room_id: String) -> Self {
        self.room_id = Some(room_id);
        self
    }

    /// 设置元数据
    pub fn with_metadata(mut self, metadata: serde_json::Value) -> Self {
        self.metadata = Some(metadata);
        self
    }

    /// 设置过期时间
    pub fn with_expires_at(mut self, expires_at: DateTime<Utc>) -> Self {
        self.expires_at = Some(expires_at);
        self
    }

    /// 检查消息是否过期
    pub fn is_expired(&self) -> bool {
        if let Some(expires_at) = self.expires_at {
            Utc::now() > expires_at
        } else {
            false
        }
    }

    /// 序列化为JSON
    pub fn to_json(&self) -> anyhow::Result<String> {
        Ok(serde_json::to_string(self)?)
    }

    /// 从JSON反序列化
    pub fn from_json(json: &str) -> anyhow::Result<Self> {
        Ok(serde_json::from_str(json)?)
    }
}

/// WebSocket连接状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ConnectionStatus {
    /// 连接中
    Connecting,
    /// 已连接
    Connected,
    /// 断开连接中
    Disconnecting,
    /// 已断开
    Disconnected,
    /// 错误状态
    Error,
}

/// WebSocket连接信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConnectionInfo {
    pub client_id: String,
    pub status: ConnectionStatus,
    pub connected_at: DateTime<Utc>,
    pub last_ping: Option<DateTime<Utc>>,
    pub user_agent: Option<String>,
    pub remote_addr: Option<String>,
    pub metadata: Option<serde_json::Value>,
}

impl ConnectionInfo {
    /// 创建新的连接信息
    pub fn new(client_id: String) -> Self {
        Self {
            client_id,
            status: ConnectionStatus::Connecting,
            connected_at: Utc::now(),
            last_ping: None,
            user_agent: None,
            remote_addr: None,
            metadata: None,
        }
    }

    /// 更新最后ping时间
    pub fn update_ping(&mut self) {
        self.last_ping = Some(Utc::now());
    }

    /// 检查连接是否活跃
    pub fn is_active(&self, timeout_seconds: u64) -> bool {
        if let Some(last_ping) = self.last_ping {
            let now = Utc::now();
            let duration = now.signed_duration_since(last_ping);
            duration.num_seconds() < timeout_seconds as i64
        } else {
            false
        }
    }
}