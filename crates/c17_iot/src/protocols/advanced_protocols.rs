//! 高级IoT通信协议模块
//! 
//! 提供更多现代IoT通信协议支持，包括WebRTC、gRPC、GraphQL等

use std::collections::HashMap;
use std::time::Duration;
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use thiserror::Error;

/// 高级协议类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum AdvancedProtocolType {
    /// WebRTC - 实时通信
    WebRTC,
    /// gRPC - 高性能RPC
    GRPC,
    /// GraphQL - 灵活数据查询
    GraphQL,
    /// WebSocket - 全双工通信
    WebSocket,
    /// Server-Sent Events - 服务器推送
    SSE,
    /// AMQP - 高级消息队列
    AMQP,
    /// Kafka - 分布式流处理
    Kafka,
    /// Redis Streams - 流数据
    RedisStreams,
    /// NATS - 轻量级消息系统
    NATS,
    /// ZeroMQ - 高性能消息库
    ZeroMQ,
}

/// 协议配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AdvancedProtocolConfig {
    /// 协议类型
    pub protocol_type: AdvancedProtocolType,
    /// 服务器地址
    pub server_url: String,
    /// 端口号
    pub port: u16,
    /// 连接超时
    pub connection_timeout: Duration,
    /// 读取超时
    pub read_timeout: Duration,
    /// 写入超时
    pub write_timeout: Duration,
    /// 重连间隔
    pub reconnect_interval: Duration,
    /// 最大重连次数
    pub max_reconnect_attempts: u32,
    /// 是否启用SSL/TLS
    pub enable_ssl: bool,
    /// 认证信息
    pub auth_info: Option<AuthInfo>,
    /// 自定义配置
    pub custom_config: HashMap<String, String>,
}

/// 认证信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthInfo {
    /// 用户名
    pub username: String,
    /// 密码
    pub password: String,
    /// 令牌
    pub token: Option<String>,
    /// API密钥
    pub api_key: Option<String>,
    /// 证书路径
    pub cert_path: Option<String>,
    /// 私钥路径
    pub key_path: Option<String>,
}

/// 连接状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum ConnectionStatus {
    /// 未连接
    Disconnected,
    /// 连接中
    Connecting,
    /// 已连接
    Connected,
    /// 重连中
    Reconnecting,
    /// 连接失败
    Failed,
    /// 已关闭
    Closed,
}

/// 消息类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MessageType {
    /// 文本消息
    Text(String),
    /// 二进制消息
    Binary(Vec<u8>),
    /// JSON消息
    Json(serde_json::Value),
    /// 结构化数据
    Structured(HashMap<String, serde_json::Value>),
    /// 心跳消息
    Heartbeat,
    /// 错误消息
    Error(String),
}

/// 消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    /// 消息ID
    pub id: String,
    /// 消息类型
    pub message_type: MessageType,
    /// 发送时间
    pub timestamp: DateTime<Utc>,
    /// 发送者
    pub sender: String,
    /// 接收者
    pub receiver: Option<String>,
    /// 主题/频道
    pub topic: Option<String>,
    /// 消息头
    pub headers: HashMap<String, String>,
    /// 消息体
    pub payload: Option<Vec<u8>>,
}

/// 连接统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConnectionStats {
    /// 连接状态
    pub status: ConnectionStatus,
    /// 连接时间
    pub connected_at: Option<DateTime<Utc>>,
    /// 断开时间
    pub disconnected_at: Option<DateTime<Utc>>,
    /// 发送消息数
    pub messages_sent: u64,
    /// 接收消息数
    pub messages_received: u64,
    /// 发送字节数
    pub bytes_sent: u64,
    /// 接收字节数
    pub bytes_received: u64,
    /// 重连次数
    pub reconnect_count: u32,
    /// 最后错误
    pub last_error: Option<String>,
    /// 平均延迟
    pub avg_latency: Duration,
    /// 最大延迟
    pub max_latency: Duration,
}

/// 高级协议管理器
pub struct AdvancedProtocolManager {
    /// 协议配置
    config: AdvancedProtocolConfig,
    /// 连接状态
    connection_status: Arc<RwLock<ConnectionStatus>>,
    /// 连接统计
    stats: Arc<RwLock<ConnectionStats>>,
    /// 消息处理器
    message_handlers: Arc<RwLock<HashMap<String, Box<dyn Fn(Message) -> Result<(), Box<dyn std::error::Error>> + Send + Sync>>>>,
    /// 连接句柄
    connection_handle: Arc<RwLock<Option<ConnectionHandle>>>,
}

/// 连接句柄
#[derive(Debug)]
pub struct ConnectionHandle {
    /// 连接ID
    pub id: String,
    /// 协议类型
    pub protocol_type: AdvancedProtocolType,
    /// 创建时间
    pub created_at: DateTime<Utc>,
}

impl AdvancedProtocolManager {
    /// 创建新的高级协议管理器
    pub fn new(config: AdvancedProtocolConfig) -> Self {
        Self {
            connection_status: Arc::new(RwLock::new(ConnectionStatus::Disconnected)),
            stats: Arc::new(RwLock::new(ConnectionStats {
                status: ConnectionStatus::Disconnected,
                connected_at: None,
                disconnected_at: None,
                messages_sent: 0,
                messages_received: 0,
                bytes_sent: 0,
                bytes_received: 0,
                reconnect_count: 0,
                last_error: None,
                avg_latency: Duration::ZERO,
                max_latency: Duration::ZERO,
            })),
            message_handlers: Arc::new(RwLock::new(HashMap::new())),
            connection_handle: Arc::new(RwLock::new(None)),
            config,
        }
    }

    /// 连接到服务器
    pub async fn connect(&self) -> Result<(), AdvancedProtocolError> {
        let mut status = self.connection_status.write().await;
        *status = ConnectionStatus::Connecting;

        // 根据协议类型建立连接
        let result = match self.config.protocol_type {
            AdvancedProtocolType::WebRTC => self.connect_webrtc().await,
            AdvancedProtocolType::GRPC => self.connect_grpc().await,
            AdvancedProtocolType::GraphQL => self.connect_graphql().await,
            AdvancedProtocolType::WebSocket => self.connect_websocket().await,
            AdvancedProtocolType::SSE => self.connect_sse().await,
            AdvancedProtocolType::AMQP => self.connect_amqp().await,
            AdvancedProtocolType::Kafka => self.connect_kafka().await,
            AdvancedProtocolType::RedisStreams => self.connect_redis_streams().await,
            AdvancedProtocolType::NATS => self.connect_nats().await,
            AdvancedProtocolType::ZeroMQ => self.connect_zeromq().await,
        };

        match result {
            Ok(handle) => {
                *status = ConnectionStatus::Connected;
                {
                    let mut connection_handle = self.connection_handle.write().await;
                    *connection_handle = Some(handle);
                }
                self.update_stats_connected().await;
                Ok(())
            }
            Err(e) => {
                *status = ConnectionStatus::Failed;
                self.update_stats_error(e.to_string()).await;
                Err(e)
            }
        }
    }

    /// 断开连接
    pub async fn disconnect(&self) -> Result<(), AdvancedProtocolError> {
        let mut status = self.connection_status.write().await;
        *status = ConnectionStatus::Disconnected;

        {
            let mut connection_handle = self.connection_handle.write().await;
            *connection_handle = None;
        }

        self.update_stats_disconnected().await;
        Ok(())
    }

    /// 发送消息
    pub async fn send_message(&self, message: Message) -> Result<(), AdvancedProtocolError> {
        let status = self.connection_status.read().await;
        if *status != ConnectionStatus::Connected {
            return Err(AdvancedProtocolError::NotConnected);
        }

        // 根据协议类型发送消息
        let result = match self.config.protocol_type {
            AdvancedProtocolType::WebRTC => self.send_webrtc_message(message).await,
            AdvancedProtocolType::GRPC => self.send_grpc_message(message).await,
            AdvancedProtocolType::GraphQL => self.send_graphql_message(message).await,
            AdvancedProtocolType::WebSocket => self.send_websocket_message(message).await,
            AdvancedProtocolType::SSE => self.send_sse_message(message).await,
            AdvancedProtocolType::AMQP => self.send_amqp_message(message).await,
            AdvancedProtocolType::Kafka => self.send_kafka_message(message).await,
            AdvancedProtocolType::RedisStreams => self.send_redis_streams_message(message).await,
            AdvancedProtocolType::NATS => self.send_nats_message(message).await,
            AdvancedProtocolType::ZeroMQ => self.send_zeromq_message(message).await,
        };

        match result {
            Ok(()) => {
                self.update_stats_message_sent().await;
                Ok(())
            }
            Err(e) => {
                self.update_stats_error(e.to_string()).await;
                Err(e)
            }
        }
    }

    /// 接收消息
    pub async fn receive_message(&self) -> Result<Message, AdvancedProtocolError> {
        let status = self.connection_status.read().await;
        if *status != ConnectionStatus::Connected {
            return Err(AdvancedProtocolError::NotConnected);
        }

        // 根据协议类型接收消息
        let result = match self.config.protocol_type {
            AdvancedProtocolType::WebRTC => self.receive_webrtc_message().await,
            AdvancedProtocolType::GRPC => self.receive_grpc_message().await,
            AdvancedProtocolType::GraphQL => self.receive_graphql_message().await,
            AdvancedProtocolType::WebSocket => self.receive_websocket_message().await,
            AdvancedProtocolType::SSE => self.receive_sse_message().await,
            AdvancedProtocolType::AMQP => self.receive_amqp_message().await,
            AdvancedProtocolType::Kafka => self.receive_kafka_message().await,
            AdvancedProtocolType::RedisStreams => self.receive_redis_streams_message().await,
            AdvancedProtocolType::NATS => self.receive_nats_message().await,
            AdvancedProtocolType::ZeroMQ => self.receive_zeromq_message().await,
        };

        match result {
            Ok(message) => {
                self.update_stats_message_received().await;
                Ok(message)
            }
            Err(e) => {
                self.update_stats_error(e.to_string()).await;
                Err(e)
            }
        }
    }

    /// 注册消息处理器
    pub async fn register_message_handler<F>(&self, topic: String, handler: F) -> Result<(), AdvancedProtocolError>
    where
        F: Fn(Message) -> Result<(), Box<dyn std::error::Error>> + Send + Sync + 'static,
    {
        let mut handlers = self.message_handlers.write().await;
        handlers.insert(topic, Box::new(handler));
        Ok(())
    }

    /// 获取连接状态
    pub async fn get_connection_status(&self) -> ConnectionStatus {
        self.connection_status.read().await.clone()
    }

    /// 获取连接统计
    pub async fn get_connection_stats(&self) -> ConnectionStats {
        self.stats.read().await.clone()
    }

    /// 获取协议配置
    pub fn get_config(&self) -> &AdvancedProtocolConfig {
        &self.config
    }

    // WebRTC连接实现
    async fn connect_webrtc(&self) -> Result<ConnectionHandle, AdvancedProtocolError> {
        println!("建立WebRTC连接: {}", self.config.server_url);
        // 这里应该实现实际的WebRTC连接逻辑
        // 目前返回模拟连接
        Ok(ConnectionHandle {
            id: uuid::Uuid::new_v4().to_string(),
            protocol_type: AdvancedProtocolType::WebRTC,
            created_at: Utc::now(),
        })
    }

    // gRPC连接实现
    async fn connect_grpc(&self) -> Result<ConnectionHandle, AdvancedProtocolError> {
        println!("建立gRPC连接: {}", self.config.server_url);
        // 这里应该实现实际的gRPC连接逻辑
        Ok(ConnectionHandle {
            id: uuid::Uuid::new_v4().to_string(),
            protocol_type: AdvancedProtocolType::GRPC,
            created_at: Utc::now(),
        })
    }

    // GraphQL连接实现
    async fn connect_graphql(&self) -> Result<ConnectionHandle, AdvancedProtocolError> {
        println!("建立GraphQL连接: {}", self.config.server_url);
        // 这里应该实现实际的GraphQL连接逻辑
        Ok(ConnectionHandle {
            id: uuid::Uuid::new_v4().to_string(),
            protocol_type: AdvancedProtocolType::GraphQL,
            created_at: Utc::now(),
        })
    }

    // WebSocket连接实现
    async fn connect_websocket(&self) -> Result<ConnectionHandle, AdvancedProtocolError> {
        println!("建立WebSocket连接: {}", self.config.server_url);
        // 这里应该实现实际的WebSocket连接逻辑
        Ok(ConnectionHandle {
            id: uuid::Uuid::new_v4().to_string(),
            protocol_type: AdvancedProtocolType::WebSocket,
            created_at: Utc::now(),
        })
    }

    // SSE连接实现
    async fn connect_sse(&self) -> Result<ConnectionHandle, AdvancedProtocolError> {
        println!("建立SSE连接: {}", self.config.server_url);
        // 这里应该实现实际的SSE连接逻辑
        Ok(ConnectionHandle {
            id: uuid::Uuid::new_v4().to_string(),
            protocol_type: AdvancedProtocolType::SSE,
            created_at: Utc::now(),
        })
    }

    // AMQP连接实现
    async fn connect_amqp(&self) -> Result<ConnectionHandle, AdvancedProtocolError> {
        println!("建立AMQP连接: {}", self.config.server_url);
        // 这里应该实现实际的AMQP连接逻辑
        Ok(ConnectionHandle {
            id: uuid::Uuid::new_v4().to_string(),
            protocol_type: AdvancedProtocolType::AMQP,
            created_at: Utc::now(),
        })
    }

    // Kafka连接实现
    async fn connect_kafka(&self) -> Result<ConnectionHandle, AdvancedProtocolError> {
        println!("建立Kafka连接: {}", self.config.server_url);
        // 这里应该实现实际的Kafka连接逻辑
        Ok(ConnectionHandle {
            id: uuid::Uuid::new_v4().to_string(),
            protocol_type: AdvancedProtocolType::Kafka,
            created_at: Utc::now(),
        })
    }

    // Redis Streams连接实现
    async fn connect_redis_streams(&self) -> Result<ConnectionHandle, AdvancedProtocolError> {
        println!("建立Redis Streams连接: {}", self.config.server_url);
        // 这里应该实现实际的Redis Streams连接逻辑
        Ok(ConnectionHandle {
            id: uuid::Uuid::new_v4().to_string(),
            protocol_type: AdvancedProtocolType::RedisStreams,
            created_at: Utc::now(),
        })
    }

    // NATS连接实现
    async fn connect_nats(&self) -> Result<ConnectionHandle, AdvancedProtocolError> {
        println!("建立NATS连接: {}", self.config.server_url);
        // 这里应该实现实际的NATS连接逻辑
        Ok(ConnectionHandle {
            id: uuid::Uuid::new_v4().to_string(),
            protocol_type: AdvancedProtocolType::NATS,
            created_at: Utc::now(),
        })
    }

    // ZeroMQ连接实现
    async fn connect_zeromq(&self) -> Result<ConnectionHandle, AdvancedProtocolError> {
        println!("建立ZeroMQ连接: {}", self.config.server_url);
        // 这里应该实现实际的ZeroMQ连接逻辑
        Ok(ConnectionHandle {
            id: uuid::Uuid::new_v4().to_string(),
            protocol_type: AdvancedProtocolType::ZeroMQ,
            created_at: Utc::now(),
        })
    }

    // 各种协议的消息发送实现
    async fn send_webrtc_message(&self, message: Message) -> Result<(), AdvancedProtocolError> {
        println!("通过WebRTC发送消息: {}", message.id);
        Ok(())
    }

    async fn send_grpc_message(&self, message: Message) -> Result<(), AdvancedProtocolError> {
        println!("通过gRPC发送消息: {}", message.id);
        Ok(())
    }

    async fn send_graphql_message(&self, message: Message) -> Result<(), AdvancedProtocolError> {
        println!("通过GraphQL发送消息: {}", message.id);
        Ok(())
    }

    async fn send_websocket_message(&self, message: Message) -> Result<(), AdvancedProtocolError> {
        println!("通过WebSocket发送消息: {}", message.id);
        Ok(())
    }

    async fn send_sse_message(&self, message: Message) -> Result<(), AdvancedProtocolError> {
        println!("通过SSE发送消息: {}", message.id);
        Ok(())
    }

    async fn send_amqp_message(&self, message: Message) -> Result<(), AdvancedProtocolError> {
        println!("通过AMQP发送消息: {}", message.id);
        Ok(())
    }

    async fn send_kafka_message(&self, message: Message) -> Result<(), AdvancedProtocolError> {
        println!("通过Kafka发送消息: {}", message.id);
        Ok(())
    }

    async fn send_redis_streams_message(&self, message: Message) -> Result<(), AdvancedProtocolError> {
        println!("通过Redis Streams发送消息: {}", message.id);
        Ok(())
    }

    async fn send_nats_message(&self, message: Message) -> Result<(), AdvancedProtocolError> {
        println!("通过NATS发送消息: {}", message.id);
        Ok(())
    }

    async fn send_zeromq_message(&self, message: Message) -> Result<(), AdvancedProtocolError> {
        println!("通过ZeroMQ发送消息: {}", message.id);
        Ok(())
    }

    // 各种协议的消息接收实现
    async fn receive_webrtc_message(&self) -> Result<Message, AdvancedProtocolError> {
        // 模拟接收消息
        Ok(Message {
            id: uuid::Uuid::new_v4().to_string(),
            message_type: MessageType::Text("WebRTC消息".to_string()),
            timestamp: Utc::now(),
            sender: "server".to_string(),
            receiver: None,
            topic: None,
            headers: HashMap::new(),
            payload: None,
        })
    }

    async fn receive_grpc_message(&self) -> Result<Message, AdvancedProtocolError> {
        Ok(Message {
            id: uuid::Uuid::new_v4().to_string(),
            message_type: MessageType::Text("gRPC消息".to_string()),
            timestamp: Utc::now(),
            sender: "server".to_string(),
            receiver: None,
            topic: None,
            headers: HashMap::new(),
            payload: None,
        })
    }

    async fn receive_graphql_message(&self) -> Result<Message, AdvancedProtocolError> {
        Ok(Message {
            id: uuid::Uuid::new_v4().to_string(),
            message_type: MessageType::Text("GraphQL消息".to_string()),
            timestamp: Utc::now(),
            sender: "server".to_string(),
            receiver: None,
            topic: None,
            headers: HashMap::new(),
            payload: None,
        })
    }

    async fn receive_websocket_message(&self) -> Result<Message, AdvancedProtocolError> {
        Ok(Message {
            id: uuid::Uuid::new_v4().to_string(),
            message_type: MessageType::Text("WebSocket消息".to_string()),
            timestamp: Utc::now(),
            sender: "server".to_string(),
            receiver: None,
            topic: None,
            headers: HashMap::new(),
            payload: None,
        })
    }

    async fn receive_sse_message(&self) -> Result<Message, AdvancedProtocolError> {
        Ok(Message {
            id: uuid::Uuid::new_v4().to_string(),
            message_type: MessageType::Text("SSE消息".to_string()),
            timestamp: Utc::now(),
            sender: "server".to_string(),
            receiver: None,
            topic: None,
            headers: HashMap::new(),
            payload: None,
        })
    }

    async fn receive_amqp_message(&self) -> Result<Message, AdvancedProtocolError> {
        Ok(Message {
            id: uuid::Uuid::new_v4().to_string(),
            message_type: MessageType::Text("AMQP消息".to_string()),
            timestamp: Utc::now(),
            sender: "server".to_string(),
            receiver: None,
            topic: None,
            headers: HashMap::new(),
            payload: None,
        })
    }

    async fn receive_kafka_message(&self) -> Result<Message, AdvancedProtocolError> {
        Ok(Message {
            id: uuid::Uuid::new_v4().to_string(),
            message_type: MessageType::Text("Kafka消息".to_string()),
            timestamp: Utc::now(),
            sender: "server".to_string(),
            receiver: None,
            topic: None,
            headers: HashMap::new(),
            payload: None,
        })
    }

    async fn receive_redis_streams_message(&self) -> Result<Message, AdvancedProtocolError> {
        Ok(Message {
            id: uuid::Uuid::new_v4().to_string(),
            message_type: MessageType::Text("Redis Streams消息".to_string()),
            timestamp: Utc::now(),
            sender: "server".to_string(),
            receiver: None,
            topic: None,
            headers: HashMap::new(),
            payload: None,
        })
    }

    async fn receive_nats_message(&self) -> Result<Message, AdvancedProtocolError> {
        Ok(Message {
            id: uuid::Uuid::new_v4().to_string(),
            message_type: MessageType::Text("NATS消息".to_string()),
            timestamp: Utc::now(),
            sender: "server".to_string(),
            receiver: None,
            topic: None,
            headers: HashMap::new(),
            payload: None,
        })
    }

    async fn receive_zeromq_message(&self) -> Result<Message, AdvancedProtocolError> {
        Ok(Message {
            id: uuid::Uuid::new_v4().to_string(),
            message_type: MessageType::Text("ZeroMQ消息".to_string()),
            timestamp: Utc::now(),
            sender: "server".to_string(),
            receiver: None,
            topic: None,
            headers: HashMap::new(),
            payload: None,
        })
    }

    // 统计更新方法
    async fn update_stats_connected(&self) {
        let mut stats = self.stats.write().await;
        stats.status = ConnectionStatus::Connected;
        stats.connected_at = Some(Utc::now());
    }

    async fn update_stats_disconnected(&self) {
        let mut stats = self.stats.write().await;
        stats.status = ConnectionStatus::Disconnected;
        stats.disconnected_at = Some(Utc::now());
    }

    async fn update_stats_error(&self, error: String) {
        let mut stats = self.stats.write().await;
        stats.last_error = Some(error);
    }

    async fn update_stats_message_sent(&self) {
        let mut stats = self.stats.write().await;
        stats.messages_sent += 1;
    }

    async fn update_stats_message_received(&self) {
        let mut stats = self.stats.write().await;
        stats.messages_received += 1;
    }
}

/// 高级协议错误
#[derive(Debug, Error)]
pub enum AdvancedProtocolError {
    #[error("连接失败: {0}")]
    ConnectionFailed(String),
    
    #[error("未连接")]
    NotConnected,
    
    #[error("发送消息失败: {0}")]
    SendMessageFailed(String),
    
    #[error("接收消息失败: {0}")]
    ReceiveMessageFailed(String),
    
    #[error("协议不支持: {0}")]
    ProtocolNotSupported(String),
    
    #[error("认证失败: {0}")]
    AuthenticationFailed(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("超时: {0}")]
    Timeout(String),
    
    #[error("内部错误: {0}")]
    InternalError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_advanced_protocol_manager_creation() {
        let config = AdvancedProtocolConfig {
            protocol_type: AdvancedProtocolType::WebSocket,
            server_url: "ws://localhost:8080".to_string(),
            port: 8080,
            connection_timeout: Duration::from_secs(10),
            read_timeout: Duration::from_secs(30),
            write_timeout: Duration::from_secs(30),
            reconnect_interval: Duration::from_secs(5),
            max_reconnect_attempts: 3,
            enable_ssl: false,
            auth_info: None,
            custom_config: HashMap::new(),
        };

        let manager = AdvancedProtocolManager::new(config);
        let status = manager.get_connection_status().await;
        assert_eq!(status, ConnectionStatus::Disconnected);
    }

    #[tokio::test]
    async fn test_websocket_connection() {
        let config = AdvancedProtocolConfig {
            protocol_type: AdvancedProtocolType::WebSocket,
            server_url: "ws://localhost:8080".to_string(),
            port: 8080,
            connection_timeout: Duration::from_secs(10),
            read_timeout: Duration::from_secs(30),
            write_timeout: Duration::from_secs(30),
            reconnect_interval: Duration::from_secs(5),
            max_reconnect_attempts: 3,
            enable_ssl: false,
            auth_info: None,
            custom_config: HashMap::new(),
        };

        let manager = AdvancedProtocolManager::new(config);
        let result = manager.connect().await;
        assert!(result.is_ok());
        
        let status = manager.get_connection_status().await;
        assert_eq!(status, ConnectionStatus::Connected);
    }

    #[tokio::test]
    async fn test_message_sending() {
        let config = AdvancedProtocolConfig {
            protocol_type: AdvancedProtocolType::WebSocket,
            server_url: "ws://localhost:8080".to_string(),
            port: 8080,
            connection_timeout: Duration::from_secs(10),
            read_timeout: Duration::from_secs(30),
            write_timeout: Duration::from_secs(30),
            reconnect_interval: Duration::from_secs(5),
            max_reconnect_attempts: 3,
            enable_ssl: false,
            auth_info: None,
            custom_config: HashMap::new(),
        };

        let manager = AdvancedProtocolManager::new(config);
        manager.connect().await.unwrap();

        let message = Message {
            id: uuid::Uuid::new_v4().to_string(),
            message_type: MessageType::Text("测试消息".to_string()),
            timestamp: Utc::now(),
            sender: "test_client".to_string(),
            receiver: None,
            topic: None,
            headers: HashMap::new(),
            payload: None,
        };

        let result = manager.send_message(message).await;
        assert!(result.is_ok());
    }
}
