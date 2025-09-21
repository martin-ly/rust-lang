//! 通信协议模块
//! 
//! 本模块提供了基于Rust 1.90的IoT通信协议支持，包括：
//! - MQTT协议
//! - CoAP协议
//! - HTTP/HTTPS
//! - WebSocket
//! - Modbus
//! - OPC UA
//! - LoRaWAN
//! - Zigbee
//! - Bluetooth
//! - 6LoWPAN

// pub mod mqtt;
// pub mod coap;
// pub mod http;
// pub mod websocket;
// pub mod modbus;
// pub mod opcua;
// pub mod lorawan;
// pub mod zigbee;
// pub mod bluetooth;
// pub mod sixlowpan;
pub mod protocol_manager;

// pub use mqtt::{MQTTClient, MQTTConfig, MQTTMessage, MQTTQoS, MQTTError};
// pub use coap::{CoAPClient, CoAPConfig, CoAPMessage, CoAPMethod, CoAPError};
// pub use http::{HTTPClient, HTTPConfig, HTTPRequest, HTTPResponse, HTTPMethod, HTTPError};
// pub use websocket::{WebSocketClient, WebSocketConfig, WebSocketMessage, WebSocketError};
// pub use modbus::{ModbusClient, ModbusConfig, ModbusRequest, ModbusResponse, ModbusError};
// pub use opcua::{OPCUAClient, OPCUAConfig, OPCUAMessage, OPCUAError};
// pub use lorawan::{LoRaWANClient, LoRaWANConfig, LoRaWANMessage, LoRaWANError};
// pub use zigbee::{ZigbeeClient, ZigbeeConfig, ZigbeeMessage, ZigbeeError};
// pub use bluetooth::{BluetoothClient, BluetoothConfig, BluetoothMessage, BluetoothError};
// pub use sixlowpan::{SixLoWPANClient, SixLoWPANConfig, SixLoWPANMessage, SixLoWPANError};
pub use protocol_manager::{ProtocolManager, ProtocolInfo};

/// 通信协议错误类型
#[derive(Debug, thiserror::Error)]
pub enum CommunicationError {
    #[error("连接失败: {0}")]
    ConnectionFailed(String),
    
    #[error("认证失败: {0}")]
    AuthenticationFailed(String),
    
    #[error("消息发送失败: {0}")]
    SendFailed(String),
    
    #[error("消息接收失败: {0}")]
    ReceiveFailed(String),
    
    #[error("协议错误: {0}")]
    ProtocolError(String),
    
    #[error("超时错误: {0}")]
    TimeoutError(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("编码错误: {0}")]
    EncodingError(String),
    
    #[error("解码错误: {0}")]
    DecodingError(String),
    
    #[error("网络错误: {0}")]
    NetworkError(String),
    
    #[error("TLS错误: {0}")]
    TLSError(String),
    
    #[error("设备错误: {0}")]
    DeviceError(String),
}

impl From<crate::communication::protocol_manager::ProtocolManagerError> for CommunicationError {
    fn from(err: crate::communication::protocol_manager::ProtocolManagerError) -> Self {
        match err {
            crate::communication::protocol_manager::ProtocolManagerError::ProtocolError(msg) => CommunicationError::ProtocolError(msg),
            crate::communication::protocol_manager::ProtocolManagerError::ConfigurationError(msg) => CommunicationError::ConfigurationError(msg),
            crate::communication::protocol_manager::ProtocolManagerError::ConnectionError(msg) => CommunicationError::ConnectionFailed(msg),
            crate::communication::protocol_manager::ProtocolManagerError::InitializationError(msg) => CommunicationError::ConfigurationError(msg),
            crate::communication::protocol_manager::ProtocolManagerError::ProtocolNotSupported(msg) => CommunicationError::ProtocolError(msg),
            crate::communication::protocol_manager::ProtocolManagerError::LoadBalancingError(msg) => CommunicationError::NetworkError(msg),
            crate::communication::protocol_manager::ProtocolManagerError::FailoverError(msg) => CommunicationError::NetworkError(msg),
        }
    }
}

/// 通信协议类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProtocolType {
    /// MQTT协议
    MQTT,
    /// CoAP协议
    CoAP,
    /// HTTP协议
    HTTP,
    /// WebSocket协议
    WebSocket,
    /// Modbus协议
    Modbus,
    /// OPC UA协议
    OPCUA,
    /// LoRaWAN协议
    LoRaWAN,
    /// Zigbee协议
    Zigbee,
    /// Bluetooth协议
    Bluetooth,
    /// 6LoWPAN协议
    SixLoWPAN,
}

/// 消息优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MessagePriority {
    /// 最低优先级
    Lowest = 0,
    /// 低优先级
    Low = 1,
    /// 普通优先级
    Normal = 2,
    /// 高优先级
    High = 3,
    /// 最高优先级
    Highest = 4,
}

/// 消息可靠性
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MessageReliability {
    /// 最多一次
    AtMostOnce,
    /// 至少一次
    AtLeastOnce,
    /// 恰好一次
    ExactlyOnce,
}

/// 通用消息结构
#[derive(Debug, Clone)]
pub struct Message {
    pub id: String,
    pub protocol: ProtocolType,
    pub topic: String,
    pub payload: Vec<u8>,
    pub priority: MessagePriority,
    pub reliability: MessageReliability,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub ttl: Option<std::time::Duration>,
    pub metadata: std::collections::HashMap<String, String>,
}

impl Message {
    /// 创建新消息
    pub fn new(
        protocol: ProtocolType,
        topic: String,
        payload: Vec<u8>,
    ) -> Self {
        Self {
            id: uuid::Uuid::new_v4().to_string(),
            protocol,
            topic,
            payload,
            priority: MessagePriority::Normal,
            reliability: MessageReliability::AtLeastOnce,
            timestamp: chrono::Utc::now(),
            ttl: None,
            metadata: std::collections::HashMap::new(),
        }
    }

    /// 设置消息优先级
    pub fn with_priority(mut self, priority: MessagePriority) -> Self {
        self.priority = priority;
        self
    }

    /// 设置消息可靠性
    pub fn with_reliability(mut self, reliability: MessageReliability) -> Self {
        self.reliability = reliability;
        self
    }

    /// 设置TTL
    pub fn with_ttl(mut self, ttl: std::time::Duration) -> Self {
        self.ttl = Some(ttl);
        self
    }

    /// 添加元数据
    pub fn with_metadata(mut self, key: String, value: String) -> Self {
        self.metadata.insert(key, value);
        self
    }

    /// 检查消息是否过期
    pub fn is_expired(&self) -> bool {
        if let Some(ttl) = self.ttl {
            chrono::Utc::now().signed_duration_since(self.timestamp).to_std().unwrap_or_default() > ttl
        } else {
            false
        }
    }

    /// 获取消息大小
    pub fn size(&self) -> usize {
        self.payload.len()
    }
}

/// 连接状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConnectionStatus {
    /// 断开连接
    Disconnected,
    /// 连接中
    Connecting,
    /// 已连接
    Connected,
    /// 重连中
    Reconnecting,
    /// 连接错误
    Error,
}

/// 连接信息
#[derive(Debug, Clone)]
pub struct ConnectionInfo {
    pub protocol: ProtocolType,
    pub endpoint: String,
    pub status: ConnectionStatus,
    pub connected_at: Option<chrono::DateTime<chrono::Utc>>,
    pub last_activity: Option<chrono::DateTime<chrono::Utc>>,
    pub message_count: u64,
    pub error_count: u64,
}

/// 通信统计信息
#[derive(Debug, Clone)]
pub struct CommunicationStats {
    pub total_messages_sent: u64,
    pub total_messages_received: u64,
    pub total_bytes_sent: u64,
    pub total_bytes_received: u64,
    pub connection_errors: u64,
    pub message_errors: u64,
    pub average_latency: std::time::Duration,
    pub uptime: std::time::Duration,
}

/// 通信管理器
#[allow(dead_code)]
#[derive(Clone)]
pub struct CommunicationManager {
    protocol_manager: ProtocolManager,
    connections: std::collections::HashMap<ProtocolType, ConnectionInfo>,
    stats: CommunicationStats,
    message_queue: std::collections::VecDeque<Message>,
    initialized: bool,
}

impl CommunicationManager {
    /// 创建新的通信管理器
    pub fn new() -> Self {
        Self {
            protocol_manager: ProtocolManager::new(),
            connections: std::collections::HashMap::new(),
            stats: CommunicationStats {
                total_messages_sent: 0,
                total_messages_received: 0,
                total_bytes_sent: 0,
                total_bytes_received: 0,
                connection_errors: 0,
                message_errors: 0,
                average_latency: std::time::Duration::ZERO,
                uptime: std::time::Duration::ZERO,
            },
            message_queue: std::collections::VecDeque::new(),
            initialized: false,
        }
    }

    /// 初始化通信管理器
    pub async fn initialize(&mut self) -> Result<(), CommunicationError> {
        if self.initialized {
            return Ok(());
        }

        self.protocol_manager.initialize().await?;
        self.initialized = true;
        Ok(())
    }

    /// 连接协议
    pub async fn connect(&mut self, protocol: ProtocolType, endpoint: String) -> Result<(), CommunicationError> {
        if !self.initialized {
            return Err(CommunicationError::ConfigurationError("通信管理器未初始化".to_string()));
        }

        let connection_info = ConnectionInfo {
            protocol,
            endpoint: endpoint.clone(),
            status: ConnectionStatus::Connecting,
            connected_at: None,
            last_activity: None,
            message_count: 0,
            error_count: 0,
        };

        self.connections.insert(protocol, connection_info);

        // 模拟连接过程
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;

        if let Some(conn) = self.connections.get_mut(&protocol) {
            conn.status = ConnectionStatus::Connected;
            conn.connected_at = Some(chrono::Utc::now());
        }

        Ok(())
    }

    /// 断开协议连接
    pub async fn disconnect(&mut self, protocol: ProtocolType) -> Result<(), CommunicationError> {
        if let Some(conn) = self.connections.get_mut(&protocol) {
            conn.status = ConnectionStatus::Disconnected;
            conn.connected_at = None;
        }
        Ok(())
    }

    /// 发送消息
    pub async fn send_message(&mut self, message: Message) -> Result<(), CommunicationError> {
        if !self.initialized {
            return Err(CommunicationError::ConfigurationError("通信管理器未初始化".to_string()));
        }

        if let Some(conn) = self.connections.get(&message.protocol) {
            if conn.status != ConnectionStatus::Connected {
                return Err(CommunicationError::ConnectionFailed(
                    format!("协议 {:?} 未连接", message.protocol)
                ));
            }
        } else {
            return Err(CommunicationError::ConnectionFailed(
                format!("协议 {:?} 未配置", message.protocol)
            ));
        }

        // 更新统计信息
        self.stats.total_messages_sent += 1;
        self.stats.total_bytes_sent += message.size() as u64;

        // 更新连接信息
        if let Some(conn) = self.connections.get_mut(&message.protocol) {
            conn.message_count += 1;
            conn.last_activity = Some(chrono::Utc::now());
        }

        Ok(())
    }

    /// 接收消息
    pub async fn receive_message(&mut self, protocol: ProtocolType) -> Result<Message, CommunicationError> {
        if !self.initialized {
            return Err(CommunicationError::ConfigurationError("通信管理器未初始化".to_string()));
        }

        // 模拟接收消息
        let message = Message::new(
            protocol,
            "test/topic".to_string(),
            b"test payload".to_vec(),
        );

        // 更新统计信息
        self.stats.total_messages_received += 1;
        self.stats.total_bytes_received += message.size() as u64;

        // 更新连接信息
        if let Some(conn) = self.connections.get_mut(&protocol) {
            conn.last_activity = Some(chrono::Utc::now());
        }

        Ok(message)
    }

    /// 获取连接状态
    pub fn get_connection_status(&self, protocol: ProtocolType) -> Option<ConnectionStatus> {
        self.connections.get(&protocol).map(|conn| conn.status)
    }

    /// 获取所有连接信息
    pub fn get_connections(&self) -> &std::collections::HashMap<ProtocolType, ConnectionInfo> {
        &self.connections
    }

    /// 获取通信统计信息
    pub fn get_stats(&self) -> &CommunicationStats {
        &self.stats
    }

    /// 获取协议管理器
    pub fn protocol_manager(&self) -> &ProtocolManager {
        &self.protocol_manager
    }
}

impl Default for CommunicationManager {
    fn default() -> Self {
        Self::new()
    }
}

/// 通信结果类型
pub type CommunicationResult<T> = Result<T, CommunicationError>;
