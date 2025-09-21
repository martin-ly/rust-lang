//! CoAP协议实现
//! 
//! 本模块提供了基于Rust 1.90的CoAP客户端实现，支持：
//! - CoAP RFC 7252标准
//! - GET, POST, PUT, DELETE方法
//! - 观察者模式
//! - 块传输
//! - DTLS安全传输

use std::collections::HashMap;
use std::time::Duration;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// CoAP客户端配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CoAPConfig {
    /// 服务器地址
    pub server: String,
    /// 端口号
    pub port: u16,
    /// 超时时间
    pub timeout: Duration,
    /// 重试次数
    pub retry_count: u8,
    /// 使用DTLS
    pub use_dtls: bool,
    /// 预共享密钥
    pub psk: Option<String>,
    /// 证书路径
    pub cert_path: Option<String>,
    /// 私钥路径
    pub key_path: Option<String>,
}

impl Default for CoAPConfig {
    fn default() -> Self {
        Self {
            server: "localhost".to_string(),
            port: 5683,
            timeout: Duration::from_secs(5),
            retry_count: 3,
            use_dtls: false,
            psk: None,
            cert_path: None,
            key_path: None,
        }
    }
}

/// CoAP方法
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum CoAPMethod {
    /// GET方法
    Get = 1,
    /// POST方法
    Post = 2,
    /// PUT方法
    Put = 3,
    /// DELETE方法
    Delete = 4,
}

/// CoAP消息
#[derive(Debug, Clone)]
pub struct CoAPMessage {
    /// 方法
    pub method: CoAPMethod,
    /// URI路径
    pub uri_path: String,
    /// 查询参数
    pub query_params: HashMap<String, String>,
    /// 消息内容
    pub payload: Vec<u8>,
    /// 内容类型
    pub content_format: Option<u16>,
    /// 消息ID
    pub message_id: u16,
    /// 令牌
    pub token: Vec<u8>,
    /// 确认标志
    pub confirmable: bool,
    /// 时间戳
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

impl CoAPMessage {
    /// 创建新消息
    pub fn new(method: CoAPMethod, uri_path: _uri_path) -> Self {
        Self {
            method,
            uri_path,
            query_params: HashMap::new(),
            payload: Vec::new(),
            content_format: None,
            message_id: 0x1234, // 模拟消息ID
            token: Vec::new(),
            confirmable: true,
            timestamp: chrono::Utc::now(),
        }
    }

    /// 设置查询参数
    pub fn with_query_param(mut self, key: String, value: _value) -> Self {
        self.query_params.insert(key, value);
        self
    }

    /// 设置消息内容
    pub fn with_payload(mut self, payload: Vec<u8>) -> Self {
        self.payload = payload;
        self
    }

    /// 设置内容类型
    pub fn with_content_format(mut self, format: _format) -> Self {
        self.content_format = Some(format);
        self
    }

    /// 设置确认标志
    pub fn with_confirmable(mut self, confirmable: _confirmable) -> Self {
        self.confirmable = confirmable;
        self
    }
}

/// CoAP错误类型
#[derive(Debug, Error)]
pub enum CoAPError {
    #[error("网络错误: {0}")]
    NetworkError(String),
    
    #[error("超时错误: {0}")]
    TimeoutError(String),
    
    #[error("协议错误: {0}")]
    ProtocolError(String),
    
    #[error("序列化错误: {0}")]
    SerializationError(String),
    
    #[error("反序列化错误: {0}")]
    DeserializationError(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("DTLS错误: {0}")]
    DTLSError(String),
    
    #[error("响应错误: {0}")]
    ResponseError(String),
    
    #[error("观察者错误: {0}")]
    ObserverError(String),
    
    #[error("块传输错误: {0}")]
    BlockTransferError(String),
}

/// CoAP观察者配置
#[derive(Debug, Clone)]
pub struct ObserverConfig {
    pub uri: String,
    pub max_age: Option<u32>,
    pub observe: bool,
    pub callback: Option<Box<dyn Fn(CoAPResponse) + Send + Sync>>,
}

/// CoAP块传输配置
#[derive(Debug, Clone)]
pub struct BlockConfig {
    pub block_size: u16,
    pub more_blocks: bool,
    pub block_number: u32,
}

/// CoAP连接状态
#[derive(Debug, Clone, PartialEq)]
pub enum CoAPConnectionState {
    Disconnected,
    Connecting,
    Connected,
    Error,
}

/// CoAP客户端
#[derive(Debug)]
pub struct CoAPClient {
    config: CoAPConfig,
    connected: bool,
    connection_state: CoAPConnectionState,
    stats: CoAPStats,
    observers: HashMap<String, ObserverConfig>,
    block_transfers: HashMap<String, BlockConfig>,
}

/// CoAP统计信息
#[derive(Debug, Clone)]
pub struct CoAPStats {
    pub requests_sent: u64,
    pub responses_received: u64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub timeouts: u64,
    pub errors: u64,
    pub last_activity: Option<chrono::DateTime<chrono::Utc>>,
}

impl CoAPClient {
    /// 创建新的CoAP客户端
    pub fn new(config: _config) -> Self {
        Self {
            config,
            connected: false,
            connection_state: CoAPConnectionState::Disconnected,
            stats: CoAPStats {
                requests_sent: 0,
                responses_received: 0,
                bytes_sent: 0,
                bytes_received: 0,
                timeouts: 0,
                errors: 0,
                average_response_time: None,
                last_activity: None,
            },
            observers: HashMap::new(),
            block_transfers: HashMap::new(),
        }
    }

    /// 连接到CoAP服务器
    pub async fn connect(&mut self) -> Result<(), CoAPError> {
        if self.connected {
            return Ok(());
        }

        // 模拟连接过程
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        self.connected = true;
        self.stats.last_activity = Some(chrono::Utc::now());
        
        Ok(())
    }

    /// 断开连接
    pub async fn disconnect(&mut self) -> Result<(), CoAPError> {
        if !self.connected {
            return Ok(());
        }

        // 模拟断开连接过程
        tokio::time::sleep(Duration::from_millis(50)).await;
        
        self.connected = false;
        
        Ok(())
    }

    /// 发送请求
    pub async fn send_request(&mut self, message: _message) -> Result<CoAPMessage, CoAPError> {
        if !self.connected {
            return Err(CoAPError::NetworkError("客户端未连接".to_string()));
        }

        // 模拟发送请求
        tokio::time::sleep(Duration::from_millis(50)).await;
        
        self.stats.requests_sent += 1;
        self.stats.bytes_sent += message.payload.len() as u64;
        self.stats.last_activity = Some(chrono::Utc::now());

        // 模拟响应
        let response = CoAPMessage {
            method: CoAPMethod::Get,
            uri_path: message.uri_path.clone(),
            query_params: HashMap::new(),
            payload: b"response data".to_vec(),
            content_format: Some(50), // text/plain
            message_id: message.message_id,
            token: message.token.clone(),
            confirmable: false,
            timestamp: chrono::Utc::now(),
        };

        self.stats.responses_received += 1;
        self.stats.bytes_received += response.payload.len() as u64;
        
        Ok(response)
    }

    /// 检查是否已连接
    pub fn is_connected(&self) -> bool {
        self.connected
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> &CoAPStats {
        &self.stats
    }

    /// 获取配置
    pub fn get_config(&self) -> &CoAPConfig {
        &self.config
    }

    /// 获取连接状态
    pub fn get_connection_state(&self) -> &CoAPConnectionState {
        &self.connection_state
    }

    /// 添加观察者
    pub fn add_observer(&mut self, uri: String, config: _config) -> Result<(), CoAPError> {
        if !self.connected {
            return Err(CoAPError::NetworkError("客户端未连接".to_string()));
        }

        self.observers.insert(uri, config);
        Ok(())
    }

    /// 移除观察者
    pub fn remove_observer(&mut self, uri: &str) -> Option<ObserverConfig> {
        self.observers.remove(uri)
    }

    /// 获取所有观察者
    pub fn get_observers(&self) -> &HashMap<String, ObserverConfig> {
        &self.observers
    }

    /// 开始块传输
    pub async fn start_block_transfer(&mut self, uri: String, config: _config) -> Result<(), CoAPError> {
        if !self.connected {
            return Err(CoAPError::NetworkError("客户端未连接".to_string()));
        }

        self.block_transfers.insert(uri, config);
        Ok(())
    }

    /// 完成块传输
    pub fn complete_block_transfer(&mut self, uri: &str) -> Option<BlockConfig> {
        self.block_transfers.remove(uri)
    }

    /// 获取块传输状态
    pub fn get_block_transfer(&self, uri: &str) -> Option<&BlockConfig> {
        self.block_transfers.get(uri)
    }

    /// 批量请求
    pub async fn batch_request(&mut self, requests: Vec<CoAPRequest>) -> Result<Vec<CoAPResponse>, CoAPError> {
        if !self.connected {
            return Err(CoAPError::NetworkError("客户端未连接".to_string()));
        }

        let mut responses = Vec::new();
        for request in requests {
            let response = self.send_request(request).await?;
            responses.push(response);
        }
        
        Ok(responses)
    }

    /// 健康检查
    pub async fn health_check(&mut self) -> Result<bool, CoAPError> {
        if !self.connected {
            return Ok(false);
        }

        let ping_request = CoAPRequest::new(CoAPMethod::GET, "/.well-known/core".to_string());
        let response = self.send_request(ping_request).await?;
        
        Ok(response.status_code >= 200 && response.status_code < 300)
    }

    /// 获取连接信息
    pub fn get_connection_info(&self) -> HashMap<String, String> {
        let mut info = HashMap::new();
        info.insert("server".to_string(), self.config.server.clone());
        info.insert("port".to_string(), self.config.port.to_string());
        info.insert("connected".to_string(), self.connected.to_string());
        info.insert("state".to_string(), format!("{:?}", self.connection_state));
        info.insert("observers".to_string(), self.observers.len().to_string());
        info.insert("block_transfers".to_string(), self.block_transfers.len().to_string());
        info
    }

    /// 重置统计信息
    pub fn reset_stats(&mut self) {
        self.stats = CoAPStats {
            requests_sent: 0,
            responses_received: 0,
            bytes_sent: 0,
            bytes_received: 0,
            timeouts: 0,
            errors: 0,
            average_response_time: None,
            last_activity: None,
        };
    }

    /// 设置超时时间
    pub fn set_timeout(&mut self, timeout: _timeout) {
        self.config.timeout = timeout;
    }

    /// 启用DTLS
    pub fn enable_dtls(&mut self, psk: Option<String>, cert_path: Option<String>, key_path: Option<String>) {
        self.config.use_dtls = true;
        self.config.psk = psk;
        self.config.cert_path = cert_path;
        self.config.key_path = key_path;
    }

    /// 禁用DTLS
    pub fn disable_dtls(&mut self) {
        self.config.use_dtls = false;
        self.config.psk = None;
        self.config.cert_path = None;
        self.config.key_path = None;
    }
}

impl Default for CoAPClient {
    fn default() -> Self {
        Self::new(CoAPConfig::default())
    }
}
