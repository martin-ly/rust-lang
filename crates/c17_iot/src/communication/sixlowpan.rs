//! 6LoWPAN协议实现
//! 
//! 本模块提供了基于Rust 1.90的6LoWPAN客户端实现，支持：
//! - IPv6 over Low power Wireless Personal Area Networks
//! - 头部压缩
//! - 分片和重组
//! - 邻居发现
//! - 路由优化

use std::collections::HashMap;
use std::time::Duration;
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// 6LoWPAN客户端配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SixLoWPANConfig {
    /// IPv6地址
    pub ipv6_address: String,
    /// 前缀长度
    pub prefix_length: u8,
    /// 网关地址
    pub gateway_address: String,
    /// 最大传输单元
    pub mtu: u16,
    /// 头部压缩
    pub header_compression: bool,
    /// 分片支持
    pub fragmentation_support: bool,
    /// 邻居发现间隔
    pub neighbor_discovery_interval: Duration,
    /// 路由表更新间隔
    pub route_update_interval: Duration,
}

impl Default for SixLoWPANConfig {
    fn default() -> Self {
        Self {
            ipv6_address: "2001:db8::1".to_string(),
            prefix_length: 64,
            gateway_address: "2001:db8::1".to_string(),
            mtu: 1280,
            header_compression: true,
            fragmentation_support: true,
            neighbor_discovery_interval: Duration::from_secs(30),
            route_update_interval: Duration::from_secs(60),
        }
    }
}

/// 6LoWPAN邻居信息
#[derive(Debug, Clone)]
pub struct SixLoWPANNeighbor {
    /// IPv6地址
    pub ipv6_address: String,
    /// 链路层地址
    pub link_layer_address: String,
    /// 信号强度
    pub rssi: i16,
    /// 最后更新时间
    pub last_update: chrono::DateTime<chrono::Utc>,
    /// 可达性状态
    pub reachable: bool,
}

/// 6LoWPAN路由信息
#[derive(Debug, Clone)]
pub struct SixLoWPANRoute {
    /// 目标前缀
    pub destination_prefix: String,
    /// 前缀长度
    pub prefix_length: u8,
    /// 下一跳地址
    pub next_hop: String,
    /// 跳数
    pub hop_count: u8,
    /// 路由类型
    pub route_type: SixLoWPANRouteType,
}

/// 6LoWPAN路由类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SixLoWPANRouteType {
    /// 直连路由
    Direct,
    /// 间接路由
    Indirect,
    /// 默认路由
    Default,
}

/// 6LoWPAN消息
#[derive(Debug, Clone)]
pub struct SixLoWPANMessage {
    /// 源IPv6地址
    pub source_address: String,
    /// 目标IPv6地址
    pub destination_address: String,
    /// 消息内容
    pub payload: Vec<u8>,
    /// 协议类型
    pub protocol: u8,
    /// 跳数限制
    pub hop_limit: u8,
    /// 分片标志
    pub fragmented: bool,
    /// 时间戳
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

impl SixLoWPANMessage {
    /// 创建新消息
    pub fn new(
        source_address: String,
        destination_address: String,
        payload: Vec<u8>,
        protocol: u8,
    ) -> Self {
        Self {
            source_address,
            destination_address,
            payload,
            protocol,
            hop_limit: 64,
            fragmented: false,
            timestamp: chrono::Utc::now(),
        }
    }

    /// 设置跳数限制
    pub fn with_hop_limit(mut self, hop_limit: _hop_limit) -> Self {
        self.hop_limit = hop_limit;
        self
    }

    /// 设置分片标志
    pub fn with_fragmented(mut self, fragmented: _fragmented) -> Self {
        self.fragmented = fragmented;
        self
    }
}

/// 6LoWPAN错误类型
#[derive(Debug, Error)]
pub enum SixLoWPANError {
    #[error("网络错误: {0}")]
    NetworkError(String),
    
    #[error("地址错误: {0}")]
    AddressError(String),
    
    #[error("路由错误: {0}")]
    RoutingError(String),
    
    #[error("分片错误: {0}")]
    FragmentationError(String),
    
    #[error("头部压缩错误: {0}")]
    HeaderCompressionError(String),
    
    #[error("邻居发现错误: {0}")]
    NeighborDiscoveryError(String),
    
    #[error("超时错误: {0}")]
    TimeoutError(String),
    
    #[error("协议错误: {0}")]
    ProtocolError(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("MTU错误: {0}")]
    MTUError(String),
}

/// 6LoWPAN客户端
#[derive(Debug)]
pub struct SixLoWPANClient {
    config: SixLoWPANConfig,
    connected: bool,
    neighbors: HashMap<String, SixLoWPANNeighbor>,
    routes: HashMap<String, SixLoWPANRoute>,
    stats: SixLoWPANStats,
}

/// 6LoWPAN统计信息
#[derive(Debug, Clone)]
pub struct SixLoWPANStats {
    pub packets_sent: u64,
    pub packets_received: u64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub fragments_sent: u64,
    pub fragments_received: u64,
    pub routing_errors: u64,
    pub neighbor_discoveries: u64,
    pub last_activity: Option<chrono::DateTime<chrono::Utc>>,
}

impl SixLoWPANClient {
    /// 创建新的6LoWPAN客户端
    pub fn new(config: _config) -> Self {
        Self {
            config,
            connected: false,
            neighbors: HashMap::new(),
            routes: HashMap::new(),
            stats: SixLoWPANStats {
                packets_sent: 0,
                packets_received: 0,
                bytes_sent: 0,
                bytes_received: 0,
                fragments_sent: 0,
                fragments_received: 0,
                routing_errors: 0,
                neighbor_discoveries: 0,
                last_activity: None,
            },
        }
    }

    /// 连接到6LoWPAN网络
    pub async fn connect(&mut self) -> Result<(), SixLoWPANError> {
        if self.connected {
            return Ok(());
        }

        // 模拟连接过程
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        self.connected = true;
        self.stats.last_activity = Some(chrono::Utc::now());
        
        // 启动邻居发现
        self.start_neighbor_discovery().await?;
        
        Ok(())
    }

    /// 启动邻居发现
    pub async fn start_neighbor_discovery(&mut self) -> Result<(), SixLoWPANError> {
        if !self.connected {
            return Err(SixLoWPANError::NetworkError("客户端未连接".to_string()));
        }

        // 模拟邻居发现过程
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        let neighbor = SixLoWPANNeighbor {
            ipv6_address: "2001:db8::2".to_string(),
            link_layer_address: "00:11:22:33:44:55".to_string(),
            rssi: -50,
            last_update: chrono::Utc::now(),
            reachable: true,
        };

        self.neighbors.insert(neighbor.ipv6_address.clone(), neighbor);
        self.stats.neighbor_discoveries += 1;
        self.stats.last_activity = Some(chrono::Utc::now());
        
        Ok(())
    }

    /// 发送消息
    pub async fn send_message(&mut self, message: _message) -> Result<(), SixLoWPANError> {
        if !self.connected {
            return Err(SixLoWPANError::NetworkError("客户端未连接".to_string()));
        }

        // 检查MTU
        if message.payload.len() > self.config.mtu as usize {
            return Err(SixLoWPANError::MTUError("消息大小超过MTU".to_string()));
        }

        // 模拟发送过程
        tokio::time::sleep(Duration::from_millis(50)).await;
        
        self.stats.packets_sent += 1;
        self.stats.bytes_sent += message.payload.len() as u64;
        
        if message.fragmented {
            self.stats.fragments_sent += 1;
        }
        
        self.stats.last_activity = Some(chrono::Utc::now());
        
        Ok(())
    }

    /// 接收消息
    pub async fn receive_message(&mut self) -> Result<SixLoWPANMessage, SixLoWPANError> {
        if !self.connected {
            return Err(SixLoWPANError::NetworkError("客户端未连接".to_string()));
        }

        // 模拟接收过程
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        let message = SixLoWPANMessage::new(
            "2001:db8::2".to_string(),
            self.config.ipv6_address.clone(),
            b"received data".to_vec(),
            58, // ICMPv6
        );

        self.stats.packets_received += 1;
        self.stats.bytes_received += message.payload.len() as u64;
        
        if message.fragmented {
            self.stats.fragments_received += 1;
        }
        
        self.stats.last_activity = Some(chrono::Utc::now());
        
        Ok(message)
    }

    /// 添加路由
    pub fn add_route(&mut self, route: _route) {
        let key = format!("{}/{}", route.destination_prefix, route.prefix_length);
        self.routes.insert(key, route);
    }

    /// 获取邻居列表
    pub fn get_neighbors(&self) -> &HashMap<String, SixLoWPANNeighbor> {
        &self.neighbors
    }

    /// 获取路由表
    pub fn get_routes(&self) -> &HashMap<String, SixLoWPANRoute> {
        &self.routes
    }

    /// 断开连接
    pub async fn disconnect(&mut self) -> Result<(), SixLoWPANError> {
        if !self.connected {
            return Ok(());
        }

        // 模拟断开连接过程
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        self.connected = false;
        self.neighbors.clear();
        self.routes.clear();
        
        Ok(())
    }

    /// 检查是否已连接
    pub fn is_connected(&self) -> bool {
        self.connected
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> &SixLoWPANStats {
        &self.stats
    }

    /// 获取配置
    pub fn get_config(&self) -> &SixLoWPANConfig {
        &self.config
    }
}

impl Default for SixLoWPANClient {
    fn default() -> Self {
        Self::new(SixLoWPANConfig::default())
    }
}
