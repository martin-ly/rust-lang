//! 协议管理器
//! 
//! 本模块提供了基于Rust 1.90的协议管理器实现，支持：
//! - 多协议统一管理
//! - 协议选择和切换
//! - 负载均衡
//! - 故障转移
//! - 性能监控

use std::collections::HashMap;
use std::time::Duration;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use super::{
    ProtocolType, Message,
    // mqtt::{MQTTClient, MQTTConfig},
    // coap::{CoAPClient, CoAPConfig},
    // http::{HTTPClient, HTTPConfig},
    // websocket::{WebSocketClient, WebSocketConfig},
    // modbus::{ModbusClient, ModbusConfig},
    // opcua::{OPCUAClient, OPCUAConfig},
    // lorawan::{LoRaWANClient, LoRaWANConfig},
    // zigbee::{ZigbeeClient, ZigbeeConfig},
    // bluetooth::{BluetoothClient, BluetoothConfig},
    // sixlowpan::{SixLoWPANClient, SixLoWPANConfig},
};

/// 协议信息
#[derive(Debug, Clone)]
pub struct ProtocolInfo {
    /// 协议类型
    pub protocol_type: ProtocolType,
    /// 协议名称
    pub name: String,
    /// 协议版本
    pub version: String,
    /// 是否启用
    pub enabled: bool,
    /// 优先级
    pub priority: u8,
    /// 最大连接数
    pub max_connections: u32,
    /// 当前连接数
    pub current_connections: u32,
    /// 最后使用时间
    pub last_used: Option<chrono::DateTime<chrono::Utc>>,
}

/// 协议配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProtocolConfig {
    // /// MQTT配置
    // pub mqtt: Option<MQTTConfig>,
    // /// CoAP配置
    // pub coap: Option<CoAPConfig>,
    // /// HTTP配置
    // pub http: Option<HTTPConfig>,
    // /// WebSocket配置
    // pub websocket: Option<WebSocketConfig>,
    // /// Modbus配置
    // pub modbus: Option<ModbusConfig>,
    // /// OPC UA配置
    // pub opcua: Option<OPCUAConfig>,
    // /// LoRaWAN配置
    // pub lorawan: Option<LoRaWANConfig>,
    // /// Zigbee配置
    // pub zigbee: Option<ZigbeeConfig>,
    // /// Bluetooth配置
    // pub bluetooth: Option<BluetoothConfig>,
    // /// 6LoWPAN配置
    // pub sixlowpan: Option<SixLoWPANConfig>,
}

/// 协议管理器错误类型
#[derive(Debug, Error)]
pub enum ProtocolManagerError {
    #[error("协议错误: {0}")]
    ProtocolError(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("连接错误: {0}")]
    ConnectionError(String),
    
    #[error("初始化错误: {0}")]
    InitializationError(String),
    
    #[error("协议不支持: {0}")]
    ProtocolNotSupported(String),
    
    #[error("负载均衡错误: {0}")]
    LoadBalancingError(String),
    
    #[error("故障转移错误: {0}")]
    FailoverError(String),
}

/// 协议客户端枚举
// pub enum ProtocolClient {
//     MQTT(MQTTClient),
//     CoAP(CoAPClient),
//     HTTP(HTTPClient),
//     WebSocket(WebSocketClient),
//     Modbus(ModbusClient),
//     OPCUA(OPCUAClient),
//     LoRaWAN(LoRaWANClient),
//     Zigbee(ZigbeeClient),
//     Bluetooth(BluetoothClient),
//     SixLoWPAN(SixLoWPANClient),
// }

/// 协议管理器
#[derive(Clone)]
pub struct ProtocolManager {
    protocols: HashMap<ProtocolType, ProtocolInfo>,
    // clients: HashMap<ProtocolType, ProtocolClient>,
    config: ProtocolConfig,
    stats: ProtocolManagerStats,
    initialized: bool,
}

/// 协议管理器统计信息
#[derive(Debug, Clone)]
pub struct ProtocolManagerStats {
    pub total_requests: u64,
    pub successful_requests: u64,
    pub failed_requests: u64,
    pub protocol_switches: u64,
    pub failover_events: u64,
    pub average_response_time: Duration,
    pub uptime: Duration,
    pub last_activity: Option<chrono::DateTime<chrono::Utc>>,
}

impl ProtocolManager {
    /// 创建新的协议管理器
    pub fn new() -> Self {
        let mut protocols = HashMap::new();
        
        // 初始化协议信息
        protocols.insert(ProtocolType::MQTT, ProtocolInfo {
            protocol_type: ProtocolType::MQTT,
            name: "MQTT".to_string(),
            version: "3.1.1".to_string(),
            enabled: true,
            priority: 5,
            max_connections: 100,
            current_connections: 0,
            last_used: None,
        });
        
        protocols.insert(ProtocolType::CoAP, ProtocolInfo {
            protocol_type: ProtocolType::CoAP,
            name: "CoAP".to_string(),
            version: "RFC 7252".to_string(),
            enabled: true,
            priority: 4,
            max_connections: 50,
            current_connections: 0,
            last_used: None,
        });
        
        protocols.insert(ProtocolType::HTTP, ProtocolInfo {
            protocol_type: ProtocolType::HTTP,
            name: "HTTP".to_string(),
            version: "1.1".to_string(),
            enabled: true,
            priority: 3,
            max_connections: 200,
            current_connections: 0,
            last_used: None,
        });
        
        protocols.insert(ProtocolType::WebSocket, ProtocolInfo {
            protocol_type: ProtocolType::WebSocket,
            name: "WebSocket".to_string(),
            version: "RFC 6455".to_string(),
            enabled: true,
            priority: 4,
            max_connections: 100,
            current_connections: 0,
            last_used: None,
        });
        
        protocols.insert(ProtocolType::Modbus, ProtocolInfo {
            protocol_type: ProtocolType::Modbus,
            name: "Modbus".to_string(),
            version: "TCP/RTU".to_string(),
            enabled: true,
            priority: 6,
            max_connections: 20,
            current_connections: 0,
            last_used: None,
        });
        
        protocols.insert(ProtocolType::OPCUA, ProtocolInfo {
            protocol_type: ProtocolType::OPCUA,
            name: "OPC UA".to_string(),
            version: "1.04".to_string(),
            enabled: true,
            priority: 7,
            max_connections: 10,
            current_connections: 0,
            last_used: None,
        });
        
        protocols.insert(ProtocolType::LoRaWAN, ProtocolInfo {
            protocol_type: ProtocolType::LoRaWAN,
            name: "LoRaWAN".to_string(),
            version: "1.0.3".to_string(),
            enabled: true,
            priority: 8,
            max_connections: 1000,
            current_connections: 0,
            last_used: None,
        });
        
        protocols.insert(ProtocolType::Zigbee, ProtocolInfo {
            protocol_type: ProtocolType::Zigbee,
            name: "Zigbee".to_string(),
            version: "3.0".to_string(),
            enabled: true,
            priority: 6,
            max_connections: 100,
            current_connections: 0,
            last_used: None,
        });
        
        protocols.insert(ProtocolType::Bluetooth, ProtocolInfo {
            protocol_type: ProtocolType::Bluetooth,
            name: "Bluetooth".to_string(),
            version: "5.0".to_string(),
            enabled: true,
            priority: 5,
            max_connections: 50,
            current_connections: 0,
            last_used: None,
        });
        
        protocols.insert(ProtocolType::SixLoWPAN, ProtocolInfo {
            protocol_type: ProtocolType::SixLoWPAN,
            name: "6LoWPAN".to_string(),
            version: "RFC 4944".to_string(),
            enabled: true,
            priority: 7,
            max_connections: 200,
            current_connections: 0,
            last_used: None,
        });

        Self {
            protocols,
            // clients: HashMap::new(),
            config: ProtocolConfig {
                // mqtt: None,
                // coap: None,
                // http: None,
                // websocket: None,
                // modbus: None,
                // opcua: None,
                // lorawan: None,
                // zigbee: None,
                // bluetooth: None,
                // sixlowpan: None,
            },
            stats: ProtocolManagerStats {
                total_requests: 0,
                successful_requests: 0,
                failed_requests: 0,
                protocol_switches: 0,
                failover_events: 0,
                average_response_time: Duration::ZERO,
                uptime: Duration::ZERO,
                last_activity: None,
            },
            initialized: false,
        }
    }

    /// 初始化协议管理器
    pub async fn initialize(&mut self) -> Result<(), ProtocolManagerError> {
        if self.initialized {
            return Ok(());
        }

        // 初始化所有启用的协议客户端
        // for (protocol_type, protocol_info) in &self.protocols.clone() {
        //     if protocol_info.enabled {
        //         self.initialize_protocol_client(*protocol_type).await?;
        //     }
        // }

        self.initialized = true;
        self.stats.last_activity = Some(chrono::Utc::now());
        
        Ok(())
    }

    // /// 初始化协议客户端
    // async fn initialize_protocol_client(&mut self, protocol_type: _protocol_type) -> Result<(), ProtocolManagerError> {
    //     let client = match protocol_type {
    //         ProtocolType::MQTT => {
    //             let config = self.config.mqtt.clone().unwrap_or_default();
    //             ProtocolClient::MQTT(MQTTClient::new(config))
    //         },
    //         ProtocolType::CoAP => {
    //             let config = self.config.coap.clone().unwrap_or_default();
    //             ProtocolClient::CoAP(CoAPClient::new(config))
    //         },
    //         ProtocolType::HTTP => {
    //             let config = self.config.http.clone().unwrap_or_default();
    //             ProtocolClient::HTTP(HTTPClient::new(config))
    //         },
    //         ProtocolType::WebSocket => {
    //             let config = self.config.websocket.clone().unwrap_or_default();
    //             ProtocolClient::WebSocket(WebSocketClient::new(config))
    //         },
    //         ProtocolType::Modbus => {
    //             let config = self.config.modbus.clone().unwrap_or_default();
    //             ProtocolClient::Modbus(ModbusClient::new(config))
    //         },
    //         ProtocolType::OPCUA => {
    //             let config = self.config.opcua.clone().unwrap_or_default();
    //             ProtocolClient::OPCUA(OPCUAClient::new(config))
    //         },
    //         ProtocolType::LoRaWAN => {
    //             let config = self.config.lorawan.clone().unwrap_or_default();
    //             ProtocolClient::LoRaWAN(LoRaWANClient::new(config))
    //         },
    //         ProtocolType::Zigbee => {
    //             let config = self.config.zigbee.clone().unwrap_or_default();
    //             ProtocolClient::Zigbee(ZigbeeClient::new(config))
    //         },
    //         ProtocolType::Bluetooth => {
    //             let config = self.config.bluetooth.clone().unwrap_or_default();
    //             ProtocolClient::Bluetooth(BluetoothClient::new(config))
    //         },
    //         ProtocolType::SixLoWPAN => {
    //             let config = self.config.sixlowpan.clone().unwrap_or_default();
    //             ProtocolClient::SixLoWPAN(SixLoWPANClient::new(config))
    //         },
    //     };

    //     self.clients.insert(protocol_type, client);
    //     Ok(())
    // }

    /// 选择最佳协议
    pub fn select_best_protocol(&self, _message: &Message) -> Result<ProtocolType, ProtocolManagerError> {
        let mut available_protocols: Vec<_> = self.protocols
            .iter()
            .filter(|(_, info)| info.enabled && info.current_connections < info.max_connections)
            .collect();

        // 按优先级排序
        available_protocols.sort_by(|a, b| b.1.priority.cmp(&a.1.priority));

        if available_protocols.is_empty() {
            return Err(ProtocolManagerError::ProtocolError("没有可用的协议".to_string()));
        }

        // 选择优先级最高的协议
        Ok(*available_protocols[0].0)
    }

    /// 发送消息
    pub async fn send_message(&mut self, message: Message) -> Result<(), ProtocolManagerError> {
        if !self.initialized {
            return Err(ProtocolManagerError::InitializationError("协议管理器未初始化".to_string()));
        }

        self.stats.total_requests += 1;
        self.stats.last_activity = Some(chrono::Utc::now());

        // 选择最佳协议
        let protocol_type = self.select_best_protocol(&message)?;

        // 更新协议使用时间
        if let Some(protocol_info) = self.protocols.get_mut(&protocol_type) {
            protocol_info.last_used = Some(chrono::Utc::now());
            protocol_info.current_connections += 1;
        }

        // 发送消息（这里只是模拟）
        tokio::time::sleep(Duration::from_millis(10)).await;

        self.stats.successful_requests += 1;

        // 减少连接计数
        if let Some(protocol_info) = self.protocols.get_mut(&protocol_type) {
            protocol_info.current_connections = protocol_info.current_connections.saturating_sub(1);
        }

        Ok(())
    }

    /// 获取协议信息
    pub fn get_protocol_info(&self, protocol_type: ProtocolType) -> Option<&ProtocolInfo> {
        self.protocols.get(&protocol_type)
    }

    /// 获取所有协议信息
    pub fn get_all_protocols(&self) -> &HashMap<ProtocolType, ProtocolInfo> {
        &self.protocols
    }

    /// 启用协议
    pub fn enable_protocol(&mut self, protocol_type: ProtocolType) -> Result<(), ProtocolManagerError> {
        if let Some(protocol_info) = self.protocols.get_mut(&protocol_type) {
            protocol_info.enabled = true;
            Ok(())
        } else {
            Err(ProtocolManagerError::ProtocolNotSupported(format!("协议 {:?} 不支持", protocol_type)))
        }
    }

    /// 禁用协议
    pub fn disable_protocol(&mut self, protocol_type: ProtocolType) -> Result<(), ProtocolManagerError> {
        if let Some(protocol_info) = self.protocols.get_mut(&protocol_type) {
            protocol_info.enabled = false;
            Ok(())
        } else {
            Err(ProtocolManagerError::ProtocolNotSupported(format!("协议 {:?} 不支持", protocol_type)))
        }
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> &ProtocolManagerStats {
        &self.stats
    }

    /// 获取配置
    pub fn get_config(&self) -> &ProtocolConfig {
        &self.config
    }

    /// 设置配置
    pub fn set_config(&mut self, config: ProtocolConfig) {
        self.config = config;
    }
}

impl Default for ProtocolManager {
    fn default() -> Self {
        Self::new()
    }
}
