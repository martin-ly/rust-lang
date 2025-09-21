# IoT代码模板和示例 - Rust 1.90

## 🎯 模板概览

本文档提供了基于Rust 1.90的IoT开发代码模板和实际示例，涵盖从基础设备管理到复杂边缘计算的完整解决方案。

## 📁 模板结构

```text
templates/
├── basic_device/           # 基础设备管理
├── sensor_network/         # 传感器网络
├── edge_computing/         # 边缘计算
├── cloud_integration/      # 云平台集成
├── security_implementation/ # 安全实现
└── monitoring_system/      # 监控系统
```

## 🚀 基础设备管理模板

### 1. 设备管理器

```rust
// templates/basic_device/device_manager.rs
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::sync::{RwLock, mpsc};
use thiserror::Error;
use chrono::{DateTime, Utc};

#[derive(Debug, Error)]
pub enum DeviceError {
    #[error("设备未找到: {0}")]
    DeviceNotFound(String),
    #[error("设备已存在: {0}")]
    DeviceExists(String),
    #[error("设备离线: {0}")]
    DeviceOffline(String),
    #[error("通信错误: {0}")]
    CommunicationError(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceConfig {
    pub id: String,
    pub name: String,
    pub device_type: DeviceType,
    pub protocol: Protocol,
    pub endpoint: String,
    pub location: Option<String>,
    pub metadata: HashMap<String, String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DeviceType {
    Sensor,
    Actuator,
    Gateway,
    Controller,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Protocol {
    MQTT,
    CoAP,
    HTTP,
    WebSocket,
    Modbus,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceStatus {
    pub device_id: String,
    pub status: Status,
    pub last_seen: DateTime<Utc>,
    pub battery_level: Option<u8>,
    pub signal_strength: Option<i8>,
    pub error_count: u32,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Status {
    Online,
    Offline,
    Maintenance,
    Error,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceData {
    pub device_id: String,
    pub timestamp: DateTime<Utc>,
    pub data_type: String,
    pub value: serde_json::Value,
    pub quality: DataQuality,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DataQuality {
    Good,
    Uncertain,
    Bad,
}

pub struct DeviceManager {
    devices: RwLock<HashMap<String, DeviceConfig>>,
    statuses: RwLock<HashMap<String, DeviceStatus>>,
    data_sender: mpsc::UnboundedSender<DeviceData>,
}

impl DeviceManager {
    pub fn new() -> (Self, mpsc::UnboundedReceiver<DeviceData>) {
        let (data_sender, data_receiver) = mpsc::unbounded_channel();
        
        let manager = Self {
            devices: RwLock::new(HashMap::new()),
            statuses: RwLock::new(HashMap::new()),
            data_sender,
        };
        
        (manager, data_receiver)
    }
    
    pub async fn register_device(&self, config: DeviceConfig) -> Result<(), DeviceError> {
        let mut devices = self.devices.write().await;
        
        if devices.contains_key(&config.id) {
            return Err(DeviceError::DeviceExists(config.id.clone()));
        }
        
        devices.insert(config.id.clone(), config);
        
        // 初始化设备状态
        let mut statuses = self.statuses.write().await;
        statuses.insert(config.id.clone(), DeviceStatus {
            device_id: config.id.clone(),
            status: Status::Offline,
            last_seen: Utc::now(),
            battery_level: None,
            signal_strength: None,
            error_count: 0,
        });
        
        Ok(())
    }
    
    pub async fn get_device(&self, device_id: &str) -> Result<DeviceConfig, DeviceError> {
        let devices = self.devices.read().await;
        devices.get(device_id)
            .cloned()
            .ok_or_else(|| DeviceError::DeviceNotFound(device_id.to_string()))
    }
    
    pub async fn update_device_status(&self, device_id: &str, status: Status) -> Result<(), DeviceError> {
        let mut statuses = self.statuses.write().await;
        
        if let Some(device_status) = statuses.get_mut(device_id) {
            device_status.status = status;
            device_status.last_seen = Utc::now();
        } else {
            return Err(DeviceError::DeviceNotFound(device_id.to_string()));
        }
        
        Ok(())
    }
    
    pub async fn send_device_data(&self, data: DeviceData) -> Result<(), DeviceError> {
        self.data_sender.send(data)
            .map_err(|_| DeviceError::CommunicationError("数据发送失败".to_string()))
    }
    
    pub async fn get_all_devices(&self) -> Vec<DeviceConfig> {
        let devices = self.devices.read().await;
        devices.values().cloned().collect()
    }
    
    pub async fn get_device_status(&self, device_id: &str) -> Result<DeviceStatus, DeviceError> {
        let statuses = self.statuses.read().await;
        statuses.get(device_id)
            .cloned()
            .ok_or_else(|| DeviceError::DeviceNotFound(device_id.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_device_registration() {
        let (manager, _receiver) = DeviceManager::new();
        
        let config = DeviceConfig {
            id: "test_device".to_string(),
            name: "Test Device".to_string(),
            device_type: DeviceType::Sensor,
            protocol: Protocol::MQTT,
            endpoint: "mqtt://localhost:1883".to_string(),
            location: Some("Building A".to_string()),
            metadata: HashMap::new(),
        };
        
        assert!(manager.register_device(config).await.is_ok());
        
        let device = manager.get_device("test_device").await.unwrap();
        assert_eq!(device.id, "test_device");
    }
}
```

### 2. 传感器数据采集

```rust
// templates/basic_device/sensor_collector.rs
use serde::{Deserialize, Serialize};
use tokio::time::{interval, Duration};
use std::sync::Arc;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum SensorError {
    #[error("传感器初始化失败: {0}")]
    InitializationFailed(String),
    #[error("数据读取失败: {0}")]
    ReadFailed(String),
    #[error("数据验证失败: {0}")]
    ValidationFailed(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SensorConfig {
    pub id: String,
    pub sensor_type: SensorType,
    pub address: u8,
    pub sampling_rate: Duration,
    pub calibration: Option<CalibrationData>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SensorType {
    Temperature,
    Humidity,
    Pressure,
    Light,
    Motion,
    Gas,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CalibrationData {
    pub offset: f64,
    pub scale: f64,
    pub min_value: f64,
    pub max_value: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SensorReading {
    pub sensor_id: String,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub value: f64,
    pub unit: String,
    pub quality: DataQuality,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum DataQuality {
    Good,
    Uncertain,
    Bad,
}

pub trait Sensor {
    async fn initialize(&mut self) -> Result<(), SensorError>;
    async fn read(&self) -> Result<f64, SensorError>;
    async fn calibrate(&mut self, calibration: CalibrationData) -> Result<(), SensorError>;
    fn get_config(&self) -> &SensorConfig;
}

pub struct TemperatureSensor {
    config: SensorConfig,
    i2c_address: u8,
}

impl TemperatureSensor {
    pub fn new(config: SensorConfig) -> Self {
        Self {
            i2c_address: config.address,
            config,
        }
    }
    
    async fn read_raw(&self) -> Result<u16, SensorError> {
        // 模拟I2C读取
        tokio::time::sleep(Duration::from_millis(10)).await;
        
        // 模拟温度传感器读取 (0-4095对应-40°C到125°C)
        let raw_value = (rand::random::<f64>() * 4095.0) as u16;
        Ok(raw_value)
    }
    
    fn convert_to_celsius(&self, raw_value: u16) -> f64 {
        // 转换原始值为摄氏度
        let voltage = (raw_value as f64 / 4095.0) * 3.3;
        let temperature = (voltage - 0.5) * 100.0;
        
        // 应用校准
        if let Some(calibration) = &self.config.calibration {
            temperature * calibration.scale + calibration.offset
        } else {
            temperature
        }
    }
}

#[async_trait::async_trait]
impl Sensor for TemperatureSensor {
    async fn initialize(&mut self) -> Result<(), SensorError> {
        // 初始化I2C通信
        tokio::time::sleep(Duration::from_millis(100)).await;
        Ok(())
    }
    
    async fn read(&self) -> Result<f64, SensorError> {
        let raw_value = self.read_raw().await?;
        let temperature = self.convert_to_celsius(raw_value);
        
        // 验证数据质量
        if let Some(calibration) = &self.config.calibration {
            if temperature < calibration.min_value || temperature > calibration.max_value {
                return Err(SensorError::ValidationFailed(
                    format!("温度值 {} 超出范围 [{}, {}]", 
                           temperature, calibration.min_value, calibration.max_value)
                ));
            }
        }
        
        Ok(temperature)
    }
    
    async fn calibrate(&mut self, calibration: CalibrationData) -> Result<(), SensorError> {
        self.config.calibration = Some(calibration);
        Ok(())
    }
    
    fn get_config(&self) -> &SensorConfig {
        &self.config
    }
}

pub struct SensorCollector {
    sensors: Vec<Box<dyn Sensor + Send + Sync>>,
    data_sender: tokio::sync::mpsc::UnboundedSender<SensorReading>,
}

impl SensorCollector {
    pub fn new() -> (Self, tokio::sync::mpsc::UnboundedReceiver<SensorReading>) {
        let (data_sender, data_receiver) = tokio::sync::mpsc::unbounded_channel();
        
        let collector = Self {
            sensors: Vec::new(),
            data_sender,
        };
        
        (collector, data_receiver)
    }
    
    pub fn add_sensor(&mut self, sensor: Box<dyn Sensor + Send + Sync>) {
        self.sensors.push(sensor);
    }
    
    pub async fn start_collection(&self) -> Result<(), SensorError> {
        let mut interval = interval(Duration::from_secs(1));
        
        loop {
            interval.tick().await;
            
            for sensor in &self.sensors {
                let config = sensor.get_config();
                
                match sensor.read().await {
                    Ok(value) => {
                        let reading = SensorReading {
                            sensor_id: config.id.clone(),
                            timestamp: chrono::Utc::now(),
                            value,
                            unit: self.get_unit(&config.sensor_type),
                            quality: DataQuality::Good,
                        };
                        
                        if let Err(_) = self.data_sender.send(reading) {
                            eprintln!("数据发送失败");
                        }
                    }
                    Err(e) => {
                        eprintln!("传感器 {} 读取失败: {}", config.id, e);
                        
                        let reading = SensorReading {
                            sensor_id: config.id.clone(),
                            timestamp: chrono::Utc::now(),
                            value: 0.0,
                            unit: self.get_unit(&config.sensor_type),
                            quality: DataQuality::Bad,
                        };
                        
                        let _ = self.data_sender.send(reading);
                    }
                }
            }
        }
    }
    
    fn get_unit(&self, sensor_type: &SensorType) -> String {
        match sensor_type {
            SensorType::Temperature => "°C".to_string(),
            SensorType::Humidity => "%".to_string(),
            SensorType::Pressure => "hPa".to_string(),
            SensorType::Light => "lux".to_string(),
            SensorType::Motion => "count".to_string(),
            SensorType::Gas => "ppm".to_string(),
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建传感器配置
    let temp_config = SensorConfig {
        id: "temp_001".to_string(),
        sensor_type: SensorType::Temperature,
        address: 0x48,
        sampling_rate: Duration::from_secs(1),
        calibration: Some(CalibrationData {
            offset: 0.0,
            scale: 1.0,
            min_value: -40.0,
            max_value: 125.0,
        }),
    };
    
    // 创建传感器
    let mut temp_sensor = TemperatureSensor::new(temp_config);
    temp_sensor.initialize().await?;
    
    // 创建数据收集器
    let (mut collector, mut receiver) = SensorCollector::new();
    collector.add_sensor(Box::new(temp_sensor));
    
    // 启动数据收集
    let collector_handle = tokio::spawn(async move {
        collector.start_collection().await
    });
    
    // 处理数据
    while let Some(reading) = receiver.recv().await {
        println!("传感器数据: {:?}", reading);
    }
    
    collector_handle.await??;
    Ok(())
}
```

## 🌐 传感器网络模板

### 1. 网络管理器

```rust
// templates/sensor_network/network_manager.rs
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::sync::{RwLock, mpsc};
use std::net::SocketAddr;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum NetworkError {
    #[error("网络连接失败: {0}")]
    ConnectionFailed(String),
    #[error("节点未找到: {0}")]
    NodeNotFound(String),
    #[error("路由失败: {0}")]
    RoutingFailed(String),
    #[error("数据包损坏: {0}")]
    PacketCorrupted(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkNode {
    pub id: String,
    pub address: SocketAddr,
    pub node_type: NodeType,
    pub capabilities: Vec<Capability>,
    pub last_heartbeat: chrono::DateTime<chrono::Utc>,
    pub battery_level: Option<u8>,
    pub signal_strength: Option<i8>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum NodeType {
    Sensor,
    Actuator,
    Gateway,
    Router,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Capability {
    Temperature,
    Humidity,
    Pressure,
    Light,
    Motion,
    Control,
    Routing,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct NetworkPacket {
    pub source: String,
    pub destination: String,
    pub packet_type: PacketType,
    pub payload: Vec<u8>,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub ttl: u8,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PacketType {
    Data,
    Control,
    Heartbeat,
    Route,
    Error,
}

pub struct NetworkManager {
    nodes: RwLock<HashMap<String, NetworkNode>>,
    routes: RwLock<HashMap<String, Vec<String>>>,
    packet_sender: mpsc::UnboundedSender<NetworkPacket>,
}

impl NetworkManager {
    pub fn new() -> (Self, mpsc::UnboundedReceiver<NetworkPacket>) {
        let (packet_sender, packet_receiver) = mpsc::unbounded_channel();
        
        let manager = Self {
            nodes: RwLock::new(HashMap::new()),
            routes: RwLock::new(HashMap::new()),
            packet_sender,
        };
        
        (manager, packet_receiver)
    }
    
    pub async fn register_node(&self, node: NetworkNode) -> Result<(), NetworkError> {
        let mut nodes = self.nodes.write().await;
        nodes.insert(node.id.clone(), node);
        Ok(())
    }
    
    pub async fn send_packet(&self, packet: NetworkPacket) -> Result<(), NetworkError> {
        self.packet_sender.send(packet)
            .map_err(|_| NetworkError::ConnectionFailed("数据包发送失败".to_string()))
    }
    
    pub async fn find_route(&self, destination: &str) -> Result<Vec<String>, NetworkError> {
        let routes = self.routes.read().await;
        routes.get(destination)
            .cloned()
            .ok_or_else(|| NetworkError::RoutingFailed(format!("无法找到到 {} 的路由", destination)))
    }
    
    pub async fn update_heartbeat(&self, node_id: &str) -> Result<(), NetworkError> {
        let mut nodes = self.nodes.write().await;
        
        if let Some(node) = nodes.get_mut(node_id) {
            node.last_heartbeat = chrono::Utc::now();
        } else {
            return Err(NetworkError::NodeNotFound(node_id.to_string()));
        }
        
        Ok(())
    }
    
    pub async fn get_network_topology(&self) -> HashMap<String, NetworkNode> {
        let nodes = self.nodes.read().await;
        nodes.clone()
    }
}
```

## 🧠 边缘计算模板

### 1. 规则引擎

```rust
// templates/edge_computing/rule_engine.rs
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::sync::{RwLock, mpsc};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum RuleError {
    #[error("规则解析失败: {0}")]
    ParseError(String),
    #[error("规则执行失败: {0}")]
    ExecutionError(String),
    #[error("条件不满足: {0}")]
    ConditionNotMet(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Rule {
    pub id: String,
    pub name: String,
    pub condition: Condition,
    pub action: Action,
    pub enabled: bool,
    pub priority: u8,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Condition {
    Simple {
        field: String,
        operator: Operator,
        value: serde_json::Value,
    },
    Compound {
        operator: LogicalOperator,
        conditions: Vec<Condition>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Operator {
    Equal,
    NotEqual,
    GreaterThan,
    LessThan,
    GreaterThanOrEqual,
    LessThanOrEqual,
    Contains,
    Regex,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogicalOperator {
    And,
    Or,
    Not,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Action {
    SendAlert {
        message: String,
        recipients: Vec<String>,
    },
    AdjustDevice {
        device_id: String,
        parameter: String,
        value: serde_json::Value,
    },
    LogEvent {
        level: String,
        message: String,
    },
    CallFunction {
        function_name: String,
        parameters: HashMap<String, serde_json::Value>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuleContext {
    pub data: HashMap<String, serde_json::Value>,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub device_id: String,
}

pub struct RuleEngine {
    rules: RwLock<Vec<Rule>>,
    action_sender: mpsc::UnboundedSender<Action>,
}

impl RuleEngine {
    pub fn new() -> (Self, mpsc::UnboundedReceiver<Action>) {
        let (action_sender, action_receiver) = mpsc::unbounded_channel();
        
        let engine = Self {
            rules: RwLock::new(Vec::new()),
            action_sender,
        };
        
        (engine, action_receiver)
    }
    
    pub async fn add_rule(&self, rule: Rule) -> Result<(), RuleError> {
        let mut rules = self.rules.write().await;
        rules.push(rule);
        rules.sort_by_key(|r| r.priority);
        Ok(())
    }
    
    pub async fn evaluate_rules(&self, context: RuleContext) -> Result<Vec<Action>, RuleError> {
        let rules = self.rules.read().await;
        let mut triggered_actions = Vec::new();
        
        for rule in rules.iter() {
            if !rule.enabled {
                continue;
            }
            
            if self.evaluate_condition(&rule.condition, &context)? {
                triggered_actions.push(rule.action.clone());
            }
        }
        
        Ok(triggered_actions)
    }
    
    fn evaluate_condition(&self, condition: &Condition, context: &RuleContext) -> Result<bool, RuleError> {
        match condition {
            Condition::Simple { field, operator, value } => {
                let field_value = context.data.get(field)
                    .ok_or_else(|| RuleError::ConditionNotMet(format!("字段 {} 不存在", field)))?;
                
                self.compare_values(field_value, operator, value)
            }
            Condition::Compound { operator, conditions } => {
                match operator {
                    LogicalOperator::And => {
                        for condition in conditions {
                            if !self.evaluate_condition(condition, context)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                    LogicalOperator::Or => {
                        for condition in conditions {
                            if self.evaluate_condition(condition, context)? {
                                return Ok(true);
                            }
                        }
                        Ok(false)
                    }
                    LogicalOperator::Not => {
                        if conditions.len() != 1 {
                            return Err(RuleError::ParseError("NOT操作符只能有一个条件".to_string()));
                        }
                        Ok(!self.evaluate_condition(&conditions[0], context)?)
                    }
                }
            }
        }
    }
    
    fn compare_values(&self, left: &serde_json::Value, operator: &Operator, right: &serde_json::Value) -> Result<bool, RuleError> {
        match operator {
            Operator::Equal => Ok(left == right),
            Operator::NotEqual => Ok(left != right),
            Operator::GreaterThan => {
                if let (Some(l), Some(r)) = (left.as_f64(), right.as_f64()) {
                    Ok(l > r)
                } else {
                    Err(RuleError::ParseError("无法比较非数值类型".to_string()))
                }
            }
            Operator::LessThan => {
                if let (Some(l), Some(r)) = (left.as_f64(), right.as_f64()) {
                    Ok(l < r)
                } else {
                    Err(RuleError::ParseError("无法比较非数值类型".to_string()))
                }
            }
            Operator::GreaterThanOrEqual => {
                if let (Some(l), Some(r)) = (left.as_f64(), right.as_f64()) {
                    Ok(l >= r)
                } else {
                    Err(RuleError::ParseError("无法比较非数值类型".to_string()))
                }
            }
            Operator::LessThanOrEqual => {
                if let (Some(l), Some(r)) = (left.as_f64(), right.as_f64()) {
                    Ok(l <= r)
                } else {
                    Err(RuleError::ParseError("无法比较非数值类型".to_string()))
                }
            }
            Operator::Contains => {
                if let (Some(l), Some(r)) = (left.as_str(), right.as_str()) {
                    Ok(l.contains(r))
                } else {
                    Err(RuleError::ParseError("Contains操作符只能用于字符串".to_string()))
                }
            }
            Operator::Regex => {
                if let (Some(l), Some(r)) = (left.as_str(), right.as_str()) {
                    let regex = regex::Regex::new(r)
                        .map_err(|e| RuleError::ParseError(format!("正则表达式错误: {}", e)))?;
                    Ok(regex.is_match(l))
                } else {
                    Err(RuleError::ParseError("Regex操作符只能用于字符串".to_string()))
                }
            }
        }
    }
    
    pub async fn execute_action(&self, action: Action) -> Result<(), RuleError> {
        self.action_sender.send(action)
            .map_err(|_| RuleError::ExecutionError("动作执行失败".to_string()))
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建规则引擎
    let (rule_engine, mut action_receiver) = RuleEngine::new();
    
    // 添加温度告警规则
    let temperature_rule = Rule {
        id: "temp_alert".to_string(),
        name: "温度告警".to_string(),
        condition: Condition::Simple {
            field: "temperature".to_string(),
            operator: Operator::GreaterThan,
            value: serde_json::Value::Number(serde_json::Number::from_f64(30.0).unwrap()),
        },
        action: Action::SendAlert {
            message: "温度过高警报".to_string(),
            recipients: vec!["admin@example.com".to_string()],
        },
        enabled: true,
        priority: 1,
    };
    
    rule_engine.add_rule(temperature_rule).await?;
    
    // 模拟传感器数据
    let mut context = RuleContext {
        data: HashMap::new(),
        timestamp: chrono::Utc::now(),
        device_id: "sensor_001".to_string(),
    };
    
    context.data.insert("temperature".to_string(), serde_json::Value::Number(serde_json::Number::from_f64(35.0).unwrap()));
    
    // 评估规则
    let actions = rule_engine.evaluate_rules(context).await?;
    
    for action in actions {
        rule_engine.execute_action(action).await?;
    }
    
    // 处理动作
    while let Some(action) = action_receiver.recv().await {
        match action {
            Action::SendAlert { message, recipients } => {
                println!("发送告警: {} 给: {:?}", message, recipients);
            }
            Action::AdjustDevice { device_id, parameter, value } => {
                println!("调整设备 {} 的 {} 为 {:?}", device_id, parameter, value);
            }
            Action::LogEvent { level, message } => {
                println!("记录事件 [{}]: {}", level, message);
            }
            Action::CallFunction { function_name, parameters } => {
                println!("调用函数 {} 参数: {:?}", function_name, parameters);
            }
        }
    }
    
    Ok(())
}
```

## 🔐 安全实现模板

### 1. 设备认证

```rust
// templates/security_implementation/device_auth.rs
use serde::{Deserialize, Serialize};
use ring::signature::{Ed25519KeyPair, Signature, UnparsedPublicKey, ED25519};
use ring::rand::{SecureRandom, SystemRandom};
use std::collections::HashMap;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum AuthError {
    #[error("认证失败: {0}")]
    AuthenticationFailed(String),
    #[error("密钥生成失败: {0}")]
    KeyGenerationFailed(String),
    #[error("签名验证失败: {0}")]
    SignatureVerificationFailed(String),
    #[error("证书无效: {0}")]
    InvalidCertificate(String),
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceCertificate {
    pub device_id: String,
    pub public_key: Vec<u8>,
    pub issued_at: chrono::DateTime<chrono::Utc>,
    pub expires_at: chrono::DateTime<chrono::Utc>,
    pub issuer: String,
    pub signature: Vec<u8>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceCredentials {
    pub device_id: String,
    pub private_key: Vec<u8>,
    pub certificate: DeviceCertificate,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthToken {
    pub device_id: String,
    pub issued_at: chrono::DateTime<chrono::Utc>,
    pub expires_at: chrono::DateTime<chrono::Utc>,
    pub permissions: Vec<String>,
    pub signature: Vec<u8>,
}

pub struct DeviceAuthenticator {
    rng: SystemRandom,
    trusted_certificates: HashMap<String, DeviceCertificate>,
}

impl DeviceAuthenticator {
    pub fn new() -> Self {
        Self {
            rng: SystemRandom::new(),
            trusted_certificates: HashMap::new(),
        }
    }
    
    pub fn generate_device_credentials(&self, device_id: String, issuer: String) -> Result<DeviceCredentials, AuthError> {
        // 生成Ed25519密钥对
        let pkcs8_bytes = Ed25519KeyPair::generate_pkcs8(&self.rng)
            .map_err(|e| AuthError::KeyGenerationFailed(format!("{}", e)))?;
        
        let key_pair = Ed25519KeyPair::from_pkcs8(pkcs8_bytes.as_ref())
            .map_err(|e| AuthError::KeyGenerationFailed(format!("{}", e)))?;
        
        let public_key = key_pair.public_key().as_ref().to_vec();
        let private_key = pkcs8_bytes.as_ref().to_vec();
        
        // 创建证书
        let now = chrono::Utc::now();
        let expires_at = now + chrono::Duration::days(365);
        
        let certificate = DeviceCertificate {
            device_id: device_id.clone(),
            public_key: public_key.clone(),
            issued_at: now,
            expires_at,
            issuer: issuer.clone(),
            signature: Vec::new(), // 将在下面签名
        };
        
        // 签名证书
        let certificate_bytes = bincode::serialize(&certificate)
            .map_err(|e| AuthError::KeyGenerationFailed(format!("序列化失败: {}", e)))?;
        
        let signature = key_pair.sign(&certificate_bytes);
        
        let mut signed_certificate = certificate;
        signed_certificate.signature = signature.as_ref().to_vec();
        
        Ok(DeviceCredentials {
            device_id,
            private_key,
            certificate: signed_certificate,
        })
    }
    
    pub fn verify_device_certificate(&self, certificate: &DeviceCertificate) -> Result<bool, AuthError> {
        // 检查证书是否过期
        if certificate.expires_at < chrono::Utc::now() {
            return Err(AuthError::InvalidCertificate("证书已过期".to_string()));
        }
        
        // 验证签名
        let public_key = UnparsedPublicKey::new(&ED25519, &certificate.public_key);
        
        let mut certificate_for_verification = certificate.clone();
        certificate_for_verification.signature = Vec::new();
        
        let certificate_bytes = bincode::serialize(&certificate_for_verification)
            .map_err(|e| AuthError::SignatureVerificationFailed(format!("序列化失败: {}", e)))?;
        
        public_key.verify(&certificate_bytes, &certificate.signature)
            .map_err(|_| AuthError::SignatureVerificationFailed("签名验证失败".to_string()))?;
        
        Ok(true)
    }
    
    pub fn generate_auth_token(&self, device_id: &str, permissions: Vec<String>) -> Result<AuthToken, AuthError> {
        let now = chrono::Utc::now();
        let expires_at = now + chrono::Duration::hours(24);
        
        let token = AuthToken {
            device_id: device_id.to_string(),
            issued_at: now,
            expires_at,
            permissions,
            signature: Vec::new(), // 将在下面签名
        };
        
        // 使用设备私钥签名令牌
        let token_bytes = bincode::serialize(&token)
            .map_err(|e| AuthError::KeyGenerationFailed(format!("序列化失败: {}", e)))?;
        
        // 这里应该使用设备的私钥签名，简化示例
        let signature = vec![0u8; 64]; // 实际应该是真实的签名
        
        let mut signed_token = token;
        signed_token.signature = signature;
        
        Ok(signed_token)
    }
    
    pub fn verify_auth_token(&self, token: &AuthToken, device_certificate: &DeviceCertificate) -> Result<bool, AuthError> {
        // 检查令牌是否过期
        if token.expires_at < chrono::Utc::now() {
            return Err(AuthError::AuthenticationFailed("令牌已过期".to_string()));
        }
        
        // 验证设备证书
        self.verify_device_certificate(device_certificate)?;
        
        // 验证令牌签名
        let public_key = UnparsedPublicKey::new(&ED25519, &device_certificate.public_key);
        
        let mut token_for_verification = token.clone();
        token_for_verification.signature = Vec::new();
        
        let token_bytes = bincode::serialize(&token_for_verification)
            .map_err(|e| AuthError::SignatureVerificationFailed(format!("序列化失败: {}", e)))?;
        
        public_key.verify(&token_bytes, &token.signature)
            .map_err(|_| AuthError::SignatureVerificationFailed("令牌签名验证失败".to_string()))?;
        
        Ok(true)
    }
    
    pub fn add_trusted_certificate(&mut self, certificate: DeviceCertificate) -> Result<(), AuthError> {
        self.verify_device_certificate(&certificate)?;
        self.trusted_certificates.insert(certificate.device_id.clone(), certificate);
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut authenticator = DeviceAuthenticator::new();
    
    // 生成设备凭证
    let credentials = authenticator.generate_device_credentials(
        "device_001".to_string(),
        "iot_ca".to_string()
    )?;
    
    println!("设备凭证生成成功: {:?}", credentials.device_id);
    
    // 验证设备证书
    let is_valid = authenticator.verify_device_certificate(&credentials.certificate)?;
    println!("证书验证结果: {}", is_valid);
    
    // 生成认证令牌
    let token = authenticator.generate_auth_token(
        "device_001",
        vec!["read".to_string(), "write".to_string()]
    )?;
    
    println!("认证令牌生成成功: {:?}", token.device_id);
    
    // 验证认证令牌
    let token_valid = authenticator.verify_auth_token(&token, &credentials.certificate)?;
    println!("令牌验证结果: {}", token_valid);
    
    Ok(())
}
```

## 📊 监控系统模板

### 1. 指标收集器

```rust
// templates/monitoring_system/metrics_collector.rs
use prometheus::{Counter, Histogram, Gauge, Registry, TextEncoder, Encoder};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricData {
    pub name: String,
    pub value: f64,
    pub labels: HashMap<String, String>,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

pub struct MetricsCollector {
    registry: Registry,
    counters: Arc<RwLock<HashMap<String, Counter>>>,
    histograms: Arc<RwLock<HashMap<String, Histogram>>>,
    gauges: Arc<RwLock<HashMap<String, Gauge>>>,
}

impl MetricsCollector {
    pub fn new() -> Self {
        let registry = Registry::new();
        
        Self {
            registry,
            counters: Arc::new(RwLock::new(HashMap::new())),
            histograms: Arc::new(RwLock::new(HashMap::new())),
            gauges: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    pub async fn record_counter(&self, name: &str, value: f64, labels: HashMap<String, String>) {
        let mut counters = self.counters.write().await;
        
        if !counters.contains_key(name) {
            let counter = Counter::new(name, format!("{} counter", name)).unwrap();
            self.registry.register(Box::new(counter.clone())).unwrap();
            counters.insert(name.to_string(), counter);
        }
        
        if let Some(counter) = counters.get(name) {
            counter.inc_by(value);
        }
    }
    
    pub async fn record_histogram(&self, name: &str, value: f64, labels: HashMap<String, String>) {
        let mut histograms = self.histograms.write().await;
        
        if !histograms.contains_key(name) {
            let histogram = Histogram::new(name, format!("{} histogram", name)).unwrap();
            self.registry.register(Box::new(histogram.clone())).unwrap();
            histograms.insert(name.to_string(), histogram);
        }
        
        if let Some(histogram) = histograms.get(name) {
            histogram.observe(value);
        }
    }
    
    pub async fn record_gauge(&self, name: &str, value: f64, labels: HashMap<String, String>) {
        let mut gauges = self.gauges.write().await;
        
        if !gauges.contains_key(name) {
            let gauge = Gauge::new(name, format!("{} gauge", name)).unwrap();
            self.registry.register(Box::new(gauge.clone())).unwrap();
            gauges.insert(name.to_string(), gauge);
        }
        
        if let Some(gauge) = gauges.get(name) {
            gauge.set(value);
        }
    }
    
    pub async fn collect_metrics(&self) -> String {
        let metric_families = self.registry.gather();
        let encoder = TextEncoder::new();
        encoder.encode_to_string(&metric_families).unwrap()
    }
    
    pub async fn process_metric_data(&self, data: MetricData) {
        match data.name.as_str() {
            name if name.ends_with("_counter") => {
                self.record_counter(&data.name, data.value, data.labels).await;
            }
            name if name.ends_with("_histogram") => {
                self.record_histogram(&data.name, data.value, data.labels).await;
            }
            name if name.ends_with("_gauge") => {
                self.record_gauge(&data.name, data.value, data.labels).await;
            }
            _ => {
                // 默认为gauge
                self.record_gauge(&data.name, data.value, data.labels).await;
            }
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let collector = MetricsCollector::new();
    
    // 模拟传感器数据
    let mut labels = HashMap::new();
    labels.insert("device_id".to_string(), "sensor_001".to_string());
    labels.insert("location".to_string(), "building_a".to_string());
    
    let metric_data = MetricData {
        name: "temperature_gauge".to_string(),
        value: 25.5,
        labels,
        timestamp: chrono::Utc::now(),
    };
    
    collector.process_metric_data(metric_data).await;
    
    // 记录计数器
    let mut counter_labels = HashMap::new();
    counter_labels.insert("device_id".to_string(), "sensor_001".to_string());
    collector.record_counter("sensor_readings_counter", 1.0, counter_labels).await;
    
    // 记录直方图
    let mut histogram_labels = HashMap::new();
    histogram_labels.insert("device_id".to_string(), "sensor_001".to_string());
    collector.record_histogram("response_time_histogram", 0.1, histogram_labels).await;
    
    // 收集指标
    let metrics = collector.collect_metrics().await;
    println!("收集的指标:\n{}", metrics);
    
    Ok(())
}
```

## 🔄 使用指南

### 1. 模板选择

根据您的IoT项目需求选择合适的模板：

- **基础设备管理**: 适用于简单的设备监控和控制
- **传感器网络**: 适用于大规模传感器网络部署
- **边缘计算**: 适用于需要本地数据处理的场景
- **安全实现**: 适用于对安全性要求较高的应用
- **监控系统**: 适用于需要全面监控的IoT系统

### 2. 自定义修改

每个模板都提供了完整的实现，您可以根据具体需求进行修改：

- 调整数据结构
- 修改业务逻辑
- 添加新的功能
- 优化性能

### 3. 集成测试

使用提供的测试用例验证模板功能：

```bash
cargo test
cargo test --release
```

### 4. 部署建议

- 使用Docker容器化部署
- 配置适当的资源限制
- 设置监控和告警
- 实施安全最佳实践

---

**IoT代码模板** - 基于Rust 1.90的完整IoT开发解决方案 🦀🌐
