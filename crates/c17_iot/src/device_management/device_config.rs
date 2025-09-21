//! 设备配置模块
//! 
//! 定义设备配置相关的数据结构和类型

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 设备配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceConfig {
    /// 设备唯一标识符
    pub id: String,
    /// 设备名称
    pub name: String,
    /// 设备类型
    pub device_type: DeviceType,
    /// 通信协议
    pub protocol: Protocol,
    /// 设备端点地址
    pub endpoint: String,
    /// 设备位置
    pub location: Option<String>,
    /// 设备元数据
    pub metadata: HashMap<String, String>,
    /// 设备描述
    pub description: Option<String>,
    /// 设备制造商
    pub manufacturer: Option<String>,
    /// 设备型号
    pub model: Option<String>,
    /// 固件版本
    pub firmware_version: Option<String>,
}

impl DeviceConfig {
    /// 创建新的设备配置
    pub fn new(
        id: String,
        name: String,
        device_type: DeviceType,
        protocol: Protocol,
        endpoint: String,
    ) -> Self {
        Self {
            id,
            name,
            device_type,
            protocol,
            endpoint,
            location: None,
            metadata: HashMap::new(),
            description: None,
            manufacturer: None,
            model: None,
            firmware_version: None,
        }
    }

    /// 设置设备位置
    pub fn with_location(mut self, location: String) -> Self {
        self.location = Some(location);
        self
    }

    /// 设置设备描述
    pub fn with_description(mut self, description: String) -> Self {
        self.description = Some(description);
        self
    }

    /// 设置设备制造商
    pub fn with_manufacturer(mut self, manufacturer: String) -> Self {
        self.manufacturer = Some(manufacturer);
        self
    }

    /// 设置设备型号
    pub fn with_model(mut self, model: String) -> Self {
        self.model = Some(model);
        self
    }

    /// 设置固件版本
    pub fn with_firmware_version(mut self, version: String) -> Self {
        self.firmware_version = Some(version);
        self
    }

    /// 添加元数据
    pub fn add_metadata(mut self, key: String, value: String) -> Self {
        self.metadata.insert(key, value);
        self
    }

    /// 获取元数据
    pub fn get_metadata(&self, key: &str) -> Option<&String> {
        self.metadata.get(key)
    }

    /// 验证配置
    pub fn validate(&self) -> Result<(), String> {
        if self.id.is_empty() {
            return Err("设备ID不能为空".to_string());
        }
        if self.name.is_empty() {
            return Err("设备名称不能为空".to_string());
        }
        if self.endpoint.is_empty() {
            return Err("设备端点不能为空".to_string());
        }
        Ok(())
    }
}

/// 设备类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum DeviceType {
    /// 传感器设备
    Sensor,
    /// 执行器设备
    Actuator,
    /// 网关设备
    Gateway,
    /// 控制器设备
    Controller,
    /// 边缘计算设备
    EdgeDevice,
    /// 云设备
    CloudDevice,
}

impl DeviceType {
    /// 获取设备类型描述
    pub fn description(&self) -> &'static str {
        match self {
            DeviceType::Sensor => "传感器设备",
            DeviceType::Actuator => "执行器设备",
            DeviceType::Gateway => "网关设备",
            DeviceType::Controller => "控制器设备",
            DeviceType::EdgeDevice => "边缘计算设备",
            DeviceType::CloudDevice => "云设备",
        }
    }

    /// 检查是否为传感器类型
    pub fn is_sensor(&self) -> bool {
        matches!(self, DeviceType::Sensor)
    }

    /// 检查是否为执行器类型
    pub fn is_actuator(&self) -> bool {
        matches!(self, DeviceType::Actuator)
    }

    /// 检查是否为网关类型
    pub fn is_gateway(&self) -> bool {
        matches!(self, DeviceType::Gateway)
    }
}

/// 通信协议
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Protocol {
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
    /// WiFi协议
    WiFi,
}

impl Protocol {
    /// 获取协议描述
    pub fn description(&self) -> &'static str {
        match self {
            Protocol::MQTT => "MQTT协议",
            Protocol::CoAP => "CoAP协议",
            Protocol::HTTP => "HTTP协议",
            Protocol::WebSocket => "WebSocket协议",
            Protocol::Modbus => "Modbus协议",
            Protocol::OPCUA => "OPC UA协议",
            Protocol::LoRaWAN => "LoRaWAN协议",
            Protocol::Zigbee => "Zigbee协议",
            Protocol::Bluetooth => "Bluetooth协议",
            Protocol::WiFi => "WiFi协议",
        }
    }

    /// 获取默认端口
    pub fn default_port(&self) -> u16 {
        match self {
            Protocol::MQTT => 1883,
            Protocol::CoAP => 5683,
            Protocol::HTTP => 80,
            Protocol::WebSocket => 80,
            Protocol::Modbus => 502,
            Protocol::OPCUA => 4840,
            Protocol::LoRaWAN => 1700,
            Protocol::Zigbee => 8080,
            Protocol::Bluetooth => 1,
            Protocol::WiFi => 80,
        }
    }

    /// 检查是否为安全协议
    pub fn is_secure(&self) -> bool {
        matches!(self, Protocol::MQTT | Protocol::CoAP | Protocol::HTTP | Protocol::WebSocket | Protocol::OPCUA)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_device_config_creation() {
        let config = DeviceConfig::new(
            "device_001".to_string(),
            "Temperature Sensor".to_string(),
            DeviceType::Sensor,
            Protocol::MQTT,
            "mqtt://localhost:1883".to_string(),
        );

        assert_eq!(config.id, "device_001");
        assert_eq!(config.name, "Temperature Sensor");
        assert_eq!(config.device_type, DeviceType::Sensor);
        assert_eq!(config.protocol, Protocol::MQTT);
    }

    #[test]
    fn test_device_config_validation() {
        let valid_config = DeviceConfig::new(
            "device_001".to_string(),
            "Test Device".to_string(),
            DeviceType::Sensor,
            Protocol::MQTT,
            "mqtt://localhost:1883".to_string(),
        );
        assert!(valid_config.validate().is_ok());

        let invalid_config = DeviceConfig::new(
            "".to_string(),
            "Test Device".to_string(),
            DeviceType::Sensor,
            Protocol::MQTT,
            "mqtt://localhost:1883".to_string(),
        );
        assert!(invalid_config.validate().is_err());
    }

    #[test]
    fn test_device_type_methods() {
        let sensor_type = DeviceType::Sensor;
        assert!(sensor_type.is_sensor());
        assert!(!sensor_type.is_actuator());
        assert!(!sensor_type.is_gateway());

        let gateway_type = DeviceType::Gateway;
        assert!(gateway_type.is_gateway());
        assert!(!gateway_type.is_sensor());
    }

    #[test]
    fn test_protocol_methods() {
        let mqtt = Protocol::MQTT;
        assert_eq!(mqtt.default_port(), 1883);
        assert!(mqtt.is_secure());

        let modbus = Protocol::Modbus;
        assert_eq!(modbus.default_port(), 502);
        assert!(!modbus.is_secure());
    }
}
