//! 设备管理器模块
//! 
//! 提供设备注册、状态管理、数据收集等核心功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use tokio::sync::{RwLock, mpsc};
use std::sync::Arc;
use chrono::{DateTime, Utc};
use super::{DeviceManagementError, DeviceConfig, DeviceStatus, DeviceData, Status};
use super::sensor_collector::SensorCollector;

/// 设备管理器
#[derive(Clone)]
pub struct DeviceManager {
    /// 设备配置映射
    devices: Arc<RwLock<HashMap<String, DeviceConfig>>>,
    /// 设备状态映射
    statuses: Arc<RwLock<HashMap<String, DeviceStatus>>>,
    /// 数据发送通道
    data_sender: mpsc::UnboundedSender<DeviceData>,
    /// 状态更新发送通道
    status_sender: mpsc::UnboundedSender<DeviceStatusUpdate>,
    /// 传感器收集器
    sensor_collector: Option<Arc<SensorCollector>>,
    /// 管理器配置
    config: DeviceManagerConfig,
}

/// 设备管理器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceManagerConfig {
    /// 最大设备数量
    pub max_devices: usize,
    /// 设备超时时间 (秒)
    pub device_timeout: u64,
    /// 状态更新间隔 (秒)
    pub status_update_interval: u64,
    /// 数据收集间隔 (秒)
    pub data_collection_interval: u64,
    /// 是否启用自动状态检查
    pub enable_auto_status_check: bool,
    /// 是否启用数据验证
    pub enable_data_validation: bool,
}

impl Default for DeviceManagerConfig {
    fn default() -> Self {
        Self {
            max_devices: 1000,
            device_timeout: 300, // 5分钟
            status_update_interval: 30, // 30秒
            data_collection_interval: 1, // 1秒
            enable_auto_status_check: true,
            enable_data_validation: true,
        }
    }
}

/// 设备状态更新事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceStatusUpdate {
    /// 设备ID
    pub device_id: String,
    /// 状态变化
    pub status_change: StatusChange,
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    /// 附加信息
    pub message: Option<String>,
}

/// 状态变化类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StatusChange {
    /// 状态变化
    StatusChanged { from: Status, to: Status },
    /// 设备注册
    DeviceRegistered,
    /// 设备注销
    DeviceUnregistered,
    /// 设备上线
    DeviceOnline,
    /// 设备离线
    DeviceOffline,
    /// 设备错误
    DeviceError { error_message: String },
    /// 设备恢复
    DeviceRecovered,
}

impl StatusChange {
    /// 获取变化描述
    pub fn description(&self) -> String {
        match self {
            StatusChange::StatusChanged { from, to } => {
                format!("状态从 {} 变为 {}", from.description(), to.description())
            }
            StatusChange::DeviceRegistered => "设备已注册".to_string(),
            StatusChange::DeviceUnregistered => "设备已注销".to_string(),
            StatusChange::DeviceOnline => "设备上线".to_string(),
            StatusChange::DeviceOffline => "设备离线".to_string(),
            StatusChange::DeviceError { error_message } => {
                format!("设备错误: {}", error_message)
            }
            StatusChange::DeviceRecovered => "设备恢复".to_string(),
        }
    }
}

impl DeviceManager {
    /// 创建新的设备管理器
    pub fn new(config: DeviceManagerConfig) -> (Self, mpsc::UnboundedReceiver<DeviceData>, mpsc::UnboundedReceiver<DeviceStatusUpdate>) {
        let (data_sender, data_receiver) = mpsc::unbounded_channel();
        let (status_sender, status_receiver) = mpsc::unbounded_channel();
        
        let manager = Self {
            devices: Arc::new(RwLock::new(HashMap::new())),
            statuses: Arc::new(RwLock::new(HashMap::new())),
            data_sender,
            status_sender,
            sensor_collector: None,
            config,
        };
        
        (manager, data_receiver, status_receiver)
    }

    /// 注册设备
    pub async fn register_device(&self, config: DeviceConfig) -> Result<(), DeviceManagementError> {
        // 验证配置
        config.validate().map_err(|e| DeviceManagementError::DeviceExists(e))?;
        
        let mut devices = self.devices.write().await;
        
        // 检查设备是否已存在
        if devices.contains_key(&config.id) {
            return Err(DeviceManagementError::DeviceExists(config.id.clone()));
        }
        
        // 检查设备数量限制
        if devices.len() >= self.config.max_devices {
            return Err(DeviceManagementError::DeviceExists(
                format!("设备数量已达到上限: {}", self.config.max_devices)
            ));
        }
        
        // 注册设备
        devices.insert(config.id.clone(), config.clone());
        
        // 初始化设备状态
        let mut statuses = self.statuses.write().await;
        let device_status = DeviceStatus::new(config.id.clone());
        statuses.insert(config.id.clone(), device_status);
        
        // 发送状态更新事件
        let status_update = DeviceStatusUpdate {
            device_id: config.id.clone(),
            status_change: StatusChange::DeviceRegistered,
            timestamp: Utc::now(),
            message: Some(format!("设备 {} 已注册", config.name)),
        };
        
        if let Err(_) = self.status_sender.send(status_update) {
            eprintln!("状态更新发送失败");
        }
        
        Ok(())
    }

    /// 注销设备
    pub async fn unregister_device(&self, device_id: &str) -> Result<(), DeviceManagementError> {
        let mut devices = self.devices.write().await;
        let mut statuses = self.statuses.write().await;
        
        if !devices.contains_key(device_id) {
            return Err(DeviceManagementError::DeviceNotFound(device_id.to_string()));
        }
        
        // 移除设备
        devices.remove(device_id);
        statuses.remove(device_id);
        
        // 发送状态更新事件
        let status_update = DeviceStatusUpdate {
            device_id: device_id.to_string(),
            status_change: StatusChange::DeviceUnregistered,
            timestamp: Utc::now(),
            message: Some(format!("设备 {} 已注销", device_id)),
        };
        
        if let Err(_) = self.status_sender.send(status_update) {
            eprintln!("状态更新发送失败");
        }
        
        Ok(())
    }

    /// 获取设备配置
    pub async fn get_device(&self, device_id: &str) -> Result<DeviceConfig, DeviceManagementError> {
        let devices = self.devices.read().await;
        devices.get(device_id)
            .cloned()
            .ok_or_else(|| DeviceManagementError::DeviceNotFound(device_id.to_string()))
    }

    /// 获取所有设备
    pub async fn get_all_devices(&self) -> Vec<DeviceConfig> {
        let devices = self.devices.read().await;
        devices.values().cloned().collect()
    }

    /// 更新设备状态
    pub async fn update_device_status(&self, device_id: &str, status: Status) -> Result<(), DeviceManagementError> {
        let mut statuses = self.statuses.write().await;
        
        if let Some(device_status) = statuses.get_mut(device_id) {
            let old_status = device_status.status.clone();
            device_status.update_status(status.clone());
            
            // 发送状态更新事件
            let status_update = DeviceStatusUpdate {
                device_id: device_id.to_string(),
                status_change: StatusChange::StatusChanged { from: old_status, to: status },
                timestamp: Utc::now(),
                message: None,
            };
            
            if let Err(_) = self.status_sender.send(status_update) {
                eprintln!("状态更新发送失败");
            }
        } else {
            return Err(DeviceManagementError::DeviceNotFound(device_id.to_string()));
        }
        
        Ok(())
    }

    /// 获取设备状态
    pub async fn get_device_status(&self, device_id: &str) -> Result<DeviceStatus, DeviceManagementError> {
        let statuses = self.statuses.read().await;
        statuses.get(device_id)
            .cloned()
            .ok_or_else(|| DeviceManagementError::DeviceNotFound(device_id.to_string()))
    }

    /// 获取所有设备状态
    pub async fn get_all_device_statuses(&self) -> Vec<DeviceStatus> {
        let statuses = self.statuses.read().await;
        statuses.values().cloned().collect()
    }

    /// 发送设备数据
    pub async fn send_device_data(&self, data: DeviceData) -> Result<(), DeviceManagementError> {
        // 验证数据
        if self.config.enable_data_validation {
            data.validate().map_err(|e| DeviceManagementError::DataValidationFailed(e))?;
        }
        
        self.data_sender.send(data)
            .map_err(|_| DeviceManagementError::CommunicationError("数据发送失败".to_string()))
    }

    /// 设置传感器收集器
    pub fn set_sensor_collector(&mut self, collector: Arc<SensorCollector>) {
        self.sensor_collector = Some(collector);
    }

    /// 启动设备管理器
    pub async fn start(&self) -> Result<(), DeviceManagementError> {
        if self.config.enable_auto_status_check {
            self.start_status_monitor().await;
        }
        
        Ok(())
    }

    /// 停止设备管理器
    pub async fn stop(&self) -> Result<(), DeviceManagementError> {
        if let Some(_collector) = &self.sensor_collector {
            // collector.stop_collection(); // 方法不存在，暂时注释
        }
        
        Ok(())
    }

    /// 启动状态监控
    async fn start_status_monitor(&self) {
        let _devices = Arc::clone(&self.devices);
        let statuses = Arc::clone(&self.statuses);
        let status_sender = self.status_sender.clone();
        let timeout = self.config.device_timeout;
        
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(tokio::time::Duration::from_secs(30));
            
            loop {
                interval.tick().await;
                
                let now = Utc::now();
                let mut statuses_guard = statuses.write().await;
                
                for (device_id, status) in statuses_guard.iter_mut() {
                    let time_since_last_seen = now.signed_duration_since(status.last_seen).num_seconds();
                    
                    if time_since_last_seen > timeout as i64 && status.status != Status::Offline {
                        let _old_status = status.status.clone();
                        status.update_status(Status::Offline);
                        
                        let status_update = DeviceStatusUpdate {
                            device_id: device_id.clone(),
                            status_change: StatusChange::DeviceOffline,
                            timestamp: now,
                            message: Some(format!("设备超时，最后在线时间: {}", status.last_seen)),
                        };
                        
                        if let Err(_) = status_sender.send(status_update) {
                            eprintln!("状态更新发送失败");
                        }
                    }
                }
            }
        });
    }

    /// 获取设备统计信息
    pub async fn get_device_statistics(&self) -> DeviceStatistics {
        let devices = self.devices.read().await;
        let statuses = self.statuses.read().await;
        
        let mut online_count = 0;
        let mut offline_count = 0;
        let mut error_count = 0;
        let mut maintenance_count = 0;
        
        for status in statuses.values() {
            match status.status {
                Status::Online => online_count += 1,
                Status::Offline => offline_count += 1,
                Status::Error => error_count += 1,
                Status::Maintenance => maintenance_count += 1,
                _ => {}
            }
        }
        
        DeviceStatistics {
            total_devices: devices.len(),
            online_devices: online_count,
            offline_devices: offline_count,
            error_devices: error_count,
            maintenance_devices: maintenance_count,
            device_types: self.get_device_type_distribution(&devices).await,
            protocols: self.get_protocol_distribution(&devices).await,
        }
    }

    /// 获取设备类型分布
    async fn get_device_type_distribution(&self, devices: &HashMap<String, DeviceConfig>) -> HashMap<String, usize> {
        let mut distribution = HashMap::new();
        
        for device in devices.values() {
            let type_name = match device.device_type {
                super::DeviceType::Sensor => "传感器",
                super::DeviceType::Actuator => "执行器",
                super::DeviceType::Gateway => "网关",
                super::DeviceType::Controller => "控制器",
                super::DeviceType::EdgeDevice => "边缘设备",
                super::DeviceType::CloudDevice => "云设备",
            };
            
            *distribution.entry(type_name.to_string()).or_insert(0) += 1;
        }
        
        distribution
    }

    /// 获取协议分布
    async fn get_protocol_distribution(&self, devices: &HashMap<String, DeviceConfig>) -> HashMap<String, usize> {
        let mut distribution = HashMap::new();
        
        for device in devices.values() {
            let protocol_name = match device.protocol {
                super::Protocol::MQTT => "MQTT",
                super::Protocol::CoAP => "CoAP",
                super::Protocol::HTTP => "HTTP",
                super::Protocol::WebSocket => "WebSocket",
                super::Protocol::Modbus => "Modbus",
                super::Protocol::OPCUA => "OPC UA",
                super::Protocol::LoRaWAN => "LoRaWAN",
                super::Protocol::Zigbee => "Zigbee",
                super::Protocol::Bluetooth => "Bluetooth",
                super::Protocol::WiFi => "WiFi",
            };
            
            *distribution.entry(protocol_name.to_string()).or_insert(0) += 1;
        }
        
        distribution
    }
}

/// 设备统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceStatistics {
    /// 总设备数
    pub total_devices: usize,
    /// 在线设备数
    pub online_devices: usize,
    /// 离线设备数
    pub offline_devices: usize,
    /// 错误设备数
    pub error_devices: usize,
    /// 维护设备数
    pub maintenance_devices: usize,
    /// 设备类型分布
    pub device_types: HashMap<String, usize>,
    /// 协议分布
    pub protocols: HashMap<String, usize>,
}

impl DeviceStatistics {
    /// 获取在线率
    pub fn get_online_rate(&self) -> f64 {
        if self.total_devices == 0 {
            0.0
        } else {
            self.online_devices as f64 / self.total_devices as f64
        }
    }

    /// 获取健康率
    pub fn get_health_rate(&self) -> f64 {
        if self.total_devices == 0 {
            0.0
        } else {
            (self.online_devices + self.maintenance_devices) as f64 / self.total_devices as f64
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::{DeviceType, Protocol};

    #[tokio::test]
    async fn test_device_manager_creation() {
        let config = DeviceManagerConfig::default();
        let (manager, _data_receiver, _status_receiver) = DeviceManager::new(config);
        
        let devices = manager.get_all_devices().await;
        assert_eq!(devices.len(), 0);
    }

    #[tokio::test]
    async fn test_device_registration() {
        let config = DeviceManagerConfig::default();
        let (manager, _data_receiver, _status_receiver) = DeviceManager::new(config);
        
        let device_config = DeviceConfig::new(
            "device_001".to_string(),
            "Test Device".to_string(),
            DeviceType::Sensor,
            Protocol::MQTT,
            "mqtt://localhost:1883".to_string(),
        );
        
        assert!(manager.register_device(device_config).await.is_ok());
        
        let device = manager.get_device("device_001").await.unwrap();
        assert_eq!(device.id, "device_001");
    }

    #[tokio::test]
    async fn test_device_status_update() {
        let config = DeviceManagerConfig::default();
        let (manager, _data_receiver, _status_receiver) = DeviceManager::new(config);
        
        let device_config = DeviceConfig::new(
            "device_001".to_string(),
            "Test Device".to_string(),
            DeviceType::Sensor,
            Protocol::MQTT,
            "mqtt://localhost:1883".to_string(),
        );
        
        manager.register_device(device_config).await.unwrap();
        
        assert!(manager.update_device_status("device_001", Status::Online).await.is_ok());
        
        let status = manager.get_device_status("device_001").await.unwrap();
        assert_eq!(status.status, Status::Online);
    }

    #[tokio::test]
    async fn test_device_statistics() {
        let config = DeviceManagerConfig::default();
        let (manager, _data_receiver, _status_receiver) = DeviceManager::new(config);
        
        let device_config = DeviceConfig::new(
            "device_001".to_string(),
            "Test Device".to_string(),
            DeviceType::Sensor,
            Protocol::MQTT,
            "mqtt://localhost:1883".to_string(),
        );
        
        manager.register_device(device_config).await.unwrap();
        manager.update_device_status("device_001", Status::Online).await.unwrap();
        
        let stats = manager.get_device_statistics().await;
        assert_eq!(stats.total_devices, 1);
        assert_eq!(stats.online_devices, 1);
        assert_eq!(stats.get_online_rate(), 1.0);
    }
}
