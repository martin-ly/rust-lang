//! 设备管理模块
//! 
//! 提供设备注册、状态管理、数据收集等核心功能

pub mod device_manager;
pub mod device_config;
pub mod device_status;
pub mod device_data;
pub mod sensor_collector;

pub use device_manager::DeviceManager;
pub use device_config::{DeviceConfig, DeviceType, Protocol};
pub use device_status::{DeviceStatus, Status};
pub use device_data::{DeviceData, DataQuality};
pub use sensor_collector::{SensorCollector, TemperatureSensor, SensorConfig, SensorType, SensorReading};

use thiserror::Error;

#[derive(Debug, Error)]
pub enum DeviceManagementError {
    #[error("设备未找到: {0}")]
    DeviceNotFound(String),
    #[error("设备已存在: {0}")]
    DeviceExists(String),
    #[error("设备离线: {0}")]
    DeviceOffline(String),
    #[error("通信错误: {0}")]
    CommunicationError(String),
    #[error("传感器初始化失败: {0}")]
    SensorInitializationFailed(String),
    #[error("数据读取失败: {0}")]
    DataReadFailed(String),
    #[error("数据验证失败: {0}")]
    DataValidationFailed(String),
}
