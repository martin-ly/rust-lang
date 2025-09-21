//! 传感器收集器模块
//! 
//! 提供传感器数据收集和处理功能

use serde::{Deserialize, Serialize};
use tokio::time::{interval, Duration};
// use std::sync::Arc;
// use std::collections::HashMap;
use chrono::{DateTime, Utc};
use super::{DeviceManagementError, DataQuality};
use super::device_data::CalibrationInfo;

/// 传感器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SensorConfig {
    /// 传感器ID
    pub id: String,
    /// 传感器类型
    pub sensor_type: SensorType,
    /// 传感器地址
    pub address: u8,
    /// 采样率
    pub sampling_rate: Duration,
    /// 校准信息
    pub calibration: Option<CalibrationInfo>,
    /// 是否启用
    pub enabled: bool,
}

/// 传感器类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum SensorType {
    /// 温度传感器
    Temperature,
    /// 湿度传感器
    Humidity,
    /// 压力传感器
    Pressure,
    /// 光照传感器
    Light,
    /// 运动传感器
    Motion,
    /// 气体传感器
    Gas,
    /// 声音传感器
    Sound,
    /// 振动传感器
    Vibration,
}

impl SensorType {
    /// 获取传感器类型描述
    pub fn description(&self) -> &'static str {
        match self {
            SensorType::Temperature => "温度传感器",
            SensorType::Humidity => "湿度传感器",
            SensorType::Pressure => "压力传感器",
            SensorType::Light => "光照传感器",
            SensorType::Motion => "运动传感器",
            SensorType::Gas => "气体传感器",
            SensorType::Sound => "声音传感器",
            SensorType::Vibration => "振动传感器",
        }
    }

    /// 获取传感器单位
    pub fn unit(&self) -> &'static str {
        match self {
            SensorType::Temperature => "°C",
            SensorType::Humidity => "%",
            SensorType::Pressure => "hPa",
            SensorType::Light => "lux",
            SensorType::Motion => "count",
            SensorType::Gas => "ppm",
            SensorType::Sound => "dB",
            SensorType::Vibration => "g",
        }
    }
}

/// 传感器状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SensorStatus {
    /// 传感器ID
    pub sensor_id: String,
    /// 是否在线
    pub online: bool,
    /// 最后读取时间
    pub last_read: Option<DateTime<Utc>>,
    /// 错误计数
    pub error_count: u32,
    /// 电池电量
    pub battery_level: Option<u8>,
    /// 信号强度
    pub signal_strength: Option<i8>,
}

/// 传感器数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SensorReading {
    /// 传感器ID
    pub sensor_id: String,
    /// 传感器类型
    pub sensor_type: SensorType,
    /// 数据值
    pub value: f64,
    /// 数据单位
    pub unit: String,
    /// 数据质量
    pub quality: DataQuality,
    /// 时间戳
    pub timestamp: DateTime<Utc>,
    /// 原始值
    pub raw_value: Option<f64>,
    /// 校准值
    pub calibrated_value: Option<f64>,
}

/// 温度传感器
#[derive(Clone)]
pub struct TemperatureSensor {
    config: SensorConfig,
    status: SensorStatus,
}

impl TemperatureSensor {
    /// 创建新的温度传感器
    pub fn new(config: SensorConfig) -> Self {
        let status = SensorStatus {
            sensor_id: config.id.clone(),
            online: false,
            last_read: None,
            error_count: 0,
            battery_level: None,
            signal_strength: None,
        };
        
        Self { config, status }
    }

    /// 初始化传感器
    pub async fn initialize(&mut self) -> Result<(), DeviceManagementError> {
        // 模拟传感器初始化
        tokio::time::sleep(Duration::from_millis(100)).await;
        self.status.online = true;
        Ok(())
    }

    /// 读取传感器数据
    pub async fn read(&self) -> Result<SensorReading, DeviceManagementError> {
        if !self.status.online {
            return Err(DeviceManagementError::SensorInitializationFailed(
                "传感器未初始化".to_string()
            ));
        }

        // 模拟传感器读取
        tokio::time::sleep(Duration::from_millis(10)).await;
        
        // 生成模拟数据
        let raw_value = (std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_secs() % 100) as f64 + 20.0; // 20-120°C范围
        
        let calibrated_value = if let Some(_calibration) = &self.config.calibration {
            // 简化实现，实际应该使用calibration.parameters中的参数
            raw_value * 1.0 + 0.0
        } else {
            raw_value
        };

        let quality = if calibrated_value < 0.0 || calibrated_value > 100.0 {
            DataQuality::Bad
        } else if calibrated_value < 10.0 || calibrated_value > 80.0 {
            DataQuality::Uncertain
        } else {
            DataQuality::Good
        };

        Ok(SensorReading {
            sensor_id: self.config.id.clone(),
            sensor_type: self.config.sensor_type.clone(),
            value: calibrated_value,
            unit: self.config.sensor_type.unit().to_string(),
            quality,
            timestamp: Utc::now(),
            raw_value: Some(raw_value),
            calibrated_value: Some(calibrated_value),
        })
    }

    /// 校准传感器
    pub async fn calibrate(&mut self, calibration: CalibrationInfo) -> Result<(), DeviceManagementError> {
        self.config.calibration = Some(calibration);
        Ok(())
    }

    /// 获取传感器状态
    pub async fn get_status(&self) -> Result<SensorStatus, DeviceManagementError> {
        Ok(self.status.clone())
    }

    /// 重置传感器
    pub async fn reset(&mut self) -> Result<(), DeviceManagementError> {
        self.status.error_count = 0;
        self.status.online = false;
        Ok(())
    }

    /// 获取传感器配置
    pub fn get_config(&self) -> &SensorConfig {
        &self.config
    }
}

/// 传感器收集器
#[derive(Clone)]
pub struct SensorCollector {
    sensors: Vec<TemperatureSensor>,
    data_sender: tokio::sync::mpsc::UnboundedSender<SensorReading>,
}

impl SensorCollector {
    /// 创建新的传感器收集器
    pub fn new() -> (Self, tokio::sync::mpsc::UnboundedReceiver<SensorReading>) {
        let (data_sender, data_receiver) = tokio::sync::mpsc::unbounded_channel();
        let collector = Self {
            sensors: Vec::new(),
            data_sender,
        };
        (collector, data_receiver)
    }

    /// 添加传感器
    pub fn add_sensor(&mut self, sensor: TemperatureSensor) {
        self.sensors.push(sensor);
    }

    /// 获取传感器数量
    pub fn sensor_count(&self) -> usize {
        self.sensors.len()
    }

    /// 启动数据收集
    pub async fn start_collection(&self) -> Result<(), DeviceManagementError> {
        let mut interval = interval(Duration::from_secs(1));
        
        loop {
            interval.tick().await;
            
            for sensor in &self.sensors {
                if let Ok(reading) = sensor.read().await {
                    if let Err(_) = self.data_sender.send(reading) {
                        eprintln!("数据发送失败");
                    }
                }
            }
        }
    }

    /// 创建传感器
    pub fn create_sensor(config: SensorConfig) -> Result<TemperatureSensor, DeviceManagementError> {
        if config.sensor_type != SensorType::Temperature {
            return Err(DeviceManagementError::SensorInitializationFailed(
                "不支持的传感器类型".to_string()
            ));
        }
        
        Ok(TemperatureSensor::new(config))
    }
}

/// 传感器工厂
pub struct SensorFactory;

impl SensorFactory {
    /// 创建传感器
    pub fn create_sensor(config: SensorConfig) -> Result<TemperatureSensor, DeviceManagementError> {
        match config.sensor_type {
            SensorType::Temperature => Ok(TemperatureSensor::new(config)),
            _ => Err(DeviceManagementError::SensorInitializationFailed(
                "不支持的传感器类型".to_string()
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_temperature_sensor_creation() {
        let config = SensorConfig {
            id: "temp_001".to_string(),
            sensor_type: SensorType::Temperature,
            address: 0x48,
            sampling_rate: Duration::from_secs(1),
            calibration: None,
            enabled: true,
        };
        
        let sensor = TemperatureSensor::new(config);
        assert_eq!(sensor.get_config().id, "temp_001");
    }

    #[tokio::test]
    async fn test_temperature_sensor_initialization() {
        let config = SensorConfig {
            id: "temp_001".to_string(),
            sensor_type: SensorType::Temperature,
            address: 0x48,
            sampling_rate: Duration::from_secs(1),
            calibration: None,
            enabled: true,
        };
        
        let mut sensor = TemperatureSensor::new(config);
        assert!(sensor.initialize().await.is_ok());
        
        let status = sensor.get_status().await.unwrap();
        assert!(status.online);
    }

    #[tokio::test]
    async fn test_temperature_sensor_reading() {
        let config = SensorConfig {
            id: "temp_001".to_string(),
            sensor_type: SensorType::Temperature,
            address: 0x48,
            sampling_rate: Duration::from_secs(1),
            calibration: None,
            enabled: true,
        };
        
        let mut sensor = TemperatureSensor::new(config);
        sensor.initialize().await.unwrap();
        
        let reading = sensor.read().await.unwrap();
        assert_eq!(reading.sensor_id, "temp_001");
        assert_eq!(reading.sensor_type, SensorType::Temperature);
        assert_eq!(reading.unit, "°C");
    }

    #[tokio::test]
    async fn test_sensor_collector_creation() {
        let (collector, _receiver) = SensorCollector::new();
        assert_eq!(collector.sensor_count(), 0);
    }

    #[tokio::test]
    async fn test_sensor_collector_add_sensor() {
        let (mut collector, _receiver) = SensorCollector::new();
        
        let config = SensorConfig {
            id: "temp_001".to_string(),
            sensor_type: SensorType::Temperature,
            address: 0x48,
            sampling_rate: Duration::from_secs(1),
            calibration: None,
            enabled: true,
        };
        
        let sensor = TemperatureSensor::new(config);
        collector.add_sensor(sensor);
        
        assert_eq!(collector.sensor_count(), 1);
    }

    #[tokio::test]
    async fn test_sensor_factory() {
        let config = SensorConfig {
            id: "temp_001".to_string(),
            sensor_type: SensorType::Temperature,
            address: 0x48,
            sampling_rate: Duration::from_secs(1),
            calibration: None,
            enabled: true,
        };
        
        let sensor = SensorFactory::create_sensor(config).unwrap();
        assert_eq!(sensor.get_config().id, "temp_001");
    }

    #[tokio::test]
    async fn test_sensor_type_descriptions() {
        assert_eq!(SensorType::Temperature.description(), "温度传感器");
        assert_eq!(SensorType::Humidity.description(), "湿度传感器");
        assert_eq!(SensorType::Pressure.description(), "压力传感器");
        assert_eq!(SensorType::Light.description(), "光照传感器");
        assert_eq!(SensorType::Motion.description(), "运动传感器");
        assert_eq!(SensorType::Gas.description(), "气体传感器");
        assert_eq!(SensorType::Sound.description(), "声音传感器");
        assert_eq!(SensorType::Vibration.description(), "振动传感器");
    }

    #[tokio::test]
    async fn test_sensor_type_units() {
        assert_eq!(SensorType::Temperature.unit(), "°C");
        assert_eq!(SensorType::Humidity.unit(), "%");
        assert_eq!(SensorType::Pressure.unit(), "hPa");
        assert_eq!(SensorType::Light.unit(), "lux");
        assert_eq!(SensorType::Motion.unit(), "count");
        assert_eq!(SensorType::Gas.unit(), "ppm");
        assert_eq!(SensorType::Sound.unit(), "dB");
        assert_eq!(SensorType::Vibration.unit(), "g");
    }
}
