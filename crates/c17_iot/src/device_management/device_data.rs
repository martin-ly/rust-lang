//! 设备数据模块
//! 
//! 定义设备数据相关的数据结构和类型

use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use std::collections::HashMap;

/// 设备数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceData {
    /// 设备ID
    pub device_id: String,
    /// 数据时间戳
    pub timestamp: DateTime<Utc>,
    /// 数据类型
    pub data_type: String,
    /// 数据值
    pub value: serde_json::Value,
    /// 数据质量
    pub quality: DataQuality,
    /// 数据单位
    pub unit: Option<String>,
    /// 数据标签
    pub tags: HashMap<String, String>,
    /// 数据来源
    pub source: Option<String>,
    /// 数据版本
    pub version: Option<String>,
}

impl DeviceData {
    /// 创建新的设备数据
    pub fn new(
        device_id: String,
        data_type: String,
        value: serde_json::Value,
        quality: DataQuality,
    ) -> Self {
        Self {
            device_id,
            timestamp: Utc::now(),
            data_type,
            value,
            quality,
            unit: None,
            tags: HashMap::new(),
            source: None,
            version: None,
        }
    }

    /// 设置数据单位
    pub fn with_unit(mut self, unit: String) -> Self {
        self.unit = Some(unit);
        self
    }

    /// 设置数据来源
    pub fn with_source(mut self, source: String) -> Self {
        self.source = Some(source);
        self
    }

    /// 设置数据版本
    pub fn with_version(mut self, version: String) -> Self {
        self.version = Some(version);
        self
    }

    /// 添加标签
    pub fn add_tag(mut self, key: String, value: String) -> Self {
        self.tags.insert(key, value);
        self
    }

    /// 获取标签值
    pub fn get_tag(&self, key: &str) -> Option<&String> {
        self.tags.get(key)
    }

    /// 验证数据
    pub fn validate(&self) -> Result<(), String> {
        if self.device_id.is_empty() {
            return Err("设备ID不能为空".to_string());
        }
        if self.data_type.is_empty() {
            return Err("数据类型不能为空".to_string());
        }
        if self.value.is_null() {
            return Err("数据值不能为空".to_string());
        }
        Ok(())
    }

    /// 检查数据是否有效
    pub fn is_valid(&self) -> bool {
        self.validate().is_ok() && matches!(self.quality, DataQuality::Good)
    }

    /// 获取数值类型的数据值
    pub fn get_numeric_value(&self) -> Option<f64> {
        self.value.as_f64()
    }

    /// 获取字符串类型的数据值
    pub fn get_string_value(&self) -> Option<&str> {
        self.value.as_str()
    }

    /// 获取布尔类型的数据值
    pub fn get_bool_value(&self) -> Option<bool> {
        self.value.as_bool()
    }
}

/// 数据质量
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum DataQuality {
    /// 良好
    Good,
    /// 不确定
    Uncertain,
    /// 不良
    Bad,
    /// 无效
    Invalid,
}

impl DataQuality {
    /// 获取质量描述
    pub fn description(&self) -> &'static str {
        match self {
            DataQuality::Good => "良好",
            DataQuality::Uncertain => "不确定",
            DataQuality::Bad => "不良",
            DataQuality::Invalid => "无效",
        }
    }

    /// 获取质量等级 (数字越小质量越好)
    pub fn level(&self) -> u8 {
        match self {
            DataQuality::Good => 1,
            DataQuality::Uncertain => 2,
            DataQuality::Bad => 3,
            DataQuality::Invalid => 4,
        }
    }

    /// 检查是否为有效数据
    pub fn is_valid(&self) -> bool {
        matches!(self, DataQuality::Good | DataQuality::Uncertain)
    }
}

/// 传感器数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SensorData {
    /// 传感器ID
    pub sensor_id: String,
    /// 数据时间戳
    pub timestamp: DateTime<Utc>,
    /// 传感器类型
    pub sensor_type: SensorDataType,
    /// 数据值
    pub value: f64,
    /// 数据单位
    pub unit: String,
    /// 数据质量
    pub quality: DataQuality,
    /// 校准信息
    pub calibration: Option<CalibrationInfo>,
    /// 环境条件
    pub environment: Option<EnvironmentData>,
}

/// 传感器数据类型
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum SensorDataType {
    /// 温度
    Temperature,
    /// 湿度
    Humidity,
    /// 压力
    Pressure,
    /// 光照
    Light,
    /// 运动
    Motion,
    /// 气体
    Gas,
    /// 声音
    Sound,
    /// 振动
    Vibration,
    /// 电流
    Current,
    /// 电压
    Voltage,
    /// 功率
    Power,
    /// 其他
    Other(String),
}

impl SensorDataType {
    /// 获取类型描述
    pub fn description(&self) -> &str {
        match self {
            SensorDataType::Temperature => "温度",
            SensorDataType::Humidity => "湿度",
            SensorDataType::Pressure => "压力",
            SensorDataType::Light => "光照",
            SensorDataType::Motion => "运动",
            SensorDataType::Gas => "气体",
            SensorDataType::Sound => "声音",
            SensorDataType::Vibration => "振动",
            SensorDataType::Current => "电流",
            SensorDataType::Voltage => "电压",
            SensorDataType::Power => "功率",
            SensorDataType::Other(name) => name,
        }
    }

    /// 获取默认单位
    pub fn default_unit(&self) -> &str {
        match self {
            SensorDataType::Temperature => "°C",
            SensorDataType::Humidity => "%",
            SensorDataType::Pressure => "hPa",
            SensorDataType::Light => "lux",
            SensorDataType::Motion => "count",
            SensorDataType::Gas => "ppm",
            SensorDataType::Sound => "dB",
            SensorDataType::Vibration => "g",
            SensorDataType::Current => "A",
            SensorDataType::Voltage => "V",
            SensorDataType::Power => "W",
            SensorDataType::Other(_) => "unit",
        }
    }
}

/// 校准信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CalibrationInfo {
    /// 校准时间
    pub calibration_time: DateTime<Utc>,
    /// 校准人员
    pub calibrator: Option<String>,
    /// 校准方法
    pub method: Option<String>,
    /// 校准参数
    pub parameters: HashMap<String, f64>,
}

/// 环境数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnvironmentData {
    /// 环境温度
    pub temperature: Option<f32>,
    /// 环境湿度
    pub humidity: Option<f32>,
    /// 环境压力
    pub pressure: Option<f32>,
    /// 环境光照
    pub light: Option<f32>,
    /// 环境噪声
    pub noise: Option<f32>,
}

/// 批量设备数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchDeviceData {
    /// 批次ID
    pub batch_id: String,
    /// 设备数据列表
    pub data_list: Vec<DeviceData>,
    /// 批次时间戳
    pub timestamp: DateTime<Utc>,
    /// 批次大小
    pub batch_size: usize,
    /// 数据源
    pub source: Option<String>,
}

impl BatchDeviceData {
    /// 创建新的批量数据
    pub fn new(batch_id: String, data_list: Vec<DeviceData>) -> Self {
        let batch_size = data_list.len();
        Self {
            batch_id,
            data_list,
            timestamp: Utc::now(),
            batch_size,
            source: None,
        }
    }

    /// 设置数据源
    pub fn with_source(mut self, source: String) -> Self {
        self.source = Some(source);
        self
    }

    /// 验证批量数据
    pub fn validate(&self) -> Result<(), String> {
        if self.batch_id.is_empty() {
            return Err("批次ID不能为空".to_string());
        }
        if self.data_list.is_empty() {
            return Err("数据列表不能为空".to_string());
        }
        if self.batch_size != self.data_list.len() {
            return Err("批次大小与数据列表长度不匹配".to_string());
        }
        
        for data in &self.data_list {
            data.validate()?;
        }
        
        Ok(())
    }

    /// 获取有效数据数量
    pub fn get_valid_data_count(&self) -> usize {
        self.data_list.iter().filter(|data| data.is_valid()).count()
    }

    /// 获取无效数据数量
    pub fn get_invalid_data_count(&self) -> usize {
        self.batch_size - self.get_valid_data_count()
    }

    /// 按设备ID分组数据
    pub fn group_by_device_id(&self) -> HashMap<String, Vec<&DeviceData>> {
        let mut groups = HashMap::new();
        for data in &self.data_list {
            groups.entry(data.device_id.clone()).or_insert_with(Vec::new).push(data);
        }
        groups
    }
}

/// 数据统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DataStatistics {
    /// 总数据量
    pub total_count: usize,
    /// 有效数据量
    pub valid_count: usize,
    /// 无效数据量
    pub invalid_count: usize,
    /// 数据质量分布
    pub quality_distribution: HashMap<DataQuality, usize>,
    /// 设备数据分布
    pub device_distribution: HashMap<String, usize>,
    /// 数据类型分布
    pub type_distribution: HashMap<String, usize>,
    /// 统计时间范围
    pub time_range: (DateTime<Utc>, DateTime<Utc>),
}

impl DataStatistics {
    /// 从批量数据创建统计信息
    pub fn from_batch_data(batch_data: &BatchDeviceData) -> Self {
        let mut quality_distribution = HashMap::new();
        let mut device_distribution = HashMap::new();
        let mut type_distribution = HashMap::new();
        
        let mut min_time = batch_data.timestamp;
        let mut max_time = batch_data.timestamp;
        
        for data in &batch_data.data_list {
            // 质量分布
            *quality_distribution.entry(data.quality.clone()).or_insert(0) += 1;
            
            // 设备分布
            *device_distribution.entry(data.device_id.clone()).or_insert(0) += 1;
            
            // 类型分布
            *type_distribution.entry(data.data_type.clone()).or_insert(0) += 1;
            
            // 时间范围
            if data.timestamp < min_time {
                min_time = data.timestamp;
            }
            if data.timestamp > max_time {
                max_time = data.timestamp;
            }
        }
        
        Self {
            total_count: batch_data.batch_size,
            valid_count: batch_data.get_valid_data_count(),
            invalid_count: batch_data.get_invalid_data_count(),
            quality_distribution,
            device_distribution,
            type_distribution,
            time_range: (min_time, max_time),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_device_data_creation() {
        let data = DeviceData::new(
            "device_001".to_string(),
            "temperature".to_string(),
            serde_json::Value::Number(serde_json::Number::from_f64(25.5).unwrap()),
            DataQuality::Good,
        );

        assert_eq!(data.device_id, "device_001");
        assert_eq!(data.data_type, "temperature");
        assert!(data.is_valid());
    }

    #[test]
    fn test_device_data_validation() {
        let valid_data = DeviceData::new(
            "device_001".to_string(),
            "temperature".to_string(),
            serde_json::Value::Number(serde_json::Number::from_f64(25.5).unwrap()),
            DataQuality::Good,
        );
        assert!(valid_data.validate().is_ok());

        let invalid_data = DeviceData::new(
            "".to_string(),
            "temperature".to_string(),
            serde_json::Value::Number(serde_json::Number::from_f64(25.5).unwrap()),
            DataQuality::Good,
        );
        assert!(invalid_data.validate().is_err());
    }

    #[test]
    fn test_data_quality() {
        assert!(DataQuality::Good.is_valid());
        assert!(DataQuality::Uncertain.is_valid());
        assert!(!DataQuality::Bad.is_valid());
        assert!(!DataQuality::Invalid.is_valid());
        
        assert_eq!(DataQuality::Good.level(), 1);
        assert_eq!(DataQuality::Invalid.level(), 4);
    }

    #[test]
    fn test_sensor_data_type() {
        let temp_type = SensorDataType::Temperature;
        assert_eq!(temp_type.description(), "温度");
        assert_eq!(temp_type.default_unit(), "°C");
    }

    #[test]
    fn test_batch_device_data() {
        let data1 = DeviceData::new(
            "device_001".to_string(),
            "temperature".to_string(),
            serde_json::Value::Number(serde_json::Number::from_f64(25.5).unwrap()),
            DataQuality::Good,
        );
        
        let data2 = DeviceData::new(
            "device_002".to_string(),
            "humidity".to_string(),
            serde_json::Value::Number(serde_json::Number::from_f64(60.0).unwrap()),
            DataQuality::Good,
        );
        
        let batch = BatchDeviceData::new("batch_001".to_string(), vec![data1, data2]);
        
        assert_eq!(batch.batch_size, 2);
        assert_eq!(batch.get_valid_data_count(), 2);
        assert_eq!(batch.get_invalid_data_count(), 0);
        
        let groups = batch.group_by_device_id();
        assert_eq!(groups.len(), 2);
        assert!(groups.contains_key("device_001"));
        assert!(groups.contains_key("device_002"));
    }
}
