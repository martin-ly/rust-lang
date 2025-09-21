//! 设备状态模块
//! 
//! 定义设备状态相关的数据结构和类型

use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};

/// 设备状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceStatus {
    /// 设备ID
    pub device_id: String,
    /// 设备状态
    pub status: Status,
    /// 最后在线时间
    pub last_seen: DateTime<Utc>,
    /// 电池电量 (0-100)
    pub battery_level: Option<u8>,
    /// 信号强度 (dBm)
    pub signal_strength: Option<i8>,
    /// 错误计数
    pub error_count: u32,
    /// 设备温度 (摄氏度)
    pub temperature: Option<f32>,
    /// 设备湿度 (%)
    pub humidity: Option<f32>,
    /// 设备压力 (hPa)
    pub pressure: Option<f32>,
    /// 设备运行时间 (秒)
    pub uptime: Option<u64>,
    /// 最后错误信息
    pub last_error: Option<String>,
    /// 设备健康状态
    pub health: HealthStatus,
}

impl DeviceStatus {
    /// 创建新的设备状态
    pub fn new(device_id: String) -> Self {
        Self {
            device_id,
            status: Status::Offline,
            last_seen: Utc::now(),
            battery_level: None,
            signal_strength: None,
            error_count: 0,
            temperature: None,
            humidity: None,
            pressure: None,
            uptime: None,
            last_error: None,
            health: HealthStatus::Unknown,
        }
    }

    /// 更新设备状态
    pub fn update_status(&mut self, status: Status) {
        self.status = status;
        self.last_seen = Utc::now();
    }

    /// 更新电池电量
    pub fn update_battery_level(&mut self, level: u8) {
        self.battery_level = Some(level);
        self.last_seen = Utc::now();
    }

    /// 更新信号强度
    pub fn update_signal_strength(&mut self, strength: i8) {
        self.signal_strength = Some(strength);
        self.last_seen = Utc::now();
    }

    /// 增加错误计数
    pub fn increment_error_count(&mut self, error_message: Option<String>) {
        self.error_count += 1;
        if let Some(message) = error_message {
            self.last_error = Some(message);
        }
        self.last_seen = Utc::now();
    }

    /// 重置错误计数
    pub fn reset_error_count(&mut self) {
        self.error_count = 0;
        self.last_error = None;
        self.last_seen = Utc::now();
    }

    /// 更新环境数据
    pub fn update_environment_data(&mut self, temperature: Option<f32>, humidity: Option<f32>, pressure: Option<f32>) {
        self.temperature = temperature;
        self.humidity = humidity;
        self.pressure = pressure;
        self.last_seen = Utc::now();
    }

    /// 更新运行时间
    pub fn update_uptime(&mut self, uptime: u64) {
        self.uptime = Some(uptime);
        self.last_seen = Utc::now();
    }

    /// 更新健康状态
    pub fn update_health(&mut self, health: HealthStatus) {
        self.health = health;
        self.last_seen = Utc::now();
    }

    /// 检查设备是否在线
    pub fn is_online(&self) -> bool {
        matches!(self.status, Status::Online)
    }

    /// 检查设备是否健康
    pub fn is_healthy(&self) -> bool {
        matches!(self.health, HealthStatus::Healthy)
    }

    /// 检查设备是否需要维护
    pub fn needs_maintenance(&self) -> bool {
        self.error_count > 10 || 
        matches!(self.health, HealthStatus::Degraded | HealthStatus::Critical) ||
        (self.battery_level.is_some() && self.battery_level.unwrap() < 20)
    }

    /// 获取设备状态摘要
    pub fn get_summary(&self) -> DeviceStatusSummary {
        DeviceStatusSummary {
            device_id: self.device_id.clone(),
            status: self.status.clone(),
            is_online: self.is_online(),
            is_healthy: self.is_healthy(),
            needs_maintenance: self.needs_maintenance(),
            last_seen: self.last_seen,
            error_count: self.error_count,
        }
    }
}

/// 设备状态枚举
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum Status {
    /// 在线
    Online,
    /// 离线
    Offline,
    /// 维护中
    Maintenance,
    /// 错误状态
    Error,
    /// 休眠状态
    Sleeping,
    /// 启动中
    Starting,
    /// 停止中
    Stopping,
}

impl Status {
    /// 获取状态描述
    pub fn description(&self) -> &'static str {
        match self {
            Status::Online => "在线",
            Status::Offline => "离线",
            Status::Maintenance => "维护中",
            Status::Error => "错误",
            Status::Sleeping => "休眠",
            Status::Starting => "启动中",
            Status::Stopping => "停止中",
        }
    }

    /// 检查是否为活跃状态
    pub fn is_active(&self) -> bool {
        matches!(self, Status::Online | Status::Starting | Status::Stopping)
    }

    /// 检查是否为错误状态
    pub fn is_error(&self) -> bool {
        matches!(self, Status::Error)
    }
}

/// 设备健康状态
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub enum HealthStatus {
    /// 健康
    Healthy,
    /// 降级
    Degraded,
    /// 严重
    Critical,
    /// 未知
    Unknown,
}

impl HealthStatus {
    /// 获取健康状态描述
    pub fn description(&self) -> &'static str {
        match self {
            HealthStatus::Healthy => "健康",
            HealthStatus::Degraded => "降级",
            HealthStatus::Critical => "严重",
            HealthStatus::Unknown => "未知",
        }
    }

    /// 获取健康状态优先级 (数字越小优先级越高)
    pub fn priority(&self) -> u8 {
        match self {
            HealthStatus::Critical => 1,
            HealthStatus::Degraded => 2,
            HealthStatus::Unknown => 3,
            HealthStatus::Healthy => 4,
        }
    }
}

/// 设备状态摘要
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DeviceStatusSummary {
    /// 设备ID
    pub device_id: String,
    /// 设备状态
    pub status: Status,
    /// 是否在线
    pub is_online: bool,
    /// 是否健康
    pub is_healthy: bool,
    /// 是否需要维护
    pub needs_maintenance: bool,
    /// 最后在线时间
    pub last_seen: DateTime<Utc>,
    /// 错误计数
    pub error_count: u32,
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
    /// 电池电量变化
    BatteryLevelChanged { from: Option<u8>, to: Option<u8> },
    /// 信号强度变化
    SignalStrengthChanged { from: Option<i8>, to: Option<i8> },
    /// 错误计数增加
    ErrorCountIncreased { count: u32 },
    /// 健康状态变化
    HealthChanged { from: HealthStatus, to: HealthStatus },
    /// 环境数据更新
    EnvironmentDataUpdated,
}

impl StatusChange {
    /// 获取变化描述
    pub fn description(&self) -> String {
        match self {
            StatusChange::StatusChanged { from, to } => {
                format!("状态从 {} 变为 {}", from.description(), to.description())
            }
            StatusChange::BatteryLevelChanged { from, to } => {
                format!("电池电量从 {:?}% 变为 {:?}%", from, to)
            }
            StatusChange::SignalStrengthChanged { from, to } => {
                format!("信号强度从 {:?}dBm 变为 {:?}dBm", from, to)
            }
            StatusChange::ErrorCountIncreased { count } => {
                format!("错误计数增加到 {}", count)
            }
            StatusChange::HealthChanged { from, to } => {
                format!("健康状态从 {} 变为 {}", from.description(), to.description())
            }
            StatusChange::EnvironmentDataUpdated => {
                "环境数据已更新".to_string()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_device_status_creation() {
        let status = DeviceStatus::new("device_001".to_string());
        assert_eq!(status.device_id, "device_001");
        assert_eq!(status.status, Status::Offline);
        assert_eq!(status.error_count, 0);
        assert!(!status.is_online());
    }

    #[test]
    fn test_device_status_updates() {
        let mut status = DeviceStatus::new("device_001".to_string());
        
        status.update_status(Status::Online);
        assert!(status.is_online());
        
        status.update_battery_level(85);
        assert_eq!(status.battery_level, Some(85));
        
        status.increment_error_count(Some("Test error".to_string()));
        assert_eq!(status.error_count, 1);
        assert_eq!(status.last_error, Some("Test error".to_string()));
    }

    #[test]
    fn test_maintenance_check() {
        let mut status = DeviceStatus::new("device_001".to_string());
        
        // 正常情况不需要维护
        assert!(!status.needs_maintenance());
        
        // 错误计数过多需要维护
        for _ in 0..11 {
            status.increment_error_count(None);
        }
        assert!(status.needs_maintenance());
        
        // 重置错误计数
        status.reset_error_count();
        status.update_battery_level(15); // 低电量
        assert!(status.needs_maintenance());
    }

    #[test]
    fn test_status_methods() {
        let online_status = Status::Online;
        assert!(online_status.is_active());
        assert!(!online_status.is_error());
        
        let error_status = Status::Error;
        assert!(!error_status.is_active());
        assert!(error_status.is_error());
    }

    #[test]
    fn test_health_status_priority() {
        assert_eq!(HealthStatus::Critical.priority(), 1);
        assert_eq!(HealthStatus::Degraded.priority(), 2);
        assert_eq!(HealthStatus::Unknown.priority(), 3);
        assert_eq!(HealthStatus::Healthy.priority(), 4);
    }
}
