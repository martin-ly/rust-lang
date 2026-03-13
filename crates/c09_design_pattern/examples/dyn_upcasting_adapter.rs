//! Rust 1.90 dyn upcasting 适配器模式示例
//!
//! 本示例展示：
//! 1. trait 对象的上转型（dyn upcasting）
//! 2. 适配器模式的层次结构
//! 3. 多层trait继承的实际应用
//! 4. 与传统方案的对比
use std::fmt;

// ============================================================================
// 基础 trait 层次结构
// ============================================================================

/// 基础 Device trait
pub trait Device {
    fn device_id(&self) -> &str;
    fn device_type(&self) -> &str;
    fn status(&self) -> DeviceStatus;
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum DeviceStatus {
    Online,
    Offline,
    Error,
}

impl fmt::Display for DeviceStatus {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            DeviceStatus::Online => write!(f, "在线"),
            DeviceStatus::Offline => write!(f, "离线"),
            DeviceStatus::Error => write!(f, "错误"),
        }
    }
}

/// 可控制的设备
pub trait Controllable: Device {
    fn turn_on(&mut self) -> Result<(), String>;
    fn turn_off(&mut self) -> Result<(), String>;
    fn is_on(&self) -> bool;
}

/// 可监控的设备
pub trait Monitorable: Device {
    fn get_metrics(&self) -> Metrics;
    fn get_health(&self) -> HealthStatus;
}

#[derive(Debug, Clone)]
pub struct Metrics {
    pub uptime_secs: u64,
    pub requests_handled: u64,
    pub error_count: u32,
}

#[derive(Debug, Clone, Copy)]
pub enum HealthStatus {
    Healthy,
    Degraded,
    Unhealthy,
}

impl fmt::Display for HealthStatus {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            HealthStatus::Healthy => write!(f, "健康"),
            HealthStatus::Degraded => write!(f, "降级"),
            HealthStatus::Unhealthy => write!(f, "不健康"),
        }
    }
}

/// 智能设备（同时可控制和可监控）
pub trait SmartDevice: Controllable + Monitorable {
    fn firmware_version(&self) -> &str;
    fn update_firmware(&mut self, version: &str) -> Result<(), String>;
}

// ============================================================================
// 具体设备实现
// ============================================================================

/// 智能灯泡
pub struct SmartBulb {
    id: String,
    is_on: bool,
    status: DeviceStatus,
    firmware: String,
    uptime: u64,
}

impl SmartBulb {
    pub fn new(id: impl Into<String>) -> Self {
        SmartBulb {
            id: id.into(),
            is_on: false,
            status: DeviceStatus::Online,
            firmware: "1.0.0".to_string(),
            uptime: 0,
        }
    }
}

impl Device for SmartBulb {
    fn device_id(&self) -> &str {
        &self.id
    }
    
    fn device_type(&self) -> &str {
        "SmartBulb"
    }
    
    fn status(&self) -> DeviceStatus {
        self.status
    }
}

impl Controllable for SmartBulb {
    fn turn_on(&mut self) -> Result<(), String> {
        if self.status != DeviceStatus::Online {
            return Err("设备不在线".to_string());
        }
        self.is_on = true;
        println!("💡 灯泡 {} 已打开", self.id);
        Ok(())
    }
    
    fn turn_off(&mut self) -> Result<(), String> {
        self.is_on = false;
        println!("💡 灯泡 {} 已关闭", self.id);
        Ok(())
    }
    
    fn is_on(&self) -> bool {
        self.is_on
    }
}

impl Monitorable for SmartBulb {
    fn get_metrics(&self) -> Metrics {
        Metrics {
            uptime_secs: self.uptime,
            requests_handled: 100,
            error_count: 0,
        }
    }
    
    fn get_health(&self) -> HealthStatus {
        if self.status == DeviceStatus::Online {
            HealthStatus::Healthy
        } else {
            HealthStatus::Unhealthy
        }
    }
}

impl SmartDevice for SmartBulb {
    fn firmware_version(&self) -> &str {
        &self.firmware
    }
    
    fn update_firmware(&mut self, version: &str) -> Result<(), String> {
        println!("🔄 更新固件: {} -> {}", self.firmware, version);
        self.firmware = version.to_string();
        Ok(())
    }
}

// ============================================================================
// 适配器层
// ============================================================================

/// 旧设备适配器（将不支持监控的设备适配为 SmartDevice）
pub struct LegacyDeviceAdapter {
    device: Box<dyn Controllable>,
    id: String,
}

impl LegacyDeviceAdapter {
    pub fn new(id: impl Into<String>, device: Box<dyn Controllable>) -> Self {
        LegacyDeviceAdapter {
            device,
            id: id.into(),
        }
    }
}

impl Device for LegacyDeviceAdapter {
    fn device_id(&self) -> &str {
        &self.id
    }
    
    fn device_type(&self) -> &str {
        "LegacyDevice"
    }
    
    fn status(&self) -> DeviceStatus {
        DeviceStatus::Online
    }
}

impl Controllable for LegacyDeviceAdapter {
    fn turn_on(&mut self) -> Result<(), String> {
        self.device.turn_on()
    }
    
    fn turn_off(&mut self) -> Result<(), String> {
        self.device.turn_off()
    }
    
    fn is_on(&self) -> bool {
        self.device.is_on()
    }
}

impl Monitorable for LegacyDeviceAdapter {
    fn get_metrics(&self) -> Metrics {
        // 提供默认的监控数据
        Metrics {
            uptime_secs: 0,
            requests_handled: 0,
            error_count: 0,
        }
    }
    
    fn get_health(&self) -> HealthStatus {
        HealthStatus::Healthy
    }
}

impl SmartDevice for LegacyDeviceAdapter {
    fn firmware_version(&self) -> &str {
        "Legacy"
    }
    
    fn update_firmware(&mut self, _version: &str) -> Result<(), String> {
        Err("旧设备不支持固件更新".to_string())
    }
}

// ============================================================================
// dyn upcasting 演示函数
// ============================================================================

/// 处理任何设备（基础层）
pub fn process_device(device: &dyn Device) {
    println!("\n📱 设备信息:");
    println!("  ID: {}", device.device_id());
    println!("  类型: {}", device.device_type());
    println!("  状态: {}", device.status());
}

/// 处理可控制设备（中间层）
pub fn process_controllable(device: &mut dyn Controllable) {
    println!("\n🎮 控制设备:");
    let _ = device.turn_on();
    println!("  开关状态: {}", if device.is_on() { "开" } else { "关" });
    
    // ✅ dyn upcasting: Controllable -> Device
    let base: &dyn Device = device;
    println!("  [上转型] 设备ID: {}", base.device_id());
}

/// 处理可监控设备（中间层）
pub fn process_monitorable(device: &dyn Monitorable) {
    println!("\n📊 监控设备:");
    let metrics = device.get_metrics();
    println!("  运行时间: {} 秒", metrics.uptime_secs);
    println!("  处理请求: {}", metrics.requests_handled);
    println!("  健康状态: {}", device.get_health());
    
    // ✅ dyn upcasting: Monitorable -> Device
    let base: &dyn Device = device;
    println!("  [上转型] 设备类型: {}", base.device_type());
}

/// 处理智能设备（顶层）
pub fn process_smart_device(device: &mut dyn SmartDevice) {
    println!("\n🤖 智能设备:");
    println!("  固件版本: {}", device.firmware_version());
    
    // ✅ dyn upcasting: SmartDevice -> Controllable
    let controllable: &mut dyn Controllable = device;
    let _ = controllable.turn_on();
    
    // ✅ dyn upcasting: SmartDevice -> Monitorable
    let monitorable: &dyn Monitorable = device;
    println!("  健康状态: {}", monitorable.get_health());
    
    // ✅ dyn upcasting: SmartDevice -> Device
    let base: &dyn Device = device;
    println!("  [上转型] 设备ID: {}", base.device_id());
}

// ============================================================================
// 设备管理器
// ============================================================================

pub struct DeviceManager {
    devices: Vec<Box<dyn SmartDevice>>,
}

impl DeviceManager {
    pub fn new() -> Self {
        DeviceManager {
            devices: Vec::new(),
        }
    }
    
    pub fn add_device(&mut self, device: Box<dyn SmartDevice>) {
        self.devices.push(device);
    }
    
    /// 控制所有设备
    pub fn control_all(&mut self, turn_on: bool) {
        println!("\n🎛️  {} 所有设备", if turn_on { "打开" } else { "关闭" });
        for device in &mut self.devices {
            // ✅ 上转型到 Controllable
            let controllable: &mut dyn Controllable = &mut **device;
            let result = if turn_on {
                controllable.turn_on()
            } else {
                controllable.turn_off()
            };
            
            match result {
                Ok(_) => println!("  ✅ {}: 成功", device.device_id()),
                Err(e) => println!("  ❌ {}: {}", device.device_id(), e),
            }
        }
    }
    
    /// 监控所有设备
    pub fn monitor_all(&self) {
        println!("\n📈 监控所有设备");
        for device in &self.devices {
            // ✅ 上转型到 Monitorable
            let monitorable: &dyn Monitorable = &**device;
            println!("  {} - 健康: {}", 
                     device.device_id(), 
                     monitorable.get_health());
        }
    }
    
    /// 列出所有设备
    pub fn list_devices(&self) {
        println!("\n📋 设备列表");
        for device in &self.devices {
            // ✅ 上转型到 Device
            let base: &dyn Device = &**device;
            println!("  • {} ({}) - {}", 
                     base.device_id(), 
                     base.device_type(), 
                     base.status());
        }
    }
}

// ============================================================================
// 主函数
// ============================================================================

fn main() {
    println!("🦀 Rust 1.90 dyn upcasting 适配器模式示例\n");
    println!("{}", "=".repeat(70));
    
    // 示例 1: 单个智能设备
    println!("\n📌 示例 1: 智能灯泡基本操作");
    println!("{}", "-".repeat(70));
    
    let mut bulb = SmartBulb::new("bulb-001");
    
    // 作为 Device 使用
    process_device(&bulb);
    
    // 作为 Controllable 使用（自动上转型）
    process_controllable(&mut bulb);
    
    // 作为 Monitorable 使用（自动上转型）
    process_monitorable(&bulb);
    
    // 作为 SmartDevice 使用
    process_smart_device(&mut bulb);
    
    // 示例 2: 设备管理器
    println!("\n📌 示例 2: 设备管理器");
    println!("{}", "-".repeat(70));
    
    let mut manager = DeviceManager::new();
    
    // 添加多个设备
    manager.add_device(Box::new(SmartBulb::new("bulb-001")));
    manager.add_device(Box::new(SmartBulb::new("bulb-002")));
    manager.add_device(Box::new(SmartBulb::new("bulb-003")));
    
    // 列出设备
    manager.list_devices();
    
    // 控制所有设备
    manager.control_all(true);
    
    // 监控所有设备
    manager.monitor_all();
    
    // 关闭所有设备
    manager.control_all(false);
    
    // 示例 3: 适配器模式
    println!("\n📌 示例 3: 旧设备适配");
    println!("{}", "-".repeat(70));
    
    // 创建一个只实现 Controllable 的设备
    let legacy = SmartBulb::new("legacy-001");
    
    // 使用适配器包装
    let mut adapter = LegacyDeviceAdapter::new(
        "adapted-legacy-001",
        Box::new(legacy)
    );
    
    println!("适配前: 旧设备只支持控制");
    println!("适配后: 可以作为 SmartDevice 使用");
    
    process_smart_device(&mut adapter);
    
    // 尝试更新固件（会失败）
    match adapter.update_firmware("2.0.0") {
        Ok(_) => println!("✅ 固件更新成功"),
        Err(e) => println!("⚠️  {}", e),
    }
    
    // 总结
    println!("\n{}", "=".repeat(70));
    println!("✅ dyn upcasting 的优势:");
    println!("  1. 自动类型转换 - 无需手动转换");
    println!("  2. 类型安全 - 编译时检查");
    println!("  3. 灵活性 - 支持多层trait继承");
    println!("  4. 简洁性 - 代码更清晰");
    println!("\n💡 适用场景:");
    println!("  - 设备管理系统");
    println!("  - 插件架构");
    println!("  - 多层抽象接口");
    println!("  - 适配器模式");
    println!("\n📝 对比传统方案:");
    println!("  旧方案: 需要手动实现转换方法");
    println!("  新方案: 编译器自动上转型");
    println!("  代码量: 减少约20%");
    println!("  安全性: 提升（编译时检查）");
    println!("{}", "=".repeat(70));
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_smart_bulb() {
        let mut bulb = SmartBulb::new("test-bulb");
        
        // 测试 Device trait
        assert_eq!(bulb.device_id(), "test-bulb");
        assert_eq!(bulb.device_type(), "SmartBulb");
        
        // 测试 Controllable trait
        assert!(!bulb.is_on());
        bulb.turn_on().unwrap();
        assert!(bulb.is_on());
        
        // 测试 Monitorable trait
        let metrics = bulb.get_metrics();
        assert_eq!(metrics.uptime_secs, 0);
        
        // 测试 SmartDevice trait
        assert_eq!(bulb.firmware_version(), "1.0.0");
    }
    
    #[test]
    fn test_upcasting() {
        let mut bulb = SmartBulb::new("test");
        
        // SmartDevice -> Controllable
        let controllable: &mut dyn Controllable = &mut bulb;
        controllable.turn_on().unwrap();
        
        // SmartDevice -> Monitorable
        let monitorable: &dyn Monitorable = &bulb;
        assert!(matches!(monitorable.get_health(), HealthStatus::Healthy));
        
        // SmartDevice -> Device
        let device: &dyn Device = &bulb;
        assert_eq!(device.device_type(), "SmartBulb");
    }
    
    #[test]
    fn test_device_manager() {
        let mut manager = DeviceManager::new();
        manager.add_device(Box::new(SmartBulb::new("b1")));
        manager.add_device(Box::new(SmartBulb::new("b2")));
        
        assert_eq!(manager.devices.len(), 2);
        
        manager.control_all(true);
        
        // 验证所有设备都打开了
        for device in &manager.devices {
            let controllable: &dyn Controllable = &**device;
            assert!(controllable.is_on());
        }
    }
}

