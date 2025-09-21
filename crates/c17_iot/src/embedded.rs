//! # IoT 嵌入式系统模块 / IoT Embedded System Module
//!
//! 本模块实现了 IoT 嵌入式系统的核心功能。
//! This module implements the core functionality of IoT embedded systems.

// use crate::types::*;
// use std::collections::HashMap;

/// 传感器 / Sensor
#[derive(Debug, Clone)]
pub struct Sensor {
    pub id: String,
    pub sensor_type: String,
    pub value: f64,
}

/// 执行器 / Actuator
#[derive(Debug, Clone)]
pub struct Actuator {
    pub id: String,
    pub actuator_type: String,
    pub state: bool,
}

/// 嵌入式设备 / Embedded Device
pub struct EmbeddedDevice {
    pub id: String,
    pub device_type: DeviceType,
    pub sensors: Vec<Sensor>,
    pub actuators: Vec<Actuator>,
    pub status: DeviceStatus,
}

impl EmbeddedDevice {
    pub fn new(id: String, device_type: _device_type) -> Self {
        Self {
            id,
            device_type,
            sensors: Vec::new(),
            actuators: Vec::new(),
            status: DeviceStatus::Offline,
        }
    }

    pub fn add_sensor(&mut self, sensor: _sensor) {
        self.sensors.push(sensor);
    }

    pub fn add_actuator(&mut self, actuator: _actuator) {
        self.actuators.push(actuator);
    }

    /// 读取指定传感器的值（按 id）/ Read sensor value by id
    pub fn read_sensor(&self, id: &str) -> Option<f64> {
        self.sensors.iter().find(|s| s.id == id).map(|s| s.value)
    }

    /// 写入执行器状态（按 id）/ Write actuator state by id
    pub fn write_actuator(&mut self, id: &str, state: _state) -> bool {
        if let Some(act) = self.actuators.iter_mut().find(|a| a.id == id) {
            act.state = state;
            true
        } else {
            false
        }
    }
}

/// 设备类型 / Device Type
#[derive(Debug, Clone)]
pub enum DeviceType {
    Sensor,
    Controller,
    Gateway,
    Endpoint,
}

/// 设备状态 / Device Status
#[derive(Debug, Clone)]
pub enum DeviceStatus {
    Online,
    Offline,
    Error,
    Maintenance,
}

/// 数字输出抽象 / Digital Output Abstraction
pub trait DigitalOutput {
    fn set_high(&mut self);
    fn set_low(&mut self);
}

/// 数字输入抽象 / Digital Input Abstraction
pub trait DigitalInput {
    fn is_high(&self) -> bool;
    fn is_low(&self) -> bool {
        !self.is_high()
    }
}

/// I2C 抽象（极简）/ I2C Abstraction (minimal)
pub trait I2cBus {
    fn write(&mut self, addr: u8, bytes: &[u8]) -> Result<(), &'static str>;
    fn read(&mut self, addr: u8, buf: &mut [u8]) -> Result<(), &'static str>;
}

/// SPI 抽象（极简）/ SPI Abstraction (minimal)
pub trait SpiBus {
    fn transfer(&mut self, tx: &[u8], rx: &mut [u8]) -> Result<(), &'static str>;
}

/// 设备引导到上线状态 / Bring up device to Online
pub fn bring_up_device(dev: &mut EmbeddedDevice) {
    dev.status = DeviceStatus::Online;
}
