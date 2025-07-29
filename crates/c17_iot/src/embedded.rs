//! # IoT 嵌入式系统模块 / IoT Embedded System Module
//! 
//! 本模块实现了 IoT 嵌入式系统的核心功能。
//! This module implements the core functionality of IoT embedded systems.

use crate::types::*;
use std::collections::HashMap;

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
    pub fn new(id: String, device_type: DeviceType) -> Self {
        Self {
            id,
            device_type,
            sensors: Vec::new(),
            actuators: Vec::new(),
            status: DeviceStatus::Offline,
        }
    }
    
    pub fn add_sensor(&mut self, sensor: Sensor) {
        self.sensors.push(sensor);
    }
    
    pub fn add_actuator(&mut self, actuator: Actuator) {
        self.actuators.push(actuator);
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