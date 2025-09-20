//! # IoT 电源管理模块 / IoT Power Management Module
//!
//! 本模块实现了 IoT 设备的电源管理功能。
//! This module implements power management functionality for IoT devices.

// use crate::types::*;
// use std::collections::HashMap;

/// IoT 电源管理器 / IoT Power Manager
pub struct PowerManager {
    battery_level: f64,
    power_mode: PowerMode,
    consumption_history: Vec<PowerConsumption>,
}

impl Default for PowerManager {
    fn default() -> Self {
        Self::new()
    }
}

impl PowerManager {
    pub fn new() -> Self {
        Self {
            battery_level: 100.0,
            power_mode: PowerMode::Normal,
            consumption_history: Vec::new(),
        }
    }

    pub fn get_battery_level(&self) -> f64 {
        self.battery_level
    }

    pub fn set_power_mode(&mut self, mode: PowerMode) {
        self.power_mode = mode;
    }

    /// 记录一次功耗样本 / Record a power consumption sample
    pub fn record_consumption(&mut self, timestamp: u64, consumption: f64) {
        self.consumption_history.push(PowerConsumption {
            timestamp,
            consumption,
        });
        // 简化：按消耗线性降低电量
        if consumption > 0.0 {
            let delta = (consumption / 1000.0).min(self.battery_level);
            self.battery_level = (self.battery_level - delta).max(0.0);
        }
    }

    /// 估算切换到某模式的单位时间功耗 / Estimate power for a mode per unit time
    pub fn estimate_mode_consumption(&self, mode: PowerMode) -> f64 {
        match mode {
            PowerMode::Normal => 100.0,
            PowerMode::LowPower => 20.0,
            PowerMode::Sleep => 2.0,
            PowerMode::DeepSleep => 0.2,
        }
    }
}

/// 电源模式 / Power Mode
#[derive(Debug, Clone)]
pub enum PowerMode {
    Normal,
    LowPower,
    Sleep,
    DeepSleep,
}

/// 电源消耗记录 / Power Consumption Record
#[derive(Debug, Clone)]
pub struct PowerConsumption {
    pub timestamp: u64,
    pub consumption: f64,
}
