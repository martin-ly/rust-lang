//! # IoT 工具模块 / IoT Tools Module
//! 
//! 本模块提供了 IoT 相关的工具函数。
//! This module provides IoT-related utility functions.

// use crate::types::*;
// use std::collections::HashMap;

/// IoT 工具 / IoT Tools
pub struct IoTTools;

impl IoTTools {
    /// 生成设备ID / Generate device ID
    pub fn generate_device_id() -> String {
        format!("device_{}", uuid::Uuid::new_v4())
    }
    
    /// 验证设备ID / Validate device ID
    pub fn validate_device_id(id: &str) -> bool {
        id.starts_with("device_") && id.len() > 7
    }
    
    /// 计算数据包大小 / Calculate packet size
    pub fn calculate_packet_size(data: &[u8]) -> usize {
        data.len()
    }

    /// 度量导出到 stdout（可替换为 OTEL 导出）/ Metrics to stdout
    pub fn export_metric(name: &str, value: f64, labels: &[(&str, &str)]) {
        let mut label_str = String::new();
        for (k, v) in labels {
            if !label_str.is_empty() { label_str.push_str(","); }
            label_str.push_str(&format!("{}={}", k, v));
        }
        println!("metric name={} value={} labels={}", name, value, label_str);
    }

    /// 简单校验：payload 是否为 UTF-8 / Payload UTF-8 validation
    pub fn is_utf8(data: &[u8]) -> bool { std::str::from_utf8(data).is_ok() }
} 

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_device_id() {
        let id = IoTTools::generate_device_id();
        assert!(IoTTools::validate_device_id(&id));
    }

    #[test]
    fn test_is_utf8() {
        assert!(IoTTools::is_utf8(b"hello"));
        assert!(!IoTTools::is_utf8(&[0xFF, 0xFE]));
    }
}