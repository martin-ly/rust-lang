//! OpenTelemetry配置模块

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// OpenTelemetry配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OpenTelemetryConfig {
    /// Jaeger追踪端点
    pub jaeger_endpoint: String,
    /// 服务名称
    pub service_name: String,
    /// 服务版本
    pub service_version: String,
    /// 是否启用追踪
    pub tracing_enabled: bool,
    /// 是否启用指标
    pub metrics_enabled: bool,
    /// 是否启用日志
    pub logging_enabled: bool,
    /// 采样率 (0.0 - 1.0)
    pub sampling_ratio: f64,
    /// 额外的资源属性
    pub resource_attributes: HashMap<String, String>,
}

impl Default for OpenTelemetryConfig {
    fn default() -> Self {
        let mut resource_attributes = HashMap::new();
        resource_attributes.insert("deployment.environment".to_string(), "development".to_string());
        resource_attributes.insert("service.instance.id".to_string(), "1".to_string());
        
        Self {
            jaeger_endpoint: "http://localhost:14268/api/traces".to_string(),
            service_name: "microservice".to_string(),
            service_version: "1.0.0".to_string(),
            tracing_enabled: true,
            metrics_enabled: true,
            logging_enabled: true,
            sampling_ratio: 1.0,
            resource_attributes,
        }
    }
}

/// 创建默认的OpenTelemetry配置
pub fn default_config() -> OpenTelemetryConfig {
    OpenTelemetryConfig::default()
}

/// 创建自定义的OpenTelemetry配置
pub fn custom_config(
    service_name: String,
    service_version: String,
    jaeger_endpoint: String,
) -> OpenTelemetryConfig {
    OpenTelemetryConfig {
        service_name,
        service_version,
        jaeger_endpoint,
        ..Default::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_default_config() {
        let config = OpenTelemetryConfig::default();
        assert_eq!(config.service_name, "microservice");
        assert_eq!(config.service_version, "1.0.0");
        assert!(config.tracing_enabled);
        assert!(config.metrics_enabled);
        assert!(config.logging_enabled);
    }
    
    #[test]
    fn test_custom_config() {
        let config = custom_config(
            "my-service".to_string(),
            "2.0.0".to_string(),
            "http://jaeger:14268/api/traces".to_string(),
        );
        
        assert_eq!(config.service_name, "my-service");
        assert_eq!(config.service_version, "2.0.0");
        assert_eq!(config.jaeger_endpoint, "http://jaeger:14268/api/traces");
    }
}
