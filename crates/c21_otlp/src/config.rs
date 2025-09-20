//! # OTLP配置模块
//! 
//! 提供OTLP客户端的配置管理，支持Rust 1.90的配置特性。

use serde::{Deserialize, Serialize};
use std::time::Duration;
use std::collections::HashMap;
use crate::error::{Result, ConfigurationError};

/// OTLP传输协议类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TransportProtocol {
    /// gRPC协议
    Grpc,
    /// HTTP/JSON协议
    Http,
    /// HTTP/Protobuf协议
    HttpProtobuf,
}

impl Default for TransportProtocol {
    fn default() -> Self {
        Self::Grpc
    }
}

impl std::fmt::Display for TransportProtocol {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TransportProtocol::Grpc => write!(f, "grpc"),
            TransportProtocol::Http => write!(f, "http"),
            TransportProtocol::HttpProtobuf => write!(f, "http/protobuf"),
        }
    }
}

/// OTLP压缩算法
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Compression {
    /// 无压缩
    None,
    /// Gzip压缩
    Gzip,
    /// Brotli压缩
    Brotli,
    /// Zstd压缩
    Zstd,
}

impl Default for Compression {
    fn default() -> Self {
        Self::None
    }
}

/// 批处理配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchConfig {
    /// 批处理大小
    pub max_export_batch_size: usize,
    /// 批处理超时时间
    pub export_timeout: Duration,
    /// 最大队列大小
    pub max_queue_size: usize,
    /// 调度间隔
    pub scheduled_delay: Duration,
}

impl Default for BatchConfig {
    fn default() -> Self {
        Self {
            max_export_batch_size: 512,
            export_timeout: Duration::from_secs(30),
            max_queue_size: 2048,
            scheduled_delay: Duration::from_millis(5000),
        }
    }
}

/// 重试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryConfig {
    /// 最大重试次数
    pub max_retries: usize,
    /// 初始重试延迟
    pub initial_retry_delay: Duration,
    /// 最大重试延迟
    pub max_retry_delay: Duration,
    /// 重试延迟倍数
    pub retry_delay_multiplier: f64,
    /// 随机化重试延迟
    pub randomize_retry_delay: bool,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_retries: 5,
            initial_retry_delay: Duration::from_millis(1000),
            max_retry_delay: Duration::from_secs(30),
            retry_delay_multiplier: 2.0,
            randomize_retry_delay: true,
        }
    }
}

/// TLS配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TlsConfig {
    /// 是否启用TLS
    pub enabled: bool,
    /// 证书文件路径
    pub cert_file: Option<String>,
    /// 私钥文件路径
    pub key_file: Option<String>,
    /// CA证书文件路径
    pub ca_file: Option<String>,
    /// 是否验证服务器证书
    pub verify_server_cert: bool,
    /// 是否验证服务器主机名
    pub verify_server_hostname: bool,
}

impl Default for TlsConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            cert_file: None,
            key_file: None,
            ca_file: None,
            verify_server_cert: true,
            verify_server_hostname: true,
        }
    }
}

/// 认证配置
#[derive(Debug, Clone, Serialize, Deserialize)]
#[derive(Default)]
pub struct AuthConfig {
    /// API密钥
    pub api_key: Option<String>,
    /// Bearer令牌
    pub bearer_token: Option<String>,
    /// 自定义头部
    pub custom_headers: HashMap<String, String>,
}


/// OTLP客户端配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OtlpConfig {
    /// 服务端点
    pub endpoint: String,
    /// 传输协议
    pub protocol: TransportProtocol,
    /// 压缩算法
    pub compression: Compression,
    /// 连接超时
    pub connect_timeout: Duration,
    /// 请求超时
    pub request_timeout: Duration,
    /// 批处理配置
    pub batch_config: BatchConfig,
    /// 重试配置
    pub retry_config: RetryConfig,
    /// TLS配置
    pub tls_config: TlsConfig,
    /// 认证配置
    pub auth_config: AuthConfig,
    /// 服务名称
    pub service_name: String,
    /// 服务版本
    pub service_version: String,
    /// 资源属性
    pub resource_attributes: HashMap<String, String>,
    /// 是否启用指标
    pub enable_metrics: bool,
    /// 是否启用追踪
    pub enable_tracing: bool,
    /// 是否启用日志
    pub enable_logs: bool,
    /// 采样率 (0.0 - 1.0)
    pub sampling_ratio: f64,
    /// 是否启用调试模式
    pub debug: bool,
}

impl Default for OtlpConfig {
    fn default() -> Self {
        Self {
            endpoint: "http://localhost:4317".to_string(),
            protocol: TransportProtocol::Grpc,
            compression: Compression::None,
            connect_timeout: Duration::from_secs(10),
            request_timeout: Duration::from_secs(30),
            batch_config: BatchConfig::default(),
            retry_config: RetryConfig::default(),
            tls_config: TlsConfig::default(),
            auth_config: AuthConfig::default(),
            service_name: "unknown-service".to_string(),
            service_version: "unknown".to_string(),
            resource_attributes: HashMap::new(),
            enable_metrics: true,
            enable_tracing: true,
            enable_logs: true,
            sampling_ratio: 1.0,
            debug: false,
        }
    }
}

impl OtlpConfig {
    /// 创建新的配置实例
    pub fn new() -> Self {
        Self::default()
    }

    /// 设置服务端点
    pub fn with_endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.endpoint = endpoint.into();
        self
    }

    /// 设置传输协议
    pub fn with_protocol(mut self, protocol: TransportProtocol) -> Self {
        self.protocol = protocol;
        self
    }

    /// 设置压缩算法
    pub fn with_compression(mut self, compression: Compression) -> Self {
        self.compression = compression;
        self
    }

    /// 设置连接超时
    pub fn with_connect_timeout(mut self, timeout: Duration) -> Self {
        self.connect_timeout = timeout;
        self
    }

    /// 设置请求超时
    pub fn with_request_timeout(mut self, timeout: Duration) -> Self {
        self.request_timeout = timeout;
        self
    }

    /// 设置服务信息
    pub fn with_service(mut self, name: impl Into<String>, version: impl Into<String>) -> Self {
        self.service_name = name.into();
        self.service_version = version.into();
        self
    }

    /// 添加资源属性
    pub fn with_resource_attribute(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.resource_attributes.insert(key.into(), value.into());
        self
    }

    /// 设置采样率
    pub fn with_sampling_ratio(mut self, ratio: f64) -> Self {
        self.sampling_ratio = ratio.max(0.0).min(1.0);
        self
    }

    /// 启用调试模式
    pub fn with_debug(mut self, debug: bool) -> Self {
        self.debug = debug;
        self
    }

    /// 设置API密钥
    pub fn with_api_key(mut self, api_key: impl Into<String>) -> Self {
        self.auth_config.api_key = Some(api_key.into());
        self
    }

    /// 设置Bearer令牌
    pub fn with_bearer_token(mut self, token: impl Into<String>) -> Self {
        self.auth_config.bearer_token = Some(token.into());
        self
    }

    /// 添加自定义头部
    pub fn with_custom_header(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.auth_config.custom_headers.insert(key.into(), value.into());
        self
    }

    /// 启用TLS
    pub fn with_tls(mut self, enabled: bool) -> Self {
        self.tls_config.enabled = enabled;
        self
    }

    /// 设置批处理配置
    pub fn with_batch_config(mut self, config: BatchConfig) -> Self {
        self.batch_config = config;
        self
    }

    /// 设置重试配置
    pub fn with_retry_config(mut self, config: RetryConfig) -> Self {
        self.retry_config = config;
        self
    }

    /// 验证配置
    pub fn validate(&self) -> Result<()> {
        // 验证端点URL
        if self.endpoint.is_empty() {
            return Err(ConfigurationError::InvalidEndpoint {
                url: "empty endpoint".to_string(),
            }.into());
        }

        // 验证超时配置
        if self.connect_timeout.is_zero() {
            return Err(ConfigurationError::InvalidTimeout {
                timeout: self.connect_timeout,
            }.into());
        }

        if self.request_timeout.is_zero() {
            return Err(ConfigurationError::InvalidTimeout {
                timeout: self.request_timeout,
            }.into());
        }

        // 验证批处理配置
        if self.batch_config.max_export_batch_size == 0 {
            return Err(ConfigurationError::InvalidBatchConfig {
                message: "max_export_batch_size must be greater than 0".to_string(),
            }.into());
        }

        if self.batch_config.max_queue_size == 0 {
            return Err(ConfigurationError::InvalidBatchConfig {
                message: "max_queue_size must be greater than 0".to_string(),
            }.into());
        }

        // 验证采样率
        if self.sampling_ratio < 0.0 || self.sampling_ratio > 1.0 {
            return Err(ConfigurationError::ValueOutOfRange {
                field: "sampling_ratio".to_string(),
                value: self.sampling_ratio,
                min: 0.0,
                max: 1.0,
            }.into());
        }

        // 验证重试配置
        if self.retry_config.retry_delay_multiplier <= 1.0 {
            return Err(ConfigurationError::ValueOutOfRange {
                field: "retry_delay_multiplier".to_string(),
                value: self.retry_config.retry_delay_multiplier,
                min: 1.0,
                max: f64::MAX,
            }.into());
        }

        Ok(())
    }

    /// 获取gRPC端点
    pub fn grpc_endpoint(&self) -> String {
        match self.protocol {
            TransportProtocol::Grpc => self.endpoint.clone(),
            TransportProtocol::Http => format!("{}/v1/traces", self.endpoint),
            TransportProtocol::HttpProtobuf => format!("{}/v1/traces", self.endpoint),
        }
    }

    /// 获取HTTP端点
    pub fn http_endpoint(&self) -> String {
        match self.protocol {
            TransportProtocol::Grpc => format!("{}/v1/traces", self.endpoint),
            TransportProtocol::Http => format!("{}/v1/traces", self.endpoint),
            TransportProtocol::HttpProtobuf => format!("{}/v1/traces", self.endpoint),
        }
    }

    /// 是否启用压缩
    pub fn is_compression_enabled(&self) -> bool {
        !matches!(self.compression, Compression::None)
    }

    /// 获取压缩算法名称
    pub fn compression_name(&self) -> &'static str {
        match self.compression {
            Compression::None => "identity",
            Compression::Gzip => "gzip",
            Compression::Brotli => "br",
            Compression::Zstd => "zstd",
        }
    }
}

/// 配置构建器模式
pub struct OtlpConfigBuilder {
    config: OtlpConfig,
}

impl OtlpConfigBuilder {
    /// 创建新的配置构建器
    pub fn new() -> Self {
        Self {
            config: OtlpConfig::default(),
        }
    }

    /// 设置服务端点
    pub fn endpoint(mut self, endpoint: impl Into<String>) -> Self {
        self.config.endpoint = endpoint.into();
        self
    }

    /// 设置传输协议
    pub fn protocol(mut self, protocol: TransportProtocol) -> Self {
        self.config.protocol = protocol;
        self
    }

    /// 设置服务信息
    pub fn service(mut self, name: impl Into<String>, version: impl Into<String>) -> Self {
        self.config.service_name = name.into();
        self.config.service_version = version.into();
        self
    }

    /// 构建配置
    pub fn build(self) -> Result<OtlpConfig> {
        self.config.validate()?;
        Ok(self.config)
    }
}

impl Default for OtlpConfigBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    #[test]
    fn test_default_config() {
        let config = OtlpConfig::default();
        assert_eq!(config.endpoint, "http://localhost:4317");
        assert_eq!(config.protocol, TransportProtocol::Grpc);
        assert_eq!(config.service_name, "unknown-service");
        assert!(config.enable_metrics);
        assert!(config.enable_tracing);
        assert!(config.enable_logs);
    }

    #[test]
    fn test_config_validation() {
        let config = OtlpConfig::new()
            .with_endpoint("http://localhost:4317")
            .with_connect_timeout(Duration::from_secs(5))
            .with_request_timeout(Duration::from_secs(10));
        
        assert!(config.validate().is_ok());
    }

    #[test]
    fn test_invalid_config() {
        let config = OtlpConfig::new()
            .with_endpoint("")
            .with_connect_timeout(Duration::from_secs(0));
        
        assert!(config.validate().is_err());
    }

    #[test]
    fn test_config_builder() {
        let config = OtlpConfigBuilder::new()
            .endpoint("http://localhost:4317")
            .protocol(TransportProtocol::Http)
            .service("test-service", "1.0.0")
            .build()
            .unwrap();
        
        assert_eq!(config.endpoint, "http://localhost:4317");
        assert_eq!(config.protocol, TransportProtocol::Http);
        assert_eq!(config.service_name, "test-service");
        assert_eq!(config.service_version, "1.0.0");
    }

    #[test]
    fn test_endpoint_generation() {
        let grpc_config = OtlpConfig::new().with_protocol(TransportProtocol::Grpc);
        assert_eq!(grpc_config.grpc_endpoint(), "http://localhost:4317");
        
        let http_config = OtlpConfig::new().with_protocol(TransportProtocol::Http);
        assert_eq!(http_config.http_endpoint(), "http://localhost:4317/v1/traces");
    }
}
