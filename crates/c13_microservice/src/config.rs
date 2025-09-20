//! 配置管理模块
//!
//! 提供统一的配置管理，支持多种配置源和环境变量。

use serde::{Deserialize, Serialize};
// use std::collections::HashMap;
use crate::error::{Error, Result};
use std::path::Path;

/// 微服务配置结构
#[derive(Debug, Clone, Serialize, Deserialize)]
#[derive(Default)]
pub struct Config {
    /// 服务配置
    pub service: ServiceConfig,
    /// 数据库配置
    pub database: DatabaseConfig,
    /// 日志配置
    pub logging: LoggingConfig,
    /// 监控配置
    pub monitoring: MonitoringConfig,
    /// 安全配置
    pub security: SecurityConfig,
    /// 服务网格配置
    pub service_mesh: ServiceMeshConfig,
    /// 消息队列配置
    pub messaging: MessagingConfig,
    /// Kubernetes配置
    pub kubernetes: KubernetesConfig,
}

/// 服务配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceConfig {
    /// 服务名称
    pub name: String,
    /// 服务版本
    pub version: String,
    /// 监听地址
    pub host: String,
    /// 监听端口
    pub port: u16,
    /// 环境
    pub environment: String,
    /// 健康检查路径
    pub health_check_path: String,
    /// 优雅关闭超时时间（秒）
    pub shutdown_timeout: u64,
}

/// 数据库配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseConfig {
    /// 数据库URL
    pub url: String,
    /// 最大连接数
    pub max_connections: u32,
    /// 连接超时时间（秒）
    pub connection_timeout: u64,
    /// 空闲超时时间（秒）
    pub idle_timeout: u64,
    /// 是否启用连接池
    pub enable_pool: bool,
}

/// 日志配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoggingConfig {
    /// 日志级别
    pub level: String,
    /// 日志格式 (json, pretty)
    pub format: String,
    /// 是否启用结构化日志
    pub structured: bool,
    /// 日志输出目标 (stdout, stderr, file)
    pub output: String,
    /// 日志文件路径（当output为file时）
    pub file_path: Option<String>,
}

/// 监控配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MonitoringConfig {
    /// 是否启用指标收集
    pub enable_metrics: bool,
    /// 指标端口
    pub metrics_port: u16,
    /// 指标路径
    pub metrics_path: String,
    /// 是否启用追踪
    pub enable_tracing: bool,
    /// Jaeger端点
    pub jaeger_endpoint: Option<String>,
    /// Prometheus端点
    pub prometheus_endpoint: Option<String>,
}

/// 安全配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityConfig {
    /// JWT密钥
    pub jwt_secret: String,
    /// JWT过期时间（秒）
    pub jwt_expiry: u64,
    /// 是否启用HTTPS
    pub enable_https: bool,
    /// SSL证书路径
    pub ssl_cert_path: Option<String>,
    /// SSL私钥路径
    pub ssl_key_path: Option<String>,
    /// CORS配置
    pub cors: CorsConfig,
}

/// CORS配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CorsConfig {
    /// 允许的源
    pub allowed_origins: Vec<String>,
    /// 允许的方法
    pub allowed_methods: Vec<String>,
    /// 允许的头部
    pub allowed_headers: Vec<String>,
    /// 是否允许凭据
    pub allow_credentials: bool,
}

/// 服务网格配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServiceMeshConfig {
    /// 是否启用服务发现
    pub enable_discovery: bool,
    /// 服务发现类型 (consul, etcd, kubernetes)
    pub discovery_type: String,
    /// 服务发现端点
    pub discovery_endpoint: Option<String>,
    /// 是否启用负载均衡
    pub enable_load_balancer: bool,
    /// 负载均衡策略 (round_robin, least_connections, random)
    pub load_balancer_strategy: String,
    /// 是否启用熔断器
    pub enable_circuit_breaker: bool,
    /// 熔断器配置
    pub circuit_breaker: CircuitBreakerConfig,
}

/// 熔断器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CircuitBreakerConfig {
    /// 失败阈值
    pub failure_threshold: u32,
    /// 恢复超时时间（秒）
    pub recovery_timeout: u64,
    /// 半开状态最大请求数
    pub half_open_max_requests: u32,
}

/// 消息队列配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MessagingConfig {
    /// 消息队列类型 (rabbitmq, kafka, redis)
    pub queue_type: String,
    /// 消息队列URL
    pub queue_url: String,
    /// 是否启用消息确认
    pub enable_ack: bool,
    /// 消息重试次数
    pub retry_count: u32,
    /// 消息过期时间（秒）
    pub message_ttl: u64,
}

/// Kubernetes配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct KubernetesConfig {
    /// 是否在Kubernetes环境中运行
    pub in_cluster: bool,
    /// Kubernetes API服务器地址
    pub api_server: Option<String>,
    /// 命名空间
    pub namespace: String,
    /// 服务账户令牌路径
    pub token_path: Option<String>,
    /// 是否启用自动扩缩容
    pub enable_autoscaling: bool,
}


impl Default for ServiceConfig {
    fn default() -> Self {
        Self {
            name: "microservice".to_string(),
            version: "1.0.0".to_string(),
            host: "0.0.0.0".to_string(),
            port: 3000,
            environment: "development".to_string(),
            health_check_path: "/health".to_string(),
            shutdown_timeout: 30,
        }
    }
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self {
            url: "postgresql://localhost/microservice".to_string(),
            max_connections: 10,
            connection_timeout: 30,
            idle_timeout: 600,
            enable_pool: true,
        }
    }
}

impl Default for LoggingConfig {
    fn default() -> Self {
        Self {
            level: "info".to_string(),
            format: "pretty".to_string(),
            structured: true,
            output: "stdout".to_string(),
            file_path: None,
        }
    }
}

impl Default for MonitoringConfig {
    fn default() -> Self {
        Self {
            enable_metrics: true,
            metrics_port: 9090,
            metrics_path: "/metrics".to_string(),
            enable_tracing: true,
            jaeger_endpoint: None,
            prometheus_endpoint: None,
        }
    }
}

impl Default for SecurityConfig {
    fn default() -> Self {
        Self {
            jwt_secret: "your-secret-key".to_string(),
            jwt_expiry: 3600,
            enable_https: false,
            ssl_cert_path: None,
            ssl_key_path: None,
            cors: CorsConfig::default(),
        }
    }
}

impl Default for CorsConfig {
    fn default() -> Self {
        Self {
            allowed_origins: vec!["*".to_string()],
            allowed_methods: vec![
                "GET".to_string(),
                "POST".to_string(),
                "PUT".to_string(),
                "DELETE".to_string(),
            ],
            allowed_headers: vec!["*".to_string()],
            allow_credentials: false,
        }
    }
}

impl Default for ServiceMeshConfig {
    fn default() -> Self {
        Self {
            enable_discovery: false,
            discovery_type: "consul".to_string(),
            discovery_endpoint: None,
            enable_load_balancer: false,
            load_balancer_strategy: "round_robin".to_string(),
            enable_circuit_breaker: false,
            circuit_breaker: CircuitBreakerConfig::default(),
        }
    }
}

impl Default for CircuitBreakerConfig {
    fn default() -> Self {
        Self {
            failure_threshold: 5,
            recovery_timeout: 60,
            half_open_max_requests: 3,
        }
    }
}

impl Default for MessagingConfig {
    fn default() -> Self {
        Self {
            queue_type: "rabbitmq".to_string(),
            queue_url: "amqp://localhost:5672".to_string(),
            enable_ack: true,
            retry_count: 3,
            message_ttl: 3600,
        }
    }
}

impl Default for KubernetesConfig {
    fn default() -> Self {
        Self {
            in_cluster: false,
            api_server: None,
            namespace: "default".to_string(),
            token_path: None,
            enable_autoscaling: false,
        }
    }
}

impl Config {
    /// 从文件加载配置
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self> {
        let content = std::fs::read_to_string(path)
            .map_err(|e| Error::config(format!("无法读取配置文件: {}", e)))?;

        let config: Config = toml::from_str(&content)
            .map_err(|e| Error::config(format!("无法解析配置文件: {}", e)))?;

        Ok(config)
    }

    /// 从环境变量加载配置
    pub fn from_env() -> Result<Self> {
        let mut config = Config::default();

        // 从环境变量覆盖配置
        if let Ok(name) = std::env::var("SERVICE_NAME") {
            config.service.name = name;
        }

        if let Ok(port) = std::env::var("SERVICE_PORT") {
            config.service.port = port
                .parse()
                .map_err(|e| Error::config(format!("无效的端口号: {}", e)))?;
        }

        if let Ok(host) = std::env::var("SERVICE_HOST") {
            config.service.host = host;
        }

        if let Ok(env) = std::env::var("ENVIRONMENT") {
            config.service.environment = env;
        }

        if let Ok(db_url) = std::env::var("DATABASE_URL") {
            config.database.url = db_url;
        }

        if let Ok(log_level) = std::env::var("LOG_LEVEL") {
            config.logging.level = log_level;
        }

        if let Ok(jwt_secret) = std::env::var("JWT_SECRET") {
            config.security.jwt_secret = jwt_secret;
        }

        Ok(config)
    }

    /// 验证配置
    pub fn validate(&self) -> Result<()> {
        if self.service.name.is_empty() {
            return Err(Error::config("服务名称不能为空"));
        }

        if self.service.port == 0 {
            return Err(Error::config("服务端口不能为0"));
        }

        if self.database.url.is_empty() {
            return Err(Error::config("数据库URL不能为空"));
        }

        if self.security.jwt_secret.is_empty() {
            return Err(Error::config("JWT密钥不能为空"));
        }

        Ok(())
    }

    /// 获取服务地址
    pub fn service_address(&self) -> String {
        format!("{}:{}", self.service.host, self.service.port)
    }

    /// 获取健康检查URL
    pub fn health_check_url(&self) -> String {
        format!(
            "http://{}{}",
            self.service_address(),
            self.service.health_check_path
        )
    }

    /// 获取指标URL
    pub fn metrics_url(&self) -> String {
        format!(
            "http://{}:{}{}",
            self.service.host, self.monitoring.metrics_port, self.monitoring.metrics_path
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = Config::default();
        assert_eq!(config.service.name, "microservice");
        assert_eq!(config.service.port, 3000);
        assert_eq!(config.database.url, "postgresql://localhost/microservice");
    }

    #[test]
    fn test_config_validation() {
        let mut config = Config::default();
        assert!(config.validate().is_ok());

        config.service.name = String::new();
        assert!(config.validate().is_err());
    }

    #[test]
    fn test_service_address() {
        let config = Config::default();
        assert_eq!(config.service_address(), "0.0.0.0:3000");
    }
}
