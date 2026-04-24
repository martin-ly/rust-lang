//! # 练习 4: Default 特质
//!
//! **难度**: Easy  
//! **考点**: Default trait、struct update syntax
//!
//! ## 题目描述
//!
//! 为自定义配置结构体实现 Default 特质，
//! 并提供使用默认值创建实例的方法。

/// 服务器配置
#[derive(Debug, Clone, PartialEq)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub timeout_ms: u64,
    pub max_connections: usize,
    pub enable_logging: bool,
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            host: String::from("127.0.0.1"),
            port: 8080,
            timeout_ms: 30000,
            max_connections: 100,
            enable_logging: true,
        }
    }
}

impl ServerConfig {
    /// 使用默认配置，但指定端口
    pub fn with_port(port: u16) -> Self {
        Self {
            port,
            ..Default::default()
        }
    }

    /// 创建生产环境配置
    pub fn production() -> Self {
        Self {
            host: String::from("0.0.0.0"),
            port: 443,
            timeout_ms: 60000,
            max_connections: 10000,
            enable_logging: true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = ServerConfig::default();
        assert_eq!(config.host, "127.0.0.1");
        assert_eq!(config.port, 8080);
        assert_eq!(config.timeout_ms, 30000);
    }

    #[test]
    fn test_with_port() {
        let config = ServerConfig::with_port(3000);
        assert_eq!(config.port, 3000);
        assert_eq!(config.host, "127.0.0.1");
        assert!(config.enable_logging);
    }

    #[test]
    fn test_production_config() {
        let config = ServerConfig::production();
        assert_eq!(config.host, "0.0.0.0");
        assert_eq!(config.port, 443);
        assert_eq!(config.max_connections, 10000);
    }
}
