//! 配置管理模块
//!
//! 提供统一的配置管理功能，支持多种配置源和格式

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::env;
use std::fs;
use std::path::Path;

#[cfg(feature = "config")]
use toml;

/// 应用配置结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppConfig {
    pub server: ServerConfig,
    pub database: DatabaseConfig,
    pub logging: LoggingConfig,
    pub features: FeatureFlags,
}

/// 服务器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub workers: Option<usize>,
    pub timeout: u64,
}

/// 数据库配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
    pub min_connections: u32,
    pub connection_timeout: u64,
}

/// 日志配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoggingConfig {
    pub level: String,
    pub format: String,
    pub output: String,
}

/// 功能开关
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FeatureFlags {
    pub enable_metrics: bool,
    pub enable_tracing: bool,
    pub enable_cors: bool,
    pub enable_compression: bool,
}

impl Default for AppConfig {
    fn default() -> Self {
        Self {
            server: ServerConfig {
                host: "127.0.0.1".to_string(),
                port: 8080,
                workers: None,
                timeout: 30,
            },
            database: DatabaseConfig {
                url: "postgresql://localhost/mydb".to_string(),
                max_connections: 10,
                min_connections: 1,
                connection_timeout: 30,
            },
            logging: LoggingConfig {
                level: "info".to_string(),
                format: "json".to_string(),
                output: "stdout".to_string(),
            },
            features: FeatureFlags {
                enable_metrics: true,
                enable_tracing: true,
                enable_cors: true,
                enable_compression: true,
            },
        }
    }
}

impl AppConfig {
    /// 从环境变量加载配置
    pub fn from_env() -> Result<Self, Box<dyn std::error::Error>> {
        let mut config = Self::default();

        // 从环境变量覆盖配置
        if let Ok(host) = env::var("SERVER_HOST") {
            config.server.host = host;
        }
        if let Ok(port) = env::var("SERVER_PORT") {
            config.server.port = port.parse()?;
        }
        if let Ok(url) = env::var("DATABASE_URL") {
            config.database.url = url;
        }
        if let Ok(level) = env::var("LOG_LEVEL") {
            config.logging.level = level;
        }

        Ok(config)
    }

    /// 从文件加载配置
    #[cfg(feature = "config")]
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn std::error::Error>> {
        let content = fs::read_to_string(path)?;
        let config: AppConfig = toml::from_str(&content)?;
        Ok(config)
    }

    /// 从文件加载配置（无toml依赖版本）
    #[cfg(not(feature = "config"))]
    pub fn from_file<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn std::error::Error>> {
        Err("TOML support not enabled. Please enable the 'config' feature.".into())
    }

    /// 从多个源合并配置
    pub fn from_sources(
        file_path: Option<&str>,
        env_prefix: Option<&str>,
    ) -> Result<Self, Box<dyn std::error::Error>> {
        let mut config = Self::default();

        // 从文件加载
        if let Some(path) = file_path {
            if Path::new(path).exists() {
                let file_config = Self::from_file(path)?;
                config = file_config;
            }
        }

        // 从环境变量覆盖
        if let Some(prefix) = env_prefix {
            config.override_from_env(prefix)?;
        }

        Ok(config)
    }

    /// 从环境变量覆盖配置
    fn override_from_env(&mut self, prefix: &str) -> Result<(), Box<dyn std::error::Error>> {
        let env_vars: HashMap<String, String> = env::vars()
            .filter(|(key, _)| key.starts_with(prefix))
            .collect();

        for (key, value) in env_vars {
            let config_key = key.trim_start_matches(prefix).trim_start_matches('_');
            self.set_config_value(config_key, &value)?;
        }

        Ok(())
    }

    /// 设置配置值
    fn set_config_value(
        &mut self,
        key: &str,
        value: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        match key.to_lowercase().as_str() {
            "server_host" => self.server.host = value.to_string(),
            "server_port" => self.server.port = value.parse()?,
            "server_workers" => self.server.workers = Some(value.parse()?),
            "server_timeout" => self.server.timeout = value.parse()?,
            "database_url" => self.database.url = value.to_string(),
            "database_max_connections" => self.database.max_connections = value.parse()?,
            "database_min_connections" => self.database.min_connections = value.parse()?,
            "database_connection_timeout" => self.database.connection_timeout = value.parse()?,
            "log_level" => self.logging.level = value.to_string(),
            "log_format" => self.logging.format = value.to_string(),
            "log_output" => self.logging.output = value.to_string(),
            "enable_metrics" => self.features.enable_metrics = value.parse()?,
            "enable_tracing" => self.features.enable_tracing = value.parse()?,
            "enable_cors" => self.features.enable_cors = value.parse()?,
            "enable_compression" => self.features.enable_compression = value.parse()?,
            _ => {} // 忽略未知配置项
        }
        Ok(())
    }

    /// 验证配置
    pub fn validate(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();

        if self.server.port == 0 {
            errors.push("服务器端口不能为0".to_string());
        }

        if self.server.timeout == 0 {
            errors.push("服务器超时时间不能为0".to_string());
        }

        if self.database.max_connections < self.database.min_connections {
            errors.push("数据库最大连接数不能小于最小连接数".to_string());
        }

        if !["debug", "info", "warn", "error"].contains(&self.logging.level.as_str()) {
            errors.push("无效的日志级别".to_string());
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// 保存配置到文件
    #[cfg(feature = "config")]
    pub fn save_to_file<P: AsRef<Path>>(&self, path: P) -> Result<(), Box<dyn std::error::Error>> {
        let content = toml::to_string_pretty(self)?;
        fs::write(path, content)?;
        Ok(())
    }

    /// 保存配置到文件（无toml依赖版本）
    #[cfg(not(feature = "config"))]
    pub fn save_to_file<P: AsRef<Path>>(&self, _path: P) -> Result<(), Box<dyn std::error::Error>> {
        Err("TOML support not enabled. Please enable the 'config' feature.".into())
    }
}

/// 配置构建器
pub struct ConfigBuilder {
    config: AppConfig,
}

impl ConfigBuilder {
    pub fn new() -> Self {
        Self {
            config: AppConfig::default(),
        }
    }

    pub fn server_host(mut self, host: String) -> Self {
        self.config.server.host = host;
        self
    }

    pub fn server_port(mut self, port: u16) -> Self {
        self.config.server.port = port;
        self
    }

    pub fn database_url(mut self, url: String) -> Self {
        self.config.database.url = url;
        self
    }

    pub fn log_level(mut self, level: String) -> Self {
        self.config.logging.level = level;
        self
    }

    pub fn enable_feature(mut self, feature: &str, enabled: bool) -> Self {
        match feature {
            "metrics" => self.config.features.enable_metrics = enabled,
            "tracing" => self.config.features.enable_tracing = enabled,
            "cors" => self.config.features.enable_cors = enabled,
            "compression" => self.config.features.enable_compression = enabled,
            _ => {}
        }
        self
    }

    pub fn build(self) -> AppConfig {
        self.config
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::NamedTempFile;

    #[test]
    fn test_default_config() {
        let config = AppConfig::default();
        assert_eq!(config.server.host, "127.0.0.1");
        assert_eq!(config.server.port, 8080);
        assert_eq!(config.database.url, "postgresql://localhost/mydb");
    }

    #[test]
    fn test_config_validation() {
        let mut config = AppConfig::default();
        assert!(config.validate().is_ok());

        config.server.port = 0;
        let result = config.validate();
        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .iter()
                .any(|e| e.contains("端口不能为0"))
        );
    }

    #[test]
    fn test_config_builder() {
        let config = ConfigBuilder::new()
            .server_host("0.0.0.0".to_string())
            .server_port(3000)
            .database_url("postgresql://test".to_string())
            .log_level("debug".to_string())
            .enable_feature("metrics", false)
            .build();

        assert_eq!(config.server.host, "0.0.0.0");
        assert_eq!(config.server.port, 3000);
        assert_eq!(config.database.url, "postgresql://test");
        assert_eq!(config.logging.level, "debug");
        assert!(!config.features.enable_metrics);
    }

    #[test]
    #[cfg(feature = "config")]
    fn test_config_file_operations() -> Result<(), Box<dyn std::error::Error>> {
        let config = AppConfig::default();
        let temp_file = NamedTempFile::new()?;
        let file_path = temp_file.path();

        // 保存配置
        config.save_to_file(file_path)?;

        // 加载配置
        let loaded_config = AppConfig::from_file(file_path)?;
        assert_eq!(config.server.host, loaded_config.server.host);
        assert_eq!(config.server.port, loaded_config.server.port);

        Ok(())
    }
}
