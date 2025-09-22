//! 配置模式定义
//! 
//! 定义系统配置的结构和验证规则

use super::{ConfigItem, ConfigValue};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 配置模式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConfigSchema {
    pub name: String,
    pub version: String,
    pub description: Option<String>,
    pub items: HashMap<String, ConfigItem>,
}

impl ConfigSchema {
    /// 创建新的配置模式
    pub fn new(name: String, version: String) -> Self {
        Self {
            name,
            version,
            description: None,
            items: HashMap::new(),
        }
    }

    /// 添加配置项
    pub fn add_item(mut self, item: ConfigItem) -> Self {
        self.items.insert(item.key.clone(), item);
        self
    }

    /// 获取配置项
    pub fn get_item(&self, key: &str) -> Option<&ConfigItem> {
        self.items.get(key)
    }

    /// 验证配置值
    pub fn validate(&self, configs: &HashMap<String, ConfigValue>) -> Result<(), String> {
        for (key, item) in &self.items {
            if item.required && !configs.contains_key(key) {
                return Err(format!("必需配置项 '{}' 未设置", key));
            }
        }
        Ok(())
    }
}

/// 服务器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
    pub workers: usize,
    pub max_connections: usize,
    pub timeout_seconds: u64,
}

/// 数据库配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DatabaseConfig {
    pub host: String,
    pub port: u16,
    pub name: String,
    pub username: String,
    pub password: String,
    pub max_connections: usize,
    pub connection_timeout: u64,
}

/// 缓存配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheConfig {
    pub default_ttl: u64,
    pub max_size: usize,
    pub cleanup_interval: u64,
}

/// 存储配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageConfig {
    pub default_backend: String,
    pub local: LocalStorageConfig,
    pub s3: Option<S3StorageConfig>,
    pub gcs: Option<GCSStorageConfig>,
    pub azure: Option<AzureStorageConfig>,
}

/// 本地存储配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LocalStorageConfig {
    pub base_path: String,
    pub max_file_size: u64,
}

/// S3存储配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct S3StorageConfig {
    pub bucket: String,
    pub region: String,
    pub access_key: String,
    pub secret_key: String,
    pub endpoint: Option<String>,
}

/// GCS存储配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct GCSStorageConfig {
    pub bucket: String,
    pub project_id: String,
    pub credentials_path: Option<String>,
}

/// Azure存储配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AzureStorageConfig {
    pub account_name: String,
    pub account_key: String,
    pub container: String,
}

/// 认证配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuthConfig {
    pub jwt_secret: String,
    pub jwt_expiry: u64,
    pub refresh_token_expiry: u64,
    pub password_min_length: usize,
    pub max_login_attempts: usize,
    pub lockout_duration: u64,
}

/// 日志配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LoggingConfig {
    pub level: String,
    pub format: String,
    pub file_path: Option<String>,
    pub max_file_size: u64,
    pub max_files: usize,
}

/// 应用配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AppConfig {
    pub server: ServerConfig,
    pub database: DatabaseConfig,
    pub cache: CacheConfig,
    pub storage: StorageConfig,
    pub auth: AuthConfig,
    pub logging: LoggingConfig,
}

impl AppConfig {
    /// 创建默认配置
    pub fn default() -> Self {
        Self {
            server: ServerConfig {
                host: "0.0.0.0".to_string(),
                port: 8080,
                workers: 4,
                max_connections: 1000,
                timeout_seconds: 30,
            },
            database: DatabaseConfig {
                host: "localhost".to_string(),
                port: 5432,
                name: "c19_ai".to_string(),
                username: "postgres".to_string(),
                password: "".to_string(),
                max_connections: 20,
                connection_timeout: 10,
            },
            cache: CacheConfig {
                default_ttl: 3600,
                max_size: 1000,
                cleanup_interval: 300,
            },
            storage: StorageConfig {
                default_backend: "local".to_string(),
                local: LocalStorageConfig {
                    base_path: "/tmp/c19_ai".to_string(),
                    max_file_size: 100 * 1024 * 1024, // 100MB
                },
                s3: None,
                gcs: None,
                azure: None,
            },
            auth: AuthConfig {
                jwt_secret: "your-secret-key".to_string(),
                jwt_expiry: 86400, // 24 hours
                refresh_token_expiry: 604800, // 7 days
                password_min_length: 8,
                max_login_attempts: 5,
                lockout_duration: 300, // 5 minutes
            },
            logging: LoggingConfig {
                level: "info".to_string(),
                format: "json".to_string(),
                file_path: None,
                max_file_size: 100 * 1024 * 1024, // 100MB
                max_files: 10,
            },
        }
    }
}

impl Default for AppConfig {
    fn default() -> Self {
        Self::default()
    }
}
