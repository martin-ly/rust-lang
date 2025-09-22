//! 配置管理器
//! 
//! 负责配置的加载、缓存和访问

use super::{ConfigError, ConfigItem, ConfigValue, ConfigSource};
use crate::database::DatabaseManager;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;
use tokio::sync::RwLock;

/// 配置管理器
#[derive(Debug)]
pub struct ConfigManager {
    configs: Arc<RwLock<HashMap<String, ConfigValue>>>,
    sources: Vec<ConfigSource>,
    db_manager: Option<Arc<DatabaseManager>>,
}

impl ConfigManager {
    /// 创建新的配置管理器
    pub fn new() -> Self {
        Self {
            configs: Arc::new(RwLock::new(HashMap::new())),
            sources: vec![
                ConfigSource::Environment,
                ConfigSource::File("config.json".to_string()),
                ConfigSource::Database,
                ConfigSource::Default,
            ],
            db_manager: None,
        }
    }

    /// 设置数据库管理器
    pub fn with_database(mut self, db_manager: Arc<DatabaseManager>) -> Self {
        self.db_manager = Some(db_manager);
        self
    }

    /// 添加配置源
    pub fn add_source(mut self, source: ConfigSource) -> Self {
        self.sources.push(source);
        self
    }

    /// 加载所有配置
    pub async fn load_all(&self) -> Result<(), ConfigError> {
        let mut configs = self.configs.write().await;
        
        // 按优先级顺序加载配置
        for source in &self.sources {
            match source {
                ConfigSource::Environment => {
                    self.load_from_environment(&mut configs).await?;
                }
                ConfigSource::File(path) => {
                    self.load_from_file(path, &mut configs).await?;
                }
                ConfigSource::Database => {
                    if let Some(db_manager) = &self.db_manager {
                        self.load_from_database(db_manager, &mut configs).await?;
                    }
                }
                ConfigSource::CommandLine => {
                    // TODO: 实现命令行参数加载
                }
                ConfigSource::Default => {
                    self.load_defaults(&mut configs).await?;
                }
            }
        }
        
        Ok(())
    }

    /// 从环境变量加载配置
    async fn load_from_environment(
        &self,
        configs: &mut HashMap<String, ConfigValue>,
    ) -> Result<(), ConfigError> {
        for (key, value) in std::env::vars() {
            if key.starts_with("C19_AI_") {
                let config_key = key.strip_prefix("C19_AI_").unwrap().to_lowercase();
                let config_value = self.parse_env_value(&value)?;
                configs.insert(config_key, config_value);
            }
        }
        Ok(())
    }

    /// 从文件加载配置
    async fn load_from_file(
        &self,
        path: &str,
        configs: &mut HashMap<String, ConfigValue>,
    ) -> Result<(), ConfigError> {
        if !Path::new(path).exists() {
            return Ok(()); // 文件不存在时跳过
        }

        let content = tokio::fs::read_to_string(path).await
            .map_err(|_| ConfigError::FileLoadError { path: path.to_string() })?;
        
        let file_configs: HashMap<String, ConfigValue> = serde_json::from_str(&content)
            .map_err(|e| ConfigError::ParseError { message: e.to_string() })?;
        
        configs.extend(file_configs);
        Ok(())
    }

    /// 从数据库加载配置
    async fn load_from_database(
        &self,
        _db_manager: &DatabaseManager,
        _configs: &mut HashMap<String, ConfigValue>,
    ) -> Result<(), ConfigError> {
        // TODO: 实现数据库配置加载
        // 这里需要查询 system_config 表
        Ok(())
    }

    /// 加载默认配置
    async fn load_defaults(
        &self,
        configs: &mut HashMap<String, ConfigValue>,
    ) -> Result<(), ConfigError> {
        let defaults = self.get_default_configs();
        for (key, value) in defaults {
            configs.entry(key).or_insert(value);
        }
        Ok(())
    }

    /// 获取默认配置
    fn get_default_configs(&self) -> HashMap<String, ConfigValue> {
        let mut configs = HashMap::new();
        
        configs.insert("server.host".to_string(), ConfigValue::String("0.0.0.0".to_string()));
        configs.insert("server.port".to_string(), ConfigValue::Integer(8080));
        configs.insert("server.workers".to_string(), ConfigValue::Integer(4));
        
        configs.insert("database.host".to_string(), ConfigValue::String("localhost".to_string()));
        configs.insert("database.port".to_string(), ConfigValue::Integer(5432));
        configs.insert("database.name".to_string(), ConfigValue::String("c19_ai".to_string()));
        configs.insert("database.username".to_string(), ConfigValue::String("postgres".to_string()));
        configs.insert("database.password".to_string(), ConfigValue::String("".to_string()));
        
        configs.insert("cache.default_ttl".to_string(), ConfigValue::Integer(3600));
        configs.insert("cache.max_size".to_string(), ConfigValue::Integer(1000));
        
        configs.insert("storage.default_backend".to_string(), ConfigValue::String("local".to_string()));
        configs.insert("storage.local.base_path".to_string(), ConfigValue::String("/tmp/c19_ai".to_string()));
        
        configs.insert("auth.jwt_secret".to_string(), ConfigValue::String("your-secret-key".to_string()));
        configs.insert("auth.jwt_expiry".to_string(), ConfigValue::Integer(86400));
        
        configs.insert("logging.level".to_string(), ConfigValue::String("info".to_string()));
        configs.insert("logging.format".to_string(), ConfigValue::String("json".to_string()));
        
        configs
    }

    /// 解析环境变量值
    fn parse_env_value(&self, value: &str) -> Result<ConfigValue, ConfigError> {
        // 尝试解析为数字
        if let Ok(int_val) = value.parse::<i64>() {
            return Ok(ConfigValue::Integer(int_val));
        }
        
        if let Ok(float_val) = value.parse::<f64>() {
            return Ok(ConfigValue::Float(float_val));
        }
        
        // 尝试解析为布尔值
        if let Ok(bool_val) = value.parse::<bool>() {
            return Ok(ConfigValue::Boolean(bool_val));
        }
        
        // 默认为字符串
        Ok(ConfigValue::String(value.to_string()))
    }

    /// 获取配置值
    pub async fn get<T>(&self, key: &str) -> Result<Option<T>, ConfigError>
    where
        T: for<'de> Deserialize<'de>,
    {
        let configs = self.configs.read().await;
        if let Some(value) = configs.get(key) {
            let json_value = serde_json::to_value(value)
                .map_err(|e| ConfigError::SerializationError(e))?;
            let typed_value = T::deserialize(json_value)
                .map_err(|e| ConfigError::ParseError { message: e.to_string() })?;
            Ok(Some(typed_value))
        } else {
            Ok(None)
        }
    }

    /// 获取配置值，如果不存在则返回默认值
    pub async fn get_or_default<T>(&self, key: &str, default: T) -> Result<T, ConfigError>
    where
        T: for<'de> Deserialize<'de> + Clone,
    {
        match self.get::<T>(key).await? {
            Some(value) => Ok(value),
            None => Ok(default),
        }
    }

    /// 设置配置值
    pub async fn set<T>(&self, key: &str, value: T) -> Result<(), ConfigError>
    where
        T: Serialize,
    {
        let config_value = serde_json::to_value(value)
            .map_err(|e| ConfigError::SerializationError(e))?;
        
        let config_value = ConfigValue::deserialize(config_value)
            .map_err(|e| ConfigError::ParseError { message: e.to_string() })?;
        
        let mut configs = self.configs.write().await;
        configs.insert(key.to_string(), config_value);
        
        Ok(())
    }

    /// 获取所有配置
    pub async fn get_all(&self) -> HashMap<String, ConfigValue> {
        let configs = self.configs.read().await;
        configs.clone()
    }

    /// 检查配置是否存在
    pub async fn has(&self, key: &str) -> bool {
        let configs = self.configs.read().await;
        configs.contains_key(key)
    }

    /// 删除配置
    pub async fn remove(&self, key: &str) -> Option<ConfigValue> {
        let mut configs = self.configs.write().await;
        configs.remove(key)
    }

    /// 重新加载配置
    pub async fn reload(&self) -> Result<(), ConfigError> {
        let mut configs = self.configs.write().await;
        configs.clear();
        drop(configs);
        
        self.load_all().await
    }
}

impl Default for ConfigManager {
    fn default() -> Self {
        Self::new()
    }
}
