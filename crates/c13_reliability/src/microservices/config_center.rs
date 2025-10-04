//! # 配置中心（Config Center）
//!
//! 提供动态配置管理、版本控制和配置推送功能。

use crate::error_handling::prelude::*;
use dashmap::DashMap;
use std::sync::Arc;
use serde::{Deserialize, Serialize};

/// 配置项
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConfigItem {
    pub key: String,
    pub value: String,
    pub version: u64,
}

/// 配置版本
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConfigVersion {
    pub version: u64,
    pub timestamp: u64,
}

/// 配置变更事件
#[derive(Debug, Clone)]
pub struct ConfigChangeEvent {
    pub key: String,
    pub old_value: Option<String>,
    pub new_value: String,
}

/// 配置中心配置
#[derive(Debug, Clone)]
pub struct ConfigCenterConfig {
    pub namespace: String,
}

/// 配置仓库
pub struct ConfigRepository {
    configs: Arc<DashMap<String, ConfigItem>>,
}

impl ConfigRepository {
    pub fn new() -> Self {
        Self {
            configs: Arc::new(DashMap::new()),
        }
    }
    
    pub fn get(&self, key: &str) -> Option<ConfigItem> {
        self.configs.get(key).map(|entry| entry.value().clone())
    }
    
    pub fn set(&self, item: ConfigItem) {
        self.configs.insert(item.key.clone(), item);
    }
}

/// 配置监听器
#[async_trait::async_trait]
pub trait ConfigWatcher: Send + Sync {
    async fn on_change(&self, event: ConfigChangeEvent);
}

/// 配置中心
pub struct ConfigCenter {
    _config: ConfigCenterConfig,
    repository: ConfigRepository,
}

impl ConfigCenter {
    pub fn new(config: ConfigCenterConfig) -> Self {
        Self {
            _config: config,
            repository: ConfigRepository::new(),
        }
    }
    
    pub async fn get_config(&self, key: &str) -> Result<Option<String>> {
        Ok(self.repository.get(key).map(|item| item.value))
    }
    
    pub async fn set_config(&self, key: String, value: String) -> Result<()> {
        let item = ConfigItem {
            key: key.clone(),
            value,
            version: 1,
        };
        self.repository.set(item);
        Ok(())
    }
}

