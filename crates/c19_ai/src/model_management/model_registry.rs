//! 模型注册表
//! 
//! 提供模型版本控制、元数据管理和发现功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use chrono::{DateTime, Utc};

/// 模型注册表
#[derive(Debug, Clone)]
pub struct ModelRegistry {
    pub name: String,
    pub models: HashMap<String, ModelEntry>,
    pub config: RegistryConfig,
}

/// 模型条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelEntry {
    pub name: String,
    pub versions: Vec<ModelVersion>,
    pub latest_version: String,
    pub tags: Vec<String>,
    pub description: String,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 模型版本
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelVersion {
    pub version: String,
    pub model_info: ModelInfo,
    pub metrics: ModelMetrics,
    pub artifacts: Vec<ModelArtifact>,
    pub created_at: DateTime<Utc>,
    pub created_by: String,
    pub status: ModelStatus,
}

/// 模型信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelInfo {
    pub name: String,
    pub format: String,
    pub size_bytes: usize,
    pub input_shape: Vec<usize>,
    pub output_shape: Vec<usize>,
    pub framework: String,
    pub architecture: String,
}

/// 模型指标
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelMetrics {
    pub accuracy: Option<f64>,
    pub precision: Option<f64>,
    pub recall: Option<f64>,
    pub f1_score: Option<f64>,
    pub inference_time_ms: Option<f64>,
    pub memory_usage_mb: Option<f64>,
    pub custom_metrics: HashMap<String, f64>,
}

/// 模型工件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelArtifact {
    pub name: String,
    pub artifact_type: ArtifactType,
    pub path: String,
    pub size_bytes: usize,
    pub checksum: String,
}

/// 工件类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ArtifactType {
    /// 模型文件
    Model,
    /// 配置文件
    Config,
    /// 预处理器
    Preprocessor,
    /// 后处理器
    Postprocessor,
    /// 文档
    Documentation,
    /// 测试数据
    TestData,
}

/// 模型状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModelStatus {
    /// 开发中
    Development,
    /// 测试中
    Testing,
    /// 生产就绪
    Production,
    /// 已弃用
    Deprecated,
    /// 已归档
    Archived,
}

/// 注册表配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegistryConfig {
    pub max_versions_per_model: usize,
    pub enable_versioning: bool,
    pub auto_cleanup: bool,
    pub retention_days: u32,
    pub enable_checksums: bool,
}

impl ModelRegistry {
    /// 创建新的模型注册表
    pub fn new(name: String, config: RegistryConfig) -> Self {
        Self {
            name,
            models: HashMap::new(),
            config,
        }
    }
    
    /// 注册模型
    pub fn register_model(&mut self, name: String, description: String, tags: Vec<String>) -> Result<(), String> {
        if self.models.contains_key(&name) {
            return Err(format!("模型 '{}' 已存在", name));
        }
        
        let now = Utc::now();
        let entry = ModelEntry {
            name: name.clone(),
            versions: Vec::new(),
            latest_version: "0.0.0".to_string(),
            tags,
            description,
            created_at: now,
            updated_at: now,
        };
        
        self.models.insert(name, entry);
        Ok(())
    }
    
    /// 添加模型版本
    pub fn add_model_version(&mut self, model_name: &str, version: ModelVersion) -> Result<(), String> {
        let entry = self.models.get_mut(model_name)
            .ok_or_else(|| format!("模型 '{}' 不存在", model_name))?;
        
        // 检查版本是否已存在
        if entry.versions.iter().any(|v| v.version == version.version) {
            return Err(format!("版本 '{}' 已存在", version.version));
        }
        
        // 检查版本数量限制
        if entry.versions.len() >= self.config.max_versions_per_model {
            if self.config.auto_cleanup {
                self.cleanup_old_versions(entry)?;
            } else {
                return Err(format!("模型版本数量超过限制 {}", self.config.max_versions_per_model));
            }
        }
        
        entry.versions.push(version);
        entry.updated_at = Utc::now();
        
        // 更新最新版本
        self.update_latest_version(entry);
        
        Ok(())
    }
    
    /// 获取模型信息
    pub fn get_model(&self, name: &str) -> Result<&ModelEntry, String> {
        self.models.get(name)
            .ok_or_else(|| format!("模型 '{}' 不存在", name))
    }
    
    /// 获取模型版本
    pub fn get_model_version(&self, name: &str, version: &str) -> Result<&ModelVersion, String> {
        let entry = self.get_model(name)?;
        entry.versions.iter()
            .find(|v| v.version == version)
            .ok_or_else(|| format!("模型 '{}' 的版本 '{}' 不存在", name, version))
    }
    
    /// 获取最新版本
    pub fn get_latest_version(&self, name: &str) -> Result<&ModelVersion, String> {
        let entry = self.get_model(name)?;
        entry.versions.iter()
            .find(|v| v.version == entry.latest_version)
            .ok_or_else(|| format!("模型 '{}' 没有有效版本", name))
    }
    
    /// 列出所有模型
    pub fn list_models(&self) -> Vec<ModelSummary> {
        self.models.values()
            .map(|entry| ModelSummary {
                name: entry.name.clone(),
                latest_version: entry.latest_version.clone(),
                version_count: entry.versions.len(),
                tags: entry.tags.clone(),
                description: entry.description.clone(),
                created_at: entry.created_at,
                updated_at: entry.updated_at,
            })
            .collect()
    }
    
    /// 搜索模型
    pub fn search_models(&self, query: &str) -> Vec<ModelSummary> {
        let query_lower = query.to_lowercase();
        
        self.models.values()
            .filter(|entry| {
                entry.name.to_lowercase().contains(&query_lower) ||
                entry.description.to_lowercase().contains(&query_lower) ||
                entry.tags.iter().any(|tag| tag.to_lowercase().contains(&query_lower))
            })
            .map(|entry| ModelSummary {
                name: entry.name.clone(),
                latest_version: entry.latest_version.clone(),
                version_count: entry.versions.len(),
                tags: entry.tags.clone(),
                description: entry.description.clone(),
                created_at: entry.created_at,
                updated_at: entry.updated_at,
            })
            .collect()
    }
    
    /// 按标签过滤模型
    pub fn filter_by_tags(&self, tags: &[String]) -> Vec<ModelSummary> {
        self.models.values()
            .filter(|entry| {
                tags.iter().all(|tag| entry.tags.contains(tag))
            })
            .map(|entry| ModelSummary {
                name: entry.name.clone(),
                latest_version: entry.latest_version.clone(),
                version_count: entry.versions.len(),
                tags: entry.tags.clone(),
                description: entry.description.clone(),
                created_at: entry.created_at,
                updated_at: entry.updated_at,
            })
            .collect()
    }
    
    /// 删除模型
    pub fn delete_model(&mut self, name: &str) -> Result<(), String> {
        self.models.remove(name)
            .ok_or_else(|| format!("模型 '{}' 不存在", name))?;
        Ok(())
    }
    
    /// 删除模型版本
    pub fn delete_model_version(&mut self, name: &str, version: &str) -> Result<(), String> {
        let entry = self.models.get_mut(name)
            .ok_or_else(|| format!("模型 '{}' 不存在", name))?;
        
        let initial_len = entry.versions.len();
        entry.versions.retain(|v| v.version != version);
        
        if entry.versions.len() == initial_len {
            return Err(format!("版本 '{}' 不存在", version));
        }
        
        // 更新最新版本
        self.update_latest_version(entry);
        entry.updated_at = Utc::now();
        
        Ok(())
    }
    
    /// 更新模型状态
    pub fn update_model_status(&mut self, name: &str, version: &str, status: ModelStatus) -> Result<(), String> {
        let entry = self.models.get_mut(name)
            .ok_or_else(|| format!("模型 '{}' 不存在", name))?;
        
        let model_version = entry.versions.iter_mut()
            .find(|v| v.version == version)
            .ok_or_else(|| format!("版本 '{}' 不存在", version))?;
        
        model_version.status = status;
        entry.updated_at = Utc::now();
        
        Ok(())
    }
    
    /// 获取注册表统计信息
    pub fn get_statistics(&self) -> RegistryStatistics {
        let total_models = self.models.len();
        let total_versions: usize = self.models.values()
            .map(|entry| entry.versions.len())
            .sum();
        
        let status_counts = self.get_status_counts();
        let framework_counts = self.get_framework_counts();
        
        RegistryStatistics {
            total_models,
            total_versions,
            average_versions_per_model: if total_models > 0 {
                total_versions as f64 / total_models as f64
            } else {
                0.0
            },
            status_counts,
            framework_counts,
        }
    }
    
    /// 更新最新版本
    fn update_latest_version(&self, entry: &mut ModelEntry) {
        if let Some(latest) = entry.versions.iter()
            .max_by(|a, b| a.version.cmp(&b.version)) {
            entry.latest_version = latest.version.clone();
        }
    }
    
    /// 清理旧版本
    fn cleanup_old_versions(&self, entry: &mut ModelEntry) -> Result<(), String> {
        if entry.versions.len() <= self.config.max_versions_per_model {
            return Ok(());
        }
        
        // 按创建时间排序，保留最新的版本
        entry.versions.sort_by(|a, b| b.created_at.cmp(&a.created_at));
        
        // 删除超出限制的版本
        let to_remove = entry.versions.len() - self.config.max_versions_per_model;
        entry.versions.truncate(self.config.max_versions_per_model);
        
        Ok(())
    }
    
    /// 获取状态统计
    fn get_status_counts(&self) -> HashMap<ModelStatus, usize> {
        let mut counts = HashMap::new();
        
        for entry in self.models.values() {
            for version in &entry.versions {
                *counts.entry(version.status.clone()).or_insert(0) += 1;
            }
        }
        
        counts
    }
    
    /// 获取框架统计
    fn get_framework_counts(&self) -> HashMap<String, usize> {
        let mut counts = HashMap::new();
        
        for entry in self.models.values() {
            for version in &entry.versions {
                *counts.entry(version.model_info.framework.clone()).or_insert(0) += 1;
            }
        }
        
        counts
    }
}

/// 模型摘要
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelSummary {
    pub name: String,
    pub latest_version: String,
    pub version_count: usize,
    pub tags: Vec<String>,
    pub description: String,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
}

/// 注册表统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegistryStatistics {
    pub total_models: usize,
    pub total_versions: usize,
    pub average_versions_per_model: f64,
    pub status_counts: HashMap<ModelStatus, usize>,
    pub framework_counts: HashMap<String, usize>,
}

impl Default for RegistryConfig {
    fn default() -> Self {
        Self {
            max_versions_per_model: 10,
            enable_versioning: true,
            auto_cleanup: true,
            retention_days: 90,
            enable_checksums: true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_model_registry_creation() {
        let config = RegistryConfig::default();
        let registry = ModelRegistry::new("test_registry".to_string(), config);
        
        assert_eq!(registry.name, "test_registry");
        assert_eq!(registry.models.len(), 0);
    }
    
    #[test]
    fn test_register_model() {
        let mut registry = ModelRegistry::new("test_registry".to_string(), RegistryConfig::default());
        
        registry.register_model(
            "test_model".to_string(),
            "测试模型".to_string(),
            vec!["test".to_string(), "demo".to_string()],
        ).unwrap();
        
        assert_eq!(registry.models.len(), 1);
        assert!(registry.models.contains_key("test_model"));
    }
    
    #[test]
    fn test_add_model_version() {
        let mut registry = ModelRegistry::new("test_registry".to_string(), RegistryConfig::default());
        
        registry.register_model(
            "test_model".to_string(),
            "测试模型".to_string(),
            vec!["test".to_string()],
        ).unwrap();
        
        let model_info = ModelInfo {
            name: "test_model".to_string(),
            format: "onnx".to_string(),
            size_bytes: 1024,
            input_shape: vec![1, 3, 224, 224],
            output_shape: vec![1, 1000],
            framework: "pytorch".to_string(),
            architecture: "resnet".to_string(),
        };
        
        let version = ModelVersion {
            version: "1.0.0".to_string(),
            model_info,
            metrics: ModelMetrics {
                accuracy: Some(0.95),
                precision: None,
                recall: None,
                f1_score: None,
                inference_time_ms: Some(10.0),
                memory_usage_mb: Some(50.0),
                custom_metrics: HashMap::new(),
            },
            artifacts: Vec::new(),
            created_at: Utc::now(),
            created_by: "test_user".to_string(),
            status: ModelStatus::Development,
        };
        
        registry.add_model_version("test_model", version).unwrap();
        
        let entry = registry.get_model("test_model").unwrap();
        assert_eq!(entry.versions.len(), 1);
        assert_eq!(entry.latest_version, "1.0.0");
    }
    
    #[test]
    fn test_search_models() {
        let mut registry = ModelRegistry::new("test_registry".to_string(), RegistryConfig::default());
        
        registry.register_model(
            "image_classifier".to_string(),
            "图像分类模型".to_string(),
            vec!["vision".to_string(), "classification".to_string()],
        ).unwrap();
        
        registry.register_model(
            "text_analyzer".to_string(),
            "文本分析模型".to_string(),
            vec!["nlp".to_string(), "analysis".to_string()],
        ).unwrap();
        
        let results = registry.search_models("image");
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].name, "image_classifier");
    }
    
    #[test]
    fn test_filter_by_tags() {
        let mut registry = ModelRegistry::new("test_registry".to_string(), RegistryConfig::default());
        
        registry.register_model(
            "model1".to_string(),
            "模型1".to_string(),
            vec!["vision".to_string(), "classification".to_string()],
        ).unwrap();
        
        registry.register_model(
            "model2".to_string(),
            "模型2".to_string(),
            vec!["vision".to_string(), "detection".to_string()],
        ).unwrap();
        
        let results = registry.filter_by_tags(&["vision".to_string()]);
        assert_eq!(results.len(), 2);
        
        let results = registry.filter_by_tags(&["vision".to_string(), "classification".to_string()]);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].name, "model1");
    }
}
