//! 模型注册表
//! 
//! 管理模型的注册、发现和元数据存储

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::PathBuf;
use uuid::Uuid;
use chrono::{DateTime, Utc};

/// 模型注册表
#[derive(Debug, Clone)]
pub struct ModelRegistry {
    models: HashMap<String, ModelEntry>,
    storage_path: PathBuf,
}

/// 模型条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelEntry {
    pub id: String,
    pub name: String,
    pub version: String,
    pub model_type: ModelType,
    pub framework: Framework,
    pub status: ModelStatus,
    pub metadata: ModelMetadata,
    pub file_path: PathBuf,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    pub tags: Vec<String>,
}

/// 模型类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModelType {
    Classification,
    Regression,
    Clustering,
    Generation,
    Embedding,
    Custom(String),
}

/// 框架类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Framework {
    Candle,
    Burn,
    Tch,
    Dfdx,
    Custom(String),
}

/// 模型状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ModelStatus {
    Draft,
    Training,
    Ready,
    Deployed,
    Archived,
    Failed,
}

/// 模型元数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ModelMetadata {
    pub description: Option<String>,
    pub author: Option<String>,
    pub license: Option<String>,
    pub parameters: HashMap<String, serde_json::Value>,
    pub input_schema: Option<serde_json::Value>,
    pub output_schema: Option<serde_json::Value>,
    pub performance_metrics: HashMap<String, f64>,
    pub dependencies: Vec<String>,
    pub size_bytes: u64,
    pub checksum: String,
}

/// 模型注册请求
#[derive(Debug, Serialize, Deserialize)]
pub struct ModelRegistrationRequest {
    pub name: String,
    pub version: String,
    pub model_type: ModelType,
    pub framework: Framework,
    pub file_path: PathBuf,
    pub metadata: ModelMetadata,
    pub tags: Option<Vec<String>>,
}

/// 模型搜索过滤器
#[derive(Debug, Serialize, Deserialize)]
pub struct ModelSearchFilter {
    pub name: Option<String>,
    pub model_type: Option<ModelType>,
    pub framework: Option<Framework>,
    pub status: Option<ModelStatus>,
    pub tags: Option<Vec<String>>,
    pub created_after: Option<DateTime<Utc>>,
    pub created_before: Option<DateTime<Utc>>,
}

impl ModelRegistry {
    /// 创建新的模型注册表
    pub fn new(storage_path: PathBuf) -> Self {
        Self {
            models: HashMap::new(),
            storage_path,
        }
    }

    /// 注册新模型
    pub async fn register_model(&mut self, request: ModelRegistrationRequest) -> Result<ModelEntry> {
        let model_id = Uuid::new_v4().to_string();
        let now = Utc::now();

        // 验证模型文件
        self.validate_model_file(&request.file_path).await?;

        // 计算文件校验和
        let checksum = self.calculate_checksum(&request.file_path).await?;

        let model_entry = ModelEntry {
            id: model_id.clone(),
            name: request.name,
            version: request.version,
            model_type: request.model_type,
            framework: request.framework,
            status: ModelStatus::Draft,
            metadata: ModelMetadata {
                checksum,
                size_bytes: tokio::fs::metadata(&request.file_path).await?.len(),
                ..request.metadata
            },
            file_path: request.file_path,
            created_at: now,
            updated_at: now,
            tags: request.tags.unwrap_or_default(),
        };

        // 保存模型元数据
        self.save_model_metadata(&model_entry).await?;

        // 添加到内存注册表
        self.models.insert(model_id.clone(), model_entry.clone());

        Ok(model_entry)
    }

    /// 获取模型
    pub fn get_model(&self, model_id: &str) -> Option<&ModelEntry> {
        self.models.get(model_id)
    }

    /// 获取所有模型
    pub fn get_all_models(&self) -> Vec<&ModelEntry> {
        self.models.values().collect()
    }

    /// 搜索模型
    pub fn search_models(&self, filter: &ModelSearchFilter) -> Vec<&ModelEntry> {
        self.models
            .values()
            .filter(|model| {
                if let Some(name) = &filter.name {
                    if !model.name.contains(name) {
                        return false;
                    }
                }

                if let Some(model_type) = &filter.model_type {
                    if std::mem::discriminant(&model.model_type) != std::mem::discriminant(model_type) {
                        return false;
                    }
                }

                if let Some(framework) = &filter.framework {
                    if std::mem::discriminant(&model.framework) != std::mem::discriminant(framework) {
                        return false;
                    }
                }

                if let Some(status) = &filter.status {
                    if std::mem::discriminant(&model.status) != std::mem::discriminant(status) {
                        return false;
                    }
                }

                if let Some(tags) = &filter.tags {
                    if !tags.iter().any(|tag| model.tags.contains(tag)) {
                        return false;
                    }
                }

                if let Some(created_after) = &filter.created_after {
                    if model.created_at < *created_after {
                        return false;
                    }
                }

                if let Some(created_before) = &filter.created_before {
                    if model.created_at > *created_before {
                        return false;
                    }
                }

                true
            })
            .collect()
    }

    /// 更新模型状态
    pub async fn update_model_status(&mut self, model_id: &str, status: ModelStatus) -> Result<()> {
        if let Some(model) = self.models.get_mut(model_id) {
            model.status = status;
            model.updated_at = Utc::now();
            let model_clone = model.clone();
            drop(model); // 释放可变借用
            self.save_model_metadata(&model_clone).await?;
        }
        Ok(())
    }

    /// 更新模型元数据
    pub async fn update_model_metadata(
        &mut self,
        model_id: &str,
        metadata: ModelMetadata,
    ) -> Result<()> {
        if let Some(model) = self.models.get_mut(model_id) {
            model.metadata = metadata;
            model.updated_at = Utc::now();
            let model_clone = model.clone();
            drop(model); // 释放可变借用
            self.save_model_metadata(&model_clone).await?;
        }
        Ok(())
    }

    /// 删除模型
    pub async fn delete_model(&mut self, model_id: &str) -> Result<()> {
        if let Some(model) = self.models.remove(model_id) {
            // 删除模型文件
            if model.file_path.exists() {
                tokio::fs::remove_file(&model.file_path).await?;
            }

            // 删除元数据文件
            let metadata_path = self.get_metadata_path(model_id);
            if metadata_path.exists() {
                tokio::fs::remove_file(metadata_path).await?;
            }
        }
        Ok(())
    }

    /// 验证模型文件
    async fn validate_model_file(&self, file_path: &PathBuf) -> Result<()> {
        if !file_path.exists() {
            return Err(anyhow::anyhow!("Model file does not exist: {:?}", file_path));
        }

        let metadata = tokio::fs::metadata(file_path).await?;
        if metadata.len() == 0 {
            return Err(anyhow::anyhow!("Model file is empty: {:?}", file_path));
        }

        // 检查文件扩展名
        if let Some(extension) = file_path.extension() {
            let valid_extensions = ["bin", "pt", "onnx", "pkl", "joblib"];
            if !valid_extensions.contains(&extension.to_string_lossy().as_ref()) {
                return Err(anyhow::anyhow!(
                    "Invalid model file extension: {:?}",
                    extension
                ));
            }
        }

        Ok(())
    }

    /// 计算文件校验和
    async fn calculate_checksum(&self, file_path: &PathBuf) -> Result<String> {
        use sha2::{Sha256, Digest};
        
        let mut file = tokio::fs::File::open(file_path).await?;
        let mut hasher = Sha256::new();
        
        use tokio::io::{AsyncReadExt, BufReader};
        let mut reader = BufReader::new(&mut file);
        let mut buffer = [0; 8192];
        
        loop {
            let bytes_read = reader.read(&mut buffer).await?;
            if bytes_read == 0 {
                break;
            }
            hasher.update(&buffer[..bytes_read]);
        }
        
        Ok(format!("{:x}", hasher.finalize()))
    }

    /// 保存模型元数据
    async fn save_model_metadata(&self, model: &ModelEntry) -> Result<()> {
        let metadata_path = self.get_metadata_path(&model.id);
        let metadata_json = serde_json::to_string_pretty(model)?;
        tokio::fs::write(metadata_path, metadata_json).await?;
        Ok(())
    }

    /// 获取元数据文件路径
    fn get_metadata_path(&self, model_id: &str) -> PathBuf {
        self.storage_path.join("metadata").join(format!("{}.json", model_id))
    }

    /// 从存储加载模型注册表
    pub async fn load_from_storage(&mut self) -> Result<()> {
        let metadata_dir = self.storage_path.join("metadata");
        if !metadata_dir.exists() {
            tokio::fs::create_dir_all(&metadata_dir).await?;
            return Ok(());
        }

        let mut entries = tokio::fs::read_dir(&metadata_dir).await?;
        while let Some(entry) = entries.next_entry().await? {
            if let Some(extension) = entry.path().extension() {
                if extension == "json" {
                    let metadata_content = tokio::fs::read_to_string(entry.path()).await?;
                    let model_entry: ModelEntry = serde_json::from_str(&metadata_content)?;
                    self.models.insert(model_entry.id.clone(), model_entry);
                }
            }
        }

        Ok(())
    }

    /// 获取模型统计信息
    pub fn get_statistics(&self) -> ModelStatistics {
        let mut stats = ModelStatistics::default();

        for model in self.models.values() {
            stats.total_models += 1;

            match model.status {
                ModelStatus::Ready => stats.ready_models += 1,
                ModelStatus::Deployed => stats.deployed_models += 1,
                ModelStatus::Training => stats.training_models += 1,
                ModelStatus::Failed => stats.failed_models += 1,
                _ => {}
            }

            match model.framework {
                Framework::Candle => stats.candle_models += 1,
                Framework::Burn => stats.burn_models += 1,
                Framework::Tch => stats.tch_models += 1,
                Framework::Dfdx => stats.dfdx_models += 1,
                _ => {}
            }

            match model.model_type {
                ModelType::Classification => stats.classification_models += 1,
                ModelType::Regression => stats.regression_models += 1,
                ModelType::Clustering => stats.clustering_models += 1,
                ModelType::Generation => stats.generation_models += 1,
                ModelType::Embedding => stats.embedding_models += 1,
                _ => {}
            }

            stats.total_size_bytes += model.metadata.size_bytes;
        }

        stats
    }
}

/// 模型统计信息
#[derive(Debug, Default, Serialize, Deserialize)]
pub struct ModelStatistics {
    pub total_models: u32,
    pub ready_models: u32,
    pub deployed_models: u32,
    pub training_models: u32,
    pub failed_models: u32,
    pub candle_models: u32,
    pub burn_models: u32,
    pub tch_models: u32,
    pub dfdx_models: u32,
    pub classification_models: u32,
    pub regression_models: u32,
    pub clustering_models: u32,
    pub generation_models: u32,
    pub embedding_models: u32,
    pub total_size_bytes: u64,
}
