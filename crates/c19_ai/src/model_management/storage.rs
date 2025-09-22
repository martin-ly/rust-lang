//! 模型存储管理
//! 
//! 提供模型的存储、检索和版本管理功能

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
// use uuid::Uuid;
use chrono::{DateTime, Utc};
use tokio::fs;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

/// 模型存储管理器
#[derive(Debug, Clone)]
pub struct ModelStorage {
    base_path: PathBuf,
    storage_config: StorageConfig,
}

/// 存储配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageConfig {
    pub max_file_size: u64,
    pub allowed_extensions: Vec<String>,
    pub compression_enabled: bool,
    pub encryption_enabled: bool,
    pub backup_enabled: bool,
    pub retention_days: u32,
}

impl Default for StorageConfig {
    fn default() -> Self {
        Self {
            max_file_size: 1024 * 1024 * 1024, // 1GB
            allowed_extensions: vec![
                "bin".to_string(),
                "pt".to_string(),
                "onnx".to_string(),
                "pkl".to_string(),
                "joblib".to_string(),
            ],
            compression_enabled: true,
            encryption_enabled: false,
            backup_enabled: true,
            retention_days: 365,
        }
    }
}

/// 存储的模型信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StoredModel {
    pub id: String,
    pub name: String,
    pub version: String,
    pub file_path: PathBuf,
    pub size_bytes: u64,
    pub checksum: String,
    pub created_at: DateTime<Utc>,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 存储操作结果
#[derive(Debug, Serialize, Deserialize)]
pub struct StorageResult {
    pub success: bool,
    pub model_id: String,
    pub file_path: PathBuf,
    pub size_bytes: u64,
    pub checksum: String,
    pub message: Option<String>,
}

impl ModelStorage {
    /// 创建新的模型存储管理器
    pub fn new(base_path: PathBuf, config: StorageConfig) -> Self {
        Self {
            base_path,
            storage_config: config,
        }
    }

    /// 存储模型文件
    pub async fn store_model(
        &self,
        model_id: &str,
        name: &str,
        version: &str,
        source_path: &Path,
        metadata: HashMap<String, serde_json::Value>,
    ) -> Result<StorageResult> {
        // 验证文件
        self.validate_file(source_path).await?;

        // 生成存储路径
        let storage_path = self.generate_storage_path(model_id, name, version, source_path)?;

        // 确保目录存在
        if let Some(parent) = storage_path.parent() {
            fs::create_dir_all(parent).await?;
        }

        // 复制文件
        let file_size = self.copy_file(source_path, &storage_path).await?;

        // 计算校验和
        let checksum = self.calculate_checksum(&storage_path).await?;

        // 创建存储记录
        let stored_model = StoredModel {
            id: model_id.to_string(),
            name: name.to_string(),
            version: version.to_string(),
            file_path: storage_path.clone(),
            size_bytes: file_size,
            checksum,
            created_at: Utc::now(),
            metadata,
        };

        // 保存存储记录
        self.save_storage_record(&stored_model).await?;

        // 如果启用备份，创建备份
        if self.storage_config.backup_enabled {
            self.create_backup(&stored_model).await?;
        }

        Ok(StorageResult {
            success: true,
            model_id: model_id.to_string(),
            file_path: storage_path,
            size_bytes: file_size,
            checksum: stored_model.checksum,
            message: Some("Model stored successfully".to_string()),
        })
    }

    /// 检索模型文件
    pub async fn retrieve_model(&self, model_id: &str) -> Result<StoredModel> {
        let record_path = self.get_record_path(model_id);
        
        if !record_path.exists() {
            return Err(anyhow::anyhow!("Model not found: {}", model_id));
        }

        let record_content = fs::read_to_string(&record_path).await?;
        let stored_model: StoredModel = serde_json::from_str(&record_content)?;

        // 验证文件是否存在
        if !stored_model.file_path.exists() {
            return Err(anyhow::anyhow!("Model file not found: {:?}", stored_model.file_path));
        }

        // 验证校验和
        let current_checksum = self.calculate_checksum(&stored_model.file_path).await?;
        if current_checksum != stored_model.checksum {
            return Err(anyhow::anyhow!("Model file checksum mismatch"));
        }

        Ok(stored_model)
    }

    /// 删除模型
    pub async fn delete_model(&self, model_id: &str) -> Result<()> {
        let stored_model = self.retrieve_model(model_id).await?;

        // 删除主文件
        if stored_model.file_path.exists() {
            fs::remove_file(&stored_model.file_path).await?;
        }

        // 删除记录文件
        let record_path = self.get_record_path(model_id);
        if record_path.exists() {
            fs::remove_file(record_path).await?;
        }

        // 删除备份文件
        if self.storage_config.backup_enabled {
            self.delete_backup(model_id).await?;
        }

        Ok(())
    }

    /// 列出所有存储的模型
    pub async fn list_models(&self) -> Result<Vec<StoredModel>> {
        let records_dir = self.base_path.join("records");
        
        if !records_dir.exists() {
            return Ok(vec![]);
        }

        let mut models = Vec::new();
        let mut entries = fs::read_dir(&records_dir).await?;

        while let Some(entry) = entries.next_entry().await? {
            if let Some(extension) = entry.path().extension() {
                if extension == "json" {
                    let content = fs::read_to_string(entry.path()).await?;
                    if let Ok(model) = serde_json::from_str::<StoredModel>(&content) {
                        models.push(model);
                    }
                }
            }
        }

        models.sort_by(|a, b| b.created_at.cmp(&a.created_at));
        Ok(models)
    }

    /// 获取存储统计信息
    pub async fn get_storage_stats(&self) -> Result<StorageStats> {
        let models = self.list_models().await?;
        
        let mut stats = StorageStats {
            total_models: models.len() as u32,
            total_size_bytes: 0,
            models_by_extension: HashMap::new(),
            oldest_model: None,
            newest_model: None,
        };

        for model in &models {
            stats.total_size_bytes += model.size_bytes;

            if let Some(extension) = model.file_path.extension() {
                let ext = extension.to_string_lossy().to_string();
                *stats.models_by_extension.entry(ext).or_insert(0) += 1;
            }

            if stats.oldest_model.is_none() || model.created_at < stats.oldest_model.unwrap() {
                stats.oldest_model = Some(model.created_at);
            }

            if stats.newest_model.is_none() || model.created_at > stats.newest_model.unwrap() {
                stats.newest_model = Some(model.created_at);
            }
        }

        Ok(stats)
    }

    /// 清理过期文件
    pub async fn cleanup_expired(&self) -> Result<CleanupResult> {
        let cutoff_date = Utc::now() - chrono::Duration::days(self.storage_config.retention_days as i64);
        let models = self.list_models().await?;
        
        let mut deleted_count = 0;
        let mut freed_bytes = 0;

        for model in models {
            if model.created_at < cutoff_date {
                self.delete_model(&model.id).await?;
                deleted_count += 1;
                freed_bytes += model.size_bytes;
            }
        }

        Ok(CleanupResult {
            deleted_models: deleted_count,
            freed_bytes,
            cutoff_date,
        })
    }

    /// 验证文件
    async fn validate_file(&self, file_path: &Path) -> Result<()> {
        if !file_path.exists() {
            return Err(anyhow::anyhow!("File does not exist: {:?}", file_path));
        }

        let metadata = fs::metadata(file_path).await?;
        if metadata.len() == 0 {
            return Err(anyhow::anyhow!("File is empty: {:?}", file_path));
        }

        if metadata.len() > self.storage_config.max_file_size {
            return Err(anyhow::anyhow!(
                "File too large: {} bytes (max: {} bytes)",
                metadata.len(),
                self.storage_config.max_file_size
            ));
        }

        if let Some(extension) = file_path.extension() {
            let ext = extension.to_string_lossy().to_string();
            if !self.storage_config.allowed_extensions.contains(&ext) {
                return Err(anyhow::anyhow!(
                    "File extension not allowed: {} (allowed: {:?})",
                    ext,
                    self.storage_config.allowed_extensions
                ));
            }
        }

        Ok(())
    }

    /// 生成存储路径
    fn generate_storage_path(
        &self,
        model_id: &str,
        name: &str,
        version: &str,
        source_path: &Path,
    ) -> Result<PathBuf> {
        let extension = source_path
            .extension()
            .and_then(|ext| ext.to_str())
            .unwrap_or("bin");

        let filename = format!("{}_{}_{}.{}", name, version, model_id, extension);
        let storage_path = self.base_path.join("models").join(&filename);
        
        Ok(storage_path)
    }

    /// 复制文件
    async fn copy_file(&self, source: &Path, destination: &PathBuf) -> Result<u64> {
        let mut source_file = fs::File::open(source).await?;
        let mut dest_file = fs::File::create(destination).await?;

        let bytes_copied = tokio::io::copy(&mut source_file, &mut dest_file).await?;
        dest_file.flush().await?;

        Ok(bytes_copied)
    }

    /// 计算文件校验和
    async fn calculate_checksum(&self, file_path: &PathBuf) -> Result<String> {
        use sha2::{Sha256, Digest};
        
        let mut file = fs::File::open(file_path).await?;
        let mut hasher = Sha256::new();
        let mut buffer = [0; 8192];
        
        loop {
            let bytes_read = file.read(&mut buffer).await?;
            if bytes_read == 0 {
                break;
            }
            hasher.update(&buffer[..bytes_read]);
        }
        
        Ok(format!("{:x}", hasher.finalize()))
    }

    /// 保存存储记录
    async fn save_storage_record(&self, model: &StoredModel) -> Result<()> {
        let records_dir = self.base_path.join("records");
        fs::create_dir_all(&records_dir).await?;

        let record_path = self.get_record_path(&model.id);
        let record_json = serde_json::to_string_pretty(model)?;
        fs::write(record_path, record_json).await?;

        Ok(())
    }

    /// 获取记录文件路径
    fn get_record_path(&self, model_id: &str) -> PathBuf {
        self.base_path.join("records").join(format!("{}.json", model_id))
    }

    /// 创建备份
    async fn create_backup(&self, model: &StoredModel) -> Result<()> {
        let backup_dir = self.base_path.join("backups");
        fs::create_dir_all(&backup_dir).await?;

        let backup_path = backup_dir.join(format!("{}.backup", model.id));
        
        if model.file_path.exists() {
            self.copy_file(&model.file_path, &backup_path).await?;
        }

        Ok(())
    }

    /// 删除备份
    async fn delete_backup(&self, model_id: &str) -> Result<()> {
        let backup_path = self.base_path.join("backups").join(format!("{}.backup", model_id));
        
        if backup_path.exists() {
            fs::remove_file(backup_path).await?;
        }

        Ok(())
    }
}

/// 存储统计信息
#[derive(Debug, Serialize, Deserialize)]
pub struct StorageStats {
    pub total_models: u32,
    pub total_size_bytes: u64,
    pub models_by_extension: HashMap<String, u32>,
    pub oldest_model: Option<DateTime<Utc>>,
    pub newest_model: Option<DateTime<Utc>>,
}

/// 清理结果
#[derive(Debug, Serialize, Deserialize)]
pub struct CleanupResult {
    pub deleted_models: u32,
    pub freed_bytes: u64,
    pub cutoff_date: DateTime<Utc>,
}
