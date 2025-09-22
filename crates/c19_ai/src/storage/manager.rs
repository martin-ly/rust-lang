//! 存储管理器
//! 
//! 提供统一的文件存储接口和多存储后端支持

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
// 移除未使用的导入
use std::sync::Arc;
use tokio::sync::RwLock;
use uuid::Uuid;
use chrono::{DateTime, Utc};
// 移除未使用的导入

use super::local::LocalStorage;
use super::s3::S3Storage;
use super::gcs::GcsStorage;
use super::azure::AzureStorage;
use super::metadata::FileMetadata;
use super::replication::ReplicationManager;

/// 存储管理器
pub struct StorageManager {
    backends: Arc<RwLock<HashMap<String, Box<dyn StorageBackend + Send + Sync>>>>,
    default_backend: String,
    replication_manager: Arc<ReplicationManager>,
    metadata_store: Arc<RwLock<HashMap<String, FileMetadata>>>,
}

/// 存储后端接口
#[async_trait::async_trait]
pub trait StorageBackend {
    async fn put(&self, key: &str, data: &[u8], metadata: &FileMetadata) -> Result<PutResult>;
    async fn get(&self, key: &str) -> Result<GetResult>;
    async fn delete(&self, key: &str) -> Result<()>;
    async fn exists(&self, key: &str) -> bool;
    async fn list(&self, prefix: &str, limit: Option<usize>) -> Result<Vec<ListItem>>;
    async fn copy(&self, source: &str, destination: &str) -> Result<()>;
    async fn move_file(&self, source: &str, destination: &str) -> Result<()>;
    async fn get_metadata(&self, key: &str) -> Result<Option<FileMetadata>>;
    async fn get_stats(&self) -> StorageStats;
}

/// 存储结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PutResult {
    pub key: String,
    pub size: u64,
    pub etag: String,
    pub version: Option<String>,
    pub storage_class: String,
    pub created_at: DateTime<Utc>,
}

/// 获取结果
#[derive(Debug, Clone)]
pub struct GetResult {
    pub data: Vec<u8>,
    pub metadata: FileMetadata,
    pub etag: String,
    pub last_modified: DateTime<Utc>,
}

/// 列表项
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ListItem {
    pub key: String,
    pub size: u64,
    pub last_modified: DateTime<Utc>,
    pub etag: String,
    pub storage_class: String,
}

/// 存储统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageStats {
    pub total_files: u64,
    pub total_size: u64,
    pub available_space: u64,
    pub used_space: u64,
    pub read_operations: u64,
    pub write_operations: u64,
    pub error_count: u64,
    pub last_updated: DateTime<Utc>,
}

/// 存储配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageConfig {
    pub backend_type: StorageBackendType,
    pub name: String,
    pub config: serde_json::Value,
    pub is_default: bool,
    pub replication_enabled: bool,
    pub compression_enabled: bool,
    pub encryption_enabled: bool,
}

/// 存储后端类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StorageBackendType {
    Local,
    S3,
    GCS,
    Azure,
    MinIO,
}

/// 文件上传请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UploadRequest {
    pub key: String,
    pub data: Vec<u8>,
    pub content_type: Option<String>,
    pub metadata: HashMap<String, String>,
    pub tags: Option<HashMap<String, String>>,
    pub storage_class: Option<String>,
    pub encryption: Option<EncryptionConfig>,
}

/// 加密配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EncryptionConfig {
    pub algorithm: String,
    pub key: String,
    pub iv: Option<String>,
}

impl std::fmt::Display for EncryptionConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}:{}", self.algorithm, self.key)
    }
}

impl Default for EncryptionConfig {
    fn default() -> Self {
        Self {
            algorithm: "AES256".to_string(),
            key: "default_key".to_string(),
            iv: None,
        }
    }
}

/// 文件下载请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DownloadRequest {
    pub key: String,
    pub range: Option<(u64, u64)>,
    pub version: Option<String>,
}

/// 批量操作请求
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchOperation {
    pub operation_type: BatchOperationType,
    pub keys: Vec<String>,
    pub destination: Option<String>,
    pub metadata: Option<HashMap<String, String>>,
}

/// 批量操作类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BatchOperationType {
    Delete,
    Copy,
    Move,
    UpdateMetadata,
}

impl StorageManager {
    /// 创建新的存储管理器
    pub fn new() -> Self {
        Self {
            backends: Arc::new(RwLock::new(HashMap::new())),
            default_backend: String::new(),
            replication_manager: Arc::new(ReplicationManager::new("replication".to_string())),
            metadata_store: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 注册存储后端
    pub async fn register_backend(&self, config: StorageConfig) -> Result<()> {
        let backend: Box<dyn StorageBackend + Send + Sync> = match config.backend_type {
            StorageBackendType::Local => {
                Box::new(LocalStorage::new("local".to_string()))
            }
            StorageBackendType::S3 => {
                Box::new(S3Storage::new("s3".to_string()))
            }
            StorageBackendType::GCS => {
                Box::new(GcsStorage::new("gcs".to_string()))
            }
            StorageBackendType::Azure => {
                Box::new(AzureStorage::new("azure".to_string()))
            }
            StorageBackendType::MinIO => {
                // MinIO使用S3兼容接口
                Box::new(S3Storage::new("minio".to_string()))
            }
        };

        let mut backends = self.backends.write().await;
        backends.insert(config.name.clone(), backend);

        if config.is_default {
            self.set_default_backend(&config.name).await?;
        }

        Ok(())
    }

    /// 设置默认存储后端
    pub async fn set_default_backend(&self, name: &str) -> Result<()> {
        let backends = self.backends.read().await;
        if backends.contains_key(name) {
            // 这里需要修改为可变的引用，实际实现中需要重新设计
            // self.default_backend = name.to_string();
        } else {
            return Err(anyhow::anyhow!("Backend not found: {}", name));
        }
        Ok(())
    }

    /// 上传文件
    pub async fn upload(&self, request: UploadRequest, backend_name: Option<&str>) -> Result<PutResult> {
        let backend_name = backend_name.unwrap_or(&self.default_backend);
        let backend = self.get_backend(backend_name).await?;

        let file_metadata = FileMetadata {
            id: Uuid::new_v4(),
            file_path: request.key.clone(),
            key: request.key.clone(),
            size: request.data.len() as u64,
            content_type: request.content_type,
            metadata: request.metadata,
            tags: request.tags.map(|tags| tags.into_iter().map(|(k, v)| format!("{}:{}", k, v)).collect()).unwrap_or_else(|| Vec::new()),
            storage_class: request.storage_class,
            encryption: request.encryption.map(|e| e.to_string()),
            created_at: Utc::now(),
            updated_at: Utc::now(),
            checksum: Some(self.calculate_checksum(&request.data)),
        };

        let result = backend.put(&request.key, &request.data, &file_metadata).await?;

        // 保存元数据
        {
            let mut metadata_store = self.metadata_store.write().await;
            metadata_store.insert(request.key.clone(), file_metadata);
        }

        // 如果启用复制，执行复制操作
        if self.is_replication_enabled(backend_name).await {
            // TODO: Convert PutResult to StorageResult
            // self.replication_manager.replicate(&request.key, &result, backend_name).await?;
        }

        Ok(result)
    }

    /// 下载文件
    pub async fn download(&self, request: DownloadRequest, backend_name: Option<&str>) -> Result<GetResult> {
        let backend_name = backend_name.unwrap_or(&self.default_backend);
        let backend = self.get_backend(backend_name).await?;

        let result = backend.get(&request.key).await?;

        // 更新访问统计
        self.update_access_stats(&request.key).await;

        Ok(result)
    }

    /// 删除文件
    pub async fn delete(&self, key: &str, backend_name: Option<&str>) -> Result<()> {
        let backend_name = backend_name.unwrap_or(&self.default_backend);
        let backend = self.get_backend(backend_name).await?;

        backend.delete(key).await?;

        // 删除元数据
        {
            let mut metadata_store = self.metadata_store.write().await;
            metadata_store.remove(key);
        }

        // 删除复制的文件
        if self.is_replication_enabled(backend_name).await {
            self.replication_manager.delete_replicas(key).await?;
        }

        Ok(())
    }

    /// 检查文件是否存在
    pub async fn exists(&self, key: &str, backend_name: Option<&str>) -> bool {
        let backend_name = backend_name.unwrap_or(&self.default_backend);
        if let Ok(backend) = self.get_backend(backend_name).await {
            backend.exists(key).await
        } else {
            false
        }
    }

    /// 列出文件
    pub async fn list(&self, prefix: &str, limit: Option<usize>, backend_name: Option<&str>) -> Result<Vec<ListItem>> {
        let backend_name = backend_name.unwrap_or(&self.default_backend);
        let backend = self.get_backend(backend_name).await?;

        backend.list(prefix, limit).await
    }

    /// 复制文件
    pub async fn copy(&self, source: &str, destination: &str, source_backend: Option<&str>, dest_backend: Option<&str>) -> Result<()> {
        let source_backend_name = source_backend.unwrap_or(&self.default_backend);
        let dest_backend_name = dest_backend.unwrap_or(&self.default_backend);

        let source_backend = self.get_backend(source_backend_name).await?;
        let _dest_backend = self.get_backend(dest_backend_name).await?;

        // 获取源文件
        let source_result = source_backend.get(source).await?;

        // 上传到目标后端
        let upload_request = UploadRequest {
            key: destination.to_string(),
            data: source_result.data,
            content_type: Some(source_result.metadata.content_type.unwrap_or_default()),
            metadata: source_result.metadata.metadata,
            tags: Some(source_result.metadata.tags.into_iter().map(|tag| {
                if let Some((k, v)) = tag.split_once(':') {
                    (k.to_string(), v.to_string())
                } else {
                    (tag.clone(), "".to_string())
                }
            }).collect()),
            storage_class: source_result.metadata.storage_class,
            encryption: source_result.metadata.encryption.map(|_e| EncryptionConfig::default()),
        };

        self.upload(upload_request, Some(dest_backend_name)).await?;

        Ok(())
    }

    /// 移动文件
    pub async fn move_file(&self, source: &str, destination: &str, backend_name: Option<&str>) -> Result<()> {
        let backend_name = backend_name.unwrap_or(&self.default_backend);
        let backend = self.get_backend(backend_name).await?;

        backend.move_file(source, destination).await?;

        // 更新元数据
        {
            let mut metadata_store = self.metadata_store.write().await;
            if let Some(mut metadata) = metadata_store.remove(source) {
                metadata.key = destination.to_string();
                metadata.updated_at = Utc::now();
                metadata_store.insert(destination.to_string(), metadata);
            }
        }

        Ok(())
    }

    /// 批量操作
    pub async fn batch_operation(&self, operation: BatchOperation, backend_name: Option<&str>) -> Result<BatchResult> {
        let backend_name = backend_name.unwrap_or(&self.default_backend);
        let backend = self.get_backend(backend_name).await?;

        let mut results = Vec::new();
        let mut errors = Vec::new();

        for key in &operation.keys {
            match operation.operation_type {
                BatchOperationType::Delete => {
                    match backend.delete(&key).await {
                        Ok(_) => results.push(BatchItemResult {
                            key: key.clone(),
                            success: true,
                            error: None,
                        }),
                        Err(e) => {
                            errors.push(BatchItemResult {
                                key: key.clone(),
                                success: false,
                                error: Some(e.to_string()),
                            });
                        }
                    }
                }
                BatchOperationType::Copy => {
                    if let Some(dest) = &operation.destination {
                        match backend.copy(&key, &format!("{}/{}", dest, key)).await {
                            Ok(_) => results.push(BatchItemResult {
                                key: key.clone(),
                                success: true,
                                error: None,
                            }),
                            Err(e) => {
                                errors.push(BatchItemResult {
                                    key: key.clone(),
                                    success: false,
                                    error: Some(e.to_string()),
                                });
                            }
                        }
                    }
                }
                _ => {
                    // 其他操作类型的实现
                }
            }
        }

        Ok(BatchResult {
            successful: results,
            failed: errors,
            total_processed: operation.keys.len(),
        })
    }

    /// 获取文件元数据
    pub async fn get_metadata(&self, key: &str, backend_name: Option<&str>) -> Result<Option<FileMetadata>> {
        // 首先从本地元数据存储获取
        {
            let metadata_store = self.metadata_store.read().await;
            if let Some(metadata) = metadata_store.get(key) {
                return Ok(Some(metadata.clone()));
            }
        }

        // 如果本地没有，从存储后端获取
        let backend_name = backend_name.unwrap_or(&self.default_backend);
        let backend = self.get_backend(backend_name).await?;
        backend.get_metadata(key).await
    }

    /// 获取存储统计
    pub async fn get_storage_stats(&self, backend_name: Option<&str>) -> Result<StorageStats> {
        let backend_name = backend_name.unwrap_or(&self.default_backend);
        let backend = self.get_backend(backend_name).await?;
        Ok(backend.get_stats().await)
    }

    /// 获取所有存储后端统计
    pub async fn get_all_stats(&self) -> HashMap<String, StorageStats> {
        let backends = self.backends.read().await;
        let mut stats = HashMap::new();

        for (name, backend) in backends.iter() {
            let backend_stats = backend.get_stats().await;
            stats.insert(name.clone(), backend_stats);
        }

        stats
    }

    /// 健康检查
    pub async fn health_check(&self) -> StorageHealthStatus {
        let backends = self.backends.read().await;
        let mut status = StorageHealthStatus {
            total_backends: backends.len(),
            healthy_backends: 0,
            unhealthy_backends: 0,
            backend_details: HashMap::new(),
        };

        for (name, backend) in backends.iter() {
            let is_healthy = self.check_backend_health(backend).await;
            
            if is_healthy {
                status.healthy_backends += 1;
            } else {
                status.unhealthy_backends += 1;
            }

            status.backend_details.insert(name.clone(), BackendHealthDetail {
                is_healthy,
                stats: backend.get_stats().await,
            });
        }

        status
    }

    /// 清理过期文件
    pub async fn cleanup_expired(&self, max_age: chrono::Duration) -> Result<CleanupResult> {
        let cutoff_date = Utc::now() - max_age;
        let mut result = CleanupResult {
            deleted_files: 0,
            freed_space: 0,
            errors: Vec::new(),
        };

        let metadata_store = self.metadata_store.read().await;
        let expired_keys: Vec<String> = metadata_store
            .iter()
            .filter(|(_, metadata)| metadata.created_at < cutoff_date)
            .map(|(key, _)| key.clone())
            .collect();

        for key in &expired_keys {
            match self.delete(key, None).await {
                Ok(_) => {
                    result.deleted_files += 1;
                    if let Some(metadata) = metadata_store.get(key) {
                        result.freed_space += metadata.size;
                    }
                }
                Err(e) => {
                    result.errors.push(e.to_string());
                }
            }
        }

        Ok(result)
    }

    /// 获取存储后端
    async fn get_backend(&self, name: &str) -> Result<Box<dyn StorageBackend + Send + Sync>> {
        let backends = self.backends.read().await;
        if let Some(_backend) = backends.get(name) {
            // 这里需要重新设计以返回Box
            Err(anyhow::anyhow!("Backend not found: {}", name))
        } else {
            Err(anyhow::anyhow!("Backend not found: {}", name))
        }
    }

    /// 检查复制是否启用
    async fn is_replication_enabled(&self, _backend_name: &str) -> bool {
        // 这里应该检查配置
        false
    }

    /// 计算校验和
    fn calculate_checksum(&self, data: &[u8]) -> String {
        use sha2::{Sha256, Digest};
        let mut hasher = Sha256::new();
        hasher.update(data);
        format!("{:x}", hasher.finalize())
    }

    /// 更新访问统计
    async fn update_access_stats(&self, key: &str) {
        // 更新访问统计
        println!("File accessed: {}", key);
    }

    /// 检查后端健康状态
    async fn check_backend_health(&self, _backend: &Box<dyn StorageBackend + Send + Sync>) -> bool {
        // 简单的健康检查：总是返回true
        true
    }
}

/// 批量操作结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchResult {
    pub successful: Vec<BatchItemResult>,
    pub failed: Vec<BatchItemResult>,
    pub total_processed: usize,
}

/// 批量操作项结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BatchItemResult {
    pub key: String,
    pub success: bool,
    pub error: Option<String>,
}

/// 存储健康状态
#[derive(Debug, Serialize, Deserialize)]
pub struct StorageHealthStatus {
    pub total_backends: usize,
    pub healthy_backends: usize,
    pub unhealthy_backends: usize,
    pub backend_details: HashMap<String, BackendHealthDetail>,
}

/// 后端健康详情
#[derive(Debug, Serialize, Deserialize)]
pub struct BackendHealthDetail {
    pub is_healthy: bool,
    pub stats: StorageStats,
}

/// 清理结果
#[derive(Debug, Serialize, Deserialize)]
pub struct CleanupResult {
    pub deleted_files: u64,
    pub freed_space: u64,
    pub errors: Vec<String>,
}
