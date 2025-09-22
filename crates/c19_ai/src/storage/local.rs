//! 本地存储模块
//! 
//! 提供本地文件系统存储实现

use chrono::{DateTime, Utc};
use uuid::Uuid;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use tokio::sync::RwLock;
use std::collections::HashMap;

use super::manager::{StorageBackend, PutResult, GetResult, ListItem, StorageStats};
use super::metadata::FileMetadata;

/// 本地存储统计
#[derive(Debug, Clone, Default)]
struct LocalStorageStats {
    total_files: u64,
    total_size: u64,
    read_operations: u64,
    write_operations: u64,
    error_count: u64,
    last_updated: DateTime<Utc>,
}

/// 本地存储
#[derive(Debug)]
pub struct LocalStorage {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
    base_path: PathBuf,
    stats: Arc<RwLock<LocalStorageStats>>,
    file_metadata: Arc<RwLock<HashMap<String, FileMetadata>>>,
}

impl LocalStorage {
    /// 创建新的本地存储
    pub fn new(name: String) -> Self {
        let base_path = std::env::temp_dir().join("c19_ai_storage").join(&name);
        
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
            base_path,
            stats: Arc::new(RwLock::new(LocalStorageStats::default())),
            file_metadata: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 创建带路径的本地存储
    pub fn with_path(name: String, base_path: PathBuf) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
            base_path,
            stats: Arc::new(RwLock::new(LocalStorageStats::default())),
            file_metadata: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 确保目录存在
    async fn ensure_directory_exists(&self, path: &Path) -> anyhow::Result<()> {
        if let Some(parent) = path.parent() {
            tokio::fs::create_dir_all(parent).await?;
        }
        Ok(())
    }

    /// 获取文件的完整路径
    fn get_file_path(&self, key: &str) -> PathBuf {
        self.base_path.join(key)
    }

    /// 更新统计信息
    async fn update_stats<F>(&self, f: F)
    where
        F: FnOnce(&mut LocalStorageStats),
    {
        let mut stats = self.stats.write().await;
        f(&mut stats);
        stats.last_updated = Utc::now();
    }
}

#[async_trait::async_trait]
impl StorageBackend for LocalStorage {
    async fn put(&self, key: &str, data: &[u8], metadata: &FileMetadata) -> anyhow::Result<PutResult> {
        let file_path = self.get_file_path(key);
        
        // 确保目录存在
        self.ensure_directory_exists(&file_path).await?;
        
        // 写入文件
        tokio::fs::write(&file_path, data).await?;
        
        // 保存元数据
        {
            let mut file_metadata = self.file_metadata.write().await;
            file_metadata.insert(key.to_string(), metadata.clone());
        }
        
        // 更新统计
        self.update_stats(|stats| {
            stats.write_operations += 1;
            stats.total_size += data.len() as u64;
            stats.total_files += 1;
        }).await;
        
        Ok(PutResult {
            key: key.to_string(),
            size: data.len() as u64,
            etag: format!("{:x}", md5::compute(data)),
            version: None,
            storage_class: "STANDARD".to_string(),
            created_at: Utc::now(),
        })
    }

    async fn get(&self, key: &str) -> anyhow::Result<GetResult> {
        let file_path = self.get_file_path(key);
        
        // 读取文件
        let data = tokio::fs::read(&file_path).await?;
        
        // 获取元数据
        let metadata = {
            let _file_metadata = self.file_metadata.read().await;
            file_metadata.get(key).cloned().unwrap_or_else(|| {
                FileMetadata::new(key.to_string(), data.len() as u64)
            })
        };
        
        // 获取文件修改时间
        let file_metadata = tokio::fs::metadata(&file_path).await?;
        let last_modified = file_metadata.modified()?.into();
        
        // 更新统计
        self.update_stats(|stats| {
            stats.read_operations += 1;
        }).await;
        
        let etag = format!("{:x}", md5::compute(&data));
        
        Ok(GetResult {
            data,
            metadata,
            etag,
            last_modified,
        })
    }

    async fn delete(&self, key: &str) -> anyhow::Result<()> {
        let file_path = self.get_file_path(key);
        
        // 删除文件
        if file_path.exists() {
            tokio::fs::remove_file(&file_path).await?;
        }
        
        // 删除元数据
        {
            let mut file_metadata = self.file_metadata.write().await;
            if let Some(metadata) = file_metadata.remove(key) {
                self.update_stats(|stats| {
                    stats.total_size = stats.total_size.saturating_sub(metadata.size);
                    stats.total_files = stats.total_files.saturating_sub(1);
                }).await;
            }
        }
        
        Ok(())
    }

    async fn exists(&self, key: &str) -> bool {
        let file_path = self.get_file_path(key);
        file_path.exists()
    }

    async fn list(&self, prefix: &str, limit: Option<usize>) -> anyhow::Result<Vec<ListItem>> {
        let mut items = Vec::new();
        let mut count = 0;
        
        // 遍历目录
        let mut entries = tokio::fs::read_dir(&self.base_path).await?;
        while let Some(entry) = entries.next_entry().await? {
            if let Some(limit) = limit {
                if count >= limit {
                    break;
                }
            }
            
            let path = entry.path();
            if let Some(file_name) = path.file_name().and_then(|n| n.to_str()) {
                if file_name.starts_with(prefix) {
                    let metadata = entry.metadata().await?;
                    if metadata.is_file() {
                        items.push(ListItem {
                            key: file_name.to_string(),
                            size: metadata.len(),
                            last_modified: metadata.modified()?.into(),
                            etag: format!("{:x}", md5::compute(file_name.as_bytes())),
                            storage_class: "STANDARD".to_string(),
                        });
                        count += 1;
                    }
                }
            }
        }
        
        Ok(items)
    }

    async fn copy(&self, source: &str, destination: &str) -> anyhow::Result<()> {
        let source_path = self.get_file_path(source);
        let dest_path = self.get_file_path(destination);
        
        // 确保目标目录存在
        self.ensure_directory_exists(&dest_path).await?;
        
        // 复制文件
        tokio::fs::copy(&source_path, &dest_path).await?;
        
        // 复制元数据
        {
            let mut file_metadata = self.file_metadata.write().await;
            if let Some(metadata) = file_metadata.get(source).cloned() {
                let mut new_metadata = metadata;
                new_metadata.key = destination.to_string();
                new_metadata.updated_at = Utc::now();
                file_metadata.insert(destination.to_string(), new_metadata);
            }
        }
        
        Ok(())
    }

    async fn move_file(&self, source: &str, destination: &str) -> anyhow::Result<()> {
        let source_path = self.get_file_path(source);
        let dest_path = self.get_file_path(destination);
        
        // 确保目标目录存在
        self.ensure_directory_exists(&dest_path).await?;
        
        // 移动文件
        tokio::fs::rename(&source_path, &dest_path).await?;
        
        // 更新元数据
        {
            let mut file_metadata = self.file_metadata.write().await;
            if let Some(mut metadata) = file_metadata.remove(source) {
                metadata.key = destination.to_string();
                metadata.updated_at = Utc::now();
                file_metadata.insert(destination.to_string(), metadata);
            }
        }
        
        Ok(())
    }

    async fn get_metadata(&self, key: &str) -> anyhow::Result<Option<FileMetadata>> {
        let _file_metadata = self.file_metadata.read().await;
        Ok(file_metadata.get(key).cloned())
    }

    async fn get_stats(&self) -> StorageStats {
        let stats = self.stats.read().await;
        let _file_metadata = self.file_metadata.read().await;
        
        // 计算可用空间（简单估算）
        let available_space = 1024 * 1024 * 1024; // 1GB 默认值
        
        StorageStats {
            total_files: stats.total_files,
            total_size: stats.total_size,
            available_space,
            used_space: stats.total_size,
            read_operations: stats.read_operations,
            write_operations: stats.write_operations,
            error_count: stats.error_count,
            last_updated: stats.last_updated,
        }
    }
}
