// 存储元数据模块
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

/// 存储元数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StorageMetadata {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
}

impl StorageMetadata {
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
        }
    }
}

/// 文件元数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileMetadata {
    pub id: Uuid,
    pub file_path: String,
    pub size: u64,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    pub content_type: Option<String>,
    pub checksum: Option<String>,
    pub metadata: std::collections::HashMap<String, String>,
    pub tags: Vec<String>,
    pub storage_class: Option<String>,
    pub encryption: Option<String>,
    pub key: String,
}

impl FileMetadata {
    pub fn new(file_path: String, size: u64) -> Self {
        Self {
            id: Uuid::new_v4(),
            file_path: file_path.clone(),
            size,
            created_at: Utc::now(),
            updated_at: Utc::now(),
            content_type: None,
            checksum: None,
            metadata: std::collections::HashMap::new(),
            tags: Vec::new(),
            storage_class: None,
            encryption: None,
            key: file_path,
        }
    }
}
