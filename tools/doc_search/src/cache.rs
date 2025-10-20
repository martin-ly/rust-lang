// 索引缓存模块

use crate::DocumentIndex;
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::{Path, PathBuf};
use chrono::{DateTime, Utc};

/// 索引缓存元数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheMetadata {
    /// 缓存创建时间
    pub created_at: DateTime<Utc>,
    /// 缓存版本
    pub version: String,
    /// 源路径
    pub source_path: PathBuf,
    /// 文件哈希值（用于检测变更）
    pub file_hashes: std::collections::HashMap<String, String>,
}

/// 带元数据的索引缓存
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IndexCache {
    pub metadata: CacheMetadata,
    pub index: DocumentIndex,
}

impl IndexCache {
    /// 创建新的缓存
    pub fn new(index: DocumentIndex, source_path: PathBuf) -> Self {
        Self {
            metadata: CacheMetadata {
                created_at: Utc::now(),
                version: env!("CARGO_PKG_VERSION").to_string(),
                source_path,
                file_hashes: std::collections::HashMap::new(),
            },
            index,
        }
    }
    
    /// 保存缓存到文件
    pub fn save<P: AsRef<Path>>(&self, path: P) -> Result<(), Box<dyn std::error::Error>> {
        // 确保目录存在
        if let Some(parent) = path.as_ref().parent() {
            fs::create_dir_all(parent)?;
        }
        
        let json = serde_json::to_string(self)?;
        fs::write(path, json)?;
        Ok(())
    }
    
    /// 从文件加载缓存
    pub fn load<P: AsRef<Path>>(path: P) -> Result<Self, Box<dyn std::error::Error>> {
        let content = fs::read_to_string(path)?;
        let cache: IndexCache = serde_json::from_str(&content)?;
        Ok(cache)
    }
    
    /// 检查缓存是否有效
    pub fn is_valid(&self) -> bool {
        // 检查版本
        if self.metadata.version != env!("CARGO_PKG_VERSION") {
            return false;
        }
        
        // 检查源路径是否存在
        if !self.metadata.source_path.exists() {
            return false;
        }
        
        true
    }
    
    /// 获取默认缓存路径
    pub fn default_cache_path() -> Option<PathBuf> {
        dirs::cache_dir().map(|mut p| {
            p.push("rust-doc-search");
            p.push("index.cache");
            p
        })
    }
}

/// 计算文件哈希（简单实现）
pub fn compute_file_hash<P: AsRef<Path>>(path: P) -> Result<String, Box<dyn std::error::Error>> {
    let metadata = fs::metadata(path)?;
    let modified = metadata.modified()?;
    let size = metadata.len();
    
    // 使用修改时间和文件大小作为简单哈希
    Ok(format!("{:?}_{}", modified, size))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    
    #[test]
    fn test_cache_save_load() {
        let index = DocumentIndex {
            documents: HashMap::new(),
            keyword_index: HashMap::new(),
            module_index: HashMap::new(),
        };
        
        let cache = IndexCache::new(index, PathBuf::from("/tmp"));
        let temp_file = std::env::temp_dir().join("test_cache.json");
        
        cache.save(&temp_file).unwrap();
        let loaded = IndexCache::load(&temp_file).unwrap();
        
        assert_eq!(cache.metadata.version, loaded.metadata.version);
        std::fs::remove_file(temp_file).ok();
    }
}

