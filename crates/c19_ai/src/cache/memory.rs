//! 内存缓存模块
//! 
//! 提供高性能的内存缓存实现，支持TTL和统计功能

// 移除未使用的导入
use chrono::{DateTime, Utc};
use uuid::Uuid;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};
use serde_json::Value;

/// 内存缓存条目
#[derive(Debug, Clone)]
struct CacheEntry {
    value: Value,
    created_at: Instant,
    expires_at: Option<Instant>,
    access_count: u64,
    last_accessed: Instant,
    metadata: HashMap<String, Value>,
}

/// 内存缓存统计
#[derive(Debug, Clone, Default)]
struct CacheStatistics {
    hits: u64,
    misses: u64,
    evictions: u64,
    total_access_time: Duration,
    access_count: u64,
}

/// 内存缓存
#[derive(Debug, Clone)]
pub struct MemoryCache {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
    data: Arc<RwLock<HashMap<String, CacheEntry>>>,
    statistics: Arc<RwLock<CacheStatistics>>,
    max_size: usize,
    default_ttl: Duration,
}

impl MemoryCache {
    /// 创建新的内存缓存
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
            data: Arc::new(RwLock::new(HashMap::new())),
            statistics: Arc::new(RwLock::new(CacheStatistics::default())),
            max_size: 1000,
            default_ttl: Duration::from_secs(3600),
        }
    }

    /// 创建带配置的内存缓存
    pub fn with_config(name: String, max_size: usize, default_ttl: Duration) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
            data: Arc::new(RwLock::new(HashMap::new())),
            statistics: Arc::new(RwLock::new(CacheStatistics::default())),
            max_size,
            default_ttl,
        }
    }

    /// 检查条目是否过期
    fn is_expired(entry: &CacheEntry) -> bool {
        if let Some(expires_at) = entry.expires_at {
            expires_at < Instant::now()
        } else {
            false
        }
    }

    /// 清理过期条目
    async fn cleanup_expired(&self) -> usize {
        let mut data = self.data.write().await;
        let mut expired_keys = Vec::new();
        
        for (key, entry) in data.iter() {
            if Self::is_expired(entry) {
                expired_keys.push(key.clone());
            }
        }
        
        let count = expired_keys.len();
        for key in expired_keys {
            data.remove(&key);
        }
        
        count
    }

    /// 执行LRU淘汰
    async fn evict_lru(&self) -> bool {
        let mut data = self.data.write().await;
        if data.len() >= self.max_size {
            // 找到最久未访问的条目
            let mut oldest_key = None;
            let mut oldest_time = Instant::now();
            
            for (key, entry) in data.iter() {
                if entry.last_accessed < oldest_time {
                    oldest_time = entry.last_accessed;
                    oldest_key = Some(key.clone());
                }
            }
            
            if let Some(key) = oldest_key {
                data.remove(&key);
                let mut stats = self.statistics.write().await;
                stats.evictions += 1;
                return true;
            }
        }
        false
    }
}

#[async_trait::async_trait]
impl super::Cache for MemoryCache {
    async fn get(&self, key: &str) -> Option<super::CacheValue> {
        let start_time = Instant::now();
        let mut data = self.data.write().await;
        
        if let Some(entry) = data.get_mut(key) {
            if !Self::is_expired(entry) {
                // 更新访问信息
                entry.access_count += 1;
                entry.last_accessed = Instant::now();
                
                // 更新统计
                let mut stats = self.statistics.write().await;
                stats.hits += 1;
                stats.access_count += 1;
                stats.total_access_time += start_time.elapsed();
                
                return Some(super::CacheValue {
                    data: entry.value.clone(),
                    created_at: entry.created_at,
                    expires_at: entry.expires_at,
                    access_count: entry.access_count,
                    last_accessed: entry.last_accessed,
                    metadata: entry.metadata.clone(),
                });
            } else {
                // 过期条目，删除
                data.remove(key);
            }
        }
        
        // 未命中
        let mut stats = self.statistics.write().await;
        stats.misses += 1;
        stats.access_count += 1;
        stats.total_access_time += start_time.elapsed();
        
        None
    }

    async fn set(&self, key: &str, value: super::CacheValue, ttl: Option<Duration>) -> Result<(), anyhow::Error> {
        let actual_ttl = ttl.unwrap_or(self.default_ttl);
        let now = Instant::now();
        
        let entry = CacheEntry {
            value: value.data,
            created_at: value.created_at,
            expires_at: Some(now + actual_ttl),
            access_count: value.access_count,
            last_accessed: now,
            metadata: value.metadata,
        };
        
        // 检查是否需要淘汰
        if self.data.read().await.len() >= self.max_size && !self.data.read().await.contains_key(key) {
            self.evict_lru().await;
        }
        
        let mut data = self.data.write().await;
        data.insert(key.to_string(), entry);
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<(), anyhow::Error> {
        let mut data = self.data.write().await;
        data.remove(key);
        Ok(())
    }

    async fn clear(&self) -> Result<(), anyhow::Error> {
        let mut data = self.data.write().await;
        data.clear();
        
        // 重置统计
        let mut stats = self.statistics.write().await;
        *stats = CacheStatistics::default();
        
        Ok(())
    }

    async fn exists(&self, key: &str) -> bool {
        let data = self.data.read().await;
        if let Some(entry) = data.get(key) {
            !Self::is_expired(entry)
        } else {
            false
        }
    }

    async fn size(&self) -> usize {
        let data = self.data.read().await;
        data.len()
    }

    async fn keys(&self) -> Vec<String> {
        let data = self.data.read().await;
        data.keys().cloned().collect()
    }

    async fn get_stats(&self) -> super::CacheStats {
        let data = self.data.read().await;
        let stats = self.statistics.read().await;
        
        let hit_rate = if stats.access_count > 0 {
            stats.hits as f64 / stats.access_count as f64
        } else {
            0.0
        };
        
        let average_access_time = if stats.access_count > 0 {
            Duration::from_nanos(stats.total_access_time.as_nanos() as u64 / stats.access_count as u64)
        } else {
            Duration::from_millis(0)
        };
        
        // 估算内存使用量
        let memory_usage = data.len() * 200; // 简单估算每个条目200字节
        
        super::CacheStats {
            hits: stats.hits,
            misses: stats.misses,
            evictions: stats.evictions,
            size: data.len(),
            memory_usage,
            hit_rate,
            average_access_time,
        }
    }
}
