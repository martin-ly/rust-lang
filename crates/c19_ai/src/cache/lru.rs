//! LRU缓存模块
//! 
//! 提供基于最近最少使用算法的缓存实现

use chrono::{DateTime, Utc};
use uuid::Uuid;
use std::collections::{HashMap, VecDeque};
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};
use serde_json::Value;

/// LRU缓存条目
#[derive(Debug, Clone)]
struct LruCacheEntry {
    value: Value,
    created_at: Instant,
    expires_at: Option<Instant>,
    access_count: u64,
    last_accessed: Instant,
    metadata: HashMap<String, Value>,
}

/// LRU缓存统计
#[derive(Debug, Clone, Default)]
struct LruCacheStatistics {
    hits: u64,
    misses: u64,
    evictions: u64,
    total_access_time: Duration,
    access_count: u64,
}

/// LRU缓存
#[derive(Debug, Clone)]
pub struct LruCache {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
    data: Arc<RwLock<HashMap<String, LruCacheEntry>>>,
    access_order: Arc<RwLock<VecDeque<String>>>, // 维护访问顺序
    statistics: Arc<RwLock<LruCacheStatistics>>,
    max_size: usize,
    default_ttl: Duration,
}

impl LruCache {
    /// 创建新的LRU缓存
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
            data: Arc::new(RwLock::new(HashMap::new())),
            access_order: Arc::new(RwLock::new(VecDeque::new())),
            statistics: Arc::new(RwLock::new(LruCacheStatistics::default())),
            max_size: 1000,
            default_ttl: Duration::from_secs(3600),
        }
    }

    /// 创建带配置的LRU缓存
    pub fn with_config(name: String, max_size: usize, default_ttl: Duration) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
            data: Arc::new(RwLock::new(HashMap::new())),
            access_order: Arc::new(RwLock::new(VecDeque::new())),
            statistics: Arc::new(RwLock::new(LruCacheStatistics::default())),
            max_size,
            default_ttl,
        }
    }

    /// 检查条目是否过期
    fn is_expired(entry: &LruCacheEntry) -> bool {
        if let Some(expires_at) = entry.expires_at {
            expires_at < Instant::now()
        } else {
            false
        }
    }

    /// 更新访问顺序
    async fn update_access_order(&self, key: &str) {
        let mut order = self.access_order.write().await;
        
        // 移除旧的位置
        order.retain(|k| k != key);
        
        // 添加到末尾（最近访问）
        order.push_back(key.to_string());
    }

    /// 执行LRU淘汰
    async fn evict_lru(&self) -> bool {
        let mut data = self.data.write().await;
        let mut order = self.access_order.write().await;
        
        if data.len() >= self.max_size {
            // 找到最久未访问的条目
            while let Some(oldest_key) = order.pop_front() {
                if data.contains_key(&oldest_key) {
                    data.remove(&oldest_key);
                    let mut stats = self.statistics.write().await;
                    stats.evictions += 1;
                    return true;
                }
            }
        }
        false
    }

    /// 清理过期条目
    async fn cleanup_expired(&self) -> usize {
        let mut data = self.data.write().await;
        let mut order = self.access_order.write().await;
        let mut expired_keys = Vec::new();
        
        for (key, entry) in data.iter() {
            if Self::is_expired(entry) {
                expired_keys.push(key.clone());
            }
        }
        
        let count = expired_keys.len();
        for key in expired_keys {
            data.remove(&key);
            order.retain(|k| k != &key);
        }
        
        count
    }
}

#[async_trait::async_trait]
impl super::Cache for LruCache {
    async fn get(&self, key: &str) -> Option<super::CacheValue> {
        let start_time = Instant::now();
        let mut data = self.data.write().await;
        
        if let Some(entry) = data.get_mut(key) {
            if !Self::is_expired(entry) {
                // 更新访问信息
                entry.access_count += 1;
                entry.last_accessed = Instant::now();
                
                // 克隆数据以避免借用问题
                let value = entry.value.clone();
                let created_at = entry.created_at;
                let expires_at = entry.expires_at;
                let access_count = entry.access_count;
                let last_accessed = entry.last_accessed;
                let metadata = entry.metadata.clone();
                
                // 更新访问顺序
                drop(data); // 释放写锁
                self.update_access_order(key).await;
                
                // 更新统计
                let mut stats = self.statistics.write().await;
                stats.hits += 1;
                stats.access_count += 1;
                stats.total_access_time += start_time.elapsed();
                
                return Some(super::CacheValue {
                    data: value,
                    created_at,
                    expires_at,
                    access_count,
                    last_accessed,
                    metadata,
                });
            } else {
                // 过期条目，删除
                data.remove(key);
                let mut order = self.access_order.write().await;
                order.retain(|k| k != key);
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
        
        let entry = LruCacheEntry {
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
        
        // 更新访问顺序
        drop(data); // 释放写锁
        self.update_access_order(key).await;
        
        Ok(())
    }

    async fn delete(&self, key: &str) -> Result<(), anyhow::Error> {
        let mut data = self.data.write().await;
        data.remove(key);
        
        let mut order = self.access_order.write().await;
        order.retain(|k| k != key);
        
        Ok(())
    }

    async fn clear(&self) -> Result<(), anyhow::Error> {
        let mut data = self.data.write().await;
        data.clear();
        
        let mut order = self.access_order.write().await;
        order.clear();
        
        // 重置统计
        let mut stats = self.statistics.write().await;
        *stats = LruCacheStatistics::default();
        
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
        let memory_usage = data.len() * 250; // LRU缓存需要额外存储访问顺序
        
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
