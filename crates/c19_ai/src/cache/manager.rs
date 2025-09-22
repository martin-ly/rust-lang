//! 缓存管理器
//! 
//! 提供统一的缓存接口和多级缓存管理

use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};
// 移除未使用的导入

use super::memory::MemoryCache;
use super::lru::LruCache;
use super::ttl::TtlCache;

/// 缓存管理器
pub struct CacheManager {
    caches: Arc<RwLock<HashMap<String, Box<dyn Cache + Send + Sync>>>>,
    default_ttl: Duration,
    max_memory_size: usize,
}

/// 缓存接口
#[async_trait::async_trait]
pub trait Cache {
    async fn get(&self, key: &str) -> Option<CacheValue>;
    async fn set(&self, key: &str, value: CacheValue, ttl: Option<Duration>) -> Result<()>;
    async fn delete(&self, key: &str) -> Result<()>;
    async fn exists(&self, key: &str) -> bool;
    async fn clear(&self) -> Result<()>;
    async fn size(&self) -> usize;
    async fn keys(&self) -> Vec<String>;
    async fn get_stats(&self) -> CacheStats;
}

/// 缓存值
#[derive(Debug, Clone)]
pub struct CacheValue {
    pub data: serde_json::Value,
    pub created_at: Instant,
    pub expires_at: Option<Instant>,
    pub access_count: u64,
    pub last_accessed: Instant,
    pub metadata: HashMap<String, serde_json::Value>,
}

/// 缓存统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheStats {
    pub hits: u64,
    pub misses: u64,
    pub evictions: u64,
    pub size: usize,
    pub memory_usage: usize,
    pub hit_rate: f64,
    pub average_access_time: Duration,
}

/// 缓存配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheConfig {
    pub cache_type: CacheType,
    pub max_size: usize,
    pub default_ttl: Duration,
    pub eviction_policy: EvictionPolicy,
    pub compression_enabled: bool,
    pub serialization_format: SerializationFormat,
}

/// 缓存类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CacheType {
    Memory,
    Lru,
    Ttl,
    Redis,
    Hybrid,
}

/// 淘汰策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EvictionPolicy {
    Lru, // Least Recently Used
    Lfu, // Least Frequently Used
    Ttl, // Time To Live
    Random,
    Size,
}

/// 序列化格式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum SerializationFormat {
    Json,
    Bincode,
    MessagePack,
    Cbor,
}

impl CacheManager {
    /// 创建新的缓存管理器
    pub fn new(default_ttl: Duration, max_memory_size: usize) -> Self {
        Self {
            caches: Arc::new(RwLock::new(HashMap::new())),
            default_ttl,
            max_memory_size,
        }
    }

    /// 创建缓存
    pub async fn create_cache(&self, name: String, config: CacheConfig) -> Result<()> {
        let cache: Box<dyn Cache + Send + Sync> = match config.cache_type {
            CacheType::Memory => {
                Box::new(MemoryCache::new("memory".to_string()))
            }
            CacheType::Lru => {
                Box::new(LruCache::new("lru".to_string()))
            }
            CacheType::Ttl => {
                Box::new(TtlCache::new("ttl".to_string()))
            }
            CacheType::Redis => {
                // TODO: 实现Redis缓存
                return Err(anyhow::anyhow!("Redis cache not implemented yet"));
            }
            CacheType::Hybrid => {
                // TODO: 实现混合缓存
                return Err(anyhow::anyhow!("Hybrid cache not implemented yet"));
            }
        };

        let mut caches = self.caches.write().await;
        caches.insert(name, cache);
        Ok(())
    }

    /// 获取缓存
    pub async fn get_cache(&self, _name: &str) -> Option<Box<dyn Cache + Send + Sync>> {
        let _caches = self.caches.read().await;
        // TODO: 修复类型转换问题
        // 当前实现存在类型系统限制，需要重新设计缓存存储结构
        None
    }

    /// 设置缓存值
    pub async fn set(&self, cache_name: &str, key: &str, value: serde_json::Value, ttl: Option<Duration>) -> Result<()> {
        let caches = self.caches.read().await;
        if let Some(cache) = caches.get(cache_name) {
            let cache_value = CacheValue {
                data: value,
                created_at: Instant::now(),
                expires_at: ttl.map(|t| Instant::now() + t),
                access_count: 0,
                last_accessed: Instant::now(),
                metadata: HashMap::new(),
            };
            cache.set(key, cache_value, ttl).await?;
        } else {
            return Err(anyhow::anyhow!("Cache not found: {}", cache_name));
        }
        Ok(())
    }

    /// 获取缓存值
    pub async fn get(&self, cache_name: &str, key: &str) -> Option<serde_json::Value> {
        let caches = self.caches.read().await;
        if let Some(cache) = caches.get(cache_name) {
            cache.get(key).await.map(|v| v.data)
        } else {
            None
        }
    }

    /// 删除缓存值
    pub async fn delete(&self, cache_name: &str, key: &str) -> Result<()> {
        let caches = self.caches.read().await;
        if let Some(cache) = caches.get(cache_name) {
            cache.delete(key).await?;
        } else {
            return Err(anyhow::anyhow!("Cache not found: {}", cache_name));
        }
        Ok(())
    }

    /// 检查缓存是否存在
    pub async fn exists(&self, cache_name: &str, key: &str) -> bool {
        let caches = self.caches.read().await;
        if let Some(cache) = caches.get(cache_name) {
            cache.exists(key).await
        } else {
            false
        }
    }

    /// 清空缓存
    pub async fn clear(&self, cache_name: &str) -> Result<()> {
        let caches = self.caches.read().await;
        if let Some(cache) = caches.get(cache_name) {
            cache.clear().await?;
        } else {
            return Err(anyhow::anyhow!("Cache not found: {}", cache_name));
        }
        Ok(())
    }

    /// 获取缓存统计
    pub async fn get_stats(&self, cache_name: &str) -> Option<CacheStats> {
        let caches = self.caches.read().await;
        if let Some(cache) = caches.get(cache_name) {
            Some(cache.get_stats().await)
        } else {
            None
        }
    }

    /// 获取所有缓存统计
    pub async fn get_all_stats(&self) -> HashMap<String, CacheStats> {
        let caches = self.caches.read().await;
        let mut stats = HashMap::new();
        
        for (name, cache) in caches.iter() {
            stats.insert(name.clone(), cache.get_stats().await);
        }
        
        stats
    }

    /// 预热缓存
    pub async fn warmup(&self, cache_name: &str, data: HashMap<String, serde_json::Value>) -> Result<()> {
        for (key, value) in data {
            self.set(cache_name, &key, value, Some(self.default_ttl)).await?;
        }
        Ok(())
    }

    /// 批量操作
    pub async fn batch_set(&self, cache_name: &str, items: HashMap<String, serde_json::Value>, ttl: Option<Duration>) -> Result<()> {
        for (key, value) in items {
            self.set(cache_name, &key, value, ttl).await?;
        }
        Ok(())
    }

    /// 批量获取
    pub async fn batch_get(&self, cache_name: &str, keys: Vec<String>) -> HashMap<String, Option<serde_json::Value>> {
        let mut results = HashMap::new();
        
        for key in keys {
            let value = self.get(cache_name, &key).await;
            results.insert(key, value);
        }
        
        results
    }

    /// 缓存模式匹配
    pub async fn get_by_pattern(&self, cache_name: &str, pattern: &str) -> HashMap<String, serde_json::Value> {
        let caches = self.caches.read().await;
        if let Some(cache) = caches.get(cache_name) {
            let keys = cache.keys().await;
            let mut results = HashMap::new();
            
            for key in keys {
                if key.contains(pattern) {
                    if let Some(value) = cache.get(&key).await {
                        results.insert(key, value.data);
                    }
                }
            }
            
            results
        } else {
            HashMap::new()
        }
    }

    /// 缓存健康检查
    pub async fn health_check(&self) -> CacheHealthStatus {
        let caches = self.caches.read().await;
        let mut status = CacheHealthStatus {
            total_caches: caches.len(),
            healthy_caches: 0,
            unhealthy_caches: 0,
            total_memory_usage: 0,
            cache_details: HashMap::new(),
        };

        for (name, cache) in caches.iter() {
            let stats = cache.get_stats().await;
            let is_healthy = stats.hit_rate > 0.5 && stats.memory_usage < self.max_memory_size;
            
            if is_healthy {
                status.healthy_caches += 1;
            } else {
                status.unhealthy_caches += 1;
            }
            
            status.total_memory_usage += stats.memory_usage;
            status.cache_details.insert(name.clone(), CacheDetail {
                is_healthy,
                stats,
            });
        }

        status
    }

    /// 自动清理过期缓存
    pub async fn cleanup_expired(&self) -> Result<CleanupResult> {
        let caches = self.caches.read().await;
        let mut result = CleanupResult {
            total_cleaned: 0,
            memory_freed: 0,
            caches_processed: 0,
        };

        for (_name, cache) in caches.iter() {
            let keys = cache.keys().await;
            let mut expired_keys = Vec::new();

            for key in keys {
                if let Some(value) = cache.get(&key).await {
                    if let Some(expires_at) = value.expires_at {
                        if expires_at < Instant::now() {
                            expired_keys.push(key);
                        }
                    }
                }
            }

            for key in expired_keys {
                cache.delete(&key).await?;
                result.total_cleaned += 1;
            }

            result.caches_processed += 1;
        }

        Ok(result)
    }
}

/// 缓存健康状态
#[derive(Debug, Serialize, Deserialize)]
pub struct CacheHealthStatus {
    pub total_caches: usize,
    pub healthy_caches: usize,
    pub unhealthy_caches: usize,
    pub total_memory_usage: usize,
    pub cache_details: HashMap<String, CacheDetail>,
}

/// 缓存详情
#[derive(Debug, Serialize, Deserialize)]
pub struct CacheDetail {
    pub is_healthy: bool,
    pub stats: CacheStats,
}

/// 清理结果
#[derive(Debug, Serialize, Deserialize)]
pub struct CleanupResult {
    pub total_cleaned: u64,
    pub memory_freed: usize,
    pub caches_processed: usize,
}

impl CacheValue {
    /// 创建新的缓存值
    pub fn new(data: serde_json::Value, ttl: Option<Duration>) -> Self {
        let now = Instant::now();
        Self {
            data,
            created_at: now,
            expires_at: ttl.map(|t| now + t),
            access_count: 0,
            last_accessed: now,
            metadata: HashMap::new(),
        }
    }

    /// 检查是否过期
    pub fn is_expired(&self) -> bool {
        if let Some(expires_at) = self.expires_at {
            expires_at < Instant::now()
        } else {
            false
        }
    }

    /// 更新访问信息
    pub fn update_access(&mut self) {
        self.access_count += 1;
        self.last_accessed = Instant::now();
    }

    /// 获取剩余生存时间
    pub fn time_to_live(&self) -> Option<Duration> {
        if let Some(expires_at) = self.expires_at {
            let now = Instant::now();
            if expires_at > now {
                Some(expires_at - now)
            } else {
                Some(Duration::from_secs(0))
            }
        } else {
            None
        }
    }
}

impl Default for CacheStats {
    fn default() -> Self {
        Self {
            hits: 0,
            misses: 0,
            evictions: 0,
            size: 0,
            memory_usage: 0,
            hit_rate: 0.0,
            average_access_time: Duration::from_millis(0),
        }
    }
}
