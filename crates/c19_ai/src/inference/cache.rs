//! 推理缓存模块
//! 
//! 提供推理结果的缓存管理

use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use std::time::{Duration, Instant};
use sha2::{Sha256, Digest};

/// 缓存条目
#[derive(Debug, Clone)]
#[allow(unused)]
struct CacheEntry {
    response: super::InferenceResponse,
    created_at: Instant,
    expires_at: Option<Instant>,
    access_count: u64,
    last_accessed: Instant,
}

/// 推理缓存统计
#[derive(Debug, Clone, Default)]
#[allow(unused)]
struct CacheStatistics {
    hits: u64,
    misses: u64,
    evictions: u64,
    total_access_time: Duration,
    access_count: u64,
}

/// 推理缓存
#[derive(Debug)]
#[allow(unused)]
pub struct InferenceCache {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
    cache: Arc<RwLock<HashMap<String, CacheEntry>>>,
    statistics: Arc<RwLock<CacheStatistics>>,
    max_size: usize,
    default_ttl: Duration,
}

impl InferenceCache {
    /// 创建新的推理缓存
    pub fn new(name: String) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
            cache: Arc::new(RwLock::new(HashMap::new())),
            statistics: Arc::new(RwLock::new(CacheStatistics::default())),
            max_size: 1000,
            default_ttl: Duration::from_secs(3600),
        }
    }

    /// 创建带配置的推理缓存
    pub fn with_config(name: String, max_size: usize, default_ttl: Duration) -> Self {
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
            cache: Arc::new(RwLock::new(HashMap::new())),
            statistics: Arc::new(RwLock::new(CacheStatistics::default())),
            max_size,
            default_ttl,
        }
    }

    /// 生成请求的缓存键
    fn generate_cache_key(&self, request: &super::InferenceRequest) -> String {
        let mut hasher = Sha256::new();
        hasher.update(request.model_id.as_bytes());
        hasher.update(serde_json::to_string(&request.input_data).unwrap_or_default().as_bytes());
        if let Some(params) = &request.parameters {
            hasher.update(serde_json::to_string(params).unwrap_or_default().as_bytes());
        }
        format!("{:x}", hasher.finalize())
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
    #[allow(unused)]
    async fn cleanup_expired(&self) -> usize {
        let mut cache = self.cache.write().await;
        let mut expired_keys = Vec::new();
        
        for (key, entry) in cache.iter() {
            if Self::is_expired(entry) {
                expired_keys.push(key.clone());
            }
        }
        
        let count = expired_keys.len();
        for key in expired_keys {
            cache.remove(&key);
        }
        
        count
    }

    /// 执行LRU淘汰
    #[allow(unused)]
    async fn evict_lru(&self) -> bool {
        let mut cache = self.cache.write().await;
        if cache.len() >= self.max_size {
            // 找到最久未访问的条目
            let mut oldest_key = None;
            let mut oldest_time = Instant::now();
            
            for (key, entry) in cache.iter() {
                if entry.last_accessed < oldest_time {
                    oldest_time = entry.last_accessed;
                    oldest_key = Some(key.clone());
                }
            }
            
            if let Some(key) = oldest_key {
                cache.remove(&key);
                let mut stats = self.statistics.write().await;
                stats.evictions += 1;
                return true;
            }
        }
        false
    }

    /// 获取缓存的推理结果
    #[allow(unused)]
    pub async fn get(&self, request: &super::InferenceRequest) -> Option<super::InferenceResponse> {
        let start_time = Instant::now();
        let cache_key = self.generate_cache_key(request);
        
        let mut cache = self.cache.write().await;
        if let Some(entry) = cache.get_mut(&cache_key) {
            if !Self::is_expired(entry) {
                // 更新访问信息
                entry.access_count += 1;
                entry.last_accessed = Instant::now();
                
                // 更新统计
                let mut stats = self.statistics.write().await;
                stats.hits += 1;
                stats.access_count += 1;
                stats.total_access_time += start_time.elapsed();
                
                return Some(entry.response.clone());
            } else {
                // 过期条目，删除
                cache.remove(&cache_key);
            }
        }
        
        // 未命中
        let mut stats = self.statistics.write().await;
        stats.misses += 1;
        stats.access_count += 1;
        stats.total_access_time += start_time.elapsed();
        
        None
    }

    /// 缓存推理结果
    #[allow(unused)]
    pub async fn put(&self, request: &super::InferenceRequest, response: &super::InferenceResponse) {
        let cache_key = self.generate_cache_key(request);
        let now = Instant::now();
        
        let entry = CacheEntry {
            response: response.clone(),
            created_at: now,
            expires_at: Some(now + self.default_ttl),
            access_count: 1,
            last_accessed: now,
        };
        
        // 检查是否需要淘汰
        if self.cache.read().await.len() >= self.max_size {
            self.evict_lru().await;
        }
        
        let mut cache = self.cache.write().await;
        cache.insert(cache_key, entry);
    }

    /// 删除缓存条目
    #[allow(unused)]
    pub async fn remove(&self, request: &super::InferenceRequest) {
        let cache_key = self.generate_cache_key(request);
        let mut cache = self.cache.write().await;
        cache.remove(&cache_key);
    }

    /// 清空缓存
    #[allow(unused)]
    pub async fn clear(&self) {
        let mut cache = self.cache.write().await;
        cache.clear();
        
        // 重置统计
        let mut stats = self.statistics.write().await;
        *stats = CacheStatistics::default();
    }

    /// 获取缓存状态
    #[allow(unused)]
    pub async fn get_status(&self) -> CacheStatus {
        let cache = self.cache.read().await;
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
        
        CacheStatus {
            cache_size: cache.len(),
            max_size: self.max_size,
            hit_rate,
            hits: stats.hits,
            misses: stats.misses,
            evictions: stats.evictions,
            average_access_time_ms: average_access_time.as_millis() as f64,
        }
    }

    /// 获取缓存大小
    #[allow(unused)]
    pub async fn size(&self) -> usize {
        let cache = self.cache.read().await;
        cache.len()
    }

    /// 检查缓存是否为空
    #[allow(unused)]
    pub async fn is_empty(&self) -> bool {
        self.size().await == 0
    }

    /// 预热缓存
    pub async fn warmup(&self, requests: Vec<super::InferenceRequest>, responses: Vec<super::InferenceResponse>) {
        if requests.len() != responses.len() {
            tracing::warn!("Requests and responses length mismatch for cache warmup");
            return;
        }
        
        for (request, response) in requests.into_iter().zip(responses.into_iter()) {
            self.put(&request, &response).await;
        }
    }
}

/// 缓存状态
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(unused)]
pub struct CacheStatus {
    pub cache_size: usize,
    pub max_size: usize,
    pub hit_rate: f64,
    pub hits: u64,
    pub misses: u64,
    pub evictions: u64,
    pub average_access_time_ms: f64,
}
