//! 缓存实现

use crate::error::NetworkResult;
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::{Arc, RwLock};
use std::time::{Duration, Instant};

/// 缓存项
#[derive(Debug, Clone)]
struct CacheItem<V> {
    value: V,
    created_at: Instant,
    last_accessed: Instant,
    access_count: u64,
}

impl<V> CacheItem<V> {
    fn new(value: V) -> Self {
        let now = Instant::now();
        Self {
            value,
            created_at: now,
            last_accessed: now,
            access_count: 1,
        }
    }

    fn access(&mut self) -> &V {
        self.last_accessed = Instant::now();
        self.access_count += 1;
        &self.value
    }

    fn age(&self) -> Duration {
        self.created_at.elapsed()
    }

    fn idle_time(&self) -> Duration {
        self.last_accessed.elapsed()
    }
}

/// 缓存统计信息
#[derive(Debug, Clone, Default)]
pub struct CacheStats {
    pub hits: u64,
    pub misses: u64,
    pub evictions: u64,
    pub total_items: usize,
    pub max_size: usize,
    pub hit_rate: f64,
    pub average_access_count: f64,
    pub oldest_item_age: Duration,
    pub newest_item_age: Duration,
}

/// 缓存实现
#[allow(dead_code)]
pub struct Cache<K, V> {
    items: Arc<RwLock<HashMap<K, CacheItem<V>>>>,
    max_size: usize,
    ttl: Option<Duration>,
    max_idle_time: Option<Duration>,
    stats: Arc<RwLock<CacheStats>>,
    created_at: Instant,
}

impl<K, V> Cache<K, V>
where
    K: Hash + Eq + Clone + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    /// 创建新的缓存
    pub fn new(max_size: usize) -> Self {
        let stats = CacheStats {
            max_size,
            ..Default::default()
        };

        Self {
            items: Arc::new(RwLock::new(HashMap::new())),
            max_size,
            ttl: None,
            max_idle_time: None,
            stats: Arc::new(RwLock::new(stats)),
            created_at: Instant::now(),
        }
    }

    /// 设置 TTL（生存时间）
    pub fn with_ttl(mut self, ttl: Duration) -> Self {
        self.ttl = Some(ttl);
        self
    }

    /// 设置最大空闲时间
    pub fn with_max_idle_time(mut self, max_idle_time: Duration) -> Self {
        self.max_idle_time = Some(max_idle_time);
        self
    }

    /// 获取值
    pub fn get(&self, key: &K) -> Option<V> {
        let mut items = self.items.write().unwrap();
        let mut stats = self.stats.write().unwrap();

        if let Some(item) = items.get_mut(key) {
            // 检查是否过期
            if self.is_expired(item) {
                items.remove(key);
                stats.misses += 1;
                stats.evictions += 1;
                return None;
            }

            // 更新访问统计
            item.access();
            stats.hits += 1;
            Some(item.value.clone())
        } else {
            stats.misses += 1;
            None
        }
    }

    /// 插入值
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        let mut items = self.items.write().unwrap();
        let mut stats = self.stats.write().unwrap();

        // 检查是否需要清理空间
        if items.len() >= self.max_size && !items.contains_key(&key) {
            self.evict_least_recently_used(&mut items, &mut stats);
        }

        let old_value = items.insert(key, CacheItem::new(value));
        stats.total_items = items.len();

        old_value.map(|item| item.value)
    }

    /// 移除值
    pub fn remove(&self, key: &K) -> Option<V> {
        let mut items = self.items.write().unwrap();
        let mut stats = self.stats.write().unwrap();

        if let Some(item) = items.remove(key) {
            stats.total_items = items.len();
            Some(item.value)
        } else {
            None
        }
    }

    /// 检查键是否存在
    pub fn contains_key(&self, key: &K) -> bool {
        let items = self.items.read().unwrap();
        items.contains_key(key)
    }

    /// 清空缓存
    pub fn clear(&self) {
        let mut items = self.items.write().unwrap();
        let mut stats = self.stats.write().unwrap();

        items.clear();
        stats.total_items = 0;
    }

    /// 获取缓存大小
    pub fn len(&self) -> usize {
        let items = self.items.read().unwrap();
        items.len()
    }

    /// 检查缓存是否为空
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> CacheStats {
        let items = self.items.read().unwrap();
        let mut stats = self.stats.read().unwrap().clone();

        // 更新统计信息
        stats.total_items = items.len();
        stats.hit_rate = if stats.hits + stats.misses > 0 {
            stats.hits as f64 / (stats.hits + stats.misses) as f64
        } else {
            0.0
        };

        // 计算平均访问次数
        if !items.is_empty() {
            let total_access = items.values().map(|item| item.access_count).sum::<u64>();
            stats.average_access_count = total_access as f64 / items.len() as f64;
        }

        // 计算最老和最新项目的年龄
        if !items.is_empty() {
            let ages: Vec<Duration> = items.values().map(|item| item.age()).collect();
            stats.oldest_item_age = ages.iter().max().copied().unwrap_or_default();
            stats.newest_item_age = ages.iter().min().copied().unwrap_or_default();
        }

        stats
    }

    /// 清理过期项
    pub async fn cleanup_expired(&self) -> NetworkResult<()> {
        let mut items = self.items.write().unwrap();
        let mut stats = self.stats.write().unwrap();

        let mut to_remove = Vec::new();
        for (key, item) in items.iter() {
            if self.is_expired(item) {
                to_remove.push(key.clone());
            }
        }

        for key in to_remove {
            items.remove(&key);
            stats.evictions += 1;
        }

        stats.total_items = items.len();
        Ok(())
    }

    /// 清理资源
    pub async fn cleanup(&self) -> NetworkResult<()> {
        self.clear();
        Ok(())
    }

    /// 检查项是否过期
    fn is_expired(&self, item: &CacheItem<V>) -> bool {
        // 检查 TTL
        if let Some(ttl) = self.ttl
            && item.age() > ttl {
                return true;
            }

        // 检查最大空闲时间
        if let Some(max_idle_time) = self.max_idle_time
            && item.idle_time() > max_idle_time {
                return true;
            }

        false
    }

    /// 驱逐最近最少使用的项
    fn evict_least_recently_used(
        &self,
        items: &mut HashMap<K, CacheItem<V>>,
        stats: &mut CacheStats,
    ) {
        if let Some((key_to_remove, _)) = items.iter().min_by_key(|(_, item)| item.last_accessed) {
            let key = key_to_remove.clone();
            items.remove(&key);
            stats.evictions += 1;
        }
    }
}

/// LRU 缓存
pub struct LruCache<K, V> {
    cache: Cache<K, V>,
}

impl<K, V> LruCache<K, V>
where
    K: Hash + Eq + Clone + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    /// 创建新的 LRU 缓存
    pub fn new(max_size: usize) -> Self {
        Self {
            cache: Cache::new(max_size),
        }
    }

    /// 获取值
    pub fn get(&self, key: &K) -> Option<V> {
        self.cache.get(key)
    }

    /// 插入值
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        self.cache.insert(key, value)
    }

    /// 移除值
    pub fn remove(&self, key: &K) -> Option<V> {
        self.cache.remove(key)
    }

    /// 获取统计信息
    pub fn get_stats(&self) -> CacheStats {
        self.cache.get_stats()
    }
}

/// 缓存管理器
pub struct CacheManager {
    caches: Arc<RwLock<HashMap<String, Arc<dyn CacheTrait + Send + Sync>>>>,
}

trait CacheTrait {
    fn get_stats(&self) -> CacheStats;
    fn cleanup(&self) -> NetworkResult<()>;
}

impl<K, V> CacheTrait for Cache<K, V>
where
    K: Hash + Eq + Clone + Send + Sync + 'static,
    V: Clone + Send + Sync + 'static,
{
    fn get_stats(&self) -> CacheStats {
        self.get_stats()
    }

    fn cleanup(&self) -> NetworkResult<()> {
        self.clear();
        Ok(())
    }
}

impl Default for CacheManager {
    fn default() -> Self {
        Self::new()
    }
}

impl CacheManager {
    /// 创建新的缓存管理器
    pub fn new() -> Self {
        Self {
            caches: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 创建缓存
    pub fn create_cache<K, V>(&self, name: String, max_size: usize) -> Arc<Cache<K, V>>
    where
        K: Hash + Eq + Clone + Send + Sync + 'static,
        V: Clone + Send + Sync + 'static,
    {
        let cache = Arc::new(Cache::new(max_size));
        let mut caches = self.caches.write().unwrap();
        caches.insert(name, cache.clone() as Arc<dyn CacheTrait + Send + Sync>);
        cache
    }

    /// 获取所有缓存的统计信息
    pub fn get_all_stats(&self) -> HashMap<String, CacheStats> {
        let caches = self.caches.read().unwrap();
        caches
            .iter()
            .map(|(name, cache)| (name.clone(), cache.get_stats()))
            .collect()
    }

    /// 清理所有缓存
    pub async fn cleanup_all(&self) -> NetworkResult<()> {
        let caches = self.caches.read().unwrap();
        for cache in caches.values() {
            cache.cleanup()?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;
    use std::time::Duration;

    #[test]
    fn test_cache_basic() {
        let cache = Cache::new(10);

        // 插入值
        cache.insert("key1".to_string(), "value1".to_string());
        assert_eq!(cache.len(), 1);

        // 获取值
        let value = cache.get(&"key1".to_string());
        assert_eq!(value, Some("value1".to_string()));

        // 获取不存在的值
        let value = cache.get(&"key2".to_string());
        assert_eq!(value, None);
    }

    #[test]
    fn test_cache_ttl() {
        let cache = Cache::new(10).with_ttl(Duration::from_millis(100));

        cache.insert("key1".to_string(), "value1".to_string());
        assert_eq!(cache.get(&"key1".to_string()), Some("value1".to_string()));

        // 等待过期
        thread::sleep(Duration::from_millis(150));
        assert_eq!(cache.get(&"key1".to_string()), None);
    }

    #[test]
    fn test_cache_max_idle_time() {
        let cache = Cache::new(10).with_max_idle_time(Duration::from_millis(100));

        cache.insert("key1".to_string(), "value1".to_string());
        assert_eq!(cache.get(&"key1".to_string()), Some("value1".to_string()));

        // 等待空闲时间过期
        thread::sleep(Duration::from_millis(150));
        assert_eq!(cache.get(&"key1".to_string()), None);
    }

    #[test]
    fn test_cache_eviction() {
        let cache = Cache::new(2);

        cache.insert("key1".to_string(), "value1".to_string());
        cache.insert("key2".to_string(), "value2".to_string());
        cache.insert("key3".to_string(), "value3".to_string());

        // 应该驱逐一个项
        assert_eq!(cache.len(), 2);

        // 检查统计信息
        let stats = cache.get_stats();
        assert!(stats.evictions > 0);
    }

    #[test]
    fn test_lru_cache() {
        let cache = LruCache::new(2);

        cache.insert("key1".to_string(), "value1".to_string());
        cache.insert("key2".to_string(), "value2".to_string());

        // 访问 key1 使其成为最近使用的
        cache.get(&"key1".to_string());

        // 插入新项，应该驱逐 key2
        cache.insert("key3".to_string(), "value3".to_string());

        assert_eq!(cache.get(&"key1".to_string()), Some("value1".to_string()));
        assert_eq!(cache.get(&"key2".to_string()), None);
        assert_eq!(cache.get(&"key3".to_string()), Some("value3".to_string()));
    }

    #[test]
    fn test_cache_stats() {
        let cache = Cache::new(10);

        cache.insert("key1".to_string(), "value1".to_string());
        cache.get(&"key1".to_string());
        cache.get(&"key2".to_string()); // 未命中

        let stats = cache.get_stats();
        assert_eq!(stats.hits, 1);
        assert_eq!(stats.misses, 1);
        assert_eq!(stats.hit_rate, 0.5);
    }

    #[test]
    fn test_cache_manager() {
        let manager = CacheManager::new();

        let cache1 = manager.create_cache("cache1".to_string(), 10);
        let cache2 = manager.create_cache("cache2".to_string(), 20);

        cache1.insert("key1".to_string(), "value1".to_string());
        cache2.insert("key2".to_string(), "value2".to_string());

        let all_stats = manager.get_all_stats();
        assert_eq!(all_stats.len(), 2);
        assert!(all_stats.contains_key("cache1"));
        assert!(all_stats.contains_key("cache2"));
    }
}
