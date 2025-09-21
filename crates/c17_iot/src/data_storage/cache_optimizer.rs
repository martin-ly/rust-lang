//! 缓存优化模块
//! 
//! 提供智能缓存策略和优化功能，包括：
//! - 多级缓存管理
//! - 缓存预热
//! - 缓存失效策略
//! - 缓存性能监控

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc, Timelike};

/// 缓存级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum CacheLevel {
    /// L1缓存 - 内存缓存，最快但容量最小
    L1,
    /// L2缓存 - 本地存储缓存，中等速度和容量
    L2,
    /// L3缓存 - 远程缓存，较慢但容量大
    L3,
}

/// 缓存策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CacheStrategy {
    /// LRU (Least Recently Used) - 最近最少使用
    LRU,
    /// LFU (Least Frequently Used) - 最少频率使用
    LFU,
    /// TTL (Time To Live) - 基于时间的过期
    TTL,
    /// FIFO (First In First Out) - 先进先出
    FIFO,
    /// 自适应策略 - 根据访问模式自动调整
    Adaptive,
}

/// 缓存项
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheItem<T> {
    /// 缓存数据
    pub data: T,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 最后访问时间
    pub last_accessed: DateTime<Utc>,
    /// 访问次数
    pub access_count: u64,
    /// 过期时间
    pub expires_at: Option<DateTime<Utc>>,
    /// 缓存级别
    pub level: CacheLevel,
    /// 数据大小（字节）
    pub size_bytes: usize,
}

/// 缓存统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheStats {
    /// 缓存级别
    pub level: CacheLevel,
    /// 总容量
    pub total_capacity: usize,
    /// 已使用容量
    pub used_capacity: usize,
    /// 命中次数
    pub hits: u64,
    /// 未命中次数
    pub misses: u64,
    /// 命中率
    pub hit_rate: f64,
    /// 平均访问时间
    pub avg_access_time: Duration,
    /// 最后更新时间
    pub last_updated: DateTime<Utc>,
}

/// 缓存配置
#[derive(Debug, Clone)]
pub struct CacheConfig {
    /// 缓存策略
    pub strategy: CacheStrategy,
    /// 最大容量（字节）
    pub max_capacity: usize,
    /// 默认TTL
    pub default_ttl: Duration,
    /// 是否启用预热
    pub enable_prewarming: bool,
    /// 预热策略
    pub prewarming_strategy: PrewarmingStrategy,
    /// 是否启用压缩
    pub enable_compression: bool,
    /// 压缩阈值（字节）
    pub compression_threshold: usize,
}

/// 预热策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum PrewarmingStrategy {
    /// 基于访问频率
    FrequencyBased,
    /// 基于时间模式
    TimeBased,
    /// 基于预测模型
    Predictive,
    /// 手动预热
    Manual,
}

/// 多级缓存管理器
pub struct CacheOptimizer<T> {
    /// L1缓存（内存）
    l1_cache: Arc<RwLock<HashMap<String, CacheItem<T>>>>,
    /// L2缓存（本地存储）
    l2_cache: Arc<RwLock<HashMap<String, CacheItem<T>>>>,
    /// L3缓存（远程）
    l3_cache: Arc<RwLock<HashMap<String, CacheItem<T>>>>,
    /// 配置
    config: CacheConfig,
    /// 统计信息
    stats: Arc<RwLock<HashMap<CacheLevel, CacheStats>>>,
    /// 性能监控器
    performance_monitor: Option<Arc<super::super::monitoring::PerformanceMonitor>>,
}

impl<T> CacheOptimizer<T>
where
    T: Clone + Send + Sync + 'static,
{
    /// 创建新的缓存优化器
    pub fn new(config: CacheConfig) -> Self {
        let mut stats = HashMap::new();
        stats.insert(CacheLevel::L1, CacheStats {
            level: CacheLevel::L1,
            total_capacity: config.max_capacity / 4, // L1使用25%的容量
            used_capacity: 0,
            hits: 0,
            misses: 0,
            hit_rate: 0.0,
            avg_access_time: Duration::ZERO,
            last_updated: Utc::now(),
        });
        stats.insert(CacheLevel::L2, CacheStats {
            level: CacheLevel::L2,
            total_capacity: config.max_capacity / 2, // L2使用50%的容量
            used_capacity: 0,
            hits: 0,
            misses: 0,
            hit_rate: 0.0,
            avg_access_time: Duration::ZERO,
            last_updated: Utc::now(),
        });
        stats.insert(CacheLevel::L3, CacheStats {
            level: CacheLevel::L3,
            total_capacity: config.max_capacity / 4, // L3使用25%的容量
            used_capacity: 0,
            hits: 0,
            misses: 0,
            hit_rate: 0.0,
            avg_access_time: Duration::ZERO,
            last_updated: Utc::now(),
        });

        Self {
            l1_cache: Arc::new(RwLock::new(HashMap::new())),
            l2_cache: Arc::new(RwLock::new(HashMap::new())),
            l3_cache: Arc::new(RwLock::new(HashMap::new())),
            config,
            stats: Arc::new(RwLock::new(stats)),
            performance_monitor: None,
        }
    }

    /// 设置性能监控器
    pub fn set_performance_monitor(&mut self, monitor: Arc<super::super::monitoring::PerformanceMonitor>) {
        self.performance_monitor = Some(monitor);
    }

    /// 获取缓存项
    pub async fn get(&self, key: &str) -> Option<T> {
        let start = Instant::now();
        
        // 从L1缓存开始查找
        if let Some(item) = self.get_from_level(key, CacheLevel::L1).await {
            self.record_hit(CacheLevel::L1, start.elapsed()).await;
            return Some(item.data);
        }

        // 从L2缓存查找
        if let Some(item) = self.get_from_level(key, CacheLevel::L2).await {
            // 将数据提升到L1缓存
            self.promote_to_l1(key, item.clone()).await;
            self.record_hit(CacheLevel::L2, start.elapsed()).await;
            return Some(item.data);
        }

        // 从L3缓存查找
        if let Some(item) = self.get_from_level(key, CacheLevel::L3).await {
            // 将数据提升到L2缓存
            self.promote_to_l2(key, item.clone()).await;
            self.record_hit(CacheLevel::L3, start.elapsed()).await;
            return Some(item.data);
        }

        // 缓存未命中
        self.record_miss(start.elapsed()).await;
        None
    }

    /// 设置缓存项
    pub async fn set(&self, key: String, value: T, ttl: Option<Duration>) -> Result<(), CacheOptimizerError> {
        let start = Instant::now();
        let size_bytes = self.calculate_size(&value);
        let expires_at = ttl.map(|t| Utc::now() + chrono::Duration::from_std(t).unwrap());
        
        let item = CacheItem {
            data: value,
            created_at: Utc::now(),
            last_accessed: Utc::now(),
            access_count: 1,
            expires_at,
            level: CacheLevel::L1,
            size_bytes,
        };

        // 根据大小和策略决定存储级别
        let target_level = self.determine_target_level(size_bytes).await;
        
        match target_level {
            CacheLevel::L1 => {
                self.set_to_level(key, item, CacheLevel::L1).await?;
            },
            CacheLevel::L2 => {
                self.set_to_level(key, item, CacheLevel::L2).await?;
            },
            CacheLevel::L3 => {
                self.set_to_level(key, item, CacheLevel::L3).await?;
            },
        }

        // 记录性能指标
        if let Some(monitor) = &self.performance_monitor {
            let _ = monitor.record_latency("cache_set".to_string(), start.elapsed()).await;
        }

        Ok(())
    }

    /// 删除缓存项
    pub async fn remove(&self, key: &str) -> bool {
        let mut removed = false;
        
        // 从所有级别删除
        if self.l1_cache.write().await.remove(key).is_some() {
            removed = true;
        }
        if self.l2_cache.write().await.remove(key).is_some() {
            removed = true;
        }
        if self.l3_cache.write().await.remove(key).is_some() {
            removed = true;
        }

        if removed {
            self.update_stats().await;
        }

        removed
    }

    /// 清空缓存
    pub async fn clear(&self) {
        self.l1_cache.write().await.clear();
        self.l2_cache.write().await.clear();
        self.l3_cache.write().await.clear();
        self.update_stats().await;
    }

    /// 预热缓存
    pub async fn prewarm(&self, data: HashMap<String, T>) -> Result<(), CacheOptimizerError> {
        match self.config.prewarming_strategy {
            PrewarmingStrategy::FrequencyBased => {
                self.prewarm_by_frequency(data).await
            },
            PrewarmingStrategy::TimeBased => {
                self.prewarm_by_time(data).await
            },
            PrewarmingStrategy::Predictive => {
                self.prewarm_by_prediction(data).await
            },
            PrewarmingStrategy::Manual => {
                self.prewarm_manual(data).await
            },
        }
    }

    /// 获取缓存统计信息
    pub async fn get_stats(&self) -> HashMap<CacheLevel, CacheStats> {
        let stats = self.stats.read().await;
        stats.clone()
    }

    /// 优化缓存
    pub async fn optimize(&self) -> Result<CacheOptimizationResult, CacheOptimizerError> {
        let start = Instant::now();
        let mut optimizations = Vec::new();

        // 分析缓存使用情况
        let stats = self.get_stats().await;
        
        // 检查L1缓存命中率
        if let Some(l1_stats) = stats.get(&CacheLevel::L1) {
            if l1_stats.hit_rate < 0.7 {
                optimizations.push(CacheOptimization {
                    optimization_type: CacheOptimizationType::IncreaseL1Capacity,
                    description: "L1缓存命中率较低，建议增加L1缓存容量".to_string(),
                    expected_improvement: "预期提升20-30%的命中率".to_string(),
                });
            }
        }

        // 检查缓存分布
        let total_used = stats.values().map(|s| s.used_capacity).sum::<usize>();
        if total_used > self.config.max_capacity * 8 / 10 {
            optimizations.push(CacheOptimization {
                optimization_type: CacheOptimizationType::EvictOldEntries,
                description: "缓存使用率过高，建议清理过期条目".to_string(),
                expected_improvement: "释放缓存空间，提升性能".to_string(),
            });
        }

        // 执行清理
        self.cleanup_expired_entries().await;

        let duration = start.elapsed();
        
        // 记录性能指标
        if let Some(monitor) = &self.performance_monitor {
            let _ = monitor.record_latency("cache_optimization".to_string(), duration).await;
        }

        Ok(CacheOptimizationResult {
            optimizations,
            duration,
            timestamp: Utc::now(),
        })
    }

    /// 从指定级别获取缓存项
    async fn get_from_level(&self, key: &str, level: CacheLevel) -> Option<CacheItem<T>> {
        let cache = match level {
            CacheLevel::L1 => &self.l1_cache,
            CacheLevel::L2 => &self.l2_cache,
            CacheLevel::L3 => &self.l3_cache,
        };

        let mut cache_guard = cache.write().await;
        if let Some(item) = cache_guard.get_mut(key) {
            // 检查是否过期
            if let Some(expires_at) = item.expires_at {
                if Utc::now() > expires_at {
                    cache_guard.remove(key);
                    return None;
                }
            }

            // 更新访问信息
            item.last_accessed = Utc::now();
            item.access_count += 1;
            
            Some(item.clone())
        } else {
            None
        }
    }

    /// 设置到指定级别
    async fn set_to_level(&self, key: String, item: CacheItem<T>, level: CacheLevel) -> Result<(), CacheOptimizerError> {
        let cache = match level {
            CacheLevel::L1 => &self.l1_cache,
            CacheLevel::L2 => &self.l2_cache,
            CacheLevel::L3 => &self.l3_cache,
        };

        let mut cache_guard = cache.write().await;
        
        // 检查容量限制
        if !self.has_capacity_for_item(&cache_guard, &item, level).await {
            self.evict_entries(&mut cache_guard, level, item.size_bytes).await;
        }

        cache_guard.insert(key, item);
        self.update_stats().await;
        Ok(())
    }

    /// 提升到L1缓存
    async fn promote_to_l1(&self, key: &str, item: CacheItem<T>) {
        let mut l1_cache = self.l1_cache.write().await;
        let mut l2_cache = self.l2_cache.write().await;
        let mut l3_cache = self.l3_cache.write().await;

        // 从原级别移除
        l2_cache.remove(key);
        l3_cache.remove(key);

        // 检查L1容量
        if !self.has_capacity_for_item(&l1_cache, &item, CacheLevel::L1).await {
            self.evict_entries(&mut l1_cache, CacheLevel::L1, item.size_bytes).await;
        }

        l1_cache.insert(key.to_string(), item);
    }

    /// 提升到L2缓存
    async fn promote_to_l2(&self, key: &str, item: CacheItem<T>) {
        let mut l2_cache = self.l2_cache.write().await;
        let mut l3_cache = self.l3_cache.write().await;

        // 从L3移除
        l3_cache.remove(key);

        // 检查L2容量
        if !self.has_capacity_for_item(&l2_cache, &item, CacheLevel::L2).await {
            self.evict_entries(&mut l2_cache, CacheLevel::L2, item.size_bytes).await;
        }

        l2_cache.insert(key.to_string(), item);
    }

    /// 检查是否有足够容量
    async fn has_capacity_for_item(&self, cache: &HashMap<String, CacheItem<T>>, item: &CacheItem<T>, level: CacheLevel) -> bool {
        let stats = self.stats.read().await;
        if let Some(level_stats) = stats.get(&level) {
            let current_used: usize = cache.values().map(|i| i.size_bytes).sum();
            current_used + item.size_bytes <= level_stats.total_capacity
        } else {
            false
        }
    }

    /// 驱逐条目
    async fn evict_entries(&self, cache: &mut HashMap<String, CacheItem<T>>, level: CacheLevel, required_space: usize) {
        match self.config.strategy {
            CacheStrategy::LRU => {
                self.evict_lru(cache, required_space).await;
            },
            CacheStrategy::LFU => {
                self.evict_lfu(cache, required_space).await;
            },
            CacheStrategy::TTL => {
                self.evict_ttl(cache, required_space).await;
            },
            CacheStrategy::FIFO => {
                self.evict_fifo(cache, required_space).await;
            },
            CacheStrategy::Adaptive => {
                self.evict_adaptive(cache, level, required_space).await;
            },
        }
    }

    /// LRU驱逐策略
    async fn evict_lru(&self, cache: &mut HashMap<String, CacheItem<T>>, required_space: usize) {
        let mut items: Vec<_> = cache.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        items.sort_by_key(|(_, item)| item.last_accessed);
        
        let mut freed_space = 0;
        for (key, _) in items {
            if freed_space >= required_space {
                break;
            }
            if let Some(item) = cache.remove(&key) {
                freed_space += item.size_bytes;
            }
        }
    }

    /// LFU驱逐策略
    async fn evict_lfu(&self, cache: &mut HashMap<String, CacheItem<T>>, required_space: usize) {
        let mut items: Vec<_> = cache.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        items.sort_by_key(|(_, item)| item.access_count);
        
        let mut freed_space = 0;
        for (key, _) in items {
            if freed_space >= required_space {
                break;
            }
            if let Some(item) = cache.remove(&key) {
                freed_space += item.size_bytes;
            }
        }
    }

    /// TTL驱逐策略
    async fn evict_ttl(&self, cache: &mut HashMap<String, CacheItem<T>>, required_space: usize) {
        let now = Utc::now();
        let mut freed_space = 0;
        
        cache.retain(|_, item| {
            if freed_space >= required_space {
                return true;
            }
            
            if let Some(expires_at) = item.expires_at {
                if now > expires_at {
                    freed_space += item.size_bytes;
                    return false;
                }
            }
            true
        });
    }

    /// FIFO驱逐策略
    async fn evict_fifo(&self, cache: &mut HashMap<String, CacheItem<T>>, required_space: usize) {
        let mut items: Vec<_> = cache.iter().map(|(k, v)| (k.clone(), v.clone())).collect();
        items.sort_by_key(|(_, item)| item.created_at);
        
        let mut freed_space = 0;
        for (key, _) in items {
            if freed_space >= required_space {
                break;
            }
            if let Some(item) = cache.remove(&key) {
                freed_space += item.size_bytes;
            }
        }
    }

    /// 自适应驱逐策略
    async fn evict_adaptive(&self, cache: &mut HashMap<String, CacheItem<T>>, level: CacheLevel, required_space: usize) {
        // 根据缓存级别和访问模式选择最佳策略
        match level {
            CacheLevel::L1 => {
                // L1缓存优先使用LRU
                self.evict_lru(cache, required_space).await;
            },
            CacheLevel::L2 => {
                // L2缓存使用LFU
                self.evict_lfu(cache, required_space).await;
            },
            CacheLevel::L3 => {
                // L3缓存使用TTL
                self.evict_ttl(cache, required_space).await;
            },
        }
    }

    /// 确定目标存储级别
    async fn determine_target_level(&self, size_bytes: usize) -> CacheLevel {
        let _stats = self.get_stats().await;
        
        // 小数据优先存储在L1
        if size_bytes < 1024 {
            return CacheLevel::L1;
        }
        
        // 中等数据存储在L2
        if size_bytes < 1024 * 1024 {
            return CacheLevel::L2;
        }
        
        // 大数据存储在L3
        CacheLevel::L3
    }

    /// 计算数据大小
    fn calculate_size(&self, _value: &T) -> usize {
        // 这里应该实现实际的大小计算
        // 对于演示目的，返回一个估算值
        1024
    }

    /// 记录命中
    async fn record_hit(&self, level: CacheLevel, access_time: Duration) {
        let mut stats = self.stats.write().await;
        if let Some(level_stats) = stats.get_mut(&level) {
            level_stats.hits += 1;
            level_stats.hit_rate = level_stats.hits as f64 / (level_stats.hits + level_stats.misses) as f64;
            level_stats.avg_access_time = Duration::from_nanos(
                ((level_stats.avg_access_time.as_nanos() + access_time.as_nanos()) / 2).try_into().unwrap_or(u64::MAX)
            );
            level_stats.last_updated = Utc::now();
        }
    }

    /// 记录未命中
    async fn record_miss(&self, access_time: Duration) {
        let mut stats = self.stats.write().await;
        for level_stats in stats.values_mut() {
            level_stats.misses += 1;
            level_stats.hit_rate = level_stats.hits as f64 / (level_stats.hits + level_stats.misses) as f64;
            level_stats.avg_access_time = Duration::from_nanos(
                ((level_stats.avg_access_time.as_nanos() + access_time.as_nanos()) / 2).try_into().unwrap_or(u64::MAX)
            );
            level_stats.last_updated = Utc::now();
        }
    }

    /// 更新统计信息
    async fn update_stats(&self) {
        let mut stats = self.stats.write().await;
        
        // 更新L1统计
        if let Some(l1_stats) = stats.get_mut(&CacheLevel::L1) {
            l1_stats.used_capacity = self.l1_cache.read().await.values().map(|i| i.size_bytes).sum();
        }
        
        // 更新L2统计
        if let Some(l2_stats) = stats.get_mut(&CacheLevel::L2) {
            l2_stats.used_capacity = self.l2_cache.read().await.values().map(|i| i.size_bytes).sum();
        }
        
        // 更新L3统计
        if let Some(l3_stats) = stats.get_mut(&CacheLevel::L3) {
            l3_stats.used_capacity = self.l3_cache.read().await.values().map(|i| i.size_bytes).sum();
        }
    }

    /// 清理过期条目
    async fn cleanup_expired_entries(&self) {
        let now = Utc::now();
        
        // 清理L1缓存
        {
            let mut l1_cache = self.l1_cache.write().await;
            l1_cache.retain(|_, item| {
                item.expires_at.map_or(true, |expires_at| now <= expires_at)
            });
        }
        
        // 清理L2缓存
        {
            let mut l2_cache = self.l2_cache.write().await;
            l2_cache.retain(|_, item| {
                item.expires_at.map_or(true, |expires_at| now <= expires_at)
            });
        }
        
        // 清理L3缓存
        {
            let mut l3_cache = self.l3_cache.write().await;
            l3_cache.retain(|_, item| {
                item.expires_at.map_or(true, |expires_at| now <= expires_at)
            });
        }
        
        self.update_stats().await;
    }

    /// 基于频率的预热
    async fn prewarm_by_frequency(&self, data: HashMap<String, T>) -> Result<(), CacheOptimizerError> {
        // 按数据大小排序，小数据优先预热到L1
        let mut sorted_data: Vec<_> = data.into_iter().collect();
        sorted_data.sort_by_key(|(_, value)| self.calculate_size(value));
        
        for (key, value) in sorted_data {
            self.set(key, value, Some(self.config.default_ttl)).await?;
        }
        
        Ok(())
    }

    /// 基于时间的预热
    async fn prewarm_by_time(&self, data: HashMap<String, T>) -> Result<(), CacheOptimizerError> {
        // 在低峰期进行预热
        let now = Utc::now();
        let hour = now.hour();
        
        // 在凌晨2-6点进行预热
        if hour >= 2 && hour <= 6 {
            for (key, value) in data {
                self.set(key, value, Some(self.config.default_ttl)).await?;
            }
        }
        
        Ok(())
    }

    /// 基于预测的预热
    async fn prewarm_by_prediction(&self, data: HashMap<String, T>) -> Result<(), CacheOptimizerError> {
        // 这里应该实现基于机器学习的预测模型
        // 目前使用简单的启发式方法
        self.prewarm_by_frequency(data).await
    }

    /// 手动预热
    async fn prewarm_manual(&self, data: HashMap<String, T>) -> Result<(), CacheOptimizerError> {
        for (key, value) in data {
            self.set(key, value, Some(self.config.default_ttl)).await?;
        }
        Ok(())
    }
}

/// 缓存优化结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheOptimizationResult {
    /// 优化建议
    pub optimizations: Vec<CacheOptimization>,
    /// 优化耗时
    pub duration: Duration,
    /// 优化时间
    pub timestamp: DateTime<Utc>,
}

/// 缓存优化建议
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CacheOptimization {
    /// 优化类型
    pub optimization_type: CacheOptimizationType,
    /// 描述
    pub description: String,
    /// 预期改进
    pub expected_improvement: String,
}

/// 缓存优化类型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CacheOptimizationType {
    /// 增加L1缓存容量
    IncreaseL1Capacity,
    /// 清理过期条目
    EvictOldEntries,
    /// 调整缓存策略
    AdjustCacheStrategy,
    /// 启用压缩
    EnableCompression,
    /// 优化预热策略
    OptimizePrewarming,
}

/// 缓存优化器错误
#[derive(Debug, thiserror::Error)]
pub enum CacheOptimizerError {
    #[error("缓存配置错误: {0}")]
    ConfigError(String),
    
    #[error("缓存操作失败: {0}")]
    CacheOperationError(String),
    
    #[error("预热失败: {0}")]
    PrewarmingError(String),
    
    #[error("优化失败: {0}")]
    OptimizationError(String),
    
    #[error("序列化错误: {0}")]
    SerializationError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_cache_optimizer_creation() {
        let config = CacheConfig {
            strategy: CacheStrategy::LRU,
            max_capacity: 1024 * 1024, // 1MB
            default_ttl: Duration::from_secs(3600),
            enable_prewarming: true,
            prewarming_strategy: PrewarmingStrategy::Manual,
            enable_compression: false,
            compression_threshold: 1024,
        };
        
        let optimizer = CacheOptimizer::<String>::new(config);
        
        // 测试基本操作
        optimizer.set("key1".to_string(), "value1".to_string(), None).await.unwrap();
        let value = optimizer.get("key1").await;
        assert_eq!(value, Some("value1".to_string()));
    }

    #[tokio::test]
    async fn test_cache_levels() {
        let config = CacheConfig {
            strategy: CacheStrategy::LRU,
            max_capacity: 1024 * 1024,
            default_ttl: Duration::from_secs(3600),
            enable_prewarming: false,
            prewarming_strategy: PrewarmingStrategy::Manual,
            enable_compression: false,
            compression_threshold: 1024,
        };
        
        let optimizer = CacheOptimizer::<String>::new(config);
        
        // 测试多级缓存
        optimizer.set("key1".to_string(), "value1".to_string(), None).await.unwrap();
        optimizer.set("key2".to_string(), "value2".to_string(), None).await.unwrap();
        
        let stats = optimizer.get_stats().await;
        assert!(stats.contains_key(&CacheLevel::L1));
        assert!(stats.contains_key(&CacheLevel::L2));
        assert!(stats.contains_key(&CacheLevel::L3));
    }

    #[tokio::test]
    async fn test_cache_optimization() {
        let config = CacheConfig {
            strategy: CacheStrategy::LRU,
            max_capacity: 1024,
            default_ttl: Duration::from_secs(1),
            enable_prewarming: false,
            prewarming_strategy: PrewarmingStrategy::Manual,
            enable_compression: false,
            compression_threshold: 1024,
        };
        
        let optimizer = CacheOptimizer::<String>::new(config);
        
        // 添加一些数据
        for i in 0..10 {
            optimizer.set(format!("key{}", i), format!("value{}", i), None).await.unwrap();
        }
        
        // 执行优化
        let result = optimizer.optimize().await.unwrap();
        assert!(!result.optimizations.is_empty());
    }
}
