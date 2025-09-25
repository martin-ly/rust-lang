use anyhow::Result;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};
use tokio::time::sleep;
use tracing::{info, warn, error, debug};
//use serde::{Deserialize, Serialize};
use std::collections::{HashMap, VecDeque};
//use std::sync::atomic::{AtomicUsize, AtomicU64, AtomicBool, Ordering};
use std::hash::{Hash, Hasher};
use std::collections::hash_map::DefaultHasher;

/// 2025年异步缓存系统演示
/// 展示最新的异步缓存编程模式和最佳实践

/// 1. 异步LRU缓存
#[derive(Debug, Clone)]
pub struct AsyncLRUCache<K, V>
where
    K: Clone + Hash + Eq + Send + Sync + 'static + std::fmt::Debug,
    V: Clone + Send + Sync + 'static,
{
    capacity: usize,
    cache: Arc<RwLock<HashMap<K, CacheNode<K, V>>>>,
    access_order: Arc<RwLock<VecDeque<K>>>,
    cache_stats: Arc<RwLock<CacheStats>>,
    eviction_policy: EvictionPolicy,
}

#[derive(Debug, Clone)]
pub struct CacheNode<K, V> 
where
    K: Clone + std::fmt::Debug,
    V: Clone,
{
    pub key: K,
    pub value: V,
    pub created_at: Instant,
    pub last_accessed: Instant,
    pub access_count: usize,
    pub size_bytes: usize,
}

#[derive(Debug, Clone, PartialEq)]
pub enum EvictionPolicy {
    LRU,           // 最近最少使用
    LFU,           // 最少频率使用
    TTL,           // 基于时间过期
    Size,          // 基于大小
    Hybrid,        // 混合策略
}

#[derive(Debug, Clone, Default)]
pub struct CacheStats {
    pub hits: usize,
    pub misses: usize,
    pub evictions: usize,
    pub total_requests: usize,
    pub current_size: usize,
    pub total_size_bytes: usize,
}

impl<K, V> AsyncLRUCache<K, V>
where
    K: Clone + Hash + Eq + Send + Sync + 'static + std::fmt::Debug,
    V: Clone + Send + Sync + 'static,
{
    pub fn new(capacity: usize, eviction_policy: EvictionPolicy) -> Self {
        Self {
            capacity,
            cache: Arc::new(RwLock::new(HashMap::new())),
            access_order: Arc::new(RwLock::new(VecDeque::new())),
            cache_stats: Arc::new(RwLock::new(CacheStats::default())),
            eviction_policy,
        }
    }

    pub async fn get(&self, key: &K) -> Option<V> {
        let mut cache = self.cache.write().await;
        let mut access_order = self.access_order.write().await;
        let mut stats = self.cache_stats.write().await;
        
        stats.total_requests += 1;
        
        if let Some(node) = cache.get_mut(key) {
            // 更新访问信息
            node.last_accessed = Instant::now();
            node.access_count += 1;
            
            // 更新访问顺序
            access_order.retain(|k| k != key);
            access_order.push_back(key.clone());
            
            stats.hits += 1;
            debug!("缓存命中: {:?}", key);
            Some(node.value.clone())
        } else {
            stats.misses += 1;
            debug!("缓存未命中: {:?}", key);
            None
        }
    }

    pub async fn put(&self, key: K, value: V, size_bytes: Option<usize>) -> Result<()> {
        let size_bytes = size_bytes.unwrap_or_else(|| std::mem::size_of_val(&value));
        let now = Instant::now();
        
        let node = CacheNode {
            key: key.clone(),
            value: value.clone(),
            created_at: now,
            last_accessed: now,
            access_count: 1,
            size_bytes,
        };
        
        let mut cache = self.cache.write().await;
        let mut access_order = self.access_order.write().await;
        let mut stats = self.cache_stats.write().await;
        
        // 检查容量限制
        if cache.len() >= self.capacity && !cache.contains_key(&key) {
            self.evict_entry(&mut cache, &mut access_order, &mut stats).await;
        }
        
        cache.insert(key.clone(), node);
        access_order.push_back(key.clone());
        stats.current_size += 1;
        stats.total_size_bytes += size_bytes;
        
        info!("缓存设置: {:?} (大小: {} 字节)", key, size_bytes);
        Ok(())
    }

    async fn evict_entry(
        &self,
        cache: &mut HashMap<K, CacheNode<K, V>>,
        access_order: &mut VecDeque<K>,
        stats: &mut CacheStats,
    ) {
        let key_to_evict = match self.eviction_policy {
            EvictionPolicy::LRU => {
                // 移除最久未访问的条目
                access_order.pop_front()
            }
            EvictionPolicy::LFU => {
                // 移除访问次数最少的条目
                let mut min_access_count = usize::MAX;
                let mut key_to_evict = None;
                
                for (key, node) in cache.iter() {
                    if node.access_count < min_access_count {
                        min_access_count = node.access_count;
                        key_to_evict = Some(key.clone());
                    }
                }
                key_to_evict
            }
            EvictionPolicy::TTL => {
                // 移除最旧的条目
                let mut oldest_time = Instant::now();
                let mut key_to_evict = None;
                
                for (key, node) in cache.iter() {
                    if node.created_at < oldest_time {
                        oldest_time = node.created_at;
                        key_to_evict = Some(key.clone());
                    }
                }
                key_to_evict
            }
            EvictionPolicy::Size => {
                // 移除最大的条目
                let mut max_size = 0;
                let mut key_to_evict = None;
                
                for (key, node) in cache.iter() {
                    if node.size_bytes > max_size {
                        max_size = node.size_bytes;
                        key_to_evict = Some(key.clone());
                    }
                }
                key_to_evict
            }
            EvictionPolicy::Hybrid => {
                // 混合策略：结合LRU和LFU
                let mut best_score = f64::INFINITY;
                let mut key_to_evict = None;
                
                for (key, node) in cache.iter() {
                    let recency_score = node.last_accessed.elapsed().as_secs() as f64;
                    let frequency_score = 1.0 / (node.access_count as f64 + 1.0);
                    let score = recency_score + frequency_score;
                    
                    if score < best_score {
                        best_score = score;
                        key_to_evict = Some(key.clone());
                    }
                }
                key_to_evict
            }
        };
        
        if let Some(key) = key_to_evict {
            if let Some(node) = cache.remove(&key) {
                access_order.retain(|k| k != &key);
                stats.current_size -= 1;
                stats.total_size_bytes -= node.size_bytes;
                stats.evictions += 1;
                
                info!("缓存驱逐: {:?} (大小: {} 字节)", key, node.size_bytes);
            }
        }
    }

    pub async fn remove(&self, key: &K) -> Option<V> {
        let mut cache = self.cache.write().await;
        let mut access_order = self.access_order.write().await;
        let mut stats = self.cache_stats.write().await;
        
        if let Some(node) = cache.remove(key) {
            access_order.retain(|k| k != key);
            stats.current_size -= 1;
            stats.total_size_bytes -= node.size_bytes;
            
            info!("缓存移除: {:?}", key);
            Some(node.value)
        } else {
            None
        }
    }

    pub async fn clear(&self) {
        let mut cache = self.cache.write().await;
        let mut access_order = self.access_order.write().await;
        let mut stats = self.cache_stats.write().await;
        
        cache.clear();
        access_order.clear();
        stats.current_size = 0;
        stats.total_size_bytes = 0;
        
        info!("缓存清空");
    }

    pub async fn get_stats(&self) -> CacheStats {
        self.cache_stats.read().await.clone()
    }

    pub async fn get_hit_rate(&self) -> f64 {
        let stats = self.cache_stats.read().await;
        if stats.total_requests == 0 {
            0.0
        } else {
            stats.hits as f64 / stats.total_requests as f64
        }
    }
}

/// 2. 异步分布式缓存
#[derive(Debug, Clone)]
pub struct AsyncDistributedCache {
    local_cache: Arc<RwLock<HashMap<String, DistributedCacheEntry>>>,
    cache_nodes: Arc<RwLock<Vec<DistributedCacheNode>>>,
    consistent_hash: Arc<RwLock<ConsistentHashRing>>,
    cache_config: DistributedCacheConfig,
    cache_stats: Arc<RwLock<DistributedCacheStats>>,
    replication_factor: usize,
}

#[derive(Debug, Clone)]
pub struct DistributedCacheNode {
    pub id: String,
    pub address: String,
    pub port: u16,
    pub is_online: bool,
    pub last_heartbeat: Instant,
    pub capacity_bytes: u64,
    pub used_bytes: u64,
}

#[derive(Debug, Clone)]
pub struct DistributedCacheEntry {
    pub key: String,
    pub value: String,
    pub created_at: Instant,
    pub expires_at: Option<Instant>,
    pub version: u64,
    pub replica_nodes: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct ConsistentHashRing {
    pub nodes: Vec<(u64, String)>,
    pub virtual_nodes: usize,
}

#[derive(Debug, Clone)]
pub struct DistributedCacheConfig {
    pub default_ttl: Duration,
    pub replication_factor: usize,
    pub virtual_nodes: usize,
    pub heartbeat_interval: Duration,
    pub read_repair_threshold: f64,
}

impl Default for DistributedCacheConfig {
    fn default() -> Self {
        Self {
            default_ttl: Duration::from_secs(3600),
            replication_factor: 3,
            virtual_nodes: 150,
            heartbeat_interval: Duration::from_secs(30),
            read_repair_threshold: 0.1,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct DistributedCacheStats {
    pub total_gets: usize,
    pub total_sets: usize,
    pub local_hits: usize,
    pub remote_hits: usize,
    pub misses: usize,
    pub replicas_created: usize,
    pub read_repairs: usize,
    pub node_failures: usize,
}

impl AsyncDistributedCache {
    pub fn new(config: DistributedCacheConfig) -> Self {
        Self {
            local_cache: Arc::new(RwLock::new(HashMap::new())),
            cache_nodes: Arc::new(RwLock::new(Vec::new())),
            consistent_hash: Arc::new(RwLock::new(ConsistentHashRing {
                nodes: Vec::new(),
                virtual_nodes: config.virtual_nodes,
            })),
            cache_config: config.clone(),
            cache_stats: Arc::new(RwLock::new(DistributedCacheStats::default())),
            replication_factor: config.replication_factor,
        }
    }

    pub async fn add_node(&self, node: DistributedCacheNode) -> Result<()> {
        let mut nodes = self.cache_nodes.write().await;
        let mut hash_ring = self.consistent_hash.write().await;
        
        nodes.push(node.clone());
        
        // 添加虚拟节点到一致性哈希环
        for i in 0..hash_ring.virtual_nodes {
            let virtual_key = format!("{}:{}", node.id, i);
            let hash = self.hash_key(&virtual_key);
            hash_ring.nodes.push((hash, node.id.clone()));
        }
        
        // 排序哈希环
        hash_ring.nodes.sort_by_key(|(hash, _)| *hash);
        
        info!("添加缓存节点: {} ({})", node.id, node.address);
        Ok(())
    }

    pub async fn get(&self, key: &str) -> Result<Option<String>> {
        let mut stats = self.cache_stats.write().await;
        stats.total_gets += 1;
        
        // 首先检查本地缓存
        {
            let local_cache = self.local_cache.read().await;
            if let Some(entry) = local_cache.get(key) {
                if entry.expires_at.map_or(true, |exp| Instant::now() < exp) {
                    stats.local_hits += 1;
                    info!("本地缓存命中: {}", key);
                    return Ok(Some(entry.value.clone()));
                }
            }
        }
        
        // 从远程节点获取
        let replica_nodes = self.get_replica_nodes(key).await;
        for node_id in replica_nodes {
            if let Some(value) = self.get_from_node(&node_id, key).await? {
                // 写回本地缓存
                self.set_local(key, value.clone()).await;
                stats.remote_hits += 1;
                info!("远程缓存命中: {} (节点: {})", key, node_id);
                return Ok(Some(value));
            }
        }
        
        stats.misses += 1;
        Ok(None)
    }

    pub async fn set(&self, key: String, value: String, ttl: Option<Duration>) -> Result<()> {
        let mut stats = self.cache_stats.write().await;
        stats.total_sets += 1;
        
        let expires_at = ttl.map(|t| Instant::now() + t);
        let replica_nodes = self.get_replica_nodes(&key).await;
        
        // 设置本地缓存
        self.set_local(&key, value.clone()).await;
        
        // 复制到其他节点
        let mut successful_replicas = 0;
        for node_id in replica_nodes {
            if self.set_to_node(&node_id, &key, &value, expires_at).await? {
                successful_replicas += 1;
            }
        }
        
        stats.replicas_created += successful_replicas;
        info!("设置缓存: {} (副本数: {})", key, successful_replicas);
        Ok(())
    }

    async fn set_local(&self, key: &str, value: String) {
        let mut local_cache = self.local_cache.write().await;
        let entry = DistributedCacheEntry {
            key: key.to_string(),
            value,
            created_at: Instant::now(),
            expires_at: Some(Instant::now() + self.cache_config.default_ttl),
            version: 1,
            replica_nodes: Vec::new(),
        };
        local_cache.insert(key.to_string(), entry);
    }

    async fn get_replica_nodes(&self, key: &str) -> Vec<String> {
        let hash_ring = self.consistent_hash.read().await;
        let key_hash = self.hash_key(key);
        
        // 找到第一个节点
        let mut start_index = 0;
        for (i, (hash, _)) in hash_ring.nodes.iter().enumerate() {
            if *hash >= key_hash {
                start_index = i;
                break;
            }
        }
        
        // 收集副本节点
        let mut replica_nodes = Vec::new();
        let mut seen_nodes = std::collections::HashSet::new();
        
        for i in 0..hash_ring.nodes.len() {
            let index = (start_index + i) % hash_ring.nodes.len();
            let node_id = &hash_ring.nodes[index].1;
            
            if !seen_nodes.contains(node_id) {
                seen_nodes.insert(node_id.clone());
                replica_nodes.push(node_id.clone());
                
                if replica_nodes.len() >= self.replication_factor {
                    break;
                }
            }
        }
        
        replica_nodes
    }

    async fn get_from_node(&self, node_id: &str, key: &str) -> Result<Option<String>> {
        // 模拟从远程节点获取数据
        sleep(Duration::from_millis(10)).await;
        
        // 模拟节点可能失败
        if rand::random::<f64>() < 0.05 {
            return Ok(None);
        }
        
        // 模拟返回数据
        Ok(Some(format!("value_from_{}_{}", node_id, key)))
    }

    #[allow(unused_variables)]
    async fn set_to_node(&self, node_id: &str, key: &str, value: &str, expires_at: Option<Instant>) -> Result<bool> {
        // 模拟向远程节点设置数据
        sleep(Duration::from_millis(15)).await;
        
        // 模拟节点可能失败
        if rand::random::<f64>() < 0.03 {
            return Ok(false);
        }
        
        debug!("设置到节点 {}: {} = {}", node_id, key, value);
        Ok(true)
    }

    fn hash_key(&self, key: &str) -> u64 {
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }

    pub async fn remove_node(&self, node_id: &str) -> Result<()> {
        let mut nodes = self.cache_nodes.write().await;
        let mut hash_ring = self.consistent_hash.write().await;
        
        // 移除节点
        nodes.retain(|node| node.id != node_id);
        
        // 从哈希环移除虚拟节点
        hash_ring.nodes.retain(|(_, id)| id != node_id);
        
        let mut stats = self.cache_stats.write().await;
        stats.node_failures += 1;
        
        info!("移除缓存节点: {}", node_id);
        Ok(())
    }

    pub async fn get_stats(&self) -> DistributedCacheStats {
        self.cache_stats.read().await.clone()
    }
}

/// 3. 异步缓存预热系统
#[derive(Debug, Clone)]
pub struct AsyncCacheWarmer {
    cache: AsyncLRUCache<String, String>,
    data_sources: Arc<RwLock<Vec<DataSource>>>,
    warming_stats: Arc<RwLock<WarmingStats>>,
    warming_config: WarmingConfig,
}

#[derive(Debug, Clone)]
pub struct DataSource {
    pub id: String,
    pub name: String,
    pub priority: u8,
    pub query: String,
    pub estimated_size: usize,
    pub refresh_interval: Duration,
}

#[derive(Debug, Clone)]
pub struct WarmingConfig {
    pub max_concurrent_warming: usize,
    pub warming_timeout: Duration,
    pub retry_attempts: usize,
    pub enable_continuous_warming: bool,
}

impl Default for WarmingConfig {
    fn default() -> Self {
        Self {
            max_concurrent_warming: 5,
            warming_timeout: Duration::from_secs(30),
            retry_attempts: 3,
            enable_continuous_warming: true,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct WarmingStats {
    pub total_warmed_items: usize,
    pub successful_warming: usize,
    pub failed_warming: usize,
    pub total_warming_time: Duration,
    pub active_warming_tasks: usize,
}

impl AsyncCacheWarmer {
    pub fn new(cache: AsyncLRUCache<String, String>, config: WarmingConfig) -> Self {
        Self {
            cache,
            data_sources: Arc::new(RwLock::new(Vec::new())),
            warming_stats: Arc::new(RwLock::new(WarmingStats::default())),
            warming_config: config,
        }
    }

    pub async fn add_data_source(&self, source: DataSource) -> Result<()> {
        let mut sources = self.data_sources.write().await;
        sources.push(source.clone());
        
        // 按优先级排序
        sources.sort_by_key(|s| s.priority);
        
        info!("添加数据源: {} (优先级: {})", source.name, source.priority);
        Ok(())
    }

    #[allow(unused_variables)]
    pub async fn warm_cache(&self) -> Result<()> {
        let sources = self.data_sources.read().await;
        let semaphore = Arc::new(Semaphore::new(self.warming_config.max_concurrent_warming));
        
        let mut warming_tasks = Vec::new();
        
        for source in sources.iter() {
            let semaphore_clone = semaphore.clone();
            let cache_clone = self.cache.clone();
            let source_clone = source.clone();
            let stats_clone = self.warming_stats.clone();
            let config_clone = self.warming_config.clone();
            
            let task = tokio::spawn(async move {
                let _permit = semaphore_clone.acquire().await.unwrap();
                let start_time = Instant::now();
                
                // 模拟数据获取
                let data = Self::fetch_data_from_source(&source_clone).await;
                
                match data {
                    Ok(value) => {
                        cache_clone.put(source_clone.query.clone(), value, Some(source_clone.estimated_size)).await?;
                        
                        let mut stats = stats_clone.write().await;
                        stats.successful_warming += 1;
                        stats.total_warmed_items += 1;
                        stats.total_warming_time += start_time.elapsed();
                        
                        info!("缓存预热成功: {} (耗时: {:?})", source_clone.name, start_time.elapsed());
                        Ok(())
                    }
                    Err(e) => {
                        let mut stats = stats_clone.write().await;
                        stats.failed_warming += 1;
                        
                        error!("缓存预热失败: {} - {}", source_clone.name, e);
                        Err(e)
                    }
                }
            });
            
            warming_tasks.push(task);
        }
        
        // 等待所有预热任务完成
        for task in warming_tasks {
            let _ = task.await;
        }
        
        info!("缓存预热完成");
        Ok(())
    }

    async fn fetch_data_from_source(source: &DataSource) -> Result<String> {
        // 模拟数据获取延迟
        sleep(Duration::from_millis(100 + source.priority as u64 * 50)).await;
        
        // 模拟偶尔失败
        if rand::random::<f64>() < 0.1 {
            return Err(anyhow::anyhow!("数据源 {} 暂时不可用", source.name));
        }
        
        // 模拟返回数据
        Ok(format!("data_from_{}_{}", source.name, source.query))
    }

    pub async fn start_continuous_warming(&self) -> Result<()> {
        if !self.warming_config.enable_continuous_warming {
            return Ok(());
        }
        
        let sources = self.data_sources.read().await;
        let mut warming_tasks = Vec::new();
        
        for source in sources.iter() {
            let warmer_clone = self.clone();
            let source_clone = source.clone();
            
            let task = tokio::spawn(async move {
                let mut interval = tokio::time::interval(source_clone.refresh_interval);
                loop {
                    interval.tick().await;
                    
                    // 重新获取数据
                    if let Ok(data) = Self::fetch_data_from_source(&source_clone).await {
                        let _ = warmer_clone.cache.put(
                            source_clone.query.clone(),
                            data,
                            Some(source_clone.estimated_size)
                        ).await;
                        
                        debug!("连续预热更新: {}", source_clone.name);
                    }
                }
            });
            
            warming_tasks.push(task);
        }
        
        info!("启动连续缓存预热，任务数: {}", warming_tasks.len());
        Ok(())
    }

    pub async fn get_warming_stats(&self) -> WarmingStats {
        self.warming_stats.read().await.clone()
    }
}

/// 4. 异步缓存监控和指标收集
#[derive(Debug, Clone)]
pub struct AsyncCacheMonitor {
    metrics_collector: Arc<RwLock<HashMap<String, CacheMetrics>>>,
    alert_rules: Arc<RwLock<Vec<AlertRule>>>,
    monitor_config: MonitorConfig,
    monitor_stats: Arc<RwLock<MonitorStats>>,
}

#[derive(Debug, Clone)]
pub struct CacheMetrics {
    pub cache_name: String,
    pub hit_rate: f64,
    pub miss_rate: f64,
    pub eviction_rate: f64,
    pub average_access_time: Duration,
    pub memory_usage_bytes: usize,
    pub total_requests: usize,
    pub last_updated: Instant,
}

#[derive(Debug, Clone)]
pub struct AlertRule {
    pub id: String,
    pub name: String,
    pub condition: AlertCondition,
    pub severity: AlertSeverity,
    pub enabled: bool,
    pub cooldown: Duration,
    pub last_triggered: Option<Instant>,
}

#[derive(Debug, Clone)]
pub enum AlertCondition {
    HitRateBelow(f64),
    MemoryUsageAbove(f64),
    AccessTimeAbove(Duration),
    EvictionRateAbove(f64),
}

#[derive(Debug, Clone, PartialEq)]
pub enum AlertSeverity {
    Info,
    Warning,
    Error,
    Critical,
}

#[derive(Debug, Clone)]
pub struct MonitorConfig {
    pub collection_interval: Duration,
    pub retention_period: Duration,
    pub enable_alerts: bool,
    pub alert_cooldown: Duration,
}

impl Default for MonitorConfig {
    fn default() -> Self {
        Self {
            collection_interval: Duration::from_secs(60),
            retention_period: Duration::from_secs(3600),
            enable_alerts: true,
            alert_cooldown: Duration::from_secs(300),
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct MonitorStats {
    pub total_metrics_collected: usize,
    pub alerts_triggered: usize,
    pub monitoring_errors: usize,
    pub last_collection_time: Option<Instant>,
}

impl AsyncCacheMonitor {
    pub fn new(config: MonitorConfig) -> Self {
        let monitor = Self {
            metrics_collector: Arc::new(RwLock::new(HashMap::new())),
            alert_rules: Arc::new(RwLock::new(Vec::new())),
            monitor_config: config.clone(),
            monitor_stats: Arc::new(RwLock::new(MonitorStats::default())),
        };
        
        // 启动监控任务
        let monitor_clone = monitor.clone();
        tokio::spawn(async move {
            monitor_clone.monitoring_loop().await;
        });
        
        monitor
    }

    pub async fn add_alert_rule(&self, rule: AlertRule) -> Result<()> {
        let mut rules = self.alert_rules.write().await;
        rules.push(rule.clone());
        info!("添加告警规则: {}", rule.name);
        Ok(())
    }

    pub async fn collect_metrics(&self, cache_name: &str, cache_stats: &CacheStats) -> Result<()> {
        let hit_rate = if cache_stats.total_requests > 0 {
            cache_stats.hits as f64 / cache_stats.total_requests as f64
        } else {
            0.0
        };
        
        let miss_rate = 1.0 - hit_rate;
        let eviction_rate = if cache_stats.total_requests > 0 {
            cache_stats.evictions as f64 / cache_stats.total_requests as f64
        } else {
            0.0
        };
        
        let metrics = CacheMetrics {
            cache_name: cache_name.to_string(),
            hit_rate,
            miss_rate,
            eviction_rate,
            average_access_time: Duration::from_millis(1), // 模拟
            memory_usage_bytes: cache_stats.total_size_bytes,
            total_requests: cache_stats.total_requests,
            last_updated: Instant::now(),
        };
        
        let mut collector = self.metrics_collector.write().await;
        collector.insert(cache_name.to_string(), metrics);
        
        let mut stats = self.monitor_stats.write().await;
        stats.total_metrics_collected += 1;
        stats.last_collection_time = Some(Instant::now());
        
        debug!("收集缓存指标: {} (命中率: {:.2}%)", cache_name, hit_rate * 100.0);
        Ok(())
    }

    async fn monitoring_loop(&self) {
        let mut interval = tokio::time::interval(self.monitor_config.collection_interval);
        loop {
            interval.tick().await;
            
            if let Err(e) = self.check_alerts().await {
                let mut stats = self.monitor_stats.write().await;
                stats.monitoring_errors += 1;
                error!("监控错误: {}", e);
            }
        }
    }

    async fn check_alerts(&self) -> Result<()> {
        if !self.monitor_config.enable_alerts {
            return Ok(());
        }
        
        let metrics = self.metrics_collector.read().await;
        let mut rules = self.alert_rules.write().await;
        
        for rule in rules.iter_mut() {
            if !rule.enabled {
                continue;
            }
            
            // 检查冷却期
            if let Some(last_triggered) = rule.last_triggered {
                if last_triggered.elapsed() < rule.cooldown {
                    continue;
                }
            }
            
            let should_alert = match &rule.condition {
                AlertCondition::HitRateBelow(threshold) => {
                    metrics.values().any(|m| m.hit_rate < *threshold)
                }
                AlertCondition::MemoryUsageAbove(threshold) => {
                    metrics.values().any(|m| m.memory_usage_bytes as f64 > *threshold)
                }
                AlertCondition::AccessTimeAbove(threshold) => {
                    metrics.values().any(|m| m.average_access_time > *threshold)
                }
                AlertCondition::EvictionRateAbove(threshold) => {
                    metrics.values().any(|m| m.eviction_rate > *threshold)
                }
            };
            
            if should_alert {
                rule.last_triggered = Some(Instant::now());
                
                let mut stats = self.monitor_stats.write().await;
                stats.alerts_triggered += 1;
                
                match rule.severity {
                    AlertSeverity::Critical => {
                        error!("🚨 严重告警: {}", rule.name);
                    }
                    AlertSeverity::Error => {
                        error!("⚠️ 错误告警: {}", rule.name);
                    }
                    AlertSeverity::Warning => {
                        warn!("⚠️ 警告告警: {}", rule.name);
                    }
                    AlertSeverity::Info => {
                        info!("ℹ️ 信息告警: {}", rule.name);
                    }
                }
            }
        }
        
        Ok(())
    }

    pub async fn get_metrics(&self, cache_name: &str) -> Option<CacheMetrics> {
        let metrics = self.metrics_collector.read().await;
        metrics.get(cache_name).cloned()
    }

    pub async fn get_all_metrics(&self) -> HashMap<String, CacheMetrics> {
        self.metrics_collector.read().await.clone()
    }

    pub async fn get_monitor_stats(&self) -> MonitorStats {
        self.monitor_stats.read().await.clone()
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();
    
    info!("🚀 开始 2025 年异步缓存系统演示");

    // 1. 演示异步LRU缓存
    info!("📦 演示异步LRU缓存");
    let lru_cache = AsyncLRUCache::new(100, EvictionPolicy::Hybrid);
    
    // 添加一些数据
    for i in 0..50 {
        let key = format!("key_{}", i);
        let value = format!("value_{}", i);
        lru_cache.put(key, value, Some(1024)).await?;
    }
    
    // 测试缓存命中
    for i in 0..20 {
        let key = format!("key_{}", i);
        if let Some(value) = lru_cache.get(&key).await {
            info!("LRU缓存命中: {} -> {}", key, value);
        }
    }
    
    let lru_stats = lru_cache.get_stats().await;
    let hit_rate = lru_cache.get_hit_rate().await;
    info!("LRU缓存统计: 命中 {}, 未命中 {}, 命中率: {:.2}%", 
          lru_stats.hits, lru_stats.misses, hit_rate * 100.0);

    // 2. 演示异步分布式缓存
    info!("🌐 演示异步分布式缓存");
    let config = DistributedCacheConfig::default();
    let distributed_cache = AsyncDistributedCache::new(config);
    
    // 添加缓存节点
    for i in 0..5 {
        let node = DistributedCacheNode {
            id: format!("node_{}", i),
            address: format!("192.168.1.{}", 100 + i),
            port: 6379,
            is_online: true,
            last_heartbeat: Instant::now(),
            capacity_bytes: 1024 * 1024 * 1024, // 1GB
            used_bytes: 0,
        };
        distributed_cache.add_node(node).await?;
    }
    
    // 设置和获取数据
    distributed_cache.set("user:1".to_string(), "Alice".to_string(), None).await?;
    distributed_cache.set("user:2".to_string(), "Bob".to_string(), Some(Duration::from_secs(300))).await?;
    
    if let Some(value) = distributed_cache.get("user:1").await? {
        info!("分布式缓存获取: user:1 -> {}", value);
    }
    
    if let Some(value) = distributed_cache.get("user:2").await? {
        info!("分布式缓存获取: user:2 -> {}", value);
    }
    
    let dist_stats = distributed_cache.get_stats().await;
    info!("分布式缓存统计: 本地命中 {}, 远程命中 {}, 未命中 {}", 
          dist_stats.local_hits, dist_stats.remote_hits, dist_stats.misses);

    // 3. 演示异步缓存预热系统
    info!("🔥 演示异步缓存预热系统");
    let warming_config = WarmingConfig::default();
    let cache_warmer = AsyncCacheWarmer::new(lru_cache.clone(), warming_config);
    
    // 添加数据源
    let data_sources = vec![
        DataSource {
            id: "source_1".to_string(),
            name: "用户数据".to_string(),
            priority: 1,
            query: "SELECT * FROM users".to_string(),
            estimated_size: 2048,
            refresh_interval: Duration::from_secs(300),
        },
        DataSource {
            id: "source_2".to_string(),
            name: "产品数据".to_string(),
            priority: 2,
            query: "SELECT * FROM products".to_string(),
            estimated_size: 4096,
            refresh_interval: Duration::from_secs(600),
        },
        DataSource {
            id: "source_3".to_string(),
            name: "订单数据".to_string(),
            priority: 3,
            query: "SELECT * FROM orders".to_string(),
            estimated_size: 1024,
            refresh_interval: Duration::from_secs(900),
        },
    ];
    
    for source in data_sources {
        cache_warmer.add_data_source(source).await?;
    }
    
    // 执行缓存预热
    cache_warmer.warm_cache().await?;
    
    let warming_stats = cache_warmer.get_warming_stats().await;
    info!("缓存预热统计: 成功 {}, 失败 {}, 总项目 {}", 
          warming_stats.successful_warming, warming_stats.failed_warming, warming_stats.total_warmed_items);

    // 4. 演示异步缓存监控和指标收集
    info!("📊 演示异步缓存监控和指标收集");
    let monitor_config = MonitorConfig::default();
    let cache_monitor = AsyncCacheMonitor::new(monitor_config);
    
    // 添加告警规则
    let alert_rules = vec![
        AlertRule {
            id: "low_hit_rate".to_string(),
            name: "缓存命中率过低".to_string(),
            condition: AlertCondition::HitRateBelow(0.8),
            severity: AlertSeverity::Warning,
            enabled: true,
            cooldown: Duration::from_secs(300),
            last_triggered: None,
        },
        AlertRule {
            id: "high_memory".to_string(),
            name: "内存使用过高".to_string(),
            condition: AlertCondition::MemoryUsageAbove(1000000.0),
            severity: AlertSeverity::Error,
            enabled: true,
            cooldown: Duration::from_secs(600),
            last_triggered: None,
        },
    ];
    
    for rule in alert_rules {
        cache_monitor.add_alert_rule(rule).await?;
    }
    
    // 收集指标
    cache_monitor.collect_metrics("lru_cache", &lru_stats).await?;
    
    // 获取指标
    if let Some(metrics) = cache_monitor.get_metrics("lru_cache").await {
        info!("缓存指标: 命中率 {:.2}%, 内存使用 {} 字节, 总请求 {}", 
              metrics.hit_rate * 100.0, metrics.memory_usage_bytes, metrics.total_requests);
    }
    
    let monitor_stats = cache_monitor.get_monitor_stats().await;
    info!("监控统计: 收集指标 {}, 触发告警 {}, 监控错误 {}", 
          monitor_stats.total_metrics_collected, monitor_stats.alerts_triggered, monitor_stats.monitoring_errors);

    info!("✅ 2025 年异步缓存系统演示完成!");
    
    Ok(())
}
