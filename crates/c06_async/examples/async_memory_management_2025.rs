use anyhow::Result;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};
use tokio::time::sleep;
use tracing::{debug, info, warn};

/// 2025年异步内存管理优化演示
/// 展示最新的异步内存管理技术和最佳实践

/// 1. 异步内存池管理器
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryPoolConfig {
    pub initial_size: usize,
    pub max_size: usize,
    pub chunk_size: usize,
    pub growth_factor: f64,
}

impl Default for MemoryPoolConfig {
    fn default() -> Self {
        Self {
            initial_size: 1024,
            max_size: 1024 * 1024,
            chunk_size: 64,
            growth_factor: 1.5,
        }
    }
}

#[derive(Debug, Clone)]
pub struct MemoryChunk {
    pub id: usize,
    pub size: usize,
    pub data: Vec<u8>,
    pub allocated_at: Instant,
    pub last_accessed: Instant,
}

pub struct AsyncMemoryPool {
    config: MemoryPoolConfig,
    chunks: Arc<RwLock<Vec<MemoryChunk>>>,
    available_chunks: Arc<RwLock<Vec<usize>>>,
    allocated_chunks: Arc<RwLock<HashMap<usize, usize>>>,
    stats: Arc<RwLock<MemoryPoolStats>>,
    semaphore: Arc<Semaphore>,
}

#[derive(Debug, Clone, Default)]
pub struct MemoryPoolStats {
    pub total_allocations: usize,
    pub total_deallocations: usize,
    pub peak_memory_usage: usize,
    pub current_memory_usage: usize,
    pub allocation_requests: usize,
    pub cache_hits: usize,
    pub cache_misses: usize,
}

impl AsyncMemoryPool {
    pub fn new(config: MemoryPoolConfig) -> Self {
        let semaphore = Arc::new(Semaphore::new(config.max_size / config.chunk_size));
        let pool = Self {
            config,
            chunks: Arc::new(RwLock::new(Vec::new())),
            available_chunks: Arc::new(RwLock::new(Vec::new())),
            allocated_chunks: Arc::new(RwLock::new(HashMap::new())),
            stats: Arc::new(RwLock::new(MemoryPoolStats::default())),
            semaphore,
        };

        // 初始化内存池
        tokio::spawn({
            let pool = pool.clone();
            async move {
                pool.initialize_pool().await;
            }
        });

        pool
    }

    async fn initialize_pool(&self) {
        let mut chunks = self.chunks.write().await;
        let mut available = self.available_chunks.write().await;

        for i in 0..(self.config.initial_size / self.config.chunk_size) {
            let chunk = MemoryChunk {
                id: i,
                size: self.config.chunk_size,
                data: vec![0u8; self.config.chunk_size],
                allocated_at: Instant::now(),
                last_accessed: Instant::now(),
            };

            chunks.push(chunk);
            available.push(i);
        }

        info!("内存池初始化完成，创建了 {} 个块", available.len());
    }

    pub async fn allocate(&self, size: usize) -> Result<usize> {
        let _permit = self.semaphore.acquire().await.unwrap();

        let mut stats = self.stats.write().await;
        stats.allocation_requests += 1;

        // 尝试从可用块中分配
        let mut available = self.available_chunks.write().await;
        if let Some(chunk_id) = available.pop() {
            let mut allocated = self.allocated_chunks.write().await;
            allocated.insert(chunk_id, size);
            stats.cache_hits += 1;
            stats.total_allocations += 1;

            let mut chunks = self.chunks.write().await;
            if let Some(chunk) = chunks.get_mut(chunk_id) {
                chunk.last_accessed = Instant::now();
            }

            info!("从内存池分配块 {}，大小: {} 字节", chunk_id, size);
            return Ok(chunk_id);
        }

        // 需要创建新块
        stats.cache_misses += 1;
        self.create_new_chunk(size).await
    }

    async fn create_new_chunk(&self, size: usize) -> Result<usize> {
        let mut chunks = self.chunks.write().await;
        let chunk_id = chunks.len();

        if chunk_id >= self.config.max_size / self.config.chunk_size {
            return Err(anyhow::anyhow!("内存池已达到最大大小限制"));
        }

        let chunk = MemoryChunk {
            id: chunk_id,
            size: self.config.chunk_size,
            data: vec![0u8; self.config.chunk_size],
            allocated_at: Instant::now(),
            last_accessed: Instant::now(),
        };

        chunks.push(chunk);

        let mut allocated = self.allocated_chunks.write().await;
        allocated.insert(chunk_id, size);

        let mut stats = self.stats.write().await;
        stats.total_allocations += 1;
        stats.current_memory_usage += self.config.chunk_size;
        if stats.current_memory_usage > stats.peak_memory_usage {
            stats.peak_memory_usage = stats.current_memory_usage;
        }

        info!("创建新内存块 {}，大小: {} 字节", chunk_id, size);
        Ok(chunk_id)
    }

    pub async fn deallocate(&self, chunk_id: usize) -> Result<()> {
        let mut allocated = self.allocated_chunks.write().await;
        if allocated.remove(&chunk_id).is_some() {
            let mut available = self.available_chunks.write().await;
            available.push(chunk_id);

            let mut stats = self.stats.write().await;
            stats.total_deallocations += 1;
            stats.current_memory_usage = stats
                .current_memory_usage
                .saturating_sub(self.config.chunk_size);

            info!("释放内存块 {}", chunk_id);
            Ok(())
        } else {
            Err(anyhow::anyhow!("块 {} 未分配", chunk_id))
        }
    }

    pub async fn get_stats(&self) -> MemoryPoolStats {
        self.stats.read().await.clone()
    }

    pub async fn cleanup_unused_chunks(&self, max_age: Duration) {
        let chunks = self.chunks.write().await;
        let mut available = self.available_chunks.write().await;
        let mut stats = self.stats.write().await;

        let now = Instant::now();
        let mut removed_count = 0;

        // 移除长时间未使用的块
        let current_len = available.len();
        available.retain(|&chunk_id| {
            if let Some(chunk) = chunks.get(chunk_id) {
                let age = now.duration_since(chunk.last_accessed);
                if age > max_age && current_len > self.config.initial_size / self.config.chunk_size
                {
                    removed_count += 1;
                    stats.current_memory_usage =
                        stats.current_memory_usage.saturating_sub(chunk.size);
                    false
                } else {
                    true
                }
            } else {
                false
            }
        });

        if removed_count > 0 {
            info!("清理了 {} 个未使用的内存块", removed_count);
        }
    }
}

impl Clone for AsyncMemoryPool {
    fn clone(&self) -> Self {
        Self {
            config: self.config.clone(),
            chunks: self.chunks.clone(),
            available_chunks: self.available_chunks.clone(),
            allocated_chunks: self.allocated_chunks.clone(),
            stats: self.stats.clone(),
            semaphore: self.semaphore.clone(),
        }
    }
}

/// 2. 异步垃圾回收器
pub struct AsyncGarbageCollector {
    objects: Arc<RwLock<HashMap<usize, GarbageCollectable>>>,
    reference_counts: Arc<RwLock<HashMap<usize, usize>>>,
    gc_stats: Arc<RwLock<GCStats>>,
    gc_interval: Duration,
}

#[derive(Debug, Clone)]
pub struct GarbageCollectable {
    pub id: usize,
    pub size: usize,
    pub created_at: Instant,
    pub last_accessed: Instant,
    pub references: Vec<usize>,
}

#[derive(Debug, Clone, Default)]
pub struct GCStats {
    pub total_objects: usize,
    pub collected_objects: usize,
    pub gc_cycles: usize,
    pub total_gc_time: Duration,
    pub memory_freed: usize,
}

impl AsyncGarbageCollector {
    pub fn new(gc_interval: Duration) -> Self {
        let gc = Self {
            objects: Arc::new(RwLock::new(HashMap::new())),
            reference_counts: Arc::new(RwLock::new(HashMap::new())),
            gc_stats: Arc::new(RwLock::new(GCStats::default())),
            gc_interval,
        };

        // 启动垃圾回收任务
        let gc_clone = gc.clone();
        tokio::spawn(async move {
            gc_clone.gc_loop().await;
        });

        gc
    }

    pub async fn create_object(&self, id: usize, size: usize) -> Result<()> {
        let object = GarbageCollectable {
            id,
            size,
            created_at: Instant::now(),
            last_accessed: Instant::now(),
            references: Vec::new(),
        };

        self.objects.write().await.insert(id, object);
        self.reference_counts.write().await.insert(id, 1);

        let mut stats = self.gc_stats.write().await;
        stats.total_objects += 1;

        info!("创建对象 {}，大小: {} 字节", id, size);
        Ok(())
    }

    pub async fn add_reference(&self, from_id: usize, to_id: usize) -> Result<()> {
        let mut objects = self.objects.write().await;
        if let Some(from_obj) = objects.get_mut(&from_id) {
            from_obj.references.push(to_id);
            from_obj.last_accessed = Instant::now();
        }

        let mut ref_counts = self.reference_counts.write().await;
        *ref_counts.entry(to_id).or_insert(0) += 1;

        debug!("对象 {} 引用对象 {}", from_id, to_id);
        Ok(())
    }

    pub async fn remove_reference(&self, from_id: usize, to_id: usize) -> Result<()> {
        let mut objects = self.objects.write().await;
        if let Some(from_obj) = objects.get_mut(&from_id) {
            from_obj.references.retain(|&id| id != to_id);
            from_obj.last_accessed = Instant::now();
        }

        let mut ref_counts = self.reference_counts.write().await;
        if let Some(count) = ref_counts.get_mut(&to_id) {
            *count = count.saturating_sub(1);
        }

        debug!("对象 {} 取消引用对象 {}", from_id, to_id);
        Ok(())
    }

    async fn gc_loop(&self) {
        let mut interval = tokio::time::interval(self.gc_interval);
        loop {
            interval.tick().await;
            let _ = self.collect_garbage().await;
        }
    }

    pub async fn collect_garbage(&self) -> Result<()> {
        let start_time = Instant::now();

        let mut stats = self.gc_stats.write().await;
        stats.gc_cycles += 1;

        // 标记阶段：标记所有可达对象
        let mut reachable = std::collections::HashSet::new();
        let objects = self.objects.read().await;
        let ref_counts = self.reference_counts.read().await;

        // 从根对象开始标记
        for (id, count) in ref_counts.iter() {
            if *count > 0 {
                self.mark_reachable(*id, &objects, &mut reachable);
            }
        }

        // 清理阶段：删除不可达对象
        let mut objects_write = self.objects.write().await;
        let mut ref_counts_write = self.reference_counts.write().await;
        let mut collected_count = 0;
        let mut memory_freed = 0;

        objects_write.retain(|id, object| {
            if reachable.contains(id) {
                true
            } else {
                collected_count += 1;
                memory_freed += object.size;
                ref_counts_write.remove(id);
                false
            }
        });

        stats.collected_objects += collected_count;
        stats.memory_freed += memory_freed;
        stats.total_gc_time += start_time.elapsed();

        if collected_count > 0 {
            info!(
                "垃圾回收完成，回收了 {} 个对象，释放内存: {} 字节",
                collected_count, memory_freed
            );
        }

        Ok(())
    }

    fn mark_reachable(
        &self,
        object_id: usize,
        objects: &HashMap<usize, GarbageCollectable>,
        reachable: &mut std::collections::HashSet<usize>,
    ) {
        if reachable.contains(&object_id) {
            return;
        }

        reachable.insert(object_id);

        if let Some(object) = objects.get(&object_id) {
            for &ref_id in &object.references {
                self.mark_reachable(ref_id, objects, reachable);
            }
        }
    }

    pub async fn get_stats(&self) -> GCStats {
        self.gc_stats.read().await.clone()
    }
}

impl Clone for AsyncGarbageCollector {
    fn clone(&self) -> Self {
        Self {
            objects: self.objects.clone(),
            reference_counts: self.reference_counts.clone(),
            gc_stats: self.gc_stats.clone(),
            gc_interval: self.gc_interval,
        }
    }
}

/// 3. 异步内存监控器
pub struct AsyncMemoryMonitor {
    memory_usage: Arc<AtomicU64>,
    peak_memory: Arc<AtomicU64>,
    allocation_count: Arc<AtomicUsize>,
    deallocation_count: Arc<AtomicUsize>,
    monitor_interval: Duration,
    alert_threshold: f64,
}

impl AsyncMemoryMonitor {
    pub fn new(monitor_interval: Duration, alert_threshold: f64) -> Self {
        let monitor = Self {
            memory_usage: Arc::new(AtomicU64::new(0)),
            peak_memory: Arc::new(AtomicU64::new(0)),
            allocation_count: Arc::new(AtomicUsize::new(0)),
            deallocation_count: Arc::new(AtomicUsize::new(0)),
            monitor_interval,
            alert_threshold,
        };

        // 启动监控任务
        let monitor_clone = monitor.clone();
        tokio::spawn(async move {
            monitor_clone.monitor_loop().await;
        });

        monitor
    }

    pub fn record_allocation(&self, size: usize) {
        self.memory_usage.fetch_add(size as u64, Ordering::Relaxed);
        self.allocation_count.fetch_add(1, Ordering::Relaxed);

        let current = self.memory_usage.load(Ordering::Relaxed);
        let peak = self.peak_memory.load(Ordering::Relaxed);
        if current > peak {
            self.peak_memory.store(current, Ordering::Relaxed);
        }
    }

    pub fn record_deallocation(&self, size: usize) {
        self.memory_usage.fetch_sub(size as u64, Ordering::Relaxed);
        self.deallocation_count.fetch_add(1, Ordering::Relaxed);
    }

    async fn monitor_loop(&self) {
        let mut interval = tokio::time::interval(self.monitor_interval);
        loop {
            interval.tick().await;
            self.check_memory_usage().await;
        }
    }

    async fn check_memory_usage(&self) {
        let current_usage = self.memory_usage.load(Ordering::Relaxed);
        let peak_usage = self.peak_memory.load(Ordering::Relaxed);

        if peak_usage > 0 {
            let usage_ratio = current_usage as f64 / peak_usage as f64;
            if usage_ratio > self.alert_threshold {
                warn!(
                    "内存使用率过高: {:.2}% ({}/{} 字节)",
                    usage_ratio * 100.0,
                    current_usage,
                    peak_usage
                );
            }
        }

        debug!(
            "内存监控 - 当前: {} 字节, 峰值: {} 字节",
            current_usage, peak_usage
        );
    }

    pub fn get_stats(&self) -> MemoryMonitorStats {
        MemoryMonitorStats {
            current_memory_usage: self.memory_usage.load(Ordering::Relaxed),
            peak_memory_usage: self.peak_memory.load(Ordering::Relaxed),
            total_allocations: self.allocation_count.load(Ordering::Relaxed),
            total_deallocations: self.deallocation_count.load(Ordering::Relaxed),
        }
    }
}

#[derive(Debug, Clone)]
pub struct MemoryMonitorStats {
    pub current_memory_usage: u64,
    pub peak_memory_usage: u64,
    pub total_allocations: usize,
    pub total_deallocations: usize,
}

impl Clone for AsyncMemoryMonitor {
    fn clone(&self) -> Self {
        Self {
            memory_usage: self.memory_usage.clone(),
            peak_memory: self.peak_memory.clone(),
            allocation_count: self.allocation_count.clone(),
            deallocation_count: self.deallocation_count.clone(),
            monitor_interval: self.monitor_interval,
            alert_threshold: self.alert_threshold,
        }
    }
}

/// 4. 异步内存优化管理器
pub struct AsyncMemoryOptimizer {
    memory_pool: AsyncMemoryPool,
    garbage_collector: AsyncGarbageCollector,
    memory_monitor: AsyncMemoryMonitor,
    optimization_config: OptimizationConfig,
}

#[derive(Debug, Clone)]
pub struct OptimizationConfig {
    pub enable_pooling: bool,
    pub enable_gc: bool,
    pub enable_monitoring: bool,
    pub gc_interval: Duration,
    pub monitor_interval: Duration,
    pub pool_cleanup_interval: Duration,
}

impl Default for OptimizationConfig {
    fn default() -> Self {
        Self {
            enable_pooling: true,
            enable_gc: true,
            enable_monitoring: true,
            gc_interval: Duration::from_secs(30),
            monitor_interval: Duration::from_secs(10),
            pool_cleanup_interval: Duration::from_secs(60),
        }
    }
}

impl AsyncMemoryOptimizer {
    pub fn new(config: OptimizationConfig) -> Self {
        let pool_config = MemoryPoolConfig::default();
        let memory_pool = AsyncMemoryPool::new(pool_config);
        let garbage_collector = AsyncGarbageCollector::new(config.gc_interval);
        let memory_monitor = AsyncMemoryMonitor::new(config.monitor_interval, 0.8);

        Self {
            memory_pool,
            garbage_collector,
            memory_monitor,
            optimization_config: config,
        }
    }

    pub async fn optimize_memory_usage(&self) -> Result<()> {
        if self.optimization_config.enable_pooling {
            self.memory_pool
                .cleanup_unused_chunks(Duration::from_secs(300))
                .await;
        }

        if self.optimization_config.enable_gc {
            self.garbage_collector.collect_garbage().await?;
        }

        Ok(())
    }

    pub async fn get_comprehensive_stats(&self) -> ComprehensiveMemoryStats {
        let pool_stats = self.memory_pool.get_stats().await;
        let gc_stats = self.garbage_collector.get_stats().await;
        let monitor_stats = self.memory_monitor.get_stats();

        ComprehensiveMemoryStats {
            pool_stats,
            gc_stats,
            monitor_stats,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ComprehensiveMemoryStats {
    pub pool_stats: MemoryPoolStats,
    pub gc_stats: GCStats,
    pub monitor_stats: MemoryMonitorStats,
}

#[tokio::main]
async fn main() -> Result<()> {
    tracing_subscriber::fmt::init();

    info!("🚀 开始 2025 年异步内存管理优化演示");

    // 1. 演示异步内存池
    info!("💾 演示异步内存池管理");
    let pool_config = MemoryPoolConfig {
        initial_size: 2048,
        max_size: 8192,
        chunk_size: 128,
        growth_factor: 1.5,
    };

    let memory_pool = AsyncMemoryPool::new(pool_config);

    // 等待初始化完成
    sleep(Duration::from_millis(100)).await;

    // 分配一些内存块
    let mut allocated_chunks = Vec::new();
    for i in 0..10 {
        let chunk_id = memory_pool.allocate(64).await?;
        allocated_chunks.push(chunk_id);
        info!("分配内存块 {} 用于对象 {}", chunk_id, i);
    }

    // 释放一些内存块
    for &chunk_id in &allocated_chunks[0..5] {
        memory_pool.deallocate(chunk_id).await?;
        info!("释放内存块 {}", chunk_id);
    }

    let pool_stats = memory_pool.get_stats().await;
    info!("内存池统计:");
    info!(
        "   总分配: {}, 总释放: {}",
        pool_stats.total_allocations, pool_stats.total_deallocations
    );
    info!(
        "   缓存命中: {}, 缓存未命中: {}",
        pool_stats.cache_hits, pool_stats.cache_misses
    );
    info!("   当前内存使用: {} 字节", pool_stats.current_memory_usage);

    // 2. 演示异步垃圾回收器
    info!("🗑️ 演示异步垃圾回收器");
    let gc = AsyncGarbageCollector::new(Duration::from_secs(5));

    // 创建一些对象
    for i in 0..20 {
        gc.create_object(i, 256).await?;
    }

    // 建立一些引用关系
    for i in 0..10 {
        gc.add_reference(i, i + 10).await?;
    }

    // 移除一些引用，使对象变为垃圾
    for i in 5..10 {
        gc.remove_reference(i, i + 10).await?;
    }

    // 手动触发垃圾回收
    gc.collect_garbage().await?;

    let gc_stats = gc.get_stats().await;
    info!("垃圾回收统计:");
    info!(
        "   总对象: {}, 回收对象: {}",
        gc_stats.total_objects, gc_stats.collected_objects
    );
    info!(
        "   GC周期: {}, 释放内存: {} 字节",
        gc_stats.gc_cycles, gc_stats.memory_freed
    );

    // 3. 演示异步内存监控器
    info!("📊 演示异步内存监控器");
    let monitor = AsyncMemoryMonitor::new(Duration::from_secs(2), 0.7);

    // 模拟内存分配和释放
    for i in 0..50 {
        monitor.record_allocation(1024);
        if i % 3 == 0 {
            monitor.record_deallocation(512);
        }
    }

    sleep(Duration::from_millis(100)).await;

    let monitor_stats = monitor.get_stats();
    info!("内存监控统计:");
    info!(
        "   当前内存使用: {} 字节",
        monitor_stats.current_memory_usage
    );
    info!("   峰值内存使用: {} 字节", monitor_stats.peak_memory_usage);
    info!(
        "   总分配: {}, 总释放: {}",
        monitor_stats.total_allocations, monitor_stats.total_deallocations
    );

    // 4. 演示综合内存优化管理器
    info!("⚡ 演示综合异步内存优化管理器");
    let config = OptimizationConfig::default();
    let optimizer = AsyncMemoryOptimizer::new(config);

    // 执行内存优化
    optimizer.optimize_memory_usage().await?;

    let comprehensive_stats = optimizer.get_comprehensive_stats().await;
    info!("综合内存统计:");
    info!(
        "   内存池 - 分配: {}, 释放: {}",
        comprehensive_stats.pool_stats.total_allocations,
        comprehensive_stats.pool_stats.total_deallocations
    );
    info!(
        "   垃圾回收 - 对象: {}, 回收: {}",
        comprehensive_stats.gc_stats.total_objects, comprehensive_stats.gc_stats.collected_objects
    );
    info!(
        "   内存监控 - 当前: {} 字节, 峰值: {} 字节",
        comprehensive_stats.monitor_stats.current_memory_usage,
        comprehensive_stats.monitor_stats.peak_memory_usage
    );

    info!("✅ 2025 年异步内存管理优化演示完成!");

    Ok(())
}
