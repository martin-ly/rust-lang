//! 内存优化和资源管理模块
//! 
//! 提供智能内存管理、资源池、内存监控和优化建议

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Semaphore};
use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use thiserror::Error;

/// 内存使用统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryStats {
    /// 总内存使用量 (字节)
    pub total_memory: u64,
    /// 已使用内存 (字节)
    pub used_memory: u64,
    /// 可用内存 (字节)
    pub available_memory: u64,
    /// 内存使用率 (%)
    pub memory_usage_percent: f64,
    /// 峰值内存使用 (字节)
    pub peak_memory: u64,
    /// 内存分配次数
    pub allocation_count: u64,
    /// 内存释放次数
    pub deallocation_count: u64,
    /// 内存泄漏检测
    pub potential_leaks: u64,
    /// 最后更新时间
    pub last_updated: DateTime<Utc>,
}

/// 内存池配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryPoolConfig {
    /// 池名称
    pub name: String,
    /// 初始大小 (字节)
    pub initial_size: u64,
    /// 最大大小 (字节)
    pub max_size: u64,
    /// 最小大小 (字节)
    pub min_size: u64,
    /// 增长因子
    pub growth_factor: f64,
    /// 是否启用自动清理
    pub auto_cleanup: bool,
    /// 清理间隔
    pub cleanup_interval: Duration,
    /// 最大空闲时间
    pub max_idle_time: Duration,
}

/// 内存池项
#[derive(Debug, Clone)]
pub struct MemoryPoolItem {
    /// 项ID
    pub id: String,
    /// 数据
    pub data: Vec<u8>,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 最后使用时间
    pub last_used: DateTime<Utc>,
    /// 使用次数
    pub usage_count: u64,
    /// 是否正在使用
    pub in_use: bool,
}

/// 内存池
pub struct MemoryPool {
    /// 配置
    config: MemoryPoolConfig,
    /// 池数据
    items: Arc<RwLock<HashMap<String, MemoryPoolItem>>>,
    /// 可用项ID
    available_items: Arc<RwLock<Vec<String>>>,
    /// 使用中项ID
    used_items: Arc<RwLock<Vec<String>>>,
    /// 统计信息
    stats: Arc<RwLock<MemoryPoolStats>>,
    /// 信号量控制并发访问
    semaphore: Arc<Semaphore>,
}

/// 内存池统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryPoolStats {
    /// 总项数
    pub total_items: u64,
    /// 可用项数
    pub available_items: u64,
    /// 使用中项数
    pub used_items: u64,
    /// 总内存使用
    pub total_memory_usage: u64,
    /// 命中率
    pub hit_rate: f64,
    /// 创建时间
    pub created_at: DateTime<Utc>,
    /// 最后清理时间
    pub last_cleanup: Option<DateTime<Utc>>,
}

/// 内存优化器
pub struct MemoryOptimizer {
    /// 内存统计
    memory_stats: Arc<RwLock<MemoryStats>>,
    /// 内存池集合
    memory_pools: Arc<RwLock<HashMap<String, Arc<MemoryPool>>>>,
    /// 优化配置
    optimization_config: OptimizationConfig,
    /// 监控任务句柄
    monitor_handle: Arc<RwLock<Option<tokio::task::JoinHandle<()>>>>,
}

/// 优化配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptimizationConfig {
    /// 是否启用自动优化
    pub auto_optimization: bool,
    /// 内存使用率阈值 (%)
    pub memory_threshold: f64,
    /// 优化间隔
    pub optimization_interval: Duration,
    /// 是否启用内存压缩
    pub enable_compression: bool,
    /// 是否启用内存预分配
    pub enable_preallocation: bool,
    /// 预分配大小 (字节)
    pub preallocation_size: u64,
    /// 是否启用垃圾回收
    pub enable_gc: bool,
    /// 垃圾回收间隔
    pub gc_interval: Duration,
}

impl Default for OptimizationConfig {
    fn default() -> Self {
        Self {
            auto_optimization: true,
            memory_threshold: 80.0,
            optimization_interval: Duration::from_secs(60),
            enable_compression: true,
            enable_preallocation: true,
            preallocation_size: 1024 * 1024, // 1MB
            enable_gc: true,
            gc_interval: Duration::from_secs(300), // 5分钟
        }
    }
}

impl MemoryPool {
    /// 创建新的内存池
    pub fn new(config: MemoryPoolConfig) -> Self {
        let max_concurrent = (config.max_size / 1024) as usize; // 假设每个项至少1KB
        Self {
            items: Arc::new(RwLock::new(HashMap::new())),
            available_items: Arc::new(RwLock::new(Vec::new())),
            used_items: Arc::new(RwLock::new(Vec::new())),
            stats: Arc::new(RwLock::new(MemoryPoolStats {
                total_items: 0,
                available_items: 0,
                used_items: 0,
                total_memory_usage: 0,
                hit_rate: 0.0,
                created_at: Utc::now(),
                last_cleanup: None,
            })),
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            config,
        }
    }

    /// 获取内存池项
    pub async fn acquire(&self, size: usize) -> Result<MemoryPoolItem, MemoryOptimizationError> {
        let _permit = self.semaphore.acquire().await.map_err(|_| MemoryOptimizationError::AcquisitionFailed("信号量获取失败".to_string()))?;
        
        let mut available_items = self.available_items.write().await;
        let mut used_items = self.used_items.write().await;
        let mut items = self.items.write().await;
        
        // 查找合适大小的可用项
        if let Some(item_id) = available_items.iter().find(|id| {
            if let Some(item) = items.get(*id) {
                item.data.len() >= size && !item.in_use
            } else {
                false
            }
        }) {
            let item_id = item_id.clone();
            available_items.retain(|id| id != &item_id);
            used_items.push(item_id.clone());
            
            if let Some(item) = items.get_mut(&item_id) {
                item.in_use = true;
                item.last_used = Utc::now();
                item.usage_count += 1;
                
                // 更新统计
                self.update_stats().await;
                
                return Ok(item.clone());
            }
        }
        
        // 如果没有合适的可用项，创建新项
        let new_item = MemoryPoolItem {
            id: uuid::Uuid::new_v4().to_string(),
            data: vec![0u8; size],
            created_at: Utc::now(),
            last_used: Utc::now(),
            usage_count: 1,
            in_use: true,
        };
        
        let item_id = new_item.id.clone();
        items.insert(item_id.clone(), new_item.clone());
        used_items.push(item_id);
        
        self.update_stats().await;
        
        Ok(new_item)
    }

    /// 释放内存池项
    pub async fn release(&self, item_id: &str) -> Result<(), MemoryOptimizationError> {
        let mut items = self.items.write().await;
        let mut available_items = self.available_items.write().await;
        let mut used_items = self.used_items.write().await;
        
        if let Some(item) = items.get_mut(item_id) {
            item.in_use = false;
            item.last_used = Utc::now();
            
            used_items.retain(|id| id != item_id);
            available_items.push(item_id.to_string());
            
            self.update_stats().await;
            Ok(())
        } else {
            Err(MemoryOptimizationError::ItemNotFound(item_id.to_string()))
        }
    }

    /// 清理未使用的项
    pub async fn cleanup(&self) -> Result<u64, MemoryOptimizationError> {
        let mut items = self.items.write().await;
        let mut available_items = self.available_items.write().await;
        let mut stats = self.stats.write().await;
        
        let cutoff_time = Utc::now() - chrono::Duration::from_std(self.config.max_idle_time).unwrap();
        let mut removed_count = 0;
        
        // 移除长时间未使用的项
        available_items.retain(|item_id| {
            if let Some(item) = items.get(item_id) {
                if item.last_used < cutoff_time && item.data.len() > self.config.min_size as usize {
                    items.remove(item_id);
                    removed_count += 1;
                    false
                } else {
                    true
                }
            } else {
                false
            }
        });
        
        stats.last_cleanup = Some(Utc::now());
        self.update_stats().await;
        
        Ok(removed_count)
    }

    /// 获取统计信息
    pub async fn get_stats(&self) -> MemoryPoolStats {
        self.stats.read().await.clone()
    }

    /// 更新统计信息
    async fn update_stats(&self) {
        let items = self.items.read().await;
        let available_items = self.available_items.read().await;
        let used_items = self.used_items.read().await;
        let mut stats = self.stats.write().await;
        
        stats.total_items = items.len() as u64;
        stats.available_items = available_items.len() as u64;
        stats.used_items = used_items.len() as u64;
        stats.total_memory_usage = items.values().map(|item| item.data.len() as u64).sum();
        
        if stats.total_items > 0 {
            stats.hit_rate = (stats.used_items as f64 / stats.total_items as f64) * 100.0;
        }
    }
}

impl MemoryOptimizer {
    /// 创建新的内存优化器
    pub fn new(config: OptimizationConfig) -> Self {
        Self {
            memory_stats: Arc::new(RwLock::new(MemoryStats {
                total_memory: 0,
                used_memory: 0,
                available_memory: 0,
                memory_usage_percent: 0.0,
                peak_memory: 0,
                allocation_count: 0,
                deallocation_count: 0,
                potential_leaks: 0,
                last_updated: Utc::now(),
            })),
            memory_pools: Arc::new(RwLock::new(HashMap::new())),
            optimization_config: config,
            monitor_handle: Arc::new(RwLock::new(None)),
        }
    }

    /// 启动内存监控
    pub async fn start_monitoring(&self) -> Result<(), MemoryOptimizationError> {
        let mut handle = self.monitor_handle.write().await;
        if handle.is_some() {
            return Err(MemoryOptimizationError::AlreadyMonitoring);
        }

        let memory_stats = self.memory_stats.clone();
        let memory_pools = self.memory_pools.clone();
        let config = self.optimization_config.clone();

        let monitor_task = tokio::spawn(async move {
            let mut interval = tokio::time::interval(Duration::from_secs(10));
            loop {
                interval.tick().await;
                
                // 更新内存统计
                Self::update_memory_stats(&memory_stats).await;
                
                // 自动优化
                if config.auto_optimization {
                    Self::auto_optimize(&memory_stats, &memory_pools, &config).await;
                }
            }
        });

        *handle = Some(monitor_task);
        Ok(())
    }

    /// 停止内存监控
    pub async fn stop_monitoring(&self) -> Result<(), MemoryOptimizationError> {
        let mut handle = self.monitor_handle.write().await;
        if let Some(task) = handle.take() {
            task.abort();
        }
        Ok(())
    }

    /// 创建内存池
    pub async fn create_memory_pool(&self, config: MemoryPoolConfig) -> Result<(), MemoryOptimizationError> {
        let pool = Arc::new(MemoryPool::new(config.clone()));
        let mut pools = self.memory_pools.write().await;
        pools.insert(config.name.clone(), pool);
        Ok(())
    }

    /// 获取内存池
    pub async fn get_memory_pool(&self, name: &str) -> Option<Arc<MemoryPool>> {
        let pools = self.memory_pools.read().await;
        pools.get(name).cloned()
    }

    /// 执行内存优化
    pub async fn optimize(&self) -> Result<OptimizationResult, MemoryOptimizationError> {
        let mut result = OptimizationResult {
            memory_freed: 0,
            pools_optimized: 0,
            items_removed: 0,
            compression_ratio: 0.0,
            optimization_time: Duration::ZERO,
            recommendations: Vec::new(),
        };

        let start_time = Instant::now();

        // 清理所有内存池
        let pools = self.memory_pools.read().await;
        for (name, pool) in pools.iter() {
            match pool.cleanup().await {
                Ok(removed_count) => {
                    result.items_removed += removed_count;
                    result.pools_optimized += 1;
                    println!("内存池 '{}' 优化完成，移除了 {} 个项", name, removed_count);
                }
                Err(e) => {
                    println!("内存池 '{}' 优化失败: {:?}", name, e);
                }
            }
        }

        // 更新内存统计
        MemoryOptimizer::update_memory_stats(&self.memory_stats).await;

        // 生成优化建议
        result.recommendations = self.generate_recommendations().await;

        result.optimization_time = start_time.elapsed();
        Ok(result)
    }

    /// 获取内存统计
    pub async fn get_memory_stats(&self) -> MemoryStats {
        self.memory_stats.read().await.clone()
    }

    /// 获取所有内存池统计
    pub async fn get_all_pool_stats(&self) -> HashMap<String, MemoryPoolStats> {
        let pools = self.memory_pools.read().await;
        let mut stats = HashMap::new();
        
        for (name, pool) in pools.iter() {
            stats.insert(name.clone(), pool.get_stats().await);
        }
        
        stats
    }

    /// 更新内存统计
    async fn update_memory_stats(memory_stats: &Arc<RwLock<MemoryStats>>) {
        let mut stats = memory_stats.write().await;
        
        // 这里应该实现实际的内存统计获取
        // 目前使用模拟数据
        stats.total_memory = 8 * 1024 * 1024 * 1024; // 8GB
        stats.used_memory = 4 * 1024 * 1024 * 1024;  // 4GB
        stats.available_memory = stats.total_memory - stats.used_memory;
        stats.memory_usage_percent = (stats.used_memory as f64 / stats.total_memory as f64) * 100.0;
        
        if stats.used_memory > stats.peak_memory {
            stats.peak_memory = stats.used_memory;
        }
        
        stats.last_updated = Utc::now();
    }

    /// 自动优化
    async fn auto_optimize(
        memory_stats: &Arc<RwLock<MemoryStats>>,
        memory_pools: &Arc<RwLock<HashMap<String, Arc<MemoryPool>>>>,
        config: &OptimizationConfig,
    ) {
        let stats = memory_stats.read().await;
        
        if stats.memory_usage_percent > config.memory_threshold {
            println!("内存使用率过高 ({}%), 开始自动优化...", stats.memory_usage_percent);
            
            let pools = memory_pools.read().await;
            for (name, pool) in pools.iter() {
                if let Ok(removed_count) = pool.cleanup().await {
                    if removed_count > 0 {
                        println!("自动优化内存池 '{}', 移除了 {} 个项", name, removed_count);
                    }
                }
            }
        }
    }

    /// 生成优化建议
    async fn generate_recommendations(&self) -> Vec<String> {
        let stats = self.memory_stats.read().await;
        let mut recommendations = Vec::new();
        
        if stats.memory_usage_percent > 90.0 {
            recommendations.push("内存使用率过高，建议增加系统内存或优化应用程序".to_string());
        }
        
        if stats.potential_leaks > 0 {
            recommendations.push(format!("检测到 {} 个潜在内存泄漏，建议检查代码", stats.potential_leaks));
        }
        
        if stats.allocation_count > stats.deallocation_count * 2 {
            recommendations.push("内存分配次数远大于释放次数，可能存在内存泄漏".to_string());
        }
        
        if stats.peak_memory > (stats.total_memory as f64 * 0.8) as u64 {
            recommendations.push("峰值内存使用接近系统限制，建议优化内存使用".to_string());
        }
        
        recommendations
    }
}

/// 优化结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OptimizationResult {
    /// 释放的内存 (字节)
    pub memory_freed: u64,
    /// 优化的内存池数量
    pub pools_optimized: u64,
    /// 移除的项数量
    pub items_removed: u64,
    /// 压缩比率
    pub compression_ratio: f64,
    /// 优化耗时
    pub optimization_time: Duration,
    /// 优化建议
    pub recommendations: Vec<String>,
}

/// 内存优化错误
#[derive(Debug, Error)]
pub enum MemoryOptimizationError {
    #[error("获取失败: {0}")]
    AcquisitionFailed(String),
    
    #[error("项未找到: {0}")]
    ItemNotFound(String),
    
    #[error("已在监控中")]
    AlreadyMonitoring,
    
    #[error("内存池已存在: {0}")]
    PoolAlreadyExists(String),
    
    #[error("内存池未找到: {0}")]
    PoolNotFound(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("内存不足")]
    OutOfMemory,
    
    #[error("内部错误: {0}")]
    InternalError(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_memory_pool_creation() {
        let config = MemoryPoolConfig {
            name: "test_pool".to_string(),
            initial_size: 1024,
            max_size: 10240,
            min_size: 512,
            growth_factor: 1.5,
            auto_cleanup: true,
            cleanup_interval: Duration::from_secs(60),
            max_idle_time: Duration::from_secs(300),
        };

        let pool = MemoryPool::new(config);
        let stats = pool.get_stats().await;
        assert_eq!(stats.total_items, 0);
    }

    #[tokio::test]
    async fn test_memory_pool_acquire_release() {
        let config = MemoryPoolConfig {
            name: "test_pool".to_string(),
            initial_size: 1024,
            max_size: 10240,
            min_size: 512,
            growth_factor: 1.5,
            auto_cleanup: true,
            cleanup_interval: Duration::from_secs(60),
            max_idle_time: Duration::from_secs(300),
        };

        let pool = MemoryPool::new(config);
        
        // 获取项
        let item = pool.acquire(512).await.unwrap();
        assert_eq!(item.data.len(), 512);
        assert!(item.in_use);
        
        // 释放项
        pool.release(&item.id).await.unwrap();
        
        let stats = pool.get_stats().await;
        assert_eq!(stats.used_items, 0);
        assert_eq!(stats.available_items, 1);
    }

    #[tokio::test]
    async fn test_memory_optimizer_creation() {
        let config = OptimizationConfig::default();
        let optimizer = MemoryOptimizer::new(config);
        
        let stats = optimizer.get_memory_stats().await;
        assert_eq!(stats.total_memory, 0);
    }

    #[tokio::test]
    async fn test_memory_optimization() {
        let config = OptimizationConfig::default();
        let optimizer = MemoryOptimizer::new(config);
        
        let result = optimizer.optimize().await.unwrap();
        assert_eq!(result.pools_optimized, 0);
    }
}
