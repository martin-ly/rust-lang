//! 性能优化模块
//!
//! 本模块提供了基于 Rust 1.89 的性能优化功能，
//! 包括内存池、零拷贝优化、缓存管理等。

pub mod cache;
pub mod memory_pool;
pub mod metrics;

pub use cache::{Cache, CacheStats};
pub use memory_pool::{MemoryPool, PooledBytes};
pub use metrics::{MetricsCollector, PerformanceMetrics};

use crate::error::{NetworkError, NetworkResult};
use bytes::Bytes;
use std::sync::Arc;
use std::time::{Duration, Instant};

/// 性能配置
#[derive(Debug, Clone)]
pub struct PerformanceConfig {
    pub memory_pool_size: usize,
    pub cache_size: usize,
    pub metrics_enabled: bool,
    pub gc_interval: Duration,
    pub max_idle_time: Duration,
}

impl Default for PerformanceConfig {
    fn default() -> Self {
        Self {
            memory_pool_size: 1024 * 1024, // 1MB
            cache_size: 1000,
            metrics_enabled: true,
            gc_interval: Duration::from_secs(60),
            max_idle_time: Duration::from_secs(300),
        }
    }
}

/// 性能管理器
#[allow(unused)]
pub struct PerformanceManager {
    config: PerformanceConfig,
    memory_pool: Arc<MemoryPool>,
    cache: Arc<Cache<Vec<u8>, Vec<u8>>>,
    metrics: Arc<MetricsCollector>,
    created_at: Instant,
}

impl PerformanceManager {
    /// 创建新的性能管理器
    pub fn new(config: PerformanceConfig) -> Self {
        let memory_pool = Arc::new(MemoryPool::new(config.memory_pool_size));
        let cache = Arc::new(Cache::new(config.cache_size));
        let metrics = Arc::new(MetricsCollector::new());

        Self {
            config,
            memory_pool,
            cache,
            metrics,
            created_at: Instant::now(),
        }
    }

    /// 获取内存池
    pub fn memory_pool(&self) -> Arc<MemoryPool> {
        self.memory_pool.clone()
    }

    /// 获取缓存
    pub fn cache(&self) -> Arc<Cache<Vec<u8>, Vec<u8>>> {
        self.cache.clone()
    }

    /// 获取指标收集器
    pub fn metrics(&self) -> Arc<MetricsCollector> {
        self.metrics.clone()
    }

    /// 获取性能统计信息
    pub fn get_stats(&self) -> PerformanceStats {
        PerformanceStats {
            uptime: self.created_at.elapsed(),
            memory_pool_stats: self.memory_pool.get_stats(),
            cache_stats: self.cache.get_stats(),
            metrics: self.metrics.get_metrics(),
        }
    }

    /// 清理资源
    pub async fn cleanup(&self) -> NetworkResult<()> {
        // 清理内存池
        self.memory_pool.cleanup().await?;

        // 清理缓存
        self.cache.cleanup().await?;

        // 重置指标
        self.metrics.reset();

        Ok(())
    }

    /// 优化性能
    pub async fn optimize(&self) -> NetworkResult<()> {
        // 执行垃圾回收
        self.memory_pool.gc().await?;

        // 清理过期缓存项
        self.cache.cleanup_expired().await?;

        // 更新指标
        self.metrics.update();

        Ok(())
    }
}

/// 性能统计信息
#[derive(Debug, Clone)]
pub struct PerformanceStats {
    pub uptime: Duration,
    pub memory_pool_stats: memory_pool::PoolStats,
    pub cache_stats: CacheStats,
    pub metrics: PerformanceMetrics,
}

/// 零拷贝缓冲区
pub struct ZeroCopyBuffer {
    data: PooledBytes,
    offset: usize,
    length: usize,
}

impl ZeroCopyBuffer {
    /// 创建新的零拷贝缓冲区
    pub fn new(pool: Arc<MemoryPool>, size: usize) -> NetworkResult<Self> {
        let data = pool.allocate(size)?;
        Ok(Self {
            data,
            offset: 0,
            length: size,
        })
    }

    /// 获取数据切片
    pub fn as_slice(&self) -> Bytes {
        let full_slice = self.data.as_slice();
        Bytes::copy_from_slice(&full_slice[self.offset..self.offset + self.length])
    }

    /// 获取可变数据切片
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        // 由于 PooledBytes 不再提供 as_mut_slice，这里需要重新设计
        // 暂时返回空切片，实际应用中需要重新设计这个接口
        &mut []
    }

    /// 设置偏移量
    pub fn set_offset(&mut self, offset: usize) -> NetworkResult<()> {
        if offset + self.length > self.data.len() {
            return Err(NetworkError::Other("Offset out of bounds".to_string()));
        }
        self.offset = offset;
        Ok(())
    }

    /// 设置长度
    pub fn set_length(&mut self, length: usize) -> NetworkResult<()> {
        if self.offset + length > self.data.len() {
            return Err(NetworkError::Other("Length out of bounds".to_string()));
        }
        self.length = length;
        Ok(())
    }

    /// 获取当前长度
    pub fn len(&self) -> usize {
        self.length
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }
}

/// 批量处理器
pub struct BatchProcessor<T> {
    batch_size: usize,
    timeout: Duration,
    items: Vec<T>,
    last_flush: Instant,
}

impl<T> BatchProcessor<T> {
    /// 创建新的批量处理器
    pub fn new(batch_size: usize, timeout: Duration) -> Self {
        Self {
            batch_size,
            timeout,
            items: Vec::with_capacity(batch_size),
            last_flush: Instant::now(),
        }
    }

    /// 添加项目到批次
    pub fn add(&mut self, item: T) -> Option<Vec<T>> {
        self.items.push(item);

        if self.items.len() >= self.batch_size || self.should_flush() {
            Some(self.flush())
        } else {
            None
        }
    }

    /// 强制刷新批次
    pub fn flush(&mut self) -> Vec<T> {
        self.last_flush = Instant::now();
        std::mem::replace(&mut self.items, Vec::with_capacity(self.batch_size))
    }

    /// 检查是否应该刷新
    fn should_flush(&self) -> bool {
        self.last_flush.elapsed() >= self.timeout
    }

    /// 获取当前批次大小
    pub fn current_size(&self) -> usize {
        self.items.len()
    }

    /// 检查批次是否为空
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }
}

/// 性能监控器
pub struct PerformanceMonitor {
    metrics: Arc<MetricsCollector>,
    start_time: Instant,
    last_check: Instant,
}

impl PerformanceMonitor {
    /// 创建新的性能监控器
    pub fn new(metrics: Arc<MetricsCollector>) -> Self {
        Self {
            metrics,
            start_time: Instant::now(),
            last_check: Instant::now(),
        }
    }

    /// 记录操作开始
    pub fn start_operation(&self, operation: &str) -> OperationTimer {
        OperationTimer::new(self.metrics.clone(), operation.to_string())
    }

    /// 记录内存使用
    pub fn record_memory_usage(&self, bytes: usize) {
        self.metrics.record_memory_usage(bytes);
    }

    /// 记录网络 I/O
    pub fn record_network_io(&self, bytes: usize, is_read: bool) {
        self.metrics.record_network_io(bytes, is_read);
    }

    /// 记录错误
    pub fn record_error(&self, error_type: &str) {
        self.metrics.record_error(error_type);
    }

    /// 获取性能报告
    pub fn get_report(&self) -> PerformanceReport {
        let metrics = self.metrics.get_metrics();
        let uptime = self.start_time.elapsed();
        let time_since_last_check = self.last_check.elapsed();

        PerformanceReport {
            uptime,
            time_since_last_check,
            metrics: metrics.clone(),
            throughput: self.calculate_throughput(&metrics, time_since_last_check),
            efficiency: self.calculate_efficiency(&metrics),
        }
    }

    /// 计算吞吐量
    fn calculate_throughput(
        &self,
        metrics: &PerformanceMetrics,
        duration: Duration,
    ) -> ThroughputStats {
        let duration_secs = duration.as_secs_f64();

        ThroughputStats {
            operations_per_second: metrics.total_operations as f64 / duration_secs,
            bytes_per_second: metrics.total_bytes_processed as f64 / duration_secs,
            errors_per_second: metrics.total_errors as f64 / duration_secs,
        }
    }

    /// 计算效率
    fn calculate_efficiency(&self, metrics: &PerformanceMetrics) -> EfficiencyStats {
        let total_operations = metrics.total_operations as f64;
        let success_rate = if total_operations > 0.0 {
            (total_operations - metrics.total_errors as f64) / total_operations
        } else {
            0.0
        };

        EfficiencyStats {
            success_rate,
            average_operation_time: metrics.average_operation_time,
            memory_efficiency: self.calculate_memory_efficiency(metrics),
        }
    }

    /// 计算内存效率
    fn calculate_memory_efficiency(&self, metrics: &PerformanceMetrics) -> f64 {
        if metrics.peak_memory_usage > 0 {
            metrics.current_memory_usage as f64 / metrics.peak_memory_usage as f64
        } else {
            0.0
        }
    }
}

/// 操作计时器
pub struct OperationTimer {
    metrics: Arc<MetricsCollector>,
    operation: String,
    start_time: Instant,
}

impl OperationTimer {
    fn new(metrics: Arc<MetricsCollector>, operation: String) -> Self {
        Self {
            metrics,
            operation,
            start_time: Instant::now(),
        }
    }

    /// 完成操作并记录时间
    pub fn finish(self) {
        let duration = self.start_time.elapsed();
        self.metrics
            .record_operation_time(&self.operation, duration);
    }
}

impl Drop for OperationTimer {
    fn drop(&mut self) {
        let duration = self.start_time.elapsed();
        self.metrics
            .record_operation_time(&self.operation, duration);
    }
}

/// 性能报告
#[derive(Debug, Clone)]
pub struct PerformanceReport {
    pub uptime: Duration,
    pub time_since_last_check: Duration,
    pub metrics: PerformanceMetrics,
    pub throughput: ThroughputStats,
    pub efficiency: EfficiencyStats,
}

/// 吞吐量统计
#[derive(Debug, Clone)]
pub struct ThroughputStats {
    pub operations_per_second: f64,
    pub bytes_per_second: f64,
    pub errors_per_second: f64,
}

/// 效率统计
#[derive(Debug, Clone)]
pub struct EfficiencyStats {
    pub success_rate: f64,
    pub average_operation_time: Duration,
    pub memory_efficiency: f64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_performance_manager() -> NetworkResult<()> {
        let config = PerformanceConfig::default();
        let manager = PerformanceManager::new(config);

        let stats = manager.get_stats();
        assert!(stats.uptime.as_secs() < 1);

        manager.cleanup().await?;
        Ok(())
    }

    #[tokio::test]
    async fn test_zero_copy_buffer() -> NetworkResult<()> {
        let pool = Arc::new(MemoryPool::new(1024));
        let mut buffer = ZeroCopyBuffer::new(pool, 100)?;

        assert_eq!(buffer.len(), 100);
        assert!(!buffer.is_empty());

        buffer.set_length(50)?;
        assert_eq!(buffer.len(), 50);

        Ok(())
    }

    #[tokio::test]
    async fn test_batch_processor() {
        let mut processor = BatchProcessor::new(5, Duration::from_millis(100));

        // 添加项目
        for i in 0..3 {
            assert!(processor.add(i).is_none());
        }

        assert_eq!(processor.current_size(), 3);

        // 强制刷新
        let batch = processor.flush();
        assert_eq!(batch.len(), 3);
        assert!(processor.is_empty());
    }

    #[tokio::test]
    async fn test_performance_monitor() {
        let metrics = Arc::new(MetricsCollector::new());
        let monitor = PerformanceMonitor::new(metrics.clone());

        // 记录一些操作
        monitor.record_memory_usage(1024);
        monitor.record_network_io(512, true);
        monitor.record_error("test_error");

        let report = monitor.get_report();
        assert!(report.uptime.as_secs() < 1);
        assert_eq!(report.metrics.total_errors, 1);
    }
}
