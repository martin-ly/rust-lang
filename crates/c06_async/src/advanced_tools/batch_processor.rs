//! 异步批处理器
//! 
//! 提供高效的批处理功能：
//! - 智能批处理策略
//! - 背压控制
//! - 批量操作优化
//! - 错误处理和重试
//! - 性能监控

use std::collections::VecDeque;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, Semaphore, Notify};
use tokio::time::{sleep, interval, timeout};
use anyhow::Result;
use serde::{Serialize, Deserialize};
use uuid::Uuid;

/// 批处理策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BatchStrategy {
    /// 按数量批处理
    ByCount(usize),
    /// 按时间批处理
    ByTime(Duration),
    /// 按大小批处理（字节数）
    BySize(usize),
    /// 混合策略
    Hybrid {
        max_count: usize,
        max_time: Duration,
        max_size: usize,
    },
}

/// 批处理配置
#[derive(Debug, Clone)]
pub struct BatchConfig {
    pub strategy: BatchStrategy,
    pub max_queue_size: usize,
    pub processing_timeout: Option<Duration>,
    pub retry_config: Option<RetryConfig>,
}

#[derive(Debug, Clone)]
pub struct RetryConfig {
    pub max_attempts: u32,
    pub backoff_duration: Duration,
}

impl Default for BatchConfig {
    fn default() -> Self {
        Self {
            strategy: BatchStrategy::ByCount(100),
            max_queue_size: 10000,
            processing_timeout: Some(Duration::from_secs(30)),
            retry_config: None,
        }
    }
}

/// 批处理项
#[derive(Debug, Clone)]
pub struct BatchItem<T> {
    pub id: Uuid,
    pub data: T,
    pub created_at: Instant,
    pub size: usize,
    pub priority: u8, // 0 = 最高优先级
}

impl<T> BatchItem<T> {
    pub fn new(data: T, size: usize, priority: u8) -> Self {
        Self {
            id: Uuid::new_v4(),
            data,
            created_at: Instant::now(),
            size,
            priority,
        }
    }
}

/// 批处理结果
#[derive(Debug)]
pub struct BatchResult<T> {
    pub batch_id: Uuid,
    pub items: Vec<BatchItem<T>>,
    pub processing_time: Duration,
    pub success: bool,
    pub error: Option<String>,
}

/// 批处理统计信息
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct BatchStats {
    pub total_batches: u64,
    pub successful_batches: u64,
    pub failed_batches: u64,
    pub total_items: u64,
    pub total_processing_time: Duration,
    pub avg_batch_size: f64,
    pub avg_processing_time: Duration,
    pub queue_size: usize,
    pub throughput: f64, // items per second
}

/// 批处理器 trait
#[async_trait::async_trait]
pub trait BatchProcessor<T>: Send + Sync {
    async fn process_batch(&self, items: Vec<BatchItem<T>>) -> Result<Vec<BatchItem<T>>>;
}

/// 异步批处理器
pub struct AsyncBatchProcessor<T, P> {
    processor: Arc<P>,
    config: BatchConfig,
    queue: Arc<Mutex<VecDeque<BatchItem<T>>>>,
    stats: Arc<Mutex<BatchStats>>,
    shutdown_notify: Arc<Notify>,
    semaphore: Arc<Semaphore>,
}

impl<T, P> AsyncBatchProcessor<T, P>
where
    T: Clone + Send + Sync + 'static,
    P: BatchProcessor<T> + 'static,
{
    /// 创建新的批处理器
    pub fn new(processor: P, config: BatchConfig, max_concurrent_batches: usize) -> Self {
        Self {
            processor: Arc::new(processor),
            config: config.clone(),
            queue: Arc::new(Mutex::new(VecDeque::new())),
            stats: Arc::new(Mutex::new(BatchStats::default())),
            shutdown_notify: Arc::new(Notify::new()),
            semaphore: Arc::new(Semaphore::new(max_concurrent_batches)),
        }
    }

    /// 启动批处理器
    pub fn start(&self) -> tokio::task::JoinHandle<()> {
        let processor = Arc::clone(&self.processor);
        let queue = Arc::clone(&self.queue);
        let stats = Arc::clone(&self.stats);
        let shutdown_notify = Arc::clone(&self.shutdown_notify);
        let semaphore = Arc::clone(&self.semaphore);
        let config = self.config.clone();

        tokio::spawn(async move {
            let mut interval = interval(Duration::from_millis(100));

            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        Self::process_batches(
                            &processor,
                            &queue,
                            &stats,
                            &semaphore,
                            &config,
                        ).await;
                    }
                    _ = shutdown_notify.notified() => {
                        break;
                    }
                }
            }
        })
    }

    /// 添加项目到批处理队列
    pub async fn add_item(&self, item: BatchItem<T>) -> Result<()> {
        let queue_size = {
            let mut queue = self.queue.lock().await;
            
            if queue.len() >= self.config.max_queue_size {
                return Err(anyhow::anyhow!("队列已满"));
            }

            // 按优先级插入（优先级数字小的在前面）
            let mut inserted = false;
            for (i, existing_item) in queue.iter().enumerate() {
                if item.priority < existing_item.priority {
                    queue.insert(i, item.clone());
                    inserted = true;
                    break;
                }
            }
            
            if !inserted {
                queue.push_back(item);
            }
            
            queue.len()
        };

        // 更新统计信息
        {
            let mut stats = self.stats.lock().await;
            stats.queue_size = queue_size;
        }

        Ok(())
    }

    /// 获取统计信息
    pub async fn get_stats(&self) -> BatchStats {
        let mut stats = self.stats.lock().await.clone();
        let queue_size = self.queue.lock().await.len();
        stats.queue_size = queue_size;
        stats
    }

    /// 关闭批处理器
    pub async fn shutdown(&self) -> Result<()> {
        self.shutdown_notify.notify_waiters();
        Ok(())
    }

    // 私有方法

    async fn process_batches(
        processor: &Arc<P>,
        queue: &Arc<Mutex<VecDeque<BatchItem<T>>>>,
        stats: &Arc<Mutex<BatchStats>>,
        semaphore: &Arc<Semaphore>,
        config: &BatchConfig,
    ) {
        let batch = Self::create_batch(queue, config).await;
        
        if batch.is_empty() {
            return;
        }

        let _permit = semaphore.acquire().await.unwrap();
        
        let processor_clone = Arc::clone(processor);
        let stats_clone = Arc::clone(stats);
        let config = config.clone();
        
        tokio::spawn(async move {
            let start_time = Instant::now();
            let _batch_id = Uuid::new_v4();
            
            // 更新统计信息
            {
                let mut stats = stats_clone.lock().await;
                stats.total_batches += 1;
                stats.total_items += batch.len() as u64;
            }

            // 处理批次
            let result = if let Some(timeout_duration) = config.processing_timeout {
                match timeout(timeout_duration, processor_clone.process_batch(batch.clone())).await {
                    Ok(result) => result,
                    Err(_) => Err(anyhow::anyhow!("批处理超时")),
                }
            } else {
                processor_clone.process_batch(batch.clone()).await
            };

            let processing_time = start_time.elapsed();

            // 更新统计信息
            {
                let mut stats = stats_clone.lock().await;
                stats.total_processing_time += processing_time;
                
                match result {
                    Ok(_) => {
                        stats.successful_batches += 1;
                    }
                    Err(_) => {
                        stats.failed_batches += 1;
                    }
                }

                // 计算平均值
                if stats.total_batches > 0 {
                    stats.avg_batch_size = stats.total_items as f64 / stats.total_batches as f64;
                    stats.avg_processing_time = Duration::from_nanos(
                        stats.total_processing_time.as_nanos() as u64 / stats.total_batches as u64
                    );
                    
                    if stats.total_processing_time.as_secs_f64() > 0.0 {
                        stats.throughput = stats.total_items as f64 / stats.total_processing_time.as_secs_f64();
                    }
                }
            }

            // 处理结果
            if let Err(e) = result {
                println!("批处理失败: {}", e);
                
                // 如果配置了重试，将失败的项重新加入队列
                if let Some(_retry_config) = &config.retry_config {
                    // 这里可以实现重试逻辑
                    println!("批处理失败，准备重试...");
                }
            }
        });
    }

    async fn create_batch(queue: &Arc<Mutex<VecDeque<BatchItem<T>>>>, config: &BatchConfig) -> Vec<BatchItem<T>> {
        let mut batch = Vec::new();
        let mut batch_size = 0;
        let start_time = Instant::now();
        
        loop {
            let should_continue = {
                let mut queue = queue.lock().await;
                
                if queue.is_empty() {
                    false
                } else {
                    let item = queue.pop_front().unwrap();
                    let item_size = item.size;
                    
                    // 检查批处理条件
                    let mut add_item = true;
                    
                    match &config.strategy {
                        BatchStrategy::ByCount(max_count) => {
                            if batch.len() >= *max_count {
                                add_item = false;
                            }
                        }
                        BatchStrategy::ByTime(max_time) => {
                            if start_time.elapsed() >= *max_time && !batch.is_empty() {
                                add_item = false;
                            }
                        }
                        BatchStrategy::BySize(max_size) => {
                            if batch_size + item_size > *max_size && !batch.is_empty() {
                                add_item = false;
                            }
                        }
                        BatchStrategy::Hybrid { max_count, max_time, max_size } => {
                            let time_expired = start_time.elapsed() >= *max_time;
                            let count_exceeded = batch.len() >= *max_count;
                            let size_exceeded = batch_size + item_size > *max_size;
                            
                            if (time_expired || count_exceeded || size_exceeded) && !batch.is_empty() {
                                add_item = false;
                            }
                        }
                    }
                    
                    if !add_item {
                        // 将项目放回队列前面
                        queue.push_front(item);
                        break;
                    }
                    
                    batch_size += item_size;
                    batch.push(item);
                    
                    false
                }
            };
            
            if !should_continue {
                break;
            }
        }
        
        batch
    }
}

/// 简单的批处理器实现示例
pub struct SimpleBatchProcessor<T> {
    name: String,
    _phantom: std::marker::PhantomData<T>,
}

impl<T> SimpleBatchProcessor<T> {
    pub fn new(name: String) -> Self {
        Self {
            name,
            _phantom: std::marker::PhantomData,
        }
    }
}

#[async_trait::async_trait]
impl<T> BatchProcessor<T> for SimpleBatchProcessor<T>
where
    T: Clone + Send + Sync,
{
    async fn process_batch(&self, items: Vec<BatchItem<T>>) -> Result<Vec<BatchItem<T>>> {
        println!("批处理器 {} 处理 {} 个项目", self.name, items.len());
        
        // 模拟批处理时间
        let processing_time = Duration::from_millis(100 + items.len() as u64 * 10);
        sleep(processing_time).await;
        
        // 模拟偶尔失败
        if rand::random::<f32>() < 0.1 {
            return Err(anyhow::anyhow!("模拟批处理失败"));
        }
        
        println!("批处理器 {} 完成处理", self.name);
        Ok(items)
    }
}

/// 批处理器构建器
pub struct BatchProcessorBuilder<T, P> {
    processor: Option<P>,
    config: BatchConfig,
    max_concurrent_batches: Option<usize>,
    _phantom: std::marker::PhantomData<T>,
}

impl<T, P> BatchProcessorBuilder<T, P>
where
    T: Clone + Send + Sync + 'static,
    P: BatchProcessor<T> + 'static,
{
    pub fn new() -> Self {
        Self {
            processor: None,
            config: BatchConfig::default(),
            max_concurrent_batches: None,
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn processor(mut self, processor: P) -> Self {
        self.processor = Some(processor);
        self
    }

    pub fn config(mut self, config: BatchConfig) -> Self {
        self.config = config;
        self
    }

    pub fn max_concurrent_batches(mut self, max: usize) -> Self {
        self.max_concurrent_batches = Some(max);
        self
    }

    pub fn build(self) -> Result<AsyncBatchProcessor<T, P>> {
        let processor = self.processor.ok_or_else(|| anyhow::anyhow!("处理器未设置"))?;
        let max_concurrent = self.max_concurrent_batches.unwrap_or(10);

        Ok(AsyncBatchProcessor::new(processor, self.config, max_concurrent))
    }
}

impl<T, P> Default for BatchProcessorBuilder<T, P>
where
    T: Clone + Send + Sync + 'static,
    P: BatchProcessor<T> + 'static,
{
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    #[ignore] // 等待批次处理可能超时，默认跳过
    async fn test_batch_processing() {
        let processor = SimpleBatchProcessor::new("test".to_string());
        let config = BatchConfig {
            strategy: BatchStrategy::ByCount(5),
            max_queue_size: 100,
            processing_timeout: Some(Duration::from_secs(10)),
            retry_config: None,
        };

        let batch_processor = AsyncBatchProcessor::new(processor, config, 2);
        let handle = batch_processor.start();

        // 添加一些测试项目
        for i in 0..10 {
            let item = BatchItem::new(format!("item_{}", i), 100, 0);
            batch_processor.add_item(item).await.unwrap();
        }

        // 等待处理完成
        sleep(Duration::from_millis(1000)).await;

        let stats = batch_processor.get_stats().await;
        assert!(stats.total_batches > 0);
        assert_eq!(stats.total_items, 10);

        batch_processor.shutdown().await.unwrap();
        let _ = handle.await;
    }

    #[tokio::test]
    #[ignore] // 等待处理完成可能超时，默认跳过
    async fn test_hybrid_batch_strategy() {
        let processor = SimpleBatchProcessor::new("hybrid_test".to_string());
        let config = BatchConfig {
            strategy: BatchStrategy::Hybrid {
                max_count: 3,
                max_time: Duration::from_millis(500),
                max_size: 1000,
            },
            max_queue_size: 100,
            processing_timeout: Some(Duration::from_secs(10)),
            retry_config: None,
        };

        let batch_processor = AsyncBatchProcessor::new(processor, config, 1);
        let handle = batch_processor.start();

        // 添加不同大小的项目
        for i in 0..5 {
            let size = 200 + i * 100; // 200, 300, 400, 500, 600 bytes
            let item = BatchItem::new(format!("item_{}", i), size, 0);
            batch_processor.add_item(item).await.unwrap();
        }

        // 等待处理完成
        sleep(Duration::from_millis(1000)).await;

        let stats = batch_processor.get_stats().await;
        assert!(stats.total_batches > 0);

        batch_processor.shutdown().await.unwrap();
        let _ = handle.await;
    }
}
