use anyhow::Result;
use std::time::{Duration, Instant};
use tokio::sync::{Semaphore, RwLock};
use tokio::time::{sleep, timeout};
use tracing::{info, warn, error, debug};
use std::sync::Arc;

/// 2025年异步性能优化演示
/// 展示最新的异步性能优化技术和最佳实践

/// 高性能异步任务池
pub struct AsyncTaskPool {
    semaphore: Arc<Semaphore>,
    max_concurrent: usize,
    metrics: Arc<RwLock<TaskPoolMetrics>>,
}

#[derive(Debug, Default, Clone)]
pub struct TaskPoolMetrics {
    pub total_tasks: u64,
    pub completed_tasks: u64,
    pub failed_tasks: u64,
    pub average_execution_time: Duration,
    pub throughput_per_second: f64,
}

impl AsyncTaskPool {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
            max_concurrent,
            metrics: Arc::new(RwLock::new(TaskPoolMetrics::default())),
        }
    }

    /// 执行任务并收集性能指标
    pub async fn execute<F, R>(&self, task_name: &str, future: F) -> Result<R>
    where
        F: std::future::Future<Output = Result<R>> + Send + 'static,
        R: Send + 'static,
    {
        let start_time = Instant::now();
        
        // 获取信号量许可
        let _permit = self.semaphore.acquire().await
            .map_err(|e| anyhow::anyhow!("Failed to acquire permit: {}", e))?;

        debug!("执行任务: {}", task_name);
        
        let result = timeout(Duration::from_secs(30), future).await
            .map_err(|_| anyhow::anyhow!("Task timeout"))?;

        let execution_time = start_time.elapsed();
        
        // 更新指标
        self.update_metrics(&result, execution_time).await;

        match &result {
            Ok(_) => {
                info!("任务完成: {} (耗时: {:?})", task_name, execution_time);
            }
            Err(e) => {
                error!("任务失败: {} - {}", task_name, e);
            }
        }

        result
    }

    async fn update_metrics<R>(&self, result: &Result<R>, execution_time: Duration) {
        let mut metrics = self.metrics.write().await;
        metrics.total_tasks += 1;
        
        match result {
            Ok(_) => metrics.completed_tasks += 1,
            Err(_) => metrics.failed_tasks += 1,
        }

        // 更新平均执行时间
        let total_time = metrics.average_execution_time * (metrics.total_tasks - 1) as u32 + execution_time;
        metrics.average_execution_time = total_time / metrics.total_tasks as u32;

        // 计算吞吐量（每秒完成的任务数）
        if metrics.average_execution_time.as_millis() > 0 {
            metrics.throughput_per_second = 1000.0 / metrics.average_execution_time.as_millis() as f64;
        }
    }

    pub async fn get_metrics(&self) -> TaskPoolMetrics {
        self.metrics.read().await.clone()
    }
}

/// 异步缓存管理器
#[allow(dead_code)]
#[derive(Debug)]
pub struct AsyncCacheManager<K, V> {
    cache: Arc<RwLock<std::collections::HashMap<K, V>>>,
    ttl: Duration,
    max_size: usize,
    hit_count: Arc<RwLock<u64>>,
    miss_count: Arc<RwLock<u64>>,
}

impl<K, V> AsyncCacheManager<K, V>
where
    K: Clone + std::hash::Hash + Eq + Send + Sync + std::fmt::Debug + 'static,
    V: Clone + Send + Sync + 'static,
{
    pub fn new(ttl: Duration, max_size: usize) -> Self {
        Self {
            cache: Arc::new(RwLock::new(std::collections::HashMap::new())),
            ttl,
            max_size,
            hit_count: Arc::new(RwLock::new(0)),
            miss_count: Arc::new(RwLock::new(0)),
        }
    }

    pub async fn get(&self, key: &K) -> Option<V> {
        let cache = self.cache.read().await;
        match cache.get(key) {
            Some(value) => {
                let mut hit_count = self.hit_count.write().await;
                *hit_count += 1;
                debug!("缓存命中: {:?}", key);
                Some(value.clone())
            }
            None => {
                let mut miss_count = self.miss_count.write().await;
                *miss_count += 1;
                debug!("缓存未命中: {:?}", key);
                None
            }
        }
    }

    pub async fn set(&self, key: K, value: V) {
        let mut cache = self.cache.write().await;
        
        // 检查缓存大小限制
        if cache.len() >= self.max_size {
            // 简单的LRU策略：移除第一个条目
            if let Some(first_key) = cache.keys().next().cloned() {
                cache.remove(&first_key);
            }
        }

        cache.insert(key.clone(), value);
        info!("缓存设置: {:?}", key);
    }

    pub async fn hit_rate(&self) -> f64 {
        let hits = *self.hit_count.read().await;
        let misses = *self.miss_count.read().await;
        
        if hits + misses == 0 {
            0.0
        } else {
            hits as f64 / (hits + misses) as f64
        }
    }
}

/// 异步批处理器
pub struct AsyncBatchProcessor<T> {
    batch_size: usize,
    flush_interval: Duration,
    buffer: Arc<RwLock<Vec<T>>>,
    processor: Arc<dyn Fn(Vec<T>) -> Result<()> + Send + Sync>,
}

impl<T> AsyncBatchProcessor<T>
where
    T: Send + Sync + 'static,
{
    pub fn new<F>(
        batch_size: usize,
        flush_interval: Duration,
        processor: F,
    ) -> Self
    where
        F: Fn(Vec<T>) -> Result<()> + Send + Sync + 'static,
    {
        Self {
            batch_size,
            flush_interval,
            buffer: Arc::new(RwLock::new(Vec::new())),
            processor: Arc::new(processor),
        }
    }

    pub async fn add(&self, item: T) -> Result<()> {
        let mut buffer = self.buffer.write().await;
        buffer.push(item);

        if buffer.len() >= self.batch_size {
            let items = buffer.drain(..).collect();
            drop(buffer); // 释放锁

            self.process_batch(items).await?;
        }

        Ok(())
    }

    pub async fn flush(&self) -> Result<()> {
        let mut buffer = self.buffer.write().await;
        if !buffer.is_empty() {
            let items = buffer.drain(..).collect();
            drop(buffer); // 释放锁

            self.process_batch(items).await?;
        }
        Ok(())
    }

    async fn process_batch(&self, items: Vec<T>) -> Result<()> {
        let start_time = Instant::now();
        let item_count = items.len();
        (self.processor)(items)?;
        let duration = start_time.elapsed();
        
        info!("批处理完成: {} 个项目, 耗时: {:?}", item_count, duration);
        Ok(())
    }

    /// 启动定时刷新任务
    pub async fn start_periodic_flush(&self) -> Result<()> {
        let buffer = self.buffer.clone();
        let processor = self.processor.clone();
        let flush_interval = self.flush_interval;

        tokio::spawn(async move {
            let mut interval = tokio::time::interval(flush_interval);
            loop {
                interval.tick().await;
                
                let mut buffer = buffer.write().await;
                if !buffer.is_empty() {
                    let items = buffer.drain(..).collect();
                    drop(buffer); // 释放锁

                    if let Err(e) = (processor)(items) {
                        error!("定时批处理失败: {}", e);
                    }
                }
            }
        });

        Ok(())
    }
}

/// 异步连接池
pub struct AsyncConnectionPool<T> {
    connections: Arc<RwLock<Vec<T>>>,
    max_size: usize,
    factory: Arc<dyn Fn() -> Result<T> + Send + Sync>,
    active_connections: Arc<RwLock<usize>>,
}

impl<T> AsyncConnectionPool<T>
where
    T: Send + Sync + 'static,
{
    pub fn new<F>(max_size: usize, factory: F) -> Self
    where
        F: Fn() -> Result<T> + Send + Sync + 'static,
    {
        Self {
            connections: Arc::new(RwLock::new(Vec::new())),
            max_size,
            factory: Arc::new(factory),
            active_connections: Arc::new(RwLock::new(0)),
        }
    }

    pub async fn acquire(&self) -> Result<PooledConnection<T>> {
        // 尝试从池中获取连接
        {
            let mut connections = self.connections.write().await;
            if let Some(connection) = connections.pop() {
                let mut active = self.active_connections.write().await;
                *active += 1;
                debug!("从池中获取连接，活跃连接数: {}", *active);
                return Ok(PooledConnection::new(connection, self.clone()));
            }
        }

        // 检查是否超过最大连接数
        {
            let active = self.active_connections.read().await;
            if *active >= self.max_size {
                return Err(anyhow::anyhow!("连接池已满"));
            }
        }

        // 创建新连接
        let connection = (self.factory)()?;
        let mut active = self.active_connections.write().await;
        *active += 1;
        debug!("创建新连接，活跃连接数: {}", *active);

        Ok(PooledConnection::new(connection, self.clone()))
    }

    pub async fn release(&self, connection: T) {
        let mut connections = self.connections.write().await;
        if connections.len() < self.max_size {
            connections.push(connection);
        }
        
        let mut active = self.active_connections.write().await;
        *active -= 1;
        debug!("释放连接，活跃连接数: {}", *active);
    }

    pub async fn active_count(&self) -> usize {
        *self.active_connections.read().await
    }

    pub async fn available_count(&self) -> usize {
        self.connections.read().await.len()
    }
}

/// 池化连接包装器
pub struct PooledConnection<T> 
where
    T: Send + Sync + 'static,
{
    connection: Option<T>,
    pool: AsyncConnectionPool<T>,
}

impl<T> PooledConnection<T> 
where
    T: Send + Sync + 'static,
{
    fn new(connection: T, pool: AsyncConnectionPool<T>) -> Self {
        Self {
            connection: Some(connection),
            pool,
        }
    }

    pub fn get(&self) -> &T {
        self.connection.as_ref().unwrap()
    }
}

impl<T> Drop for PooledConnection<T> 
where
    T: Send + Sync + 'static,
{
    fn drop(&mut self) {
        if let Some(connection) = self.connection.take() {
            let pool = self.pool.clone();
            tokio::spawn(async move {
                pool.release(connection).await;
            });
        }
    }
}

impl<T> Clone for AsyncConnectionPool<T> {
    fn clone(&self) -> Self {
        Self {
            connections: self.connections.clone(),
            max_size: self.max_size,
            factory: self.factory.clone(),
            active_connections: self.active_connections.clone(),
        }
    }
}

impl Clone for AsyncTaskPool {
    fn clone(&self) -> Self {
        Self {
            semaphore: self.semaphore.clone(),
            max_concurrent: self.max_concurrent,
            metrics: self.metrics.clone(),
        }
    }
}

/// 性能优化演示
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();

    info!("🚀 开始 2025 年异步性能优化演示");

    // 1. 异步任务池演示
    demo_task_pool().await?;

    // 2. 异步缓存演示
    demo_async_cache().await?;

    // 3. 异步批处理演示
    demo_batch_processing().await?;

    // 4. 异步连接池演示
    demo_connection_pool().await?;

    info!("✅ 2025 年异步性能优化演示完成!");
    Ok(())
}

async fn demo_task_pool() -> Result<()> {
    info!("📊 演示异步任务池");

    let pool = AsyncTaskPool::new(10);

    // 并发执行多个任务
    let mut handles = Vec::new();
    for i in 0..50 {
        let pool = pool.clone();
        let handle = tokio::spawn(async move {
            pool.execute(
                &format!("任务_{}", i),
                async move {
                    // 模拟一些工作
                    sleep(Duration::from_millis(rand::random::<u64>() % 100)).await;
                    if i % 10 == 0 {
                        Err(anyhow::anyhow!("模拟错误"))
                    } else {
                        Ok(())
                    }
                },
            ).await
        });
        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        handle.await??;
    }

    // 显示指标
    let metrics = pool.get_metrics().await;
    info!("任务池指标:");
    info!("  总任务数: {}", metrics.total_tasks);
    info!("  完成任务数: {}", metrics.completed_tasks);
    info!("  失败任务数: {}", metrics.failed_tasks);
    info!("  平均执行时间: {:?}", metrics.average_execution_time);
    info!("  吞吐量: {:.2} 任务/秒", metrics.throughput_per_second);

    Ok(())
}

async fn demo_async_cache() -> Result<()> {
    info!("🗄️ 演示异步缓存管理器");

    let cache = AsyncCacheManager::new(Duration::from_secs(60), 1000);

    // 填充缓存
    for i in 0..100 {
        cache.set(i, format!("值_{}", i)).await;
    }

    // 读取测试
    for i in 0..200 {
        cache.get(&i).await;
    }

    let hit_rate = cache.hit_rate().await;
    info!("缓存命中率: {:.2}%", hit_rate * 100.0);
    info!("预期命中率: 50% (100/200)");

    Ok(())
}

async fn demo_batch_processing() -> Result<()> {
    info!("📦 演示异步批处理器");

    let processor = AsyncBatchProcessor::new(
        10, // 批大小
        Duration::from_secs(5), // 刷新间隔
        |items| {
            info!("处理批次: {} 个项目", items.len());
            Ok(())
        },
    );

    // 启动定时刷新
    processor.start_periodic_flush().await?;

    // 添加一些数据
    for i in 0..25 {
        processor.add(format!("数据_{}", i)).await?;
        sleep(Duration::from_millis(100)).await;
    }

    // 手动刷新剩余数据
    processor.flush().await?;

    Ok(())
}

async fn demo_connection_pool() -> Result<()> {
    info!("🔗 演示异步连接池");

    let pool = AsyncConnectionPool::new(
        5, // 最大连接数
        || {
            // 模拟连接创建
            Ok(format!("连接_{}", rand::random::<u32>()))
        },
    );

    // 获取一些连接
    let mut connections = Vec::new();
    for i in 0..7 {
        match pool.acquire().await {
            Ok(conn) => {
                info!("获取连接 {}: {}", i, conn.get());
                connections.push(conn);
            }
            Err(e) => {
                warn!("无法获取连接 {}: {}", i, e);
            }
        }
    }

    info!("活跃连接数: {}", pool.active_count().await);
    info!("可用连接数: {}", pool.available_count().await);

    // 释放一些连接
    connections.truncate(3);
    drop(connections);

    sleep(Duration::from_millis(100)).await; // 等待连接释放

    info!("释放后活跃连接数: {}", pool.active_count().await);
    info!("释放后可用连接数: {}", pool.available_count().await);

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_task_pool() {
        let pool = AsyncTaskPool::new(2);
        let result = pool.execute("test_task", async { Ok(()) }).await;
        assert!(result.is_ok());
        
        let metrics = pool.get_metrics().await;
        assert_eq!(metrics.total_tasks, 1);
        assert_eq!(metrics.completed_tasks, 1);
    }

    #[tokio::test]
    async fn test_cache_manager() {
        let cache = AsyncCacheManager::new(Duration::from_secs(60), 10);
        
        cache.set("key1", "value1").await;
        let value = cache.get(&"key1").await;
        assert_eq!(value, Some("value1".to_string()));
        
        let hit_rate = cache.hit_rate().await;
        assert!(hit_rate > 0.0);
    }

    #[tokio::test]
    async fn test_batch_processor() {
        let processor = AsyncBatchProcessor::new(
            3,
            Duration::from_secs(1),
            |items| {
                assert_eq!(items.len(), 3);
                Ok(())
            },
        );

        for i in 0..3 {
            processor.add(i).await.unwrap();
        }
    }

    #[tokio::test]
    async fn test_connection_pool() {
        let pool = AsyncConnectionPool::new(2, || Ok("test_connection"));
        
        let conn1 = pool.acquire().await.unwrap();
        assert_eq!(conn1.get(), &"test_connection");
        
        let conn2 = pool.acquire().await.unwrap();
        assert_eq!(conn2.get(), &"test_connection");
        
        // 第三个连接应该失败
        let conn3 = pool.acquire().await;
        assert!(conn3.is_err());
    }
}
