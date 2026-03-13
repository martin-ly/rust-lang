//! 高级异步工具演示
//! 
//! 本示例展示了高级异步工具的使用：
//! - 异步任务管理器
//! - 智能重试引擎
//! - 异步批处理器
//! - 异步限流器
//! - 异步缓存管理器
//! - 异步事件总线
//! - 异步健康检查器
//! - 异步配置管理器
//! 
//! 运行方式：
//! ```bash
//! cargo run --example advanced_tools_demo
//! ```
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::Mutex;
use tokio::time::{sleep, interval};
use anyhow::Result;
use serde::{Serialize, Deserialize};

// 模拟高级工具模块（在实际项目中这些会从 advanced_tools 模块导入）
mod mock_tools {
    use super::*;

    /// 模拟异步任务管理器
    pub struct MockTaskManager {
        pub tasks: Arc<Mutex<Vec<TaskInfo>>>,
        pub stats: Arc<Mutex<TaskStats>>,
    }

    #[allow(dead_code)]
    #[derive(Debug, Clone)]
    pub struct TaskInfo {
        pub id: String,
        pub name: String,
        pub status: String,
        #[allow(dead_code)]
        pub created_at: Instant,
        pub completed_at: Option<Instant>,
    }

    #[allow(dead_code)]
    #[derive(Debug, Default, Clone)]
    pub struct TaskStats {
        pub total_tasks: u64,
        pub completed_tasks: u64,
        pub failed_tasks: u64,
        pub avg_execution_time: Duration,
    }

    impl MockTaskManager {
        #[allow(dead_code)]
        pub fn new() -> Self {
            Self {
                tasks: Arc::new(Mutex::new(Vec::new())),
                stats: Arc::new(Mutex::new(TaskStats::default())),
            }
        }

        #[allow(dead_code)]
        pub async fn submit_task(&self, name: String) -> Result<String> {
            let task_id = format!("task_{}", uuid::Uuid::new_v4());
            let task = TaskInfo {
                id: task_id.clone(),
                name,
                status: "pending".to_string(),
                created_at: Instant::now(),
                completed_at: None,
            };

            {
                let mut tasks = self.tasks.lock().await;
                tasks.push(task);
            }

            {
                let mut stats = self.stats.lock().await;
                stats.total_tasks += 1;
            }

            println!("    📝 提交任务: {}", task_id);
            Ok(task_id)
        }

        #[allow(dead_code)]
        pub async fn get_stats(&self) -> TaskStats {
            self.stats.lock().await.clone()
        }

        #[allow(dead_code)]
        #[allow(unused_variables)]
        pub async fn simulate_task_execution(&self) {
            let mut interval = interval(Duration::from_millis(200));

            loop {
                interval.tick().await;

                let mut tasks = self.tasks.lock().await;
                let stats = self.stats.lock().await;

                for task in tasks.iter_mut() {
                    if task.status == "pending" {
                        task.status = "running".to_string();
                        println!("    🏃 开始执行任务: {}", task.name);

                        // 模拟任务执行
                        tokio::spawn({
                            let task_id = task.id.clone();
                            let tasks = Arc::clone(&self.tasks);
                            let stats = Arc::clone(&self.stats);
                            async move {
                                sleep(Duration::from_millis(500)).await;

                                let mut tasks = tasks.lock().await;
                                let mut stats = stats.lock().await;

                                if let Some(task) = tasks.iter_mut().find(|t| t.id == task_id) {
                                    if rand::random::<f32>() < 0.8 {
                                        task.status = "completed".to_string();
                                        task.completed_at = Some(Instant::now());
                                        stats.completed_tasks += 1;
                                        println!("    ✅ 任务完成: {}", task.name);
                                    } else {
                                        task.status = "failed".to_string();
                                        stats.failed_tasks += 1;
                                        println!("    ❌ 任务失败: {}", task.name);
                                    }
                                }
                            }
                        });
                        break;
                    }
                }
            }
        }
    }

    /// 模拟智能重试引擎
    #[allow(dead_code)]
    pub struct MockRetryEngine {
        config: RetryConfig,
        stats: Arc<Mutex<RetryStats>>,
    }

    #[allow(dead_code)]
    #[derive(Debug, Clone)]
    pub struct RetryConfig {
        pub max_attempts: u32,
        pub backoff_strategy: BackoffStrategy,
        pub jitter: bool,
    }

    #[allow(dead_code)]
    #[derive(Debug, Clone)]
    pub enum BackoffStrategy {
        #[allow(dead_code)]
        Fixed(Duration),
        Exponential(Duration, f64),
        #[allow(dead_code)]
        Linear(Duration, Duration),
    }

    #[derive(Debug, Default, Clone)]
    pub struct RetryStats {
        pub total_attempts: u64,
        pub successful_attempts: u64,
        pub failed_attempts: u64,
        pub avg_retry_time: Duration,
    }

    impl MockRetryEngine {
        #[allow(dead_code)]
        pub fn new(config: RetryConfig) -> Self {
            Self {
                config,
                stats: Arc::new(Mutex::new(RetryStats::default())),
            }
        }

        #[allow(dead_code)]
        pub async fn execute<F, Fut, T>(&self, operation: F) -> Result<T>
        where
            F: Fn() -> Fut,
            Fut: std::future::Future<Output = Result<T>>,
        {
            let mut attempts = 0;
            let start_time = Instant::now();

            loop {
                attempts += 1;
                println!("    🔄 重试尝试 #{}", attempts);

                match operation().await {
                    Ok(result) => {
                        let total_time = start_time.elapsed();
                        {
                            let mut stats = self.stats.lock().await;
                            stats.total_attempts += attempts as u64;
                            stats.successful_attempts += 1;
                            stats.avg_retry_time = total_time;
                        }
                        println!("    ✅ 操作成功，总尝试次数: {}", attempts);
                        return Ok(result);
                    }
                    Err(e) if attempts >= self.config.max_attempts => {
                        {
                            let mut stats = self.stats.lock().await;
                            stats.total_attempts += attempts as u64;
                            stats.failed_attempts += 1;
                        }
                        println!("    ❌ 达到最大重试次数，操作失败");
                        return Err(e);
                    }
                    Err(e) => {
                        let delay = self.calculate_delay(attempts);
                        println!("    ⏳ 操作失败: {}，等待 {:?} 后重试", e, delay);
                        sleep(delay).await;
                    }
                }
            }
        }

        fn calculate_delay(&self, attempt: u32) -> Duration {
            let base_delay = match &self.config.backoff_strategy {
                BackoffStrategy::Fixed(delay) => *delay,
                BackoffStrategy::Exponential(initial, multiplier) => {
                    Duration::from_millis((initial.as_millis() as f64 * multiplier.powi(attempt as i32)) as u64)
                }
                BackoffStrategy::Linear(initial, max) => {
                    let delay = *initial + Duration::from_millis(attempt as u64 * 100);
                    delay.min(*max)
                }
            };

            if self.config.jitter {
                // 添加 ±25% 的抖动
                let jitter_range = base_delay.as_millis() as f64 * 0.25;
                let jitter = (rand::random::<f64>() - 0.5) * 2.0 * jitter_range;
                let jittered_ms = (base_delay.as_millis() as f64 + jitter).max(1.0) as u64;
                Duration::from_millis(jittered_ms)
            } else {
                base_delay
            }
        }

        pub async fn get_stats(&self) -> RetryStats {
            self.stats.lock().await.clone()
        }
    }

    /// 模拟异步批处理器
    pub struct MockBatchProcessor<T> {
        pub batch_size: usize,
        pub processing_interval: Duration,
        pub stats: Arc<Mutex<BatchStats>>,
        pub _phantom: std::marker::PhantomData<T>,
    }

    #[derive(Debug, Default, Clone)]
    pub struct BatchStats {
        pub total_batches: u64,
        pub total_items: u64,
        pub avg_batch_size: f64,
        pub avg_processing_time: Duration,
        pub throughput: f64,
    }

    impl<T> MockBatchProcessor<T> {
        #[allow(dead_code)]
        pub fn new(batch_size: usize, processing_interval: Duration) -> Self {
            Self {
                batch_size,
                processing_interval,
                stats: Arc::new(Mutex::new(BatchStats::default())),
                _phantom: std::marker::PhantomData,
            }
        }

        #[allow(dead_code)]
        #[allow(unused_variables)]
        pub async fn add_item(&self, _item: T) -> Result<()> {
            println!("    📦 添加项目到批处理队列");
            Ok(())
        }

        pub async fn get_stats(&self) -> BatchStats {
            self.stats.lock().await.clone()
        }

        pub async fn simulate_batch_processing(&self) {
            let mut interval = interval(self.processing_interval);
            let mut batch_count = 0;

            loop {
                interval.tick().await;
                batch_count += 1;

                let batch_size = (rand::random::<u32>() as usize) % self.batch_size + 1;
                let processing_time = Duration::from_millis(batch_size as u64 * 10);

                println!("    🔄 处理批次 #{}，大小: {}", batch_count, batch_size);

                sleep(processing_time).await;

                {
                    let mut stats = self.stats.lock().await;
                    stats.total_batches += 1;
                    stats.total_items += batch_size as u64;
                    stats.avg_batch_size = stats.total_items as f64 / stats.total_batches as f64;
                    stats.avg_processing_time = processing_time;
                    stats.throughput = stats.total_items as f64 / 
                        (batch_count as f64 * self.processing_interval.as_secs_f64());
                }

                println!("    ✅ 批次 #{} 处理完成", batch_count);
            }
        }
    }

    /// 模拟异步限流器
    pub struct MockRateLimiter {
        requests_per_second: u32,
        current_requests: Arc<Mutex<u32>>,
        last_reset: Arc<Mutex<Instant>>,
    }

    impl MockRateLimiter {
        pub fn new(requests_per_second: u32) -> Self {
            Self {
                requests_per_second,
                current_requests: Arc::new(Mutex::new(0)),
                last_reset: Arc::new(Mutex::new(Instant::now())),
            }
        }

        pub async fn try_acquire(&self) -> bool {
            let now = Instant::now();
            let mut current_requests = self.current_requests.lock().await;
            let mut last_reset = self.last_reset.lock().await;

            // 每秒重置计数器
            if now.duration_since(*last_reset) >= Duration::from_secs(1) {
                *current_requests = 0;
                *last_reset = now;
            }

            if *current_requests < self.requests_per_second {
                *current_requests += 1;
                true
            } else {
                false
            }
        }

        pub async fn acquire(&self) {
            while !self.try_acquire().await {
                sleep(Duration::from_millis(10)).await;
            }
        }
    }

    /// 模拟异步缓存管理器
    pub struct MockCacheManager<K, V> {
        cache: Arc<Mutex<std::collections::HashMap<K, CacheEntry<V>>>>,
        ttl: Duration,
        stats: Arc<Mutex<CacheStats>>,
    }

    #[derive(Debug, Clone)]
    pub struct CacheEntry<V> {
        pub value: V,
        pub created_at: Instant,
        pub access_count: u64,
    }

    #[derive(Debug, Default, Clone, Serialize, Deserialize)]
    pub struct CacheStats {
        pub total_requests: u64,
        pub cache_hits: u64,
        pub cache_misses: u64,
        pub hit_rate: f64,
    }

    impl<K, V> MockCacheManager<K, V>
    where
        K: Clone + std::hash::Hash + Eq + Send + Sync + 'static,
        V: Clone + Send + Sync + 'static,
    {
        pub fn new(ttl: Duration) -> Self {
            Self {
                cache: Arc::new(Mutex::new(std::collections::HashMap::new())),
                ttl,
                stats: Arc::new(Mutex::new(CacheStats::default())),
            }
        }

        pub async fn get(&self, key: &K) -> Option<V> {
            {
                let mut stats = self.stats.lock().await;
                stats.total_requests += 1;
            }

            let mut cache = self.cache.lock().await;
            
            if let Some(entry) = cache.get_mut(key) {
                if entry.created_at.elapsed() < self.ttl {
                    entry.access_count += 1;
                    {
                        let mut stats = self.stats.lock().await;
                        stats.cache_hits += 1;
                        stats.hit_rate = stats.cache_hits as f64 / stats.total_requests as f64;
                    }
                    return Some(entry.value.clone());
                } else {
                    cache.remove(key);
                }
            }
            
            {
                let mut stats = self.stats.lock().await;
                stats.cache_misses += 1;
                stats.hit_rate = stats.cache_hits as f64 / stats.total_requests as f64;
            }
            None
        }

        pub async fn set(&self, key: K, value: V) {
            let entry = CacheEntry {
                value,
                created_at: Instant::now(),
                access_count: 1,
            };

            let mut cache = self.cache.lock().await;
            cache.insert(key, entry);
        }

        pub async fn get_stats(&self) -> CacheStats {
            self.stats.lock().await.clone()
        }
    }

    /// 模拟异步事件总线
    pub struct MockEventBus<T> {
        subscribers: Arc<Mutex<Vec<tokio::sync::mpsc::UnboundedSender<T>>>>,
        stats: Arc<Mutex<EventStats>>,
    }

    #[derive(Debug, Default, Clone, Serialize, Deserialize)]
    pub struct EventStats {
        pub total_events: u64,
        pub total_subscribers: u64,
        pub events_per_second: f64,
    }

    impl<T> MockEventBus<T>
    where
        T: Clone + Send + Sync + 'static,
    {
        pub fn new() -> Self {
            Self {
                subscribers: Arc::new(Mutex::new(Vec::new())),
                stats: Arc::new(Mutex::new(EventStats::default())),
            }
        }

        pub async fn subscribe(&self) -> tokio::sync::mpsc::UnboundedReceiver<T> {
            let (tx, rx) = tokio::sync::mpsc::unbounded_channel();
            
            {
                let mut subscribers = self.subscribers.lock().await;
                subscribers.push(tx);
            }

            {
                let mut stats = self.stats.lock().await;
                stats.total_subscribers += 1;
            }

            rx
        }

        pub async fn publish(&self, event: T) -> Result<()> {
            let subscribers = {
                let subscribers = self.subscribers.lock().await;
                subscribers.clone()
            };

            for subscriber in subscribers {
                if let Err(_) = subscriber.send(event.clone()) {
                    // 订阅者已断开连接
                }
            }

            {
                let mut stats = self.stats.lock().await;
                stats.total_events += 1;
            }

            Ok(())
        }

        pub async fn get_stats(&self) -> EventStats {
            self.stats.lock().await.clone()
        }
    }
}

use mock_tools::*;

struct AdvancedToolsDemo;

impl AdvancedToolsDemo {
    async fn run() -> Result<()> {
        println!("🛠️ 高级异步工具演示");
        println!("================================");

        // 1. 异步任务管理器演示
        println!("\n📋 1. 异步任务管理器演示");
        Self::demo_task_manager().await?;

        // 2. 智能重试引擎演示
        println!("\n🔄 2. 智能重试引擎演示");
        Self::demo_retry_engine().await?;

        // 3. 异步批处理器演示
        println!("\n📦 3. 异步批处理器演示");
        Self::demo_batch_processor().await?;

        // 4. 异步限流器演示
        println!("\n🚦 4. 异步限流器演示");
        Self::demo_rate_limiter().await?;

        // 5. 异步缓存管理器演示
        println!("\n💾 5. 异步缓存管理器演示");
        Self::demo_cache_manager().await?;

        // 6. 异步事件总线演示
        println!("\n📡 6. 异步事件总线演示");
        Self::demo_event_bus().await?;

        // 7. 综合应用演示
        println!("\n🎯 7. 综合应用演示");
        Self::demo_integrated_application().await?;

        Ok(())
    }

    async fn demo_task_manager() -> Result<()> {
        let task_manager = MockTaskManager::new();

        // 启动任务执行器
        let task_manager_clone = task_manager.clone();
        let _handle = tokio::spawn(async move {
            task_manager_clone.simulate_task_execution().await;
        });

        // 提交一些任务
        let task_names = vec![
            "数据处理任务".to_string(),
            "文件上传任务".to_string(),
            "邮件发送任务".to_string(),
            "数据库备份任务".to_string(),
            "日志分析任务".to_string(),
        ];

        for name in task_names {
            let _ = task_manager.submit_task(name).await;
            sleep(Duration::from_millis(100)).await;
        }

        // 等待任务执行
        sleep(Duration::from_secs(2)).await;

        // 显示统计信息
        let stats = task_manager.get_stats().await;
        println!("    任务管理器统计:");
        println!("      总任务数: {}", stats.total_tasks);
        println!("      完成任务数: {}", stats.completed_tasks);
        println!("      失败任务数: {}", stats.failed_tasks);

        Ok(())
    }

    async fn demo_retry_engine() -> Result<()> {
        let config = RetryConfig {
            max_attempts: 3,
            backoff_strategy: BackoffStrategy::Exponential(Duration::from_millis(100), 2.0),
            jitter: true,
        };

        let retry_engine = MockRetryEngine::new(config);

        // 模拟一个不稳定的操作
        let result = retry_engine.execute(|| async {
            if rand::random::<f32>() < 0.7 {
                Err(anyhow::anyhow!("模拟网络错误"))
            } else {
                Ok("操作成功".to_string())
            }
        }).await;

        match result {
            Ok(value) => println!("    ✅ 最终结果: {}", value),
            Err(e) => println!("    ❌ 最终失败: {}", e),
        }

        // 显示统计信息
        let stats = retry_engine.get_stats().await;
        println!("    重试引擎统计:");
        println!("      总尝试次数: {}", stats.total_attempts);
        println!("      成功尝试次数: {}", stats.successful_attempts);
        println!("      失败尝试次数: {}", stats.failed_attempts);
        println!("      平均重试时间: {:?}", stats.avg_retry_time);

        Ok(())
    }

    async fn demo_batch_processor() -> Result<()> {
        let batch_processor = MockBatchProcessor::new(5, Duration::from_millis(500));

        // 启动批处理器
        let batch_processor_clone = batch_processor.clone();
        let _handle = tokio::spawn(async move {
            batch_processor_clone.simulate_batch_processing().await;
        });

        // 添加一些项目
        for i in 0..15 {
            batch_processor.add_item(format!("item_{}", i)).await?;
            sleep(Duration::from_millis(50)).await;
        }

        // 等待处理完成
        sleep(Duration::from_secs(2)).await;

        // 显示统计信息
        let stats = batch_processor.get_stats().await;
        println!("    批处理器统计:");
        println!("      总批次数: {}", stats.total_batches);
        println!("      总项目数: {}", stats.total_items);
        println!("      平均批次大小: {:.2}", stats.avg_batch_size);
        println!("      平均处理时间: {:?}", stats.avg_processing_time);
        println!("      吞吐量: {:.2} items/sec", stats.throughput);

        Ok(())
    }

    async fn demo_rate_limiter() -> Result<()> {
        let rate_limiter = MockRateLimiter::new(3); // 每秒最多3个请求

        println!("    测试限流器 (每秒最多3个请求):");
        
        for i in 0..10 {
            if rate_limiter.try_acquire().await {
                println!("      ✅ 请求 {} 通过", i);
            } else {
                println!("      ❌ 请求 {} 被限流", i);
            }
            sleep(Duration::from_millis(200)).await;
        }

        println!("    等待限流重置...");
        sleep(Duration::from_secs(1)).await;

        for i in 10..15 {
            if rate_limiter.try_acquire().await {
                println!("      ✅ 请求 {} 通过", i);
            } else {
                println!("      ❌ 请求 {} 被限流", i);
            }
            sleep(Duration::from_millis(200)).await;
        }

        Ok(())
    }

    async fn demo_cache_manager() -> Result<()> {
        let cache = MockCacheManager::new(Duration::from_secs(2));

        // 设置一些缓存项
        for i in 0..5 {
            cache.set(format!("key_{}", i), format!("value_{}", i)).await;
        }

        println!("    测试缓存命中:");
        
        // 测试缓存命中
        for i in 0..5 {
            if let Some(value) = cache.get(&format!("key_{}", i)).await {
                println!("      ✅ 缓存命中: key_{} = {}", i, value);
            } else {
                println!("      ❌ 缓存未命中: key_{}", i);
            }
        }

        // 测试缓存未命中
        if let Some(value) = cache.get(&"nonexistent_key".to_string()).await {
            println!("      ✅ 缓存命中: nonexistent_key = {}", value);
        } else {
            println!("      ❌ 缓存未命中: nonexistent_key");
        }

        // 显示统计信息
        let stats = cache.get_stats().await;
        println!("    缓存管理器统计:");
        println!("      总请求数: {}", stats.total_requests);
        println!("      缓存命中数: {}", stats.cache_hits);
        println!("      缓存未命中数: {}", stats.cache_misses);
        println!("      命中率: {:.1}%", stats.hit_rate * 100.0);

        Ok(())
    }

    async fn demo_event_bus() -> Result<()> {
        let event_bus = MockEventBus::new();

        // 创建订阅者
        let mut subscriber1 = event_bus.subscribe().await;
        let mut subscriber2 = event_bus.subscribe().await;

        // 启动订阅者处理
        let handle1 = tokio::spawn(async move {
            while let Some(event) = subscriber1.recv().await {
                println!("      订阅者1收到事件: {}", event);
            }
        });

        let handle2 = tokio::spawn(async move {
            while let Some(event) = subscriber2.recv().await {
                println!("      订阅者2收到事件: {}", event);
            }
        });

        // 发布一些事件
        for i in 0..5 {
            event_bus.publish(format!("事件_{}", i)).await?;
            sleep(Duration::from_millis(100)).await;
        }

        // 等待事件处理
        sleep(Duration::from_millis(500)).await;

        // 显示统计信息
        let stats = event_bus.get_stats().await;
        println!("    事件总线统计:");
        println!("      总事件数: {}", stats.total_events);
        println!("      总订阅者数: {}", stats.total_subscribers);

        // 清理
        drop(handle1);
        drop(handle2);

        Ok(())
    }

    async fn demo_integrated_application() -> Result<()> {
        println!("    集成应用演示 - 模拟一个完整的异步系统");

        // 创建各种组件
        let task_manager = MockTaskManager::new();
        let retry_engine = MockRetryEngine::new(RetryConfig {
            max_attempts: 3,
            backoff_strategy: BackoffStrategy::Exponential(Duration::from_millis(100), 2.0),
            jitter: true,
        });
        let rate_limiter = MockRateLimiter::new(5);
        let cache = MockCacheManager::new(Duration::from_secs(5));

        // 启动任务管理器
        let task_manager_clone = task_manager.clone();
        let _handle = tokio::spawn(async move {
            task_manager_clone.simulate_task_execution().await;
        });

        // 模拟集成工作流
        for i in 0..3 {
            println!("      处理工作流 #{}", i + 1);

            // 1. 限流控制
            rate_limiter.acquire().await;
            println("        ✅ 通过限流检查");

            // 2. 检查缓存
            let cache_key = format!("workflow_{}", i);
            if let Some(cached_result) = cache.get(&cache_key).await {
                println!("        ✅ 从缓存获取结果: {}", cached_result);
                continue;
            }

            // 3. 提交任务
            let task_name = format!("工作流任务_{}", i);
            let _task_id = task_manager.submit_task(task_name).await?;

            // 4. 执行重试操作
            let result = retry_engine.execute(|| async {
                if rand::random::<f32>() < 0.6 {
                    Err(anyhow::anyhow!("模拟操作失败"))
                } else {
                    Ok(format!("工作流_{} 处理成功", i))
                }
            }).await?;

            // 5. 缓存结果
            cache.set(cache_key, result.clone()).await;
            println!("        ✅ 工作流完成: {}", result);

            sleep(Duration::from_millis(200)).await;
        }

        // 显示各组件统计信息
        println!("      系统统计信息:");
        
        let task_stats = task_manager.get_stats().await;
        println!("        任务管理器: {} 任务, {} 完成", task_stats.total_tasks, task_stats.completed_tasks);
        
        let retry_stats = retry_engine.get_stats().await;
        println!("        重试引擎: {} 尝试, {} 成功", retry_stats.total_attempts, retry_stats.successful_attempts);
        
        let cache_stats = cache.get_stats().await;
        println!("        缓存管理器: {} 请求, {:.1}% 命中率", 
            cache_stats.total_requests, cache_stats.hit_rate * 100.0);

        Ok(())
    }
}

// 辅助函数
fn println(s: &str) {
    println!("{}", s);
}

// 为 MockTaskManager 实现 Clone
impl Clone for MockTaskManager {
    fn clone(&self) -> Self {
        Self {
            tasks: Arc::clone(&self.tasks),
            stats: Arc::clone(&self.stats),
        }
    }
}

// 为 MockBatchProcessor 实现 Clone
impl<T> Clone for MockBatchProcessor<T> {
    fn clone(&self) -> Self {
        Self {
            batch_size: self.batch_size,
            processing_interval: self.processing_interval,
            stats: Arc::clone(&self.stats),
            _phantom: std::marker::PhantomData,
        }
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    AdvancedToolsDemo::run().await?;

    println!("\n🎉 高级异步工具演示完成！");
    Ok(())
}
