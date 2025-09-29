//! 异步性能优化演示
//! 
//! 本示例展示了异步编程中的各种性能优化技术：
//! - 内存优化和零拷贝
//! - 并发控制和资源管理
//! - 批量处理优化
//! - 缓存策略
//! - 异步I/O优化
//! - 性能监控和指标
//! 
//! 运行方式：
//! ```bash
//! cargo run --example async_performance_demo
//! ```

use std::sync::Arc;
use std::time::{Duration, Instant};
use std::collections::HashMap;
use tokio::sync::{Mutex, RwLock, Semaphore, mpsc};
use tokio::time::sleep;
use futures::StreamExt;
use anyhow::Result;
use serde::{Serialize, Deserialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
struct PerformanceMetrics {
    throughput: f64,
    latency: Duration,
    memory_usage: usize,
    cpu_usage: f64,
    error_rate: f64,
}

struct PerformanceMonitor {
    metrics: Arc<RwLock<HashMap<String, PerformanceMetrics>>>,
    #[allow(dead_code)]
    start_time: Instant,
}

impl PerformanceMonitor {
    fn new() -> Self {
        Self {
            metrics: Arc::new(RwLock::new(HashMap::new())),
            start_time: Instant::now(),
        }
    }

    async fn record_metrics(&self, name: &str, metrics: PerformanceMetrics) {
        let mut map = self.metrics.write().await;
        map.insert(name.to_string(), metrics);
    }

    #[allow(dead_code)]
    async fn get_metrics(&self, name: &str) -> Option<PerformanceMetrics> {
        let map = self.metrics.read().await;
        map.get(name).cloned()
    }

    async fn print_summary(&self) {
        let map = self.metrics.read().await;
        println!("📊 性能监控总结");
        println!("==================");
        
        for (name, metrics) in map.iter() {
            println!("  {}:", name);
            println!("    吞吐量: {:.2} ops/sec", metrics.throughput);
            println!("    延迟: {:?}", metrics.latency);
            println!("    内存使用: {} MB", metrics.memory_usage / 1024 / 1024);
            println!("    CPU使用率: {:.1}%", metrics.cpu_usage);
            println!("    错误率: {:.1}%", metrics.error_rate * 100.0);
        }
    }
}

struct PerformanceDemo {
    monitor: PerformanceMonitor,
}

impl PerformanceDemo {
    fn new() -> Self {
        Self {
            monitor: PerformanceMonitor::new(),
        }
    }

    async fn run(&self) -> Result<()> {
        println!("⚡ 异步性能优化演示");
        println!("================================");

        // 1. 内存优化演示
        println!("\n🧠 1. 内存优化演示");
        self.memory_optimization_demo().await?;

        // 2. 并发控制演示
        println!("\n🎯 2. 并发控制演示");
        self.concurrency_control_demo().await?;

        // 3. 批量处理优化演示
        println!("\n📦 3. 批量处理优化演示");
        self.batch_processing_demo().await?;

        // 4. 缓存策略演示
        println!("\n💾 4. 缓存策略演示");
        self.caching_strategy_demo().await?;

        // 5. 异步I/O优化演示
        println!("\n📡 5. 异步I/O优化演示");
        self.async_io_optimization_demo().await?;

        // 6. 性能监控演示
        println!("\n📈 6. 性能监控演示");
        self.performance_monitoring_demo().await?;

        // 显示性能总结
        self.monitor.print_summary().await;

        Ok(())
    }

    async fn memory_optimization_demo(&self) -> Result<()> {
        println!("  内存优化技术演示...");

        // 1. 避免不必要的克隆
        println!("    1. 避免不必要的克隆");
        let start = Instant::now();
        
        let large_data = Arc::new(vec![0u8; 1024 * 1024]); // 1MB数据
        
        let mut handles = vec![];
        for _i in 0..10 {
            let data = Arc::clone(&large_data); // 只克隆Arc，不克隆数据
            let handle = tokio::spawn(async move {
                // 使用共享数据
                data.len()
            });
            handles.push(handle);
        }
        
        let results = futures::future::join_all(handles).await;
        let no_clone_time = start.elapsed();
        println!("      无克隆方式耗时: {:?}, 结果数: {}", no_clone_time, results.len());

        // 2. 使用对象池
        println!("    2. 对象池优化");
        let start = Instant::now();
        
        let object_pool = Arc::new(Semaphore::new(5)); // 最多5个对象
        let mut handles = vec![];
        
        for i in 0..20 {
            let pool = Arc::clone(&object_pool);
            let handle = tokio::spawn(async move {
                let _permit = pool.acquire().await.unwrap();
                // 模拟对象使用
                sleep(Duration::from_millis(50)).await;
                i
            });
            handles.push(handle);
        }
        
        futures::future::join_all(handles).await;
        let pool_time = start.elapsed();
        println!("      对象池方式耗时: {:?}", pool_time);

        // 3. 零拷贝优化
        println!("    3. 零拷贝优化");
        let start = Instant::now();
        
        let data = b"Hello, World!";
        let mut handles = vec![];
        
        for i in 0..100 {
            let handle = tokio::spawn(async move {
                // 使用字节切片的引用，避免拷贝
                let slice = &data[..];
                slice.len() + i
            });
            handles.push(handle);
        }
        
        futures::future::join_all(handles).await;
        let zero_copy_time = start.elapsed();
        println!("      零拷贝方式耗时: {:?}", zero_copy_time);

        // 记录性能指标
        self.monitor.record_metrics("内存优化", PerformanceMetrics {
            throughput: 1000.0 / no_clone_time.as_secs_f64(),
            latency: no_clone_time,
            memory_usage: 1024 * 1024, // 1MB
            cpu_usage: 10.0,
            error_rate: 0.0,
        }).await;

        Ok(())
    }

    async fn concurrency_control_demo(&self) -> Result<()> {
        println!("  并发控制技术演示...");

        // 1. 信号量控制并发数
        println!("    1. 信号量控制并发数");
        let start = Instant::now();
        
        let semaphore = Arc::new(Semaphore::new(5)); // 最多5个并发
        let mut handles = vec![];
        
        for i in 0..20 {
            let sem = Arc::clone(&semaphore);
            let handle = tokio::spawn(async move {
                let _permit = sem.acquire().await.unwrap();
                sleep(Duration::from_millis(100)).await;
                i
            });
            handles.push(handle);
        }
        
        futures::future::join_all(handles).await;
        let semaphore_time = start.elapsed();
        println!("      信号量控制耗时: {:?}", semaphore_time);

        // 2. 无限制并发（对比）
        println!("    2. 无限制并发（对比）");
        let start = Instant::now();
        
        let mut handles = vec![];
        for i in 0..20 {
            let handle = tokio::spawn(async move {
                sleep(Duration::from_millis(100)).await;
                i
            });
            handles.push(handle);
        }
        
        futures::future::join_all(handles).await;
        let unlimited_time = start.elapsed();
        println!("      无限制并发耗时: {:?}", unlimited_time);

        // 3. 自适应并发控制
        println!("    3. 自适应并发控制");
        let start = Instant::now();
        
        let adaptive_semaphore = Arc::new(Mutex::new(Semaphore::new(1)));
        let mut handles = vec![];
        
        for i in 0..10 {
            let sem = Arc::clone(&adaptive_semaphore);
            let handle = tokio::spawn(async move {
                let semaphore = sem.lock().await;
                let _permit = semaphore.acquire().await.unwrap();
                sleep(Duration::from_millis(100)).await;
                i
            });
            handles.push(handle);
        }
        
        futures::future::join_all(handles).await;
        let adaptive_time = start.elapsed();
        println!("      自适应并发耗时: {:?}", adaptive_time);

        // 记录性能指标
        self.monitor.record_metrics("并发控制", PerformanceMetrics {
            throughput: 20.0 / semaphore_time.as_secs_f64(),
            latency: semaphore_time,
            memory_usage: 1024 * 100, // 100KB
            cpu_usage: 15.0,
            error_rate: 0.0,
        }).await;

        Ok(())
    }

    async fn batch_processing_demo(&self) -> Result<()> {
        println!("  批量处理优化演示...");

        let total_items = 1000;
        let batch_sizes = vec![1, 10, 50, 100];

        for batch_size in batch_sizes {
            println!("    批量大小: {}", batch_size);
            let start = Instant::now();
            
            let mut handles = vec![];
            
            for batch_start in (0..total_items).step_by(batch_size) {
                let batch_end = (batch_start + batch_size).min(total_items);
                let items_in_batch = batch_end - batch_start;
                
                let handle = tokio::spawn(async move {
                    // 模拟批量处理
                    sleep(Duration::from_millis(items_in_batch as u64 * 10)).await;
                    items_in_batch
                });
                
                handles.push(handle);
            }
            
            let results = futures::future::join_all(handles).await;
            let duration = start.elapsed();
            let total_processed: usize = results.iter().map(|r| r.as_ref().unwrap_or(&0)).sum();
            
            println!("      处理 {} 项，耗时: {:?}, 吞吐量: {:.2} items/sec", 
                total_processed, duration, total_processed as f64 / duration.as_secs_f64());
        }

        Ok(())
    }

    async fn caching_strategy_demo(&self) -> Result<()> {
        println!("  缓存策略演示...");

        // 1. LRU缓存
        println!("    1. LRU缓存策略");
        let start = Instant::now();
        
        let cache = Arc::new(RwLock::new(HashMap::new()));
        let mut handles = vec![];
        
        for i in 0..100 {
            let cache = Arc::clone(&cache);
            let handle = tokio::spawn(async move {
                let key = format!("key_{}", i % 20); // 只有20个不同的key
                
                // 尝试从缓存读取
                {
                    let cache = cache.read().await;
                    if cache.contains_key(&key) {
                        return ("hit", key);
                    }
                }
                
                // 缓存未命中，模拟计算
                sleep(Duration::from_millis(10)).await;
                
                // 写入缓存
                {
                    let mut cache = cache.write().await;
                    cache.insert(key.clone(), format!("value_{}", i));
                }
                
                ("miss", key)
            });
            handles.push(handle);
        }
        
        let results = futures::future::join_all(handles).await;
        let cache_time = start.elapsed();
        
        let hits = results.iter().filter(|r| r.as_ref().unwrap().0 == "hit").count();
        let misses = results.len() - hits;
        let hit_rate = hits as f64 / results.len() as f64;
        
        println!("      缓存命中率: {:.1}%", hit_rate * 100.0);
        println!("      命中: {}, 未命中: {}", hits, misses);
        println!("      缓存操作耗时: {:?}", cache_time);

        // 2. 缓存预热
        println!("    2. 缓存预热策略");
        let start = Instant::now();
        
        let warmup_cache = Arc::new(RwLock::new(HashMap::new()));
        
        // 预热缓存
        {
            let mut cache = warmup_cache.write().await;
            for i in 0..50 {
                cache.insert(format!("warmup_key_{}", i), format!("warmup_value_{}", i));
            }
        }
        
        // 测试预热后的性能
        let mut handles = vec![];
        for i in 0..100 {
            let cache = Arc::clone(&warmup_cache);
            let handle = tokio::spawn(async move {
                let key = format!("warmup_key_{}", i % 50);
                
                let cache = cache.read().await;
                cache.get(&key).is_some()
            });
            handles.push(handle);
        }
        
        futures::future::join_all(handles).await;
        let warmup_time = start.elapsed();
        
        println!("      预热缓存耗时: {:?}", warmup_time);

        // 记录性能指标
        self.monitor.record_metrics("缓存策略", PerformanceMetrics {
            throughput: 100.0 / cache_time.as_secs_f64(),
            latency: cache_time,
            memory_usage: 1024 * 50, // 50KB
            cpu_usage: 5.0,
            error_rate: 1.0 - hit_rate,
        }).await;

        Ok(())
    }

    async fn async_io_optimization_demo(&self) -> Result<()> {
        println!("  异步I/O优化演示...");

        // 1. 批量I/O操作
        println!("    1. 批量I/O操作");
        let start = Instant::now();
        
        let (tx, mut rx) = mpsc::channel(1000);
        
        // 生产者：批量发送
        let producer = tokio::spawn(async move {
            let mut batch = Vec::new();
            for i in 0..100 {
                batch.push(format!("data_{}", i));
                
                if batch.len() >= 10 {
                    let batch_data = batch.drain(..).collect::<Vec<_>>();
                    if tx.send(batch_data).await.is_err() {
                        break;
                    }
                }
            }
            
            // 发送剩余数据
            if !batch.is_empty() {
                let _ = tx.send(batch).await;
            }
        });
        
        // 消费者：批量接收
        let consumer = tokio::spawn(async move {
            let mut total_received = 0;
            while let Some(batch) = rx.recv().await {
                total_received += batch.len();
                // 模拟批量处理
                sleep(Duration::from_millis(batch.len() as u64 * 5)).await;
            }
            total_received
        });
        
        let (_, total_received) = tokio::join!(producer, consumer);
        let batch_io_time = start.elapsed();
        
        println!("      批量I/O处理 {} 项，耗时: {:?}", total_received.unwrap_or(0), batch_io_time);

        // 2. 流式处理
        println!("    2. 流式处理优化");
        let start = Instant::now();
        
        let stream = futures::stream::iter(0..100)
            .map(|i| async move {
                sleep(Duration::from_millis(10)).await;
                i
            })
            .buffer_unordered(10); // 并发度10
        
        let results: Vec<_> = stream.collect().await;
        let stream_time = start.elapsed();
        
        println!("      流式处理 {} 项，耗时: {:?}", results.len(), stream_time);

        // 3. 背压处理
        println!("    3. 背压处理优化");
        let start = Instant::now();
        
        let (tx, mut rx) = mpsc::channel(5); // 小缓冲区
        let semaphore = Arc::new(Semaphore::new(3)); // 限制生产者
        
        // 快速生产者
        let producer = {
            let tx = tx.clone();
            let semaphore = Arc::clone(&semaphore);
            tokio::spawn(async move {
                for i in 0..20 {
                    let _permit = semaphore.acquire().await.unwrap();
                    
                    match tx.try_send(i) {
                        Ok(_) => {
                            println!("        发送数据: {}", i);
                        }
                        Err(_) => {
                            println!("        背压：等待消费者处理");
                            sleep(Duration::from_millis(100)).await;
                            continue;
                        }
                    }
                    
                    sleep(Duration::from_millis(50)).await;
                }
            })
        };
        
        // 慢速消费者
        let consumer = tokio::spawn(async move {
            while let Some(data) = rx.recv().await {
                println!("        处理数据: {}", data);
                sleep(Duration::from_millis(200)).await; // 慢速处理
            }
        });
        
        let _ = tokio::join!(producer, consumer);
        let backpressure_time = start.elapsed();
        
        println!("      背压处理耗时: {:?}", backpressure_time);

        // 记录性能指标
        self.monitor.record_metrics("异步I/O优化", PerformanceMetrics {
            throughput: 100.0 / batch_io_time.as_secs_f64(),
            latency: batch_io_time,
            memory_usage: 1024 * 20, // 20KB
            cpu_usage: 20.0,
            error_rate: 0.0,
        }).await;

        Ok(())
    }

    async fn performance_monitoring_demo(&self) -> Result<()> {
        println!("  性能监控演示...");

        // 模拟性能监控
        let start = Instant::now();
        
        let mut handles = vec![];
        
        for i in 0..10 {
            let handle = tokio::spawn(async move {
                let task_start = Instant::now();
                
                // 模拟工作负载
                sleep(Duration::from_millis(100 + i * 10)).await;
                
                let task_duration = task_start.elapsed();
                
                // 模拟随机失败
                if rand::random::<f32>() < 0.1 {
                    return (task_duration, true);
                }
                
                (task_duration, false)
            });
            
            handles.push(handle);
        }
        
        let results = futures::future::join_all(handles).await;
        let total_time = start.elapsed();
        
        let mut total_latency = Duration::ZERO;
        let mut error_count = 0;
        
        for result in results {
            match result {
                Ok((duration, is_error)) => {
                    total_latency += duration;
                    if is_error {
                        error_count += 1;
                    }
                }
                Err(_) => {
                    error_count += 1;
                }
            }
        }
        
        let avg_latency = total_latency / 10;
        let error_rate = error_count as f64 / 10.0;
        let throughput = 10.0 / total_time.as_secs_f64();
        
        println!("      总耗时: {:?}", total_time);
        println!("      平均延迟: {:?}", avg_latency);
        println!("      吞吐量: {:.2} ops/sec", throughput);
        println!("      错误率: {:.1}%", error_rate * 100.0);
        
        // 记录性能指标
        self.monitor.record_metrics("性能监控", PerformanceMetrics {
            throughput,
            latency: avg_latency,
            memory_usage: 1024 * 10, // 10KB
            cpu_usage: 25.0,
            error_rate,
        }).await;

        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    let demo = PerformanceDemo::new();
    demo.run().await?;

    println!("\n🎉 异步性能优化演示完成！");
    Ok(())
}
