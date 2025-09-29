//! 异步性能基准测试套件
//! 
//! 本基准测试套件评估各种异步操作和模式的性能：
//! - 异步任务生成和调度性能
//! - 异步同步原语性能
//! - 异步I/O操作性能
//! - 并发控制性能
//! - 内存使用和分配性能
//! 
//! 运行方式：
//! ```bash
//! cargo bench --bench async_benchmarks
//! ```

use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId};
use std::hint::black_box;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{Mutex, RwLock, Semaphore, mpsc};
use tokio::time::{sleep};
use futures::{StreamExt};
use std::collections::HashMap;

/// 异步任务生成基准测试
async fn benchmark_task_spawning(num_tasks: usize) {
    let mut handles = Vec::with_capacity(num_tasks);
    
    for _ in 0..num_tasks {
        let handle = tokio::spawn(async {
            // 模拟轻量级任务
            black_box(42)
        });
        handles.push(handle);
    }
    
    for handle in handles {
        black_box(handle.await.unwrap());
    }
}

/// 异步计数器基准测试
async fn benchmark_async_counter(num_operations: usize) {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = Vec::with_capacity(num_operations);
    
    for _ in 0..num_operations {
        let counter = Arc::clone(&counter);
        let handle = tokio::spawn(async move {
            let mut count = counter.lock().await;
            *count += 1;
            black_box(*count)
        });
        handles.push(handle);
    }
    
    for handle in handles {
        black_box(handle.await.unwrap());
    }
}

/// 异步读写锁基准测试
async fn benchmark_rwlock(num_readers: usize, num_writers: usize) {
    let data = Arc::new(RwLock::new(HashMap::<usize, String>::new()));
    let mut handles = Vec::new();
    
    // 启动读取者
    for _i in 0..num_readers {
        let data = Arc::clone(&data);
        let handle = tokio::spawn(async move {
            let data = data.read().await;
            black_box(data.len())
        });
        handles.push(handle);
    }
    
    // 启动写入者
    for i in 0..num_writers {
        let data = Arc::clone(&data);
        let handle = tokio::spawn(async move {
            let mut data = data.write().await;
            data.insert(i, format!("value_{}", i));
            black_box(data.len())
        });
        handles.push(handle);
    }
    
    for handle in handles {
        black_box(handle.await.unwrap());
    }
}

/// 异步通道基准测试
async fn benchmark_channels(num_messages: usize, buffer_size: usize) {
    let (tx, mut rx) = mpsc::channel(buffer_size);
    
    // 发送者
    let sender = tokio::spawn(async move {
        for i in 0..num_messages {
            tx.send(black_box(i)).await.unwrap();
        }
    });
    
    // 接收者
    let receiver = tokio::spawn(async move {
        let mut received = 0;
        while let Some(msg) = rx.recv().await {
            black_box(msg);
            received += 1;
        }
        received
    });
    
    sender.await.unwrap();
    let received = receiver.await.unwrap();
    black_box(received);
}

/// 信号量基准测试
async fn benchmark_semaphore(num_tasks: usize, permits: usize) {
    let semaphore = Arc::new(Semaphore::new(permits));
    let mut handles = Vec::with_capacity(num_tasks);
    
    for _ in 0..num_tasks {
        let semaphore = Arc::clone(&semaphore);
        let handle = tokio::spawn(async move {
            let _permit = semaphore.acquire().await.unwrap();
            // 模拟工作
            sleep(Duration::from_millis(1)).await;
            black_box(42)
        });
        handles.push(handle);
    }
    
    for handle in handles {
        black_box(handle.await.unwrap());
    }
}

/// 异步流处理基准测试
async fn benchmark_stream_processing(num_items: usize) {
    let stream = futures::stream::iter(0..num_items)
        .map(|i| async move {
            // 模拟异步处理
            sleep(Duration::from_micros(1)).await;
            black_box(i * 2)
        })
        .buffer_unordered(100); // 并发度100
    
    let results: Vec<_> = stream.collect().await;
    black_box(results.len());
}

/// 异步批处理基准测试
async fn benchmark_batch_processing(num_items: usize, batch_size: usize) {
    let mut batches = Vec::new();
    
    for chunk in (0..num_items).collect::<Vec<_>>().chunks(batch_size) {
        let batch = chunk.to_vec();
        batches.push(batch);
    }
    
    let mut handles = Vec::new();
    
    for batch in batches {
        let handle = tokio::spawn(async move {
            // 模拟批处理
            sleep(Duration::from_micros(batch.len() as u64 * 10)).await;
            black_box(batch.len())
        });
        handles.push(handle);
    }
    
    for handle in handles {
        black_box(handle.await.unwrap());
    }
}

/// 异步超时基准测试
async fn benchmark_timeout(num_operations: usize) {
    let mut handles = Vec::with_capacity(num_operations);
    
    for i in 0..num_operations {
        let delay_ms = if i % 2 == 0 { 50 } else { 150 };
        let handle = tokio::spawn(async move {
            match tokio::time::timeout(
                Duration::from_millis(100),
                sleep(Duration::from_millis(delay_ms))
            ).await {
                Ok(_) => black_box("completed"),
                Err(_) => black_box("timeout"),
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        black_box(handle.await.unwrap());
    }
}

/// 异步重试基准测试
async fn benchmark_retry(num_operations: usize, max_attempts: u32) {
    let mut handles = Vec::with_capacity(num_operations);
    
    for _ in 0..num_operations {
        let handle = tokio::spawn(async move {
            let mut attempts = 0;
            loop {
                attempts += 1;
                // 模拟70%失败率
                if rand::random::<f32>() < 0.7 && attempts < max_attempts {
                    sleep(Duration::from_millis(1)).await;
                    continue;
                }
                break;
            }
            black_box(attempts)
        });
        handles.push(handle);
    }
    
    for handle in handles {
        black_box(handle.await.unwrap());
    }
}

/// 异步缓存基准测试
async fn benchmark_cache(num_operations: usize, cache_size: usize) {
    let cache = Arc::new(RwLock::new(HashMap::<usize, String>::with_capacity(cache_size)));
    let mut handles = Vec::with_capacity(num_operations);
    
    for i in 0..num_operations {
        let cache = Arc::clone(&cache);
        let key = i % cache_size;
        
        let handle = tokio::spawn(async move {
            // 模拟缓存操作
            if i % 3 == 0 {
                // 写操作
                let mut cache = cache.write().await;
                cache.insert(key, format!("value_{}", key));
            } else {
                // 读操作
                let cache = cache.read().await;
                black_box(cache.get(&key));
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        black_box(handle.await.unwrap());
    }
}

/// 异步事件循环基准测试
async fn benchmark_event_loop(num_events: usize) {
    let (tx, mut rx) = mpsc::unbounded_channel();
    
    // 事件发送者
    let sender = tokio::spawn(async move {
        for i in 0..num_events {
            tx.send(i).unwrap();
        }
    });
    
    // 事件处理器
    let mut processed = 0;
    while let Some(event) = rx.recv().await {
        black_box(event);
        processed += 1;
        
        if processed >= num_events {
            break;
        }
    }
    
    sender.await.unwrap();
    black_box(processed);
}

/// 设置基准测试
fn setup_benchmark(c: &mut Criterion) {
    let rt = tokio::runtime::Runtime::new().unwrap();
    
    // 任务生成基准测试
    let mut group = c.benchmark_group("task_spawning");
    for num_tasks in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("spawn_tasks", num_tasks), num_tasks, |b, &num_tasks| {
            b.to_async(&rt).iter(|| benchmark_task_spawning(num_tasks));
        });
    }
    group.finish();
    
    // 异步计数器基准测试
    let mut group = c.benchmark_group("async_counter");
    for num_ops in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("counter_operations", num_ops), num_ops, |b, &num_ops| {
            b.to_async(&rt).iter(|| benchmark_async_counter(num_ops));
        });
    }
    group.finish();
    
    // 读写锁基准测试
    let mut group = c.benchmark_group("rwlock");
    for &(readers, writers) in [(10, 1), (100, 10), (1000, 100)].iter() {
        group.bench_with_input(
            BenchmarkId::new("read_write", format!("{}r_{}w", readers, writers)), 
            &(readers, writers), 
            |b, &(readers, writers)| {
                b.to_async(&rt).iter(|| benchmark_rwlock(readers, writers));
            }
        );
    }
    group.finish();
    
    // 通道基准测试
    let mut group = c.benchmark_group("channels");
    for &(msgs, buf_size) in [(1000, 100), (10000, 1000), (100000, 10000)].iter() {
        group.bench_with_input(
            BenchmarkId::new("channel_throughput", format!("{}msgs_{}buf", msgs, buf_size)), 
            &(msgs, buf_size), 
            |b, &(msgs, buf_size)| {
                b.to_async(&rt).iter(|| benchmark_channels(msgs, buf_size));
            }
        );
    }
    group.finish();
    
    // 信号量基准测试
    let mut group = c.benchmark_group("semaphore");
    for &(tasks, permits) in [(100, 10), (1000, 100), (10000, 1000)].iter() {
        group.bench_with_input(
            BenchmarkId::new("semaphore_control", format!("{}tasks_{}permits", tasks, permits)), 
            &(tasks, permits), 
            |b, &(tasks, permits)| {
                b.to_async(&rt).iter(|| benchmark_semaphore(tasks, permits));
            }
        );
    }
    group.finish();
    
    // 流处理基准测试
    let mut group = c.benchmark_group("stream_processing");
    for num_items in [1000, 10000, 100000].iter() {
        group.bench_with_input(BenchmarkId::new("stream_items", num_items), num_items, |b, &num_items| {
            b.to_async(&rt).iter(|| benchmark_stream_processing(num_items));
        });
    }
    group.finish();
    
    // 批处理基准测试
    let mut group = c.benchmark_group("batch_processing");
    for &(items, batch_size) in [(1000, 100), (10000, 1000), (100000, 10000)].iter() {
        group.bench_with_input(
            BenchmarkId::new("batch_size", format!("{}items_{}batch", items, batch_size)), 
            &(items, batch_size), 
            |b, &(items, batch_size)| {
                b.to_async(&rt).iter(|| benchmark_batch_processing(items, batch_size));
            }
        );
    }
    group.finish();
    
    // 超时基准测试
    let mut group = c.benchmark_group("timeout");
    for num_ops in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("timeout_operations", num_ops), num_ops, |b, &num_ops| {
            b.to_async(&rt).iter(|| benchmark_timeout(num_ops));
        });
    }
    group.finish();
    
    // 重试基准测试
    let mut group = c.benchmark_group("retry");
    for num_ops in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::new("retry_operations", num_ops), num_ops, |b, &num_ops| {
            b.to_async(&rt).iter(|| benchmark_retry(num_ops, 3));
        });
    }
    group.finish();
    
    // 缓存基准测试
    let mut group = c.benchmark_group("cache");
    for &(ops, cache_size) in [(1000, 100), (10000, 1000), (100000, 10000)].iter() {
        group.bench_with_input(
            BenchmarkId::new("cache_operations", format!("{}ops_{}size", ops, cache_size)), 
            &(ops, cache_size), 
            |b, &(ops, cache_size)| {
                b.to_async(&rt).iter(|| benchmark_cache(ops, cache_size));
            }
        );
    }
    group.finish();
    
    // 事件循环基准测试
    let mut group = c.benchmark_group("event_loop");
    for num_events in [1000, 10000, 100000].iter() {
        group.bench_with_input(BenchmarkId::new("event_processing", num_events), num_events, |b, &num_events| {
            b.to_async(&rt).iter(|| benchmark_event_loop(num_events));
        });
    }
    group.finish();
}

criterion_group!(benches, setup_benchmark);
criterion_main!(benches);
