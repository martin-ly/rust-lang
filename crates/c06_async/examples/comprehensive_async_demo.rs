//! 异步编程综合演示示例
//! 
//! 本示例展示了 Rust 异步编程的各个方面：
//! - Future 状态机
//! - async/await 用法
//! - Stream 流处理
//! - 并发控制
//! - 错误处理
//! - 性能优化
//! 
//! 运行方式：
//! ```bash
//! cargo run --example comprehensive_async_demo
//! ```

use std::time::Duration;
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock, Semaphore, Notify};
use tokio::time::{sleep, timeout};
use futures::{StreamExt, future, stream};
use anyhow::{Result, Context};

/// 演示基本的异步函数和并发执行
#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 Rust 异步编程综合演示");
    println!("================================");

    // 1. 基本异步函数演示
    println!("\n📋 1. 基本异步函数演示");
    demo_basic_async().await?;

    // 2. Future 组合子演示
    println!("\n🔧 2. Future 组合子演示");
    demo_future_combinators().await?;

    // 3. Stream 流处理演示
    println!("\n🌊 3. Stream 流处理演示");
    demo_stream_processing().await?;

    // 4. 并发控制演示
    println!("\n🔒 4. 并发控制演示");
    demo_concurrency_control().await?;

    // 5. 错误处理演示
    println!("\n❌ 5. 错误处理演示");
    demo_error_handling().await?;

    // 6. 性能优化演示
    println!("\n⚡ 6. 性能优化演示");
    demo_performance_optimization().await?;

    println!("\n✅ 所有演示完成！");
    Ok(())
}

/// 1. 基本异步函数演示
#[allow(dead_code)]
async fn demo_basic_async() -> Result<()> {
    println!("  基本异步函数调用...");

    // 顺序执行
    let start = std::time::Instant::now();
    let result1 = async_task("任务1", 100).await;
    let result2 = async_task("任务2", 100).await;
    let sequential_time = start.elapsed();
    println!("  顺序执行结果: {}, {}, 耗时: {:?}", result1, result2, sequential_time);

    // 并发执行
    let start = std::time::Instant::now();
    let (result1, result2) = futures::join!(
        async_task("任务1", 100),
        async_task("任务2", 100)
    );
    let concurrent_time = start.elapsed();
    println!("  并发执行结果: {}, {}, 耗时: {:?}", result1, result2, concurrent_time);

    // 选择执行（先完成的返回）
    let result = tokio::select! {
        result = async_task("快速任务", 50) => result,
        result = async_task("慢速任务", 200) => result,
    };
    println!("  选择执行结果: {}", result);

    Ok(())
}

/// 2. Future 组合子演示
#[allow(dead_code)]
async fn demo_future_combinators() -> Result<()> {
    println!("  Future 组合子操作...");

    // 创建多个 Future
    let futures = vec![
        async_task("Future1", 100),
        async_task("Future2", 150),
        async_task("Future3", 200),
    ];

    // join_all - 等待所有 Future 完成
    let start = std::time::Instant::now();
    let results = future::join_all(futures).await;
    let join_all_time = start.elapsed();
    println!("  join_all 结果: {:?}, 耗时: {:?}", results, join_all_time);

    // try_join_all - 等待所有 Future 完成，任何一个失败就返回错误
    let futures: Vec<_> = (1..=3)
        .map(|i| async move {
            if i == 2 {
                Err(anyhow::anyhow!("模拟错误"))?;
            }
            Ok::<String, anyhow::Error>(async_task(&format!("TryJoin{}", i), 100).await)
        })
        .collect();

    match future::try_join_all(futures).await {
        Ok(results) => println!("  try_join_all 成功: {:?}", results),
        Err(e) => println!("  try_join_all 失败: {}", e),
    }

    Ok(())
}

/// 3. Stream 流处理演示
#[allow(dead_code)]
async fn demo_stream_processing() -> Result<()> {
    println!("  Stream 流处理操作...");

    // 基本 Stream 操作
    let numbers = stream::iter(1..=10);
    let result = numbers
        .map(|x| x * 2)
        .take(3)
        .collect::<Vec<_>>()
        .await;
    println!("  基本 Stream 操作结果: {:?}", result);

    // 并发 Stream 处理
    let urls = vec![
        "https://example.com".to_string(),
        "https://httpbin.org/get".to_string(),
        "https://jsonplaceholder.typicode.com/posts/1".to_string(),
    ];

    let client = reqwest::Client::new();
    let futures = stream::iter(urls.into_iter().map(|url| {
        let client = client.clone();
        async move {
            match client.get(&url).send().await {
                Ok(response) => Ok((url, response.status())),
                Err(e) => Err(e),
            }
        }
    }));

    let results = futures
        .buffer_unordered(2) // 最多 2 个并发
        .collect::<Vec<_>>()
        .await;

    println!("  并发 Stream 处理结果:");
    for result in results {
        match result {
            Ok((url, status)) => println!("    {}: {}", url, status),
            Err(e) => println!("    错误: {}", e),
        }
    }

    Ok(())
}

/// 4. 并发控制演示
#[allow(dead_code)]
async fn demo_concurrency_control() -> Result<()> {
    println!("  并发控制原语演示...");

    // Mutex 演示
    demo_mutex().await?;

    // RwLock 演示
    demo_rwlock().await?;

    // Semaphore 演示
    demo_semaphore().await?;

    // Notify 演示
    demo_notify().await?;

    Ok(())
}

/// Mutex 演示
#[allow(dead_code)]
async fn demo_mutex() -> Result<()> {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for i in 0..5 {
        let counter = Arc::clone(&counter);
        let handle = tokio::spawn(async move {
            let mut num = counter.lock().await;
            *num += 1;
            println!("    Mutex: 任务 {} 增加计数器到 {}", i, *num);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await?;
    }

    println!("  Mutex 最终计数: {}", *counter.lock().await);
    Ok(())
}

/// RwLock 演示
#[allow(dead_code)]
async fn demo_rwlock() -> Result<()> {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));

    // 并发读取
    let read_handles: Vec<_> = (0..3)
        .map(|i| {
            let data = Arc::clone(&data);
            tokio::spawn(async move {
                let reader = data.read().await;
                println!("    RwLock 读任务 {}: {:?}", i, *reader);
            })
        })
        .collect();

    // 写入操作
    let write_handle = {
        let data = Arc::clone(&data);
        tokio::spawn(async move {
            let mut writer = data.write().await;
            writer.push(4);
            println!("    RwLock 写入完成");
        })
    };

    // 等待所有操作完成
    futures::future::join_all(read_handles).await;
    write_handle.await?;

    Ok(())
}

/// Semaphore 演示
#[allow(dead_code)]
async fn demo_semaphore() -> Result<()> {
    let semaphore = Arc::new(Semaphore::new(2)); // 最多 2 个并发
    let mut handles = vec![];

    for i in 0..5 {
        let semaphore = Arc::clone(&semaphore);
        let handle = tokio::spawn(async move {
            let _permit = semaphore.acquire().await.unwrap();
            println!("    Semaphore: 任务 {} 获得许可", i);
            sleep(Duration::from_millis(100)).await;
            println!("    Semaphore: 任务 {} 释放许可", i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await?;
    }

    Ok(())
}

/// Notify 演示
#[allow(dead_code)]
async fn demo_notify() -> Result<()> {
    let notify = Arc::new(Notify::new());

    // 等待任务
    let waiting_task = {
        let notify = Arc::clone(&notify);
        tokio::spawn(async move {
            println!("    Notify: 等待通知...");
            notify.notified().await;
            println!("    Notify: 收到通知！");
        })
    };

    // 通知任务
    let notifying_task = {
        let notify = Arc::clone(&notify);
        tokio::spawn(async move {
            sleep(Duration::from_millis(100)).await;
            println!("    Notify: 发送通知");
            notify.notify_one();
        })
    };

    let _ = tokio::join!(waiting_task, notifying_task);
    Ok(())
}

/// 5. 错误处理演示
async fn demo_error_handling() -> Result<()> {
    println!("  错误处理策略演示...");

    // 重试机制
    let result = retry_operation(3).await;
    match result {
        Ok(value) => println!("  重试成功: {}", value),
        Err(e) => println!("  重试失败: {}", e),
    }

    // 超时处理
    match timeout(Duration::from_millis(50), slow_operation()).await {
        Ok(result) => println!("  超时操作成功: {}", result),
        Err(_) => println!("  操作超时"),
    }

    // 错误转换
    match error_transformation().await {
        Ok(result) => println!("  错误转换成功: {}", result),
        Err(e) => println!("  错误转换失败: {}", e),
    }

    Ok(())
}

/// 重试操作演示
async fn retry_operation(max_attempts: u32) -> Result<String> {
    let mut attempts = 0;
    loop {
        attempts += 1;
        match risky_operation().await {
            Ok(result) => return Ok(result),
            Err(e) if attempts >= max_attempts => return Err(e),
            Err(_) => {
                println!("    重试第 {} 次", attempts);
                sleep(Duration::from_millis(100)).await;
            }
        }
    }
}

/// 慢速操作演示
async fn slow_operation() -> String {
    sleep(Duration::from_millis(100)).await;
    "慢速操作完成".to_string()
}

/// 错误转换演示
async fn error_transformation() -> Result<String, anyhow::Error> {
    let result = risky_operation().await
        .context("执行风险操作失败")?;
    Ok(result)
}

/// 6. 性能优化演示
async fn demo_performance_optimization() -> Result<()> {
    println!("  性能优化技术演示...");

    // 批量处理
    let items = (1..=100).collect::<Vec<_>>();
    let batch_size = 10;

    let start = std::time::Instant::now();
    let mut results = Vec::new();

    for chunk in items.chunks(batch_size) {
        let chunk_futures = chunk.iter().map(|&item| async move {
            process_item(item).await
        });
        let chunk_results = future::join_all(chunk_futures).await;
        results.extend(chunk_results);
    }

    let batch_time = start.elapsed();
    println!("  批量处理 {} 个项目耗时: {:?}", items.len(), batch_time);

    // 连接池演示（模拟）
    let pool_size = 5;
    let semaphore = Arc::new(Semaphore::new(pool_size));

    let start = std::time::Instant::now();
    let handles: Vec<_> = (0..20)
        .map(|i| {
            let semaphore = Arc::clone(&semaphore);
            tokio::spawn(async move {
                let _permit = semaphore.acquire().await.unwrap();
                simulate_database_operation(i).await
            })
        })
        .collect();

    let results = futures::future::join_all(handles).await;
    let pool_time = start.elapsed();
    println!("  连接池处理 {} 个任务耗时: {:?}", results.len(), pool_time);

    Ok(())
}

// 辅助函数

/// 模拟异步任务
async fn async_task(name: &str, delay_ms: u64) -> String {
    sleep(Duration::from_millis(delay_ms)).await;
    format!("{}完成", name)
}

/// 模拟风险操作（可能失败）
async fn risky_operation() -> Result<String, anyhow::Error> {
    // 模拟 30% 的失败率
    if rand::random::<f32>() < 0.3 {
        Err(anyhow::anyhow!("随机失败"))
    } else {
        Ok("操作成功".to_string())
    }
}

/// 模拟处理单个项目
async fn process_item(item: i32) -> i32 {
    sleep(Duration::from_millis(10)).await;
    item * 2
}

/// 模拟数据库操作
async fn simulate_database_operation(id: i32) -> String {
    sleep(Duration::from_millis(50)).await;
    format!("数据库操作 {} 完成", id)
}
