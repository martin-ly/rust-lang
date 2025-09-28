//! 改进的异步特性演示程序
//! 
//! 本程序展示了当前稳定版本中实际可用的异步特性，
//! 包括超时控制、结构化并发、错误恢复等实际功能。

use std::sync::Arc;
use std::time::Duration;
use anyhow::Result;
use tracing::{info, error};
use c06_async::improved_async_features::{
    ImprovedAsyncResourceManager,
    AsyncTaskScheduler,
    AsyncErrorRecovery,
    BackoffStrategy,
    ScheduledTask,
};

#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();
    
    info!("🚀 开始改进的异步特性演示");
    info!("==========================================");

    // 1. 演示改进的异步资源管理
    demo_improved_resource_management().await?;
    
    // 2. 演示结构化并发
    demo_structured_concurrency().await?;
    
    // 3. 演示异步任务调度
    demo_async_task_scheduling().await?;
    
    // 4. 演示错误恢复机制
    demo_error_recovery().await?;
    
    // 5. 演示超时控制
    demo_timeout_control().await?;

    info!("🎉 改进的异步特性演示完成！");
    Ok(())
}

/// 演示改进的异步资源管理
async fn demo_improved_resource_management() -> Result<()> {
    info!("📦 演示改进的异步资源管理");
    
    let manager = Arc::new(ImprovedAsyncResourceManager::new(5));
    
    // 并发获取资源
    let mut handles = Vec::new();
    for i in 0..10 {
        let manager = Arc::clone(&manager);
        let handle = tokio::spawn(async move {
            match manager.acquire_with_timeout(Duration::from_millis(100)).await {
                Ok(resource) => {
                    info!("成功获取资源: {}", resource.id);
                    Ok(i)
                }
                Err(e) => {
                    error!("获取资源失败: {}", e);
                    Err(e)
                }
            }
        });
        handles.push(handle);
    }

    // 等待所有任务完成
    let results = futures::future::join_all(handles).await;
    let success_count = results.iter().filter(|r| r.is_ok()).count();
    info!("资源获取完成，成功: {}/{}", success_count, results.len());

    // 显示统计信息
    let stats = manager.get_statistics().await;
    info!("资源管理器统计: 总资源={}, 最大并发={}, 可用许可={}", 
          stats.total_resources, stats.max_concurrent, stats.available_permits);

    Ok(())
}

/// 演示结构化并发
async fn demo_structured_concurrency() -> Result<()> {
    info!("🔗 演示结构化并发");
    
    let manager = ImprovedAsyncResourceManager::new(3);
    
    // 创建并发任务
    let tasks: Vec<Box<dyn std::future::Future<Output = Result<i32, anyhow::Error>> + Send>> = (0..5).map(|i| {
        let future = async move {
            tokio::time::sleep(Duration::from_millis(50)).await;
            info!("任务 {} 完成", i);
            Ok::<i32, anyhow::Error>(i * 2)
        };
        Box::new(future) as Box<dyn std::future::Future<Output = Result<i32, anyhow::Error>> + Send>
    }).collect();

    // 使用结构化并发执行
    let results = manager.process_with_structured_concurrency(tasks).await?;
    
    let successful_results: Vec<i32> = results.into_iter()
        .filter_map(|r| r.ok())
        .collect();
    
    info!("结构化并发完成，成功处理 {} 个任务", successful_results.len());
    info!("结果: {:?}", successful_results);

    Ok(())
}

/// 演示异步任务调度
async fn demo_async_task_scheduling() -> Result<()> {
    info!("⏰ 演示异步任务调度");
    
    let scheduler = Arc::new(AsyncTaskScheduler::new(3));
    
    // 调度一些任务
    for i in 0..5 {
        let task = ScheduledTask {
            id: format!("task_{}", i),
            delay: Duration::from_millis(i * 100),
            task: Box::new(move || {
                let i = i;
                Box::pin(async move {
                    info!("执行延迟任务 {}", i);
                    tokio::time::sleep(Duration::from_millis(50)).await;
                })
            }),
        };
        
        scheduler.schedule_task(task).await?;
    }

    // 启动调度器（运行一段时间）
    let scheduler_clone = Arc::clone(&scheduler);
    let scheduler_handle = tokio::spawn(async move {
        if let Err(e) = scheduler_clone.start().await {
            error!("调度器错误: {}", e);
        }
    });

    // 等待一段时间让任务执行
    tokio::time::sleep(Duration::from_secs(2)).await;
    
    // 取消调度器
    scheduler_handle.abort();
    info!("任务调度演示完成");

    Ok(())
}

/// 演示错误恢复机制
async fn demo_error_recovery() -> Result<()> {
    info!("🔄 演示错误恢复机制");
    
    // 创建错误恢复器
    let recovery = AsyncErrorRecovery::new(
        3,
        BackoffStrategy::Exponential(Duration::from_millis(100), 2.0),
    );

    // 模拟可能失败的操作
    let mut attempt_count = 0;
    let result = recovery.execute_with_retry(|| {
        attempt_count += 1;
        Box::pin(async move {
            if attempt_count < 3 {
                error!("操作失败，第 {} 次尝试", attempt_count);
                Err(anyhow::anyhow!("模拟网络错误"))
            } else {
                info!("操作成功，第 {} 次尝试", attempt_count);
                Ok(format!("成功结果 - 尝试次数: {}", attempt_count))
            }
        })
    }).await?;

    info!("错误恢复演示完成: {}", result);
    info!("总尝试次数: {}", attempt_count);

    Ok(())
}

/// 演示超时控制
async fn demo_timeout_control() -> Result<()> {
    info!("⏱️ 演示超时控制");
    
    let manager = ImprovedAsyncResourceManager::new(2);
    
    // 测试正常超时
    info!("测试正常超时场景...");
    let start = std::time::Instant::now();
    let result = manager.acquire_with_timeout(Duration::from_millis(200)).await;
    let duration = start.elapsed();
    
    match result {
        Ok(resource) => {
            info!("正常获取资源成功: {}, 耗时: {:?}", resource.id, duration);
        }
        Err(e) => {
            error!("获取资源失败: {}", e);
        }
    }

    // 测试超时场景
    info!("测试超时场景...");
    let start = std::time::Instant::now();
    let result = manager.acquire_with_timeout(Duration::from_millis(1)).await;
    let duration = start.elapsed();
    
    match result {
        Ok(_) => {
            info!("意外成功获取资源，耗时: {:?}", duration);
        }
        Err(e) => {
            info!("预期的超时错误: {}, 耗时: {:?}", e, duration);
        }
    }

    info!("超时控制演示完成");

    Ok(())
}
