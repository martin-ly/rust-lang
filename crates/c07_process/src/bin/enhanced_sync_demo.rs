//! 增强的同步原语演示程序
//! 
//! 这个程序展示了增强的同步原语功能，包括死锁检测、
//! 性能监控、自适应锁策略等 Rust 1.90 新特性

#[cfg(feature = "async")]
use c07_process::prelude::*;
#[cfg(feature = "async")]
use c07_process::{EnhancedSyncManager, DeadlockRisk};
#[cfg(feature = "async")]
use std::time::Duration;

#[cfg(feature = "async")]
#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 增强的同步原语演示程序");
    println!("========================\n");

    // 创建增强的同步管理器
    println!("🔧 创建增强的同步管理器...");
    let config = SyncConfig::default();
    let manager = EnhancedSyncManager::new(config).await?;
    println!("✅ 增强的同步管理器创建成功！\n");

    // 演示基础同步原语功能
    println!("1️⃣ 基础同步原语功能演示");
    println!("------------------------");
    demonstrate_basic_sync_features(&manager).await?;
    println!();

    // 演示死锁检测
    println!("2️⃣ 死锁检测演示");
    println!("---------------");
    demonstrate_deadlock_detection(&manager).await?;
    println!();

    // 演示性能监控
    println!("3️⃣ 性能监控演示");
    println!("---------------");
    demonstrate_performance_monitoring(&manager).await?;
    println!();

    // 演示自适应锁策略
    println!("4️⃣ 自适应锁策略演示");
    println!("-------------------");
    demonstrate_adaptive_scheduling(&manager).await?;
    println!();

    // 演示高级同步功能
    println!("5️⃣ 高级同步功能演示");
    println!("-------------------");
    demonstrate_advanced_sync_features(&manager).await?;
    println!();

    println!("\n🎉 增强的同步原语演示完成！");
    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_basic_sync_features(manager: &EnhancedSyncManager) -> Result<()> {
    // 创建增强的互斥锁
    println!("  创建增强的互斥锁...");
    let mutex = manager.create_enhanced_mutex("basic_mutex").await?;
    println!("  ✅ 增强的互斥锁创建成功");

    // 创建增强的读写锁
    println!("  创建增强的读写锁...");
    let rwlock = manager.create_enhanced_rwlock("basic_rwlock").await?;
    println!("  ✅ 增强的读写锁创建成功");

    // 创建增强的信号量
    println!("  创建增强的信号量...");
    let semaphore = manager.create_enhanced_semaphore("basic_semaphore", 3).await?;
    println!("  ✅ 增强的信号量创建成功");

    // 创建增强的屏障
    println!("  创建增强的屏障...");
    let barrier = manager.create_enhanced_barrier("basic_barrier", 3).await?;
    println!("  ✅ 增强的屏障创建成功");

    // 测试互斥锁
    println!("  测试互斥锁...");
    let _guard = mutex.lock().await?;
    println!("  ✅ 互斥锁获取成功");

    // 测试读写锁
    println!("  测试读写锁...");
    let _read_guard = rwlock.read().await;
    println!("  ✅ 读写锁读锁获取成功");

    // 测试信号量
    println!("  测试信号量...");
    let _permit = semaphore.acquire().await?;
    println!("  ✅ 信号量获取成功");

    // 测试屏障
    println!("  测试屏障...");
    let _barrier_guard = barrier.wait().await;
    println!("  ✅ 屏障等待成功");

    // 获取统计信息
    println!("  获取统计信息...");
    let mutex_stats = manager.get_primitive_stats("basic_mutex").await.unwrap();
    println!("    互斥锁统计: 锁定次数={}, 解锁次数={}", 
            mutex_stats.lock_count, mutex_stats.unlock_count);

    let rwlock_stats = manager.get_primitive_stats("basic_rwlock").await.unwrap();
    println!("    读写锁统计: 锁定次数={}, 解锁次数={}", 
            rwlock_stats.lock_count, rwlock_stats.unlock_count);

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_deadlock_detection(manager: &EnhancedSyncManager) -> Result<()> {
    // 创建多个互斥锁用于死锁检测
    println!("  创建多个互斥锁用于死锁检测...");
    let mutex1 = manager.create_enhanced_mutex("deadlock_mutex1").await?;
    let mutex2 = manager.create_enhanced_mutex("deadlock_mutex2").await?;
    println!("  ✅ 多个互斥锁创建成功");

    // 模拟死锁场景
    println!("  模拟死锁场景...");
    let mutex1_clone = mutex1.clone();
    let mutex2_clone = mutex2.clone();

    // 任务1：先获取mutex1，再获取mutex2
    let task1 = tokio::spawn(async move {
        let _guard1 = mutex1_clone.lock().await.unwrap();
        println!("    任务1: 获取mutex1成功");
        
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        let _guard2 = mutex2_clone.lock().await.unwrap();
        println!("    任务1: 获取mutex2成功");
    });

    // 任务2：先获取mutex2，再获取mutex1
    let task2 = tokio::spawn(async move {
        let _guard2 = mutex2.lock().await.unwrap();
        println!("    任务2: 获取mutex2成功");
        
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        let _guard1 = mutex1.lock().await.unwrap();
        println!("    任务2: 获取mutex1成功");
    });

    // 等待任务完成
    let _ = tokio::join!(task1, task2);

    // 检查死锁风险
    println!("  检查死锁风险...");
    let risks = manager.check_deadlock_risk().await;
    for (name, risk) in risks {
        println!("    {} 死锁风险: {:?}", name, risk);
    }

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_performance_monitoring(manager: &EnhancedSyncManager) -> Result<()> {
    // 创建高性能互斥锁
    println!("  创建高性能互斥锁...");
    let mutex = manager.create_enhanced_mutex("perf_mutex").await?;
    println!("  ✅ 高性能互斥锁创建成功");

    // 进行大量锁操作
    println!("  进行大量锁操作...");
    let mut handles = Vec::new();

    for _i in 0..100 {
        let mutex_clone = mutex.clone();
        let handle = tokio::spawn(async move {
            for _ in 0..10 {
                let _guard = mutex_clone.lock().await.unwrap();
                // 模拟一些工作
                tokio::time::sleep(Duration::from_micros(100)).await;
            }
        });
        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        let _ = handle.await;
    }
    println!("  ✅ 大量锁操作完成");

    // 获取性能指标
    println!("  获取性能指标...");
    let stats = manager.get_primitive_stats("perf_mutex").await.unwrap();
    println!("    锁定次数: {}", stats.lock_count);
    println!("    解锁次数: {}", stats.unlock_count);
    println!("    总等待时间: {:?}", stats.total_wait_time);
    println!("    最大等待时间: {:?}", stats.max_wait_time);
    println!("    平均等待时间: {:?}", stats.average_wait_time);
    println!("    争用次数: {}", stats.contention_count);

    // 获取性能指标
    if let Some(metrics) = manager.get_performance_metrics("perf_mutex").await {
        println!("    吞吐量: {:.2} ops/sec", metrics.throughput);
        println!("    延迟: {:?}", metrics.latency);
        println!("    争用率: {:.2}%", metrics.contention_rate * 100.0);
        println!("    利用率: {:.2}%", metrics.utilization * 100.0);
    }

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_adaptive_scheduling(manager: &EnhancedSyncManager) -> Result<()> {
    // 创建自适应互斥锁
    println!("  创建自适应互斥锁...");
    let mutex = manager.create_enhanced_mutex("adaptive_mutex").await?;
    println!("  ✅ 自适应互斥锁创建成功");

    // 模拟不同负载场景
    println!("  模拟不同负载场景...");

    // 低负载场景
    println!("    低负载场景...");
    for _ in 0..10 {
        let _guard = mutex.lock().await?;
        tokio::time::sleep(Duration::from_millis(10)).await;
    }

    // 高负载场景
    println!("    高负载场景...");
    let mut handles = Vec::new();
    for _ in 0..50 {
        let mutex_clone = mutex.clone();
        let handle = tokio::spawn(async move {
            let _guard = mutex_clone.lock().await.unwrap();
            tokio::time::sleep(Duration::from_millis(5)).await;
        });
        handles.push(handle);
    }

    // 等待高负载任务完成
    for handle in handles {
        let _ = handle.await;
    }

    // 自适应调整
    println!("  自适应调整...");
    manager.adaptive_adjust_all(0.8).await?;
    println!("  ✅ 自适应调整完成");

    // 获取调整后的统计信息
    let stats = manager.get_primitive_stats("adaptive_mutex").await.unwrap();
    println!("    调整后统计: 锁定次数={}, 争用次数={}", 
            stats.lock_count, stats.contention_count);

    Ok(())
}

#[cfg(feature = "async")]
async fn demonstrate_advanced_sync_features(manager: &EnhancedSyncManager) -> Result<()> {
    // 演示高级同步功能
    println!("  演示高级同步功能...");

    // 创建复杂的同步原语组合
    println!("    创建复杂的同步原语组合...");
    let mutex = manager.create_enhanced_mutex("advanced_mutex").await?;
    let rwlock = manager.create_enhanced_rwlock("advanced_rwlock").await?;
    let semaphore = manager.create_enhanced_semaphore("advanced_semaphore", 5).await?;
    let barrier = manager.create_enhanced_barrier("advanced_barrier", 3).await?;

    // 测试复杂的同步场景
    println!("    测试复杂的同步场景...");
    let mut handles = Vec::new();

    for i in 0..3 {
        let mutex_clone = mutex.clone();
        let rwlock_clone = rwlock.clone();
        let semaphore_clone = semaphore.clone();
        let barrier_clone = barrier.clone();

        let handle = tokio::spawn(async move {
            // 获取信号量
            let _permit = semaphore_clone.acquire().await.unwrap();
            println!("      任务{}: 获取信号量成功", i);

            // 获取读锁
            let _read_guard = rwlock_clone.read().await;
            println!("      任务{}: 获取读锁成功", i);

            // 获取互斥锁
            let _mutex_guard = mutex_clone.lock().await.unwrap();
            println!("      任务{}: 获取互斥锁成功", i);

            // 等待屏障
            let _barrier_guard = barrier_clone.wait().await;
            println!("      任务{}: 屏障等待成功", i);

            // 模拟工作
            tokio::time::sleep(Duration::from_millis(100)).await;
        });

        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        let _ = handle.await;
    }

    // 获取所有原语的统计信息
    println!("    获取所有原语的统计信息...");
    let all_stats = manager.get_all_stats().await;
    for (name, stats) in all_stats {
        println!("      {}: 锁定次数={}, 争用次数={}, 死锁风险={:?}", 
                name, stats.lock_count, stats.contention_count, stats.deadlock_risk);
    }

    // 获取所有性能指标
    println!("    获取所有性能指标...");
    let all_metrics = manager.get_all_performance_metrics().await;
    for (name, metrics) in all_metrics {
        println!("      {}: 吞吐量={:.2}, 延迟={:?}, 争用率={:.2}%", 
                name, metrics.throughput, metrics.latency, metrics.contention_rate * 100.0);
    }

    // 检查死锁风险
    println!("    检查死锁风险...");
    let risks = manager.check_deadlock_risk().await;
    for (name, risk) in risks {
        match risk {
            DeadlockRisk::Low => println!("      {}: 死锁风险低", name),
            DeadlockRisk::Medium => println!("      {}: 死锁风险中等", name),
            DeadlockRisk::High => println!("      {}: 死锁风险高", name),
            DeadlockRisk::Critical => println!("      {}: 死锁风险严重", name),
        }
    }

    Ok(())
}

#[cfg(not(feature = "async"))]
fn main() {
    println!("❌ 异步功能未启用");
    println!("请使用 --features async 重新编译以启用异步功能");
}
