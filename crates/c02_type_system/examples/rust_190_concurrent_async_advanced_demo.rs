//! Rust 1.90 并发和异步高级特性演示示例
//! 
//! 本示例展示了如何使用 c02_type_system 库中的并发和异步高级特性模块。

use c02_type_system::concurrent_async_advanced::*;
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 Rust 1.90 并发和异步高级特性演示");
    println!("=====================================");
    
    // 运行主演示函数
    demonstrate_concurrent_async_advanced().await;
    
    // 额外的详细演示
    demonstrate_advanced_async_patterns().await;
    demonstrate_concurrent_data_structures().await;
    demonstrate_async_streams().await;
    demonstrate_performance_monitoring().await;
    
    Ok(())
}

/// 演示高级异步模式
async fn demonstrate_advanced_async_patterns() {
    println!("\n🔧 高级异步模式详细演示");
    println!("=========================");
    
    // 1. 异步状态机详细演示
    println!("\n--- 异步状态机详细演示 ---");
    let state_machine = async_patterns::AsyncStateMachine::new();
    
    // 创建状态监听器
    let mut state_receiver = state_machine.subscribe_to_changes();
    let state_listener = tokio::spawn(async move {
        while let Ok(state) = state_receiver.recv().await {
            match state {
                async_patterns::AsyncState::Idle => println!("  📍 状态: 空闲"),
                async_patterns::AsyncState::Processing => println!("  ⚙️  状态: 处理中"),
                async_patterns::AsyncState::Completed => println!("  ✅ 状态: 完成"),
                async_patterns::AsyncState::Error(msg) => println!("  ❌ 状态: 错误 - {}", msg),
            }
        }
    });
    
    // 模拟一个完整的处理流程
    println!("开始处理流程...");
    state_machine.transition_to(async_patterns::AsyncState::Processing).await.unwrap();
    sleep(Duration::from_millis(200)).await;
    
    // 模拟处理成功
    state_machine.transition_to(async_patterns::AsyncState::Completed).await.unwrap();
    sleep(Duration::from_millis(100)).await;
    
    // 重置为空闲状态
    state_machine.transition_to(async_patterns::AsyncState::Idle).await.unwrap();
    
    // 等待状态监听器完成
    state_listener.abort();
    
    // 2. 异步超时包装器演示
    println!("\n--- 异步超时包装器演示 ---");
    let fast_task = Box::pin(async {
        sleep(Duration::from_millis(50)).await;
        "快速任务完成"
    });
    
    let slow_task = Box::pin(async {
        sleep(Duration::from_millis(200)).await;
        "慢速任务完成"
    });
    
    let timeout_wrapper_fast = async_patterns::AsyncTimeout::new(fast_task, Duration::from_millis(100));
    let timeout_wrapper_slow = async_patterns::AsyncTimeout::new(slow_task, Duration::from_millis(100));
    
    match timeout_wrapper_fast.await {
        Ok(result) => println!("  ✅ 快速任务: {}", result),
        Err(_) => println!("  ❌ 快速任务超时"),
    }
    
    match timeout_wrapper_slow.await {
        Ok(result) => println!("  ✅ 慢速任务: {}", result),
        Err(_) => println!("  ❌ 慢速任务超时"),
    }
    
    // 3. 异步批处理演示
    println!("\n--- 异步批处理演示 ---");
    let batch_processor = async_patterns::AsyncBatchProcessor::new(
        3, // 批处理大小
        Duration::from_millis(500), // 刷新间隔
        |batch: Vec<i32>| {
            Box::pin(async move {
                println!("  📦 处理批次: {:?}", batch);
                sleep(Duration::from_millis(100)).await;
                Ok(())
            })
        }
    );
    
    // 启动自动刷新
    let _flush_handle = batch_processor.start_auto_flush();
    
    // 添加项目
    for i in 1..=7 {
        batch_processor.add_item(i).await.unwrap();
        println!("  ➕ 添加项目: {}", i);
        sleep(Duration::from_millis(100)).await;
    }
    
    // 手动刷新剩余项目
    batch_processor.flush().await.unwrap();
    println!("  🔄 手动刷新完成");
}

/// 演示并发数据结构
async fn demonstrate_concurrent_data_structures() {
    println!("\n🏗️  并发数据结构详细演示");
    println!("=========================");
    
    // 1. 无锁环形缓冲区演示
    println!("\n--- 无锁环形缓冲区演示 ---");
    let ring_buffer = concurrent_data_structures::LockFreeRingBuffer::new(5);
    
    // 并发写入
    let write_handles: Vec<_> = (0..3).map(|i| {
        let buffer = ring_buffer.clone();
        tokio::spawn(async move {
            for j in 0..3 {
                let item = format!("生产者{}_项目{}", i, j);
                match buffer.push(item) {
                    Ok(_) => println!("  ✅ 写入: 生产者{}_项目{}", i, j),
                    Err(e) => println!("  ❌ 写入失败: {}", e),
                }
                sleep(Duration::from_millis(10)).await;
            }
        })
    }).collect();
    
    // 并发读取
    let read_handles: Vec<_> = (0..2).map(|i| {
        let buffer = ring_buffer.clone();
        tokio::spawn(async move {
            for _ in 0..5 {
                if let Some(item) = buffer.pop() {
                    println!("  📖 消费者{} 读取: {}", i, item);
                } else {
                    println!("  📭 消费者{} 缓冲区为空", i);
                }
                sleep(Duration::from_millis(20)).await;
            }
        })
    }).collect();
    
    // 等待所有任务完成
    futures::future::join_all(write_handles).await;
    futures::future::join_all(read_handles).await;
    
    println!("  📊 最终缓冲区大小: {}", ring_buffer.len());
    
    // 2. 并发哈希表演示
    println!("\n--- 并发哈希表演示 ---");
    let concurrent_map = concurrent_data_structures::ConcurrentHashMap::new(4);
    
    // 并发插入操作
    let insert_handles: Vec<_> = (0..10).map(|i| {
        let map = concurrent_map.clone();
        tokio::spawn(async move {
            let key = format!("key_{}", i);
            let value = format!("value_{}", i);
            map.insert(key, value);
            println!("  ➕ 插入: key_{} -> value_{}", i, i);
        })
    }).collect();
    
    futures::future::join_all(insert_handles).await;
    println!("  📊 并发哈希表大小: {}", concurrent_map.len());
    
    // 并发读取操作
    let read_handles: Vec<_> = (0..5).map(|i| {
        let map = concurrent_map.clone();
        tokio::spawn(async move {
            let key = format!("key_{}", i * 2);
            if let Some(value) = map.get(&key) {
                println!("  📖 读取: {} -> {}", key, value);
            } else {
                println!("  ❌ 未找到: {}", key);
            }
        })
    }).collect();
    
    futures::future::join_all(read_handles).await;
    
    // 3. 工作窃取队列演示
    println!("\n--- 工作窃取队列演示 ---");
    let work_queue = concurrent_data_structures::WorkStealingQueue::new();
    
    // 添加任务
    for i in 0..10 {
        work_queue.push(format!("任务_{}", i));
        println!("  ➕ 添加任务: 任务_{}", i);
    }
    
    // 创建窃取者
    let _stealer = work_queue.create_stealer();
    
    // 模拟工作窃取
    for _i in 0..5 {
        if let Some(task) = work_queue.pop() {
            println!("  🔄 主队列执行: {}", task);
        }
        
        if let Some(task) = work_queue.steal() {
            println!("  🥷 窃取执行: {}", task);
        }
        
        sleep(Duration::from_millis(10)).await;
    }
}

/// 演示异步流处理
async fn demonstrate_async_streams() {
    println!("\n🌊 异步流处理详细演示");
    println!("=====================");
    
    // 1. 异步流处理器演示
    println!("\n--- 异步流处理器演示 ---");
    let stream_processor = async_streams::AsyncStreamProcessor::new(
        5, // 缓冲区大小
        3, // 并发数
        |item: i32| {
            Box::pin(async move {
                println!("  ⚙️  处理项目: {}", item);
                sleep(Duration::from_millis(100)).await;
                Ok(item * item) // 计算平方
            })
        }
    );
    
    // 创建数据流
    let data_stream = futures::stream::iter(1..=10);
    let results = stream_processor.process_stream(data_stream).await.unwrap();
    println!("  📊 处理结果: {:?}", results);
    
    // 2. 异步管道演示
    println!("\n--- 异步管道演示 ---");
    let mut pipeline = async_streams::AsyncPipeline::new();
    
    // 添加处理阶段
    pipeline.add_stage(|input: i32| {
        Box::pin(async move {
            println!("  🔢 阶段1 - 输入: {}", input);
            sleep(Duration::from_millis(50)).await;
            Ok(input * 2)
        })
    });
    
    pipeline.add_stage(|input: i32| {
        Box::pin(async move {
            println!("  🔢 阶段2 - 输入: {}", input);
            sleep(Duration::from_millis(50)).await;
            Ok(input + 10)
        })
    });
    
    pipeline.add_stage(|input: i32| {
        Box::pin(async move {
            println!("  🔢 阶段3 - 输入: {}", input);
            sleep(Duration::from_millis(50)).await;
            Ok(input * input)
        })
    });
    
    // 处理数据
    let result = pipeline.process(5).await.unwrap();
    println!("  📊 管道处理结果: {}", result);
    
    // 3. 异步窗口聚合器演示
    println!("\n--- 异步窗口聚合器演示 ---");
    let window_aggregator = async_streams::AsyncWindowAggregator::new(
        Duration::from_millis(1000), // 窗口大小
        |items: Vec<i32>| {
            Box::pin(async move {
                let sum: i32 = items.iter().sum();
                let count = items.len();
                let avg = if count > 0 { sum as f64 / count as f64 } else { 0.0 };
                println!("  📊 窗口聚合: 项目数={}, 总和={}, 平均值={:.2}", count, sum, avg);
                Ok((sum, count, avg))
            })
        }
    );
    
    // 启动窗口处理器
    let _window_handle = window_aggregator.start_window_processor();
    
    // 添加数据到窗口
    for i in 1..=15 {
        window_aggregator.add_item(i).await.unwrap();
        println!("  ➕ 添加数据: {}", i);
        sleep(Duration::from_millis(200)).await;
    }
    
    // 等待窗口处理
    sleep(Duration::from_millis(2000)).await;
}

/// 演示性能监控
async fn demonstrate_performance_monitoring() {
    println!("\n📊 性能监控详细演示");
    println!("===================");
    
    // 1. 异步性能监控器演示
    println!("\n--- 异步性能监控器演示 ---");
    let monitor = performance_monitoring::AsyncPerformanceMonitor::new();
    
    // 记录各种指标
    monitor.record_metric("cpu_usage".to_string(), 75.5).await;
    monitor.record_metric("memory_usage".to_string(), 1024.0).await;
    monitor.record_metric("response_time".to_string(), 150.0).await;
    
    // 增加计数器
    for _ in 0..5 {
        monitor.increment_counter("requests".to_string()).await;
    }
    
    for _ in 0..3 {
        monitor.increment_counter("errors".to_string()).await;
    }
    
    // 获取指标
    let metrics = monitor.get_all_metrics().await;
    println!("  📊 性能指标:");
    for (name, value) in metrics {
        println!("    {}: {}", name, value);
    }
    
    println!("  ⏱️  运行时间: {:?}", monitor.uptime());
    
    // 2. 异步任务性能分析器演示
    println!("\n--- 异步任务性能分析器演示 ---");
    let profiler = performance_monitoring::AsyncTaskProfiler::new();
    
    // 执行不同类型的任务
    let task_handles: Vec<_> = (0..3).map(|i| {
        let profiler = profiler.clone();
        tokio::spawn(async move {
            for j in 0..3 {
                let task_name = format!("task_type_{}", i);
                let result = profiler.profile_task(task_name.clone(), async {
                    sleep(Duration::from_millis(100 + i * 50 + j * 10)).await;
                    format!("任务类型{}_执行{}", i, j)
                }).await;
                println!("  ✅ {}: {}", task_name, result);
            }
        })
    }).collect();
    
    // 等待所有任务完成
    futures::future::join_all(task_handles).await;
    
    // 获取任务统计
    let stats = profiler.get_all_task_stats().await;
    println!("  📊 任务性能统计:");
    for stat in stats {
        println!("    {}: 执行次数={}, 总时间={:?}, 平均时间={:?}, 最小时间={:?}, 最大时间={:?}",
            stat.task_name,
            stat.execution_count,
            stat.total_time,
            stat.average_time,
            stat.min_time,
            stat.max_time
        );
    }
    
    // 3. 异步错误处理演示
    println!("\n--- 异步错误处理演示 ---");
    let error_aggregator = async_error_handling::AsyncErrorAggregator::new(10);
    
    // 模拟一些错误
    let error_types = vec!["网络错误", "数据库错误", "验证错误", "超时错误"];
    for (_i, error_type) in error_types.iter().enumerate() {
        for j in 0..3 {
            let error_msg = format!("{} - 实例{}", error_type, j);
            error_aggregator.add_error(error_msg).await;
        }
        sleep(Duration::from_millis(50)).await;
    }
    
    let errors = error_aggregator.get_errors().await;
    println!("  📊 错误统计 (总数: {}):", error_aggregator.error_count().await);
    for error in errors {
        println!("    ❌ {}", error);
    }
    
    println!("\n✅ 所有演示完成！");
}
