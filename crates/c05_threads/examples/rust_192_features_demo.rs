//! Rust 1.92.0 线程特性演示示例
//!
//! 本示例展示了 Rust 1.92.0 在线程和并发编程场景中的新特性应用：
//! - MaybeUninit: 线程安全的无锁数据初始化
//! - rotate_right: 线程池任务轮转
//! - NonZero::div_ceil: 线程数量计算
//!
//! 运行方式:
//! ```bash
//! cargo run --example rust_192_features_demo
//! ```

use c05_threads::rust_192_features::{
    ThreadPoolTaskQueue, ThreadPoolManager, ThreadResourceAllocator,
    ThreadTask, calculate_thread_pool_size, ThreadSchedulingConfig,
    ThreadSafeUninitBuffer, demonstrate_rust_192_thread_features,
};
use std::num::NonZeroUsize;
use std::sync::Arc;
use std::thread;
use std::time::Duration;

fn main() -> anyhow::Result<()> {
    println!("🚀 Rust 1.92.0 线程特性演示\n");
    println!("{}", "=".repeat(60));

    // 使用内置的演示函数
    demonstrate_rust_192_thread_features();

    println!("\n{}", "=".repeat(60));
    println!("\n📊 实际应用场景演示\n");

    // 场景 1: 线程池任务队列管理
    demonstrate_thread_pool_queue_management();

    // 场景 2: 线程资源池配置
    demonstrate_thread_resource_pool_configuration();

    // 场景 3: 线程池管理器
    demonstrate_thread_pool_manager();

    // 场景 4: MaybeUninit 在并发编程中的应用
    demonstrate_maybe_uninit_concurrency();

    // 场景 5: 并发场景下的线程池管理
    demonstrate_concurrent_thread_pool_management()?;

    println!("\n✅ 所有演示完成！");

    Ok(())
}

/// 演示线程池任务队列管理
fn demonstrate_thread_pool_queue_management() {
    println!("\n📋 场景 1: 线程池任务队列管理");
    println!("{}", "-".repeat(60));

    let mut queue = ThreadPoolTaskQueue::new();

    // 添加任务（使用不同的构造函数）
    println!("\n添加任务到队列:");
    queue.push(ThreadTask::high_priority(1));
    queue.push(ThreadTask::medium_priority(2));
    queue.push(ThreadTask::low_priority(3));
    queue.push(ThreadTask::new(4, 150));
    queue.push(ThreadTask::new(5, 50));
    println!("  ✓ 使用不同优先级构造函数添加了 5 个任务");

    println!("\n当前队列状态:");
    for task in queue.iter() {
        println!("  - Task {}: Priority={}", task.id, task.priority);
    }

    // 轮转队列
    println!("\n执行队列轮转 (rotate_right):");
    queue.rotate(2);
    println!("轮转后的队列顺序:");
    for task in queue.iter() {
        println!("  - Task {}: Priority={}", task.id, task.priority);
    }

    // 演示 peek 功能
    println!("\n查看队列头部任务（不移除）:");
    if let Some(task) = queue.peek() {
        println!("  队列头部任务: ID={}, Priority={}", task.id, task.priority);
    }

    // 演示批量操作
    println!("\n批量添加任务:");
    let batch_tasks = vec![
        ThreadTask { id: 6, priority: 60 },
        ThreadTask { id: 7, priority: 70 },
    ];
    queue.push_batch(batch_tasks);
    println!("  批量添加后队列长度: {}", queue.len());

    // 演示优先级排序
    println!("\n按优先级排序任务:");
    queue.sort_by_priority();
    println!("排序后的队列顺序:");
    for task in queue.iter() {
        println!("  - Task {}: Priority={}", task.id, task.priority);
    }

    // 处理任务
    println!("\n处理队列中的任务:");
    while let Some(task) = queue.pop() {
        println!("  ✓ 处理任务 ID={}, Priority={}", task.id, task.priority);
        // 模拟处理时间
        thread::sleep(Duration::from_millis(10));
    }
}

/// 演示线程资源池配置
fn demonstrate_thread_resource_pool_configuration() {
    println!("\n\n💾 场景 2: 线程资源池配置");
    println!("{}", "-".repeat(60));

    // 场景：配置线程池
    println!("\n配置线程池:");
    let total_tasks = 100;
    let tasks_per_thread = NonZeroUsize::new(10).unwrap();
    let pool_size = calculate_thread_pool_size(total_tasks, tasks_per_thread);

    println!("  总任务数: {}", total_tasks);
    println!("  每线程任务数: {}", tasks_per_thread);
    println!("  需要的线程数: {}", pool_size);

    // 场景：配置线程资源分配器
    println!("\n配置线程资源分配器:");
    let total_cpus = 16;
    let cpus_per_thread = NonZeroUsize::new(2).unwrap();
    let allocator = ThreadResourceAllocator::new(total_cpus, cpus_per_thread);

    println!("  CPU 核心数: {}", total_cpus);
    println!("  每线程 CPU: {}", cpus_per_thread);
    println!("  最大线程数: {}", allocator.max_threads());

    // 场景：计算线程调度配置
    println!("\n配置线程调度:");
    let min_threads = NonZeroUsize::new(2).unwrap();
    let max_threads = 10;
    let config = ThreadSchedulingConfig::new(min_threads, max_threads);

    println!("  最小线程数: {}", min_threads);
    println!("  最大线程数: {}", max_threads);

    for task_count in [10, 50, 100, 200] {
        let threads = config.calculate_threads_for_tasks(task_count);
        println!("  {} 个任务需要线程数: {}", task_count, threads);
    }
}

/// 演示线程池管理器
fn demonstrate_thread_pool_manager() {
    println!("\n\n⚙️ 场景 3: 线程池管理器");
    println!("{}", "-".repeat(60));

    let manager = ThreadPoolManager::new();

    // 添加多个任务
    println!("\n添加任务到管理器:");
    for i in 1..=5 {
        let task = ThreadTask {
            id: i,
            priority: (i * 10) as u8,
        };
        manager.add_task(task);
        println!("  ✓ 添加任务 ID={}, Priority={}", i, i * 10);
    }

    // 演示任务计数
    println!("\n当前队列中的任务数: {}", manager.task_count());

    // 演示批量添加
    println!("\n批量添加任务:");
    let batch_tasks = vec![
        ThreadTask { id: 6, priority: 60 },
        ThreadTask { id: 7, priority: 70 },
    ];
    manager.add_tasks_batch(batch_tasks);
    println!("  批量添加后任务数: {}", manager.task_count());

    // 演示优先级排序
    println!("\n按优先级排序任务:");
    manager.sort_by_priority();
    println!("  ✓ 排序完成");

    // 执行轮转
    println!("\n执行任务轮转:");
    manager.rotate();
    println!("  ✓ 轮转完成（队列已轮转）");

    // 处理任务
    println!("\n处理轮转后的任务:");
    let mut processed_count = 0;
    while let Some(task) = manager.next_task() {
        processed_count += 1;
        println!("  ✓ [{}] 处理任务 ID={}, Priority={}",
                 processed_count, task.id, task.priority);
        // 模拟处理时间
        thread::sleep(Duration::from_millis(50));
    }

    println!("\n总共处理了 {} 个任务", processed_count);

    // 演示清空队列
    println!("\n清空队列:");
    manager.clear();
    println!("  队列是否为空: {}", manager.is_empty());
    println!("  队列中的任务数: {}", manager.task_count());

    // 演示统计信息
    println!("\n演示统计信息:");
    manager.add_task(ThreadTask::high_priority(1));
    manager.add_task(ThreadTask::high_priority(2));
    manager.add_task(ThreadTask::medium_priority(3));
    manager.add_task(ThreadTask::low_priority(4));

    let stats = manager.get_stats();
    println!("  总任务数: {}", stats.total_tasks);
    println!("  高优先级任务: {}", stats.high_priority_tasks);
    println!("  中优先级任务: {}", stats.medium_priority_tasks);
    println!("  低优先级任务: {}", stats.low_priority_tasks);
    println!("  平均优先级: {:.2}", stats.average_priority);

    // 演示移除任务
    println!("\n演示移除任务:");
    println!("  移除前任务数: {}", manager.task_count());
    let removed = manager.remove_task(2);
    println!("  移除任务 ID=2: {}", if removed { "成功" } else { "失败" });
    println!("  移除后任务数: {}", manager.task_count());

    // 演示获取所有任务
    println!("\n获取所有任务:");
    let all_tasks = manager.get_all_tasks();
    for task in &all_tasks {
        println!("  - Task ID={}, Priority={}", task.id, task.priority);
    }
}

/// 演示 MaybeUninit 在并发编程中的应用
fn demonstrate_maybe_uninit_concurrency() {
    println!("\n\n🔍 场景 4: MaybeUninit 在并发编程中的应用");
    println!("{}", "-".repeat(60));

    // 创建未初始化缓冲区
    println!("\n创建未初始化缓冲区:");
    let buffer_size = 10;
    let mut buffer = ThreadSafeUninitBuffer::<i32>::new(buffer_size);
    println!("  缓冲区大小: {}", buffer_size);

    // 初始化数据
    println!("\n初始化缓冲区数据:");
    unsafe {
        for i in 0..buffer_size {
            let value = (i * 10) as i32;
            buffer.init_at(i, value);
            println!("  位置 {}: 值 = {}", i, value);
        }
    }

    // 读取数据
    println!("\n读取缓冲区数据:");
    unsafe {
        for i in 0..buffer_size {
            let value = *buffer.get(i);
            println!("  位置 {}: 值 = {}", i, value);
        }
    }

    // 修改数据
    println!("\n修改缓冲区数据:");
    unsafe {
        *buffer.get_mut(0) = 999;
        println!("  位置 0 修改为: {}", *buffer.get(0));
    }
}

/// 演示并发场景下的线程池管理
fn demonstrate_concurrent_thread_pool_management() -> anyhow::Result<()> {
    println!("\n\n🔄 场景 5: 并发场景下的线程池管理");
    println!("{}", "-".repeat(60));

    let manager = Arc::new(ThreadPoolManager::new());
    let mut handles = vec![];

    // 并发添加任务
    println!("\n并发添加任务:");
    for i in 1..=10 {
        let manager_clone = manager.clone();
        let handle = thread::spawn(move || {
            manager_clone.add_task(ThreadTask {
                id: i,
                priority: (i * 10) as u8,
            });
            println!("  [线程] 添加任务 ID={}", i);
        });
        handles.push(handle);
    }

    // 等待所有任务添加完成
    for handle in handles {
        handle.join().unwrap();
    }

    println!("\n所有任务添加完成");

    // 执行轮转
    println!("\n执行任务轮转:");
    manager.rotate();
    println!("  ✓ 轮转完成");

    // 并发处理任务
    println!("\n并发处理任务:");
    let manager_clone = manager.clone();
    let process_handle = thread::spawn(move || {
        let mut count = 0;
        while let Some(task) = manager_clone.next_task() {
            count += 1;
            println!("  [处理线程] 处理任务 ID={}, Priority={}", task.id, task.priority);
            thread::sleep(Duration::from_millis(10));
        }
        count
    });

    let processed = process_handle.join().unwrap();
    println!("\n总共处理了 {} 个任务", processed);

    Ok(())
}
