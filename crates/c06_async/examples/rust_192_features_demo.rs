//! Rust 1.92.0 异步编程特性演示示例
//!
//! 本示例展示了 Rust 1.92.0 在异步编程场景中的新特性应用：
//! - rotate_right: 异步任务队列轮转
//! - NonZero::div_ceil: 异步池大小计算
//! - 迭代器方法特化: 异步任务列表比较
//!
//! 运行方式:
//! ```bash
//! cargo run --example rust_192_features_demo
//! ```

use c06_async::rust_192_features::{
    AsyncTaskQueue, AsyncTaskScheduler, AsyncResourceAllocator,
    TaskItem, calculate_async_pool_size, compare_async_task_lists,
    check_async_task_states, demonstrate_rust_192_async_features,
};
use std::num::NonZeroUsize;
use std::time::Duration;
use tokio::time::sleep;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    println!("🚀 Rust 1.92.0 异步编程特性演示\n");
    println!("{}", "=".repeat(60));

    // 使用内置的演示函数
    demonstrate_rust_192_async_features().await;

    println!("\n{}", "=".repeat(60));
    println!("\n📊 实际应用场景演示\n");

    // 场景 1: 异步任务队列管理
    demonstrate_async_task_queue_management().await;

    // 场景 2: 异步资源池配置
    demonstrate_async_resource_pool_configuration().await;

    // 场景 3: 异步任务调度
    demonstrate_async_task_scheduling().await;

    // 场景 4: 异步任务列表比较和验证
    demonstrate_async_task_list_comparison().await;

    println!("\n✅ 所有演示完成！");

    Ok(())
}

/// 演示异步任务队列管理
async fn demonstrate_async_task_queue_management() {
    println!("\n📋 场景 1: 异步任务队列管理");
    println!("{}", "-".repeat(60));

    let mut queue: AsyncTaskQueue<String> = AsyncTaskQueue::new();

    // 添加任务
    println!("\n添加任务到队列:");
    for i in 1..=5 {
        let task = TaskItem {
            id: i,
            priority: (i * 10) as u8,
            data: format!("处理数据批次 {}", i),
        };
        queue.push(task);
        println!("  ✓ 添加任务 ID={}, Priority={}", i, i * 10);
    }

    println!("\n当前队列状态:");
    for task in queue.iter() {
        println!("  - Task {}: Priority={}, Data={}", task.id, task.priority, task.data);
    }

    // 轮转队列
    println!("\n执行队列轮转 (rotate_right):");
    queue.rotate(2);
    println!("轮转后的队列顺序:");
    for task in queue.iter() {
        println!("  - Task {}: Priority={}", task.id, task.priority);
    }

    // 处理任务
    println!("\n处理队列中的任务:");
    while let Some(task) = queue.pop() {
        println!("  ✓ 处理任务 ID={}, Data={}", task.id, task.data);
        // 模拟异步处理
        sleep(Duration::from_millis(10)).await;
    }
}

/// 演示异步资源池配置
async fn demonstrate_async_resource_pool_configuration() {
    println!("\n\n💾 场景 2: 异步资源池配置");
    println!("{}", "-".repeat(60));

    // 场景：配置数据库连接池
    println!("\n配置数据库连接池:");
    let total_connections = 100;
    let connections_per_pool = NonZeroUsize::new(10).unwrap();
    let pool_count = calculate_async_pool_size(total_connections, connections_per_pool);

    println!("  总连接数: {}", total_connections);
    println!("  每池连接数: {}", connections_per_pool);
    println!("  需要的连接池数: {}", pool_count);

    // 场景：配置异步任务资源分配器
    println!("\n配置异步任务资源分配器:");
    let total_memory_mb = 4096;
    let memory_per_task_mb = NonZeroUsize::new(256).unwrap();
    let allocator = AsyncResourceAllocator::new(total_memory_mb, memory_per_task_mb);

    println!("  总内存: {} MB", total_memory_mb);
    println!("  每任务内存: {} MB", memory_per_task_mb);
    println!("  最大并发任务数: {}", allocator.max_concurrent_tasks());

    // 场景：计算批处理配置
    println!("\n配置批处理任务:");
    let total_items = 127;
    let batch_size = NonZeroUsize::new(20).unwrap();
    let batch_count = calculate_async_pool_size(total_items, batch_size);

    println!("  总项目数: {}", total_items);
    println!("  每批大小: {}", batch_size);
    println!("  需要的批次数: {}", batch_count);
}

/// 演示异步任务调度
async fn demonstrate_async_task_scheduling() {
    println!("\n\n⚙️ 场景 3: 异步任务调度");
    println!("{}", "-".repeat(60));

    let scheduler = AsyncTaskScheduler::new(1);

    // 添加多个任务
    println!("\n添加任务到调度器:");
    for i in 1..=5 {
        let task = TaskItem {
            id: i,
            priority: (i * 10) as u8,
            data: format!("异步任务 {}", i),
        };
        scheduler.add_task(task).await;
        println!("  ✓ 添加任务 ID={}, Priority={}", i, i * 10);
    }

    // 执行调度
    println!("\n执行任务调度:");
    scheduler.schedule().await;
    println!("  ✓ 调度完成（队列已轮转）");

    // 处理任务
    println!("\n处理调度后的任务:");
    let mut processed_count = 0;
    while let Some(task) = scheduler.next_task().await {
        processed_count += 1;
        println!("  ✓ [{}] 处理任务 ID={}, Priority={}, Data={}",
                 processed_count, task.id, task.priority, task.data);
        // 模拟异步处理
        sleep(Duration::from_millis(50)).await;
    }

    println!("\n总共处理了 {} 个任务", processed_count);
}

/// 演示异步任务列表比较和验证
async fn demonstrate_async_task_list_comparison() {
    println!("\n\n🔍 场景 4: 异步任务列表比较和验证");
    println!("{}", "-".repeat(60));

    // 创建两个任务列表
    let list1 = vec![
        TaskItem {
            id: 1,
            priority: 10,
            data: "任务1".to_string(),
        },
        TaskItem {
            id: 2,
            priority: 20,
            data: "任务2".to_string(),
        },
        TaskItem {
            id: 3,
            priority: 30,
            data: "任务3".to_string(),
        },
    ];

    let list2 = list1.clone();
    let list3 = vec![
        TaskItem {
            id: 1,
            priority: 10,
            data: "任务1".to_string(),
        },
        TaskItem {
            id: 2,
            priority: 20,
            data: "任务2".to_string(),
        },
        TaskItem {
            id: 4, // 不同的 ID
            priority: 30,
            data: "任务4".to_string(),
        },
    ];

    println!("\n比较任务列表:");
    println!("  List1 和 List2 相等: {}", compare_async_task_lists(&list1, &list2));
    println!("  List1 和 List3 相等: {}", compare_async_task_lists(&list1, &list3));

    // 验证任务状态
    println!("\n验证任务状态:");
    let expected_ids = vec![1, 2, 3];
    println!("  List1 的 ID 列表匹配 [1, 2, 3]: {}",
             check_async_task_states(&list1, &expected_ids));

    let wrong_ids = vec![1, 2, 4];
    println!("  List1 的 ID 列表匹配 [1, 2, 4]: {}",
             check_async_task_states(&list1, &wrong_ids));
}
