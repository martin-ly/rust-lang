//! Rust 1.92.0 异步编程综合测试套件
//!
//! 本测试套件验证 Rust 1.92.0 版本中的所有异步编程新特性，确保：
//! - rotate_right 在异步任务队列中正常工作
//! - NonZero::div_ceil 在异步池计算中正确应用
//! - 迭代器方法特化性能优化有效
//! - 异步任务调度器功能完整
//! - 异步资源分配器工作正常

use c06_async::rust_192_features::{
    AsyncTaskQueue, AsyncTaskScheduler, AsyncResourceAllocator,
    TaskItem, calculate_async_pool_size, compare_async_task_lists,
    check_async_task_states,
};
use anyhow::Result;
use std::num::NonZeroUsize;
use std::time::Duration;
use tokio::time::timeout;

/// 测试 rotate_right 在异步任务队列中的应用
#[tokio::test]
async fn test_async_task_queue_rotate() -> Result<()> {
    let mut queue = AsyncTaskQueue::new();

    // 添加多个任务
    for i in 1..=5 {
        queue.push(TaskItem {
            id: i,
            priority: (i * 10) as u8,
            data: format!("task{}", i),
        });
    }

    // 验证初始顺序
    let initial_ids: Vec<u64> = queue.iter().map(|t| t.id).collect();
    assert_eq!(initial_ids, vec![1, 2, 3, 4, 5]);

    // 轮转 2 个位置
    queue.rotate(2);
    let rotated_ids: Vec<u64> = queue.iter().map(|t| t.id).collect();
    assert_eq!(rotated_ids, vec![4, 5, 1, 2, 3]);

    // 再次轮转 1 个位置
    queue.rotate(1);
    let final_ids: Vec<u64> = queue.iter().map(|t| t.id).collect();
    assert_eq!(final_ids, vec![3, 4, 5, 1, 2]);

    Ok(())
}

/// 测试空队列的轮转
#[tokio::test]
async fn test_async_task_queue_rotate_empty() {
    let mut queue: AsyncTaskQueue<&str> = AsyncTaskQueue::new();
    // 空队列轮转不应该 panic
    queue.rotate(5);
    assert_eq!(queue.len(), 0);
}

/// 测试 NonZero::div_ceil 在异步池计算中的应用
#[test]
fn test_async_pool_size_calculation() {
    let tasks_per_worker = NonZeroUsize::new(5).unwrap();

    // 测试各种情况
    assert_eq!(calculate_async_pool_size(23, tasks_per_worker), 5);
    assert_eq!(calculate_async_pool_size(25, tasks_per_worker), 5);
    assert_eq!(calculate_async_pool_size(26, tasks_per_worker), 6);
    assert_eq!(calculate_async_pool_size(1, tasks_per_worker), 1);
    assert_eq!(calculate_async_pool_size(5, tasks_per_worker), 1);
    assert_eq!(calculate_async_pool_size(10, tasks_per_worker), 2);
}

/// 测试异步资源分配器
#[test]
fn test_async_resource_allocator() {
    // 测试基本分配
    let allocator = AsyncResourceAllocator::new(1024, NonZeroUsize::new(64).unwrap());
    assert_eq!(allocator.max_concurrent_tasks(), 16);

    // 测试边界情况
    let allocator2 = AsyncResourceAllocator::new(100, NonZeroUsize::new(50).unwrap());
    assert_eq!(allocator2.max_concurrent_tasks(), 2);

    // 测试最小资源
    let allocator3 = AsyncResourceAllocator::new(10, NonZeroUsize::new(1).unwrap());
    assert_eq!(allocator3.max_concurrent_tasks(), 10);
}

/// 测试异步任务调度器
#[tokio::test]
async fn test_async_task_scheduler() -> Result<()> {
    let scheduler = AsyncTaskScheduler::new(1);

    // 添加多个任务
    for i in 1..=3 {
        scheduler.add_task(TaskItem {
            id: i,
            priority: (i * 10) as u8,
            data: format!("task{}", i),
        }).await;
    }

    // 执行调度（轮转队列）
    scheduler.schedule().await;

    // 获取任务（轮转后，最后一个任务会移到前面）
    let task1 = scheduler.next_task().await;
    assert!(task1.is_some());
    // 轮转后，最后一个任务（id=3）会移到前面
    assert_eq!(task1.unwrap().id, 3);

    let task2 = scheduler.next_task().await;
    assert!(task2.is_some());
    assert_eq!(task2.unwrap().id, 1);

    Ok(())
}

/// 测试异步任务调度器的并发安全性
#[tokio::test]
async fn test_async_task_scheduler_concurrent() -> Result<()> {
    let scheduler = AsyncTaskScheduler::new(1);

    // 并发添加任务（使用 Arc 共享调度器）
    use std::sync::Arc;
    let scheduler_arc = Arc::new(scheduler);
    let mut handles = vec![];
    for i in 1..=10 {
        let scheduler_clone = scheduler_arc.clone();
        let handle = tokio::spawn(async move {
            scheduler_clone.add_task(TaskItem {
                id: i,
                priority: (i * 10) as u8,
                data: format!("task{}", i),
            }).await;
        });
        handles.push(handle);
    }

    // 等待所有任务添加完成
    for handle in handles {
        handle.await?;
    }

    // 执行调度
    scheduler_arc.schedule().await;

    // 验证所有任务都被调度
    let mut count = 0;
    while scheduler_arc.next_task().await.is_some() {
        count += 1;
    }
    assert_eq!(count, 10);

    Ok(())
}

/// 测试迭代器方法特化在异步任务列表比较中的应用
#[test]
fn test_compare_async_task_lists() {
    let list1 = vec![
        TaskItem {
            id: 1,
            priority: 10,
            data: "task1",
        },
        TaskItem {
            id: 2,
            priority: 20,
            data: "task2",
        },
    ];

    // 测试相等列表
    let list2 = list1.clone();
    assert!(compare_async_task_lists(&list1, &list2));

    // 测试不相等列表
    let list3 = vec![
        TaskItem {
            id: 1,
            priority: 10,
            data: "task1",
        },
        TaskItem {
            id: 3, // 不同的 ID
            priority: 20,
            data: "task2",
        },
    ];
    assert!(!compare_async_task_lists(&list1, &list3));

    // 测试不同长度的列表
    let list4 = vec![
        TaskItem {
            id: 1,
            priority: 10,
            data: "task1",
        },
    ];
    assert!(!compare_async_task_lists(&list1, &list4));
}

/// 测试异步任务状态检查
#[test]
fn test_check_async_task_states() {
    let tasks = vec![
        TaskItem {
            id: 1,
            priority: 10,
            data: "task1",
        },
        TaskItem {
            id: 2,
            priority: 20,
            data: "task2",
        },
        TaskItem {
            id: 3,
            priority: 30,
            data: "task3",
        },
    ];

    // 测试匹配的 ID 列表
    let expected_ids = vec![1, 2, 3];
    assert!(check_async_task_states(&tasks, &expected_ids));

    // 测试不匹配的 ID 列表
    let wrong_ids = vec![1, 2, 4];
    assert!(!check_async_task_states(&tasks, &wrong_ids));

    // 测试不同顺序
    let reversed_ids = vec![3, 2, 1];
    assert!(!check_async_task_states(&tasks, &reversed_ids));
}

/// 测试异步任务队列的基本操作
#[tokio::test]
async fn test_async_task_queue_operations() {
    let mut queue = AsyncTaskQueue::new();

    // 测试空队列
    assert_eq!(queue.len(), 0);
    assert!(queue.pop().is_none());

    // 添加任务
    queue.push(TaskItem {
        id: 1,
        priority: 10,
        data: "task1",
    });
    assert_eq!(queue.len(), 1);

    // 弹出任务
    let task = queue.pop().unwrap();
    assert_eq!(task.id, 1);
    assert_eq!(queue.len(), 0);
}

/// 测试异步任务调度器的超时处理
#[tokio::test]
async fn test_async_task_scheduler_timeout() -> Result<()> {
    let scheduler = AsyncTaskScheduler::new(1);

    // 添加任务
    scheduler.add_task(TaskItem {
        id: 1,
        priority: 10,
        data: "task1",
    }).await;

    // 执行调度（应该很快完成）
    let result = timeout(Duration::from_secs(1), scheduler.schedule()).await;
    assert!(result.is_ok());

    Ok(())
}

/// 综合测试：完整的异步任务处理流程
#[tokio::test]
async fn test_complete_async_task_workflow() -> Result<()> {
    // 1. 创建资源分配器
    let allocator = AsyncResourceAllocator::new(1000, NonZeroUsize::new(100).unwrap());
    assert_eq!(allocator.max_concurrent_tasks(), 10);

    // 2. 创建任务队列
    let mut queue: AsyncTaskQueue<String> = AsyncTaskQueue::new();
    for i in 1..=5 {
        queue.push(TaskItem {
            id: i,
            priority: (i * 10) as u8,
            data: format!("task{}", i),
        });
    }

    // 3. 轮转队列
    queue.rotate(2);
    let rotated_ids: Vec<u64> = queue.iter().map(|t| t.id).collect();
    assert_eq!(rotated_ids, vec![4, 5, 1, 2, 3]);

    // 4. 创建调度器并添加任务
    let scheduler = AsyncTaskScheduler::new(1);
    while let Some(task) = queue.pop() {
        scheduler.add_task(task).await;
    }

    // 5. 执行调度（轮转）
    scheduler.schedule().await;

    // 6. 验证任务被处理（轮转后顺序会改变）
    let mut ids = vec![];
    while let Some(task) = scheduler.next_task().await {
        ids.push(task.id);
    }
    // 验证所有任务都被处理
    assert_eq!(ids.len(), 5);
    // 验证任务 ID 都在范围内
    for id in &ids {
        assert!(*id >= 1 && *id <= 5);
    }

    Ok(())
}

/// 测试新增的队列操作方法
#[tokio::test]
async fn test_queue_utility_methods() {
    let mut queue: AsyncTaskQueue<String> = AsyncTaskQueue::new();

    // 测试 is_empty
    assert!(queue.is_empty());

    // 测试 push 和 len
    queue.push(TaskItem {
        id: 1,
        priority: 10,
        data: "task1".to_string(),
    });
    assert_eq!(queue.len(), 1);
    assert!(!queue.is_empty());

    // 测试 peek
    let peeked = queue.peek();
    assert!(peeked.is_some());
    assert_eq!(peeked.unwrap().id, 1);

    // 测试 peek_mut
    if let Some(task) = queue.peek_mut() {
        task.priority = 20;
    }
    assert_eq!(queue.peek().unwrap().priority, 20);

    // 测试 capacity
    let _capacity = queue.capacity();

    // 测试 clear
    queue.clear();
    assert!(queue.is_empty());
    assert_eq!(queue.len(), 0);
}

/// 测试批量添加任务
#[tokio::test]
async fn test_batch_operations() {
    let mut queue: AsyncTaskQueue<u64> = AsyncTaskQueue::new();

    // 批量添加任务
    let tasks = vec![
        TaskItem { id: 1, priority: 10, data: 1 },
        TaskItem { id: 2, priority: 20, data: 2 },
        TaskItem { id: 3, priority: 30, data: 3 },
    ];

    queue.push_batch(tasks);
    assert_eq!(queue.len(), 3);

    // 测试按优先级排序
    queue.sort_by_priority();
    let priorities: Vec<u8> = queue.iter().map(|t| t.priority).collect();
    assert_eq!(priorities, vec![30, 20, 10]);
}

/// 测试调度器的新方法
#[tokio::test]
async fn test_scheduler_utility_methods() -> Result<()> {
    let scheduler = AsyncTaskScheduler::new(1);

    // 测试 is_empty
    assert!(scheduler.is_empty().await);

    // 添加任务
    scheduler.add_task(TaskItem {
        id: 1,
        priority: 10,
        data: "task1",
    }).await;

    // 测试 task_count
    assert_eq!(scheduler.task_count().await, 1);
    assert!(!scheduler.is_empty().await);

    // 测试批量添加
    let tasks = vec![
        TaskItem { id: 2, priority: 20, data: "task2" },
        TaskItem { id: 3, priority: 30, data: "task3" },
    ];
    scheduler.add_tasks_batch(tasks).await;
    assert_eq!(scheduler.task_count().await, 3);

    // 测试按优先级排序
    scheduler.sort_by_priority().await;
    let first_task = scheduler.next_task().await;
    assert!(first_task.is_some());
    assert_eq!(first_task.unwrap().priority, 30); // 最高优先级

    // 测试 clear
    scheduler.clear().await;
    assert!(scheduler.is_empty().await);
    assert_eq!(scheduler.task_count().await, 0);

    Ok(())
}
