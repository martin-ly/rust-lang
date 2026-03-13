//! Rust 1.92.0 线程特性综合测试套件
//!
//! 本测试套件验证 Rust 1.92.0 版本中的所有线程和并发编程新特性，确保：
//! - MaybeUninit 在并发编程中正常工作
//! - rotate_right 在线程池管理中正确应用
//! - NonZero::div_ceil 在线程数量计算中正确应用
//! - 线程池管理器功能完整
//! - 线程资源分配器工作正常

use c05_threads::rust_192_features::{
    ThreadPoolTaskQueue, ThreadPoolManager, ThreadResourceAllocator,
    ThreadTask, calculate_thread_pool_size, ThreadSchedulingConfig,
    ThreadSafeUninitBuffer, ThreadPoolQueue,
};
use std::num::NonZeroUsize;
use std::sync::Arc;
use std::thread;

/// 测试 rotate_right 在线程池任务队列中的应用
#[test]
fn test_thread_pool_queue_rotate() {
    let mut queue = ThreadPoolTaskQueue::new();

    // 添加多个任务
    for i in 1..=5 {
        queue.push(ThreadTask {
            id: i,
            priority: (i * 10) as u8,
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
}

/// 测试空队列的轮转
#[test]
fn test_thread_pool_queue_rotate_empty() {
    let mut queue = ThreadPoolTaskQueue::new();
    // 空队列轮转不应该 panic
    queue.rotate(5);
    assert_eq!(queue.len(), 0);
    assert!(queue.is_empty());
}

/// 测试 NonZero::div_ceil 在线程池大小计算中的应用
#[test]
fn test_thread_pool_size_calculation() {
    let tasks_per_thread = NonZeroUsize::new(5).unwrap();

    // 测试各种情况
    assert_eq!(calculate_thread_pool_size(23, tasks_per_thread), 5);
    assert_eq!(calculate_thread_pool_size(25, tasks_per_thread), 5);
    assert_eq!(calculate_thread_pool_size(26, tasks_per_thread), 6);
    assert_eq!(calculate_thread_pool_size(1, tasks_per_thread), 1);
    assert_eq!(calculate_thread_pool_size(5, tasks_per_thread), 1);
    assert_eq!(calculate_thread_pool_size(10, tasks_per_thread), 2);
    assert_eq!(calculate_thread_pool_size(0, tasks_per_thread), 0);
}

/// 测试线程资源分配器
#[test]
fn test_thread_resource_allocator() {
    // 测试基本分配
    let allocator = ThreadResourceAllocator::new(16, NonZeroUsize::new(2).unwrap());
    assert_eq!(allocator.max_threads(), 8);

    // 测试边界情况
    let allocator2 = ThreadResourceAllocator::new(10, NonZeroUsize::new(5).unwrap());
    assert_eq!(allocator2.max_threads(), 2);

    // 测试最小资源
    let allocator3 = ThreadResourceAllocator::new(10, NonZeroUsize::new(1).unwrap());
    assert_eq!(allocator3.max_threads(), 10);

    // 测试零资源
    let allocator4 = ThreadResourceAllocator::new(0, NonZeroUsize::new(1).unwrap());
    assert_eq!(allocator4.max_threads(), 0);
}

/// 测试线程调度配置
#[test]
fn test_thread_scheduling_config() {
    let config = ThreadSchedulingConfig::new(NonZeroUsize::new(2).unwrap(), 10);

    // 测试零任务
    assert_eq!(config.calculate_threads_for_tasks(0), 2);

    // 测试小任务数
    assert_eq!(config.calculate_threads_for_tasks(5), 3);

    // 测试大任务数（应该限制在最大值）
    assert_eq!(config.calculate_threads_for_tasks(100), 10);

    // 测试边界情况
    assert_eq!(config.calculate_threads_for_tasks(20), 10);
    assert_eq!(config.calculate_threads_for_tasks(4), 2);
}

/// 测试线程池管理器
#[test]
fn test_thread_pool_manager() {
    let manager = ThreadPoolManager::new();

    // 添加多个任务
    for i in 1..=3 {
        manager.add_task(ThreadTask {
            id: i,
            priority: (i * 10) as u8,
        });
    }

    // 执行轮转
    manager.rotate();

    // 获取任务（轮转后，最后一个任务会移到前面）
    let task1 = manager.next_task();
    assert!(task1.is_some());
    // 轮转后，最后一个任务（id=3）会移到前面
    assert_eq!(task1.unwrap().id, 3);

    let task2 = manager.next_task();
    assert!(task2.is_some());
    assert_eq!(task2.unwrap().id, 1);
}

/// 测试线程池管理器的并发安全性
#[test]
fn test_thread_pool_manager_concurrent() {
    let manager = Arc::new(ThreadPoolManager::new());
    let mut handles = vec![];

    // 并发添加任务
    for i in 1..=10 {
        let manager_clone = manager.clone();
        let handle = thread::spawn(move || {
            manager_clone.add_task(ThreadTask {
                id: i,
                priority: (i * 10) as u8,
            });
        });
        handles.push(handle);
    }

    // 等待所有任务添加完成
    for handle in handles {
        handle.join().unwrap();
    }

    // 执行轮转
    manager.rotate();

    // 验证所有任务都被处理
    let mut count = 0;
    while manager.next_task().is_some() {
        count += 1;
    }
    assert_eq!(count, 10);
}

/// 测试 ThreadSafeUninitBuffer
#[test]
fn test_thread_safe_uninit_buffer() {
    let mut buffer = ThreadSafeUninitBuffer::<i32>::new(10);

    // 初始化数据
    unsafe {
        buffer.init_at(0, 42);
        buffer.init_at(1, 84);
        buffer.init_at(2, 126);
    }

    // 读取数据
    unsafe {
        assert_eq!(*buffer.get(0), 42);
        assert_eq!(*buffer.get(1), 84);
        assert_eq!(*buffer.get(2), 126);
    }

    // 修改数据
    unsafe {
        *buffer.get_mut(0) = 100;
        assert_eq!(*buffer.get(0), 100);
    }
}

/// 测试 ThreadPoolQueue
#[test]
fn test_thread_pool_queue() {
    let mut queue = ThreadPoolQueue::new(10);

    // 添加任务
    unsafe {
        queue.push(ThreadTask { id: 1, priority: 10 });
        queue.push(ThreadTask { id: 2, priority: 20 });
        queue.push(ThreadTask { id: 3, priority: 30 });
    }

    // 获取任务
    unsafe {
        let task1 = queue.pop();
        assert!(task1.is_some());
        assert_eq!(task1.unwrap().id, 3); // 后进先出

        let task2 = queue.pop();
        assert!(task2.is_some());
        assert_eq!(task2.unwrap().id, 2);

        let task3 = queue.pop();
        assert!(task3.is_some());
        assert_eq!(task3.unwrap().id, 1);

        // 队列应该为空
        let task4 = queue.pop();
        assert!(task4.is_none());
    }
}

/// 测试线程池任务队列的基本操作
#[test]
fn test_thread_pool_task_queue_operations() {
    let mut queue = ThreadPoolTaskQueue::new();

    // 测试空队列
    assert_eq!(queue.len(), 0);
    assert!(queue.is_empty());
    assert!(queue.pop().is_none());

    // 添加任务
    queue.push(ThreadTask {
        id: 1,
        priority: 10,
    });
    assert_eq!(queue.len(), 1);
    assert!(!queue.is_empty());

    // 弹出任务
    let task = queue.pop().unwrap();
    assert_eq!(task.id, 1);
    assert_eq!(queue.len(), 0);
}

/// 综合测试：完整的线程池处理流程
#[test]
fn test_complete_thread_pool_workflow() {
    // 1. 创建资源分配器
    let allocator = ThreadResourceAllocator::new(16, NonZeroUsize::new(2).unwrap());
    assert_eq!(allocator.max_threads(), 8);

    // 2. 创建任务队列
    let mut queue = ThreadPoolTaskQueue::new();
    for i in 1..=5 {
        queue.push(ThreadTask {
            id: i,
            priority: (i * 10) as u8,
        });
    }

    // 3. 轮转队列
    queue.rotate(2);
    let rotated_ids: Vec<u64> = queue.iter().map(|t| t.id).collect();
    assert_eq!(rotated_ids, vec![4, 5, 1, 2, 3]);

    // 4. 创建管理器并添加任务
    let manager = ThreadPoolManager::new();
    while let Some(task) = queue.pop() {
        manager.add_task(task);
    }

    // 5. 执行轮转
    manager.rotate();

    // 6. 验证任务被处理
    let mut ids = vec![];
    while let Some(task) = manager.next_task() {
        ids.push(task.id);
    }
    // 验证所有任务都被处理
    assert_eq!(ids.len(), 5);
    // 验证任务 ID 都在范围内
    for id in &ids {
        assert!(*id >= 1 && *id <= 5);
    }
}

/// 测试新增的队列操作方法
#[test]
fn test_queue_utility_methods() {
    let mut queue = ThreadPoolTaskQueue::new();

    // 测试 is_empty
    assert!(queue.is_empty());

    // 测试 push 和 len
    queue.push(ThreadTask {
        id: 1,
        priority: 10,
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
#[test]
fn test_batch_operations() {
    let mut queue = ThreadPoolTaskQueue::new();

    // 批量添加任务
    let tasks = vec![
        ThreadTask { id: 1, priority: 10 },
        ThreadTask { id: 2, priority: 20 },
        ThreadTask { id: 3, priority: 30 },
    ];

    queue.push_batch(tasks);
    assert_eq!(queue.len(), 3);

    // 测试按优先级排序
    queue.sort_by_priority();
    let priorities: Vec<u8> = queue.iter().map(|t| t.priority).collect();
    assert_eq!(priorities, vec![30, 20, 10]);
}

/// 测试调度器的新方法
#[test]
fn test_scheduler_utility_methods() {
    let manager = ThreadPoolManager::new();

    // 测试 is_empty
    assert!(manager.is_empty());

    // 添加任务
    manager.add_task(ThreadTask {
        id: 1,
        priority: 10,
    });

    // 测试 task_count
    assert_eq!(manager.task_count(), 1);
    assert!(!manager.is_empty());

    // 测试批量添加
    let tasks = vec![
        ThreadTask { id: 2, priority: 20 },
        ThreadTask { id: 3, priority: 30 },
    ];
    manager.add_tasks_batch(tasks);
    assert_eq!(manager.task_count(), 3);

    // 测试按优先级排序
    manager.sort_by_priority();
    let first_task = manager.next_task();
    assert!(first_task.is_some());
    assert_eq!(first_task.unwrap().priority, 30); // 最高优先级

    // 测试 clear
    manager.clear();
    assert!(manager.is_empty());
    assert_eq!(manager.task_count(), 0);
}

/// 测试 ThreadTask 的实用方法
#[test]
fn test_thread_task_utility_methods() {
    // 测试构造函数
    let task1 = ThreadTask::new(1, 100);
    assert_eq!(task1.id, 1);
    assert_eq!(task1.priority, 100);

    // 测试优先级构造函数
    let high_task = ThreadTask::high_priority(2);
    assert!(high_task.is_high_priority());
    assert_eq!(high_task.priority, 255);

    let medium_task = ThreadTask::medium_priority(3);
    assert!(!medium_task.is_high_priority());
    assert!(!medium_task.is_low_priority());
    assert_eq!(medium_task.priority, 128);

    let low_task = ThreadTask::low_priority(4);
    assert!(low_task.is_low_priority());
    assert_eq!(low_task.priority, 0);

    // 测试优先级检查
    let task_high = ThreadTask::new(5, 200);
    assert!(task_high.is_high_priority());
    assert!(!task_high.is_low_priority());

    let task_low = ThreadTask::new(6, 30);
    assert!(!task_low.is_high_priority());
    assert!(task_low.is_low_priority());
}

/// 测试线程池统计信息
#[test]
fn test_thread_pool_stats() {
    let manager = ThreadPoolManager::new();

    // 添加不同优先级的任务
    manager.add_task(ThreadTask::high_priority(1));
    manager.add_task(ThreadTask::high_priority(2));
    manager.add_task(ThreadTask::medium_priority(3));
    manager.add_task(ThreadTask::low_priority(4));
    manager.add_task(ThreadTask::low_priority(5));

    let stats = manager.get_stats();
    assert_eq!(stats.total_tasks, 5);
    assert_eq!(stats.high_priority_tasks, 2);
    assert_eq!(stats.medium_priority_tasks, 1);
    assert_eq!(stats.low_priority_tasks, 2);
    assert!(stats.average_priority > 0.0);
}

/// 测试获取所有任务
#[test]
fn test_get_all_tasks() {
    let manager = ThreadPoolManager::new();

    manager.add_task(ThreadTask::new(1, 10));
    manager.add_task(ThreadTask::new(2, 20));
    manager.add_task(ThreadTask::new(3, 30));

    let tasks = manager.get_all_tasks();
    assert_eq!(tasks.len(), 3);
    assert_eq!(tasks[0].id, 1);
    assert_eq!(tasks[1].id, 2);
    assert_eq!(tasks[2].id, 3);
}

/// 测试移除任务
#[test]
fn test_remove_task() {
    let manager = ThreadPoolManager::new();

    manager.add_task(ThreadTask::new(1, 10));
    manager.add_task(ThreadTask::new(2, 20));
    manager.add_task(ThreadTask::new(3, 30));

    assert_eq!(manager.task_count(), 3);

    // 移除存在的任务
    let removed = manager.remove_task(2);
    assert!(removed);
    assert_eq!(manager.task_count(), 2);

    // 移除不存在的任务
    let not_removed = manager.remove_task(99);
    assert!(!not_removed);
    assert_eq!(manager.task_count(), 2);

    // 验证剩余任务
    let tasks = manager.get_all_tasks();
    assert_eq!(tasks.len(), 2);
    assert!(tasks.iter().any(|t| t.id == 1));
    assert!(tasks.iter().any(|t| t.id == 3));
    assert!(!tasks.iter().any(|t| t.id == 2));
}

/// 测试新的排序方法
#[test]
fn test_additional_sort_methods() {
    let mut queue = ThreadPoolTaskQueue::new();

    queue.push(ThreadTask::new(3, 30));
    queue.push(ThreadTask::new(1, 10));
    queue.push(ThreadTask::new(2, 20));

    // 测试按 ID 排序
    queue.sort_by_id();
    let ids: Vec<u64> = queue.iter().map(|t| t.id).collect();
    assert_eq!(ids, vec![1, 2, 3]);

    // 测试按优先级升序排序
    queue.sort_by_priority_asc();
    let priorities: Vec<u8> = queue.iter().map(|t| t.priority).collect();
    assert_eq!(priorities, vec![10, 20, 30]);
}

/// 测试 ThreadSafeUninitBuffer 的新方法
#[test]
fn test_buffer_utility_methods() {
    let buffer = ThreadSafeUninitBuffer::<i32>::new(10);

    assert_eq!(buffer.len(), 10);
    assert!(!buffer.is_empty());
    assert!(buffer.is_valid_index(0));
    assert!(buffer.is_valid_index(9));
    assert!(!buffer.is_valid_index(10));

    let empty_buffer = ThreadSafeUninitBuffer::<i32>::new(0);
    assert_eq!(empty_buffer.len(), 0);
    assert!(empty_buffer.is_empty());
}

/// 测试 rotate 方法的边界情况
#[test]
fn test_rotate_edge_cases() {
    let mut queue = ThreadPoolTaskQueue::new();

    queue.push(ThreadTask::new(1, 10));
    queue.push(ThreadTask::new(2, 20));
    queue.push(ThreadTask::new(3, 30));

    // 测试轮转位置大于队列长度
    queue.rotate(10); // 应该等价于 rotate(10 % 3 = 1)
    let first_id = queue.pop().unwrap().id;
    assert_eq!(first_id, 3); // 轮转1位后，3应该在前面

    // 测试空队列轮转
    let mut empty_queue = ThreadPoolTaskQueue::new();
    empty_queue.rotate(5); // 不应该 panic
    assert!(empty_queue.is_empty());
}

/// 测试 ThreadResourceAllocator 的新方法
#[test]
fn test_resource_allocator_utility_methods() {
    let allocator = ThreadResourceAllocator::new(16, NonZeroUsize::new(2).unwrap());

    assert_eq!(allocator.total_cpus(), 16);
    assert_eq!(allocator.cpus_per_thread().get(), 2);
    assert_eq!(allocator.max_threads(), 8);

    // 测试资源检查
    assert!(allocator.has_sufficient_resources(5));
    assert!(!allocator.has_sufficient_resources(10));

    // 测试可用线程数
    assert_eq!(allocator.available_threads(3), 5);
    assert_eq!(allocator.available_threads(10), 0); // 饱和减法
}

/// 测试 ThreadSchedulingConfig 的新方法
#[test]
fn test_scheduling_config_utility_methods() {
    let config = ThreadSchedulingConfig::new(NonZeroUsize::new(2).unwrap(), 10);

    assert_eq!(config.min_threads().get(), 2);
    assert_eq!(config.max_threads(), 10);

    // 测试线程数验证
    assert!(config.is_valid_thread_count(5));
    assert!(config.is_valid_thread_count(2));
    assert!(config.is_valid_thread_count(10));
    assert!(!config.is_valid_thread_count(1));
    assert!(!config.is_valid_thread_count(11));

    // 测试带每线程任务数的计算
    let threads = config.calculate_threads_with_tasks_per_thread(
        23,
        NonZeroUsize::new(5).unwrap()
    );
    assert_eq!(threads, 5); // 23 / 5 = 4.6 -> 5, 在 2-10 范围内
}

/// 测试便利函数
#[test]
fn test_convenience_functions() {
    use c05_threads::rust_192_features::{
        create_default_resource_allocator, create_default_scheduling_config,
        create_tasks_batch,
    };

    // 测试创建默认资源分配器
    let allocator = create_default_resource_allocator();
    assert!(allocator.max_threads() > 0);

    // 测试创建默认调度配置
    let config = create_default_scheduling_config();
    assert_eq!(config.min_threads().get(), 2);
    assert_eq!(config.max_threads(), 16);

    // 测试批量创建任务
    let tasks = create_tasks_batch(1..=5, |id| (id * 10) as u8);
    assert_eq!(tasks.len(), 5);
    assert_eq!(tasks[0].id, 1);
    assert_eq!(tasks[0].priority, 10);
    assert_eq!(tasks[4].id, 5);
    assert_eq!(tasks[4].priority, 50);
}

/// 测试更多便利函数
#[test]
fn test_more_convenience_functions() {
    use c05_threads::rust_192_features::{
        create_high_priority_tasks, create_low_priority_tasks, create_manager_with_tasks,
        ThreadTask,
    };

    // 测试创建高优先级任务批次
    let high_tasks = create_high_priority_tasks(1..=3);
    assert_eq!(high_tasks.len(), 3);
    for task in &high_tasks {
        assert!(task.is_high_priority());
    }

    // 测试创建低优先级任务批次
    let low_tasks = create_low_priority_tasks(1..=3);
    assert_eq!(low_tasks.len(), 3);
    for task in &low_tasks {
        assert!(task.is_low_priority());
    }

    // 测试从任务列表创建管理器
    let tasks = vec![
        ThreadTask::new(1, 10),
        ThreadTask::new(2, 20),
        ThreadTask::new(3, 30),
    ];
    let manager = create_manager_with_tasks(tasks);
    assert_eq!(manager.task_count(), 3);
}
