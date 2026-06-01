//! Rust 1.92.0 异步编程特性实现模块
//! Rust 1.92.0 async feature module
//!
//! 本模块展示了 Rust 1.92.0 在异步编程场景中的应用，包括：
//! This module demonstrates Rust 1.92.0 in async scenario in application ，：
//! - 新的稳定 API（`rotate_right`, `NonZero::div_ceil`）
//! - 性能优化（迭代器方法特化）
//! - performance optimization （method ）
//! - 异步任务队列优化
//! - async task optimization
//!
//! # 文件信息
//! #
//! - 文件: rust_192_features.rs
//! - 创建日期: 2025-12-11
//! - date : 2025-12-11
//! - 版本: 1.0
//! - this : 1.0
//! - Rust版本: 1.92.0
//! - Rustthis : 1.92.0
//! - Edition: 2024
use std::collections::VecDeque;
use std::num::NonZeroUsize;
use std::sync::Arc;
use tokio::sync::Mutex;

// ==================== 1. rotate_right 在异步任务队列中的应用 ====================

/// 使用 rotate_right 实现异步任务队列
/// rotate_right async task
///
/// Rust 1.92.0: 新增的 `rotate_right` 方法可以高效实现异步任务队列的轮转调度
/// Rust 1.92.0: `rotate_right` method can efficient async task
pub struct AsyncTaskQueue<T> {
    tasks: VecDeque<TaskItem<T>>,
}

/// 异步任务项
/// async task
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TaskItem<T> {
    /// 任务 ID
    /// task ID
    pub id: u64,
    /// 任务优先级（数值越大优先级越高）
    /// task （）
    pub priority: u8,
    /// 任务数据
    /// task
    pub data: T,
}

impl<T> AsyncTaskQueue<T> {
    /// 创建一个新的异步任务队列
    /// async task
    pub fn new() -> Self {
        AsyncTaskQueue {
            tasks: VecDeque::new(),
        }
    }

    /// 轮转异步任务队列
    /// async task
    ///
    /// Rust 1.92.0: 使用新的 rotate_right 方法实现高效的队列轮转
    /// Rust 1.92.0: rotate_right method efficient
    pub fn rotate(&mut self, positions: usize) {
        if self.tasks.is_empty() {
            return;
        }

        // 转换为 Vec 以便使用 rotate_right
        let mut vec: Vec<TaskItem<T>> = self.tasks.drain(..).collect();
        vec.rotate_right(positions);
        self.tasks = vec.into_iter().collect();
    }

    /// 向队列末尾添加一个任务
    /// task
    pub fn push(&mut self, task: TaskItem<T>) {
        self.tasks.push_back(task);
    }

    /// 从队列头部移除并返回一个任务
    /// from and task
    pub fn pop(&mut self) -> Option<TaskItem<T>> {
        self.tasks.pop_front()
    }

    /// 获取队列中的所有任务（用于演示）
    /// in all task （demonstration ）
    pub fn iter(&self) -> impl Iterator<Item = &TaskItem<T>> {
        self.tasks.iter()
    }

    /// 获取队列长度
    pub fn len(&self) -> usize {
        self.tasks.len()
    }

    /// 检查队列是否为空
    /// as
    pub fn is_empty(&self) -> bool {
        self.tasks.is_empty()
    }

    /// 清空队列
    pub fn clear(&mut self) {
        self.tasks.clear();
    }

    /// 查看队列头部的任务（不移除）
    /// task （）
    pub fn peek(&self) -> Option<&TaskItem<T>> {
        self.tasks.front()
    }

    /// 查看队列头部的任务（可变引用）
    /// task （reference ）
    pub fn peek_mut(&mut self) -> Option<&mut TaskItem<T>> {
        self.tasks.front_mut()
    }

    /// 批量添加任务
    /// task
    pub fn push_batch(&mut self, tasks: impl IntoIterator<Item = TaskItem<T>>) {
        for task in tasks {
            self.tasks.push_back(task);
        }
    }

    /// 按优先级排序任务（高优先级在前）
    /// ordering task （in before ）
    pub fn sort_by_priority(&mut self) {
        let mut vec: Vec<TaskItem<T>> = self.tasks.drain(..).collect();
        vec.sort_by_key(|a| std::cmp::Reverse(a.priority));
        self.tasks = vec.into_iter().collect();
    }

    /// 获取队列容量（如果使用 VecDeque 的容量）
    /// （if VecDeque ）
    pub fn capacity(&self) -> usize {
        self.tasks.capacity()
    }
}

impl<T> Default for AsyncTaskQueue<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 使用 rotate_right 实现异步任务轮转调度器
/// rotate_right async task
pub struct AsyncTaskScheduler<T> {
    queue: Arc<Mutex<AsyncTaskQueue<T>>>,
    #[allow(dead_code)]
    quantum: usize,
}

impl<T> AsyncTaskScheduler<T> {
    pub fn new(quantum: usize) -> Self {
        AsyncTaskScheduler {
            queue: Arc::new(Mutex::new(AsyncTaskQueue::new())),
            quantum,
        }
    }

    /// 执行一轮调度（异步）
    /// （async ）
    pub async fn schedule(&self) {
        let mut queue = self.queue.lock().await;

        // Rust 1.92.0: 使用 rotate_right 实现时间片轮转
        if queue.len() > 1 {
            queue.rotate(1);
        }
    }

    /// 添加任务（异步）
    /// task （async ）
    pub async fn add_task(&self, task: TaskItem<T>) {
        let mut queue = self.queue.lock().await;
        queue.push(task);
    }

    /// 获取下一个任务（异步）
    /// under task （async ）
    pub async fn next_task(&self) -> Option<TaskItem<T>> {
        let mut queue = self.queue.lock().await;
        queue.pop()
    }

    /// 获取队列中的任务数量（异步）
    /// in task quantity （async ）
    pub async fn task_count(&self) -> usize {
        let queue = self.queue.lock().await;
        queue.len()
    }

    /// 检查队列是否为空（异步）
    /// as （async ）
    pub async fn is_empty(&self) -> bool {
        let queue = self.queue.lock().await;
        queue.is_empty()
    }

    /// 清空队列（异步）
    /// （async ）
    pub async fn clear(&self) {
        let mut queue = self.queue.lock().await;
        queue.clear();
    }

    /// 批量添加任务（异步）
    /// task （async ）
    pub async fn add_tasks_batch(&self, tasks: impl IntoIterator<Item = TaskItem<T>>) {
        let mut queue = self.queue.lock().await;
        queue.push_batch(tasks);
    }

    /// 按优先级排序任务（异步）
    /// ordering task （async ）
    pub async fn sort_by_priority(&self) {
        let mut queue = self.queue.lock().await;
        queue.sort_by_priority();
    }
}

// ==================== 2. NonZero::div_ceil 在异步池大小计算中的应用 ====================

/// 使用 NonZero::div_ceil 计算异步任务池大小
/// NonZero::div_ceil async task
///
/// Rust 1.92.0: 新增的 `div_ceil` 方法可以安全地计算异步池的容量
/// Rust 1.92.0: `div_ceil` method can async
pub fn calculate_async_pool_size(total_tasks: usize, tasks_per_worker: NonZeroUsize) -> usize {
    if total_tasks == 0 {
        return 0;
    }

    let total = NonZeroUsize::new(total_tasks).expect("任务总数应非零");
    // Rust 1.92.0: 使用 div_ceil 计算需要的 worker 数
    total.div_ceil(tasks_per_worker).get()
}

/// 使用 div_ceil 实现异步资源分配器
/// div_ceil async
pub struct AsyncResourceAllocator {
    total_resources: usize,
    resources_per_task: NonZeroUsize,
}

impl AsyncResourceAllocator {
    pub fn new(total_resources: usize, resources_per_task: NonZeroUsize) -> Self {
        AsyncResourceAllocator {
            total_resources,
            resources_per_task,
        }
    }

    /// 计算可以创建的异步任务数
    /// can async task
    pub fn max_concurrent_tasks(&self) -> usize {
        if self.total_resources == 0 {
            return 0;
        }

        let total = NonZeroUsize::new(self.total_resources).expect("资源总数应非零");
        // Rust 1.92.0: 使用 div_ceil 计算最大并发任务数
        total.div_ceil(self.resources_per_task).get()
    }
}

/// 异步批处理配置
/// async
pub struct AsyncBatchConfig {
    batch_size: NonZeroUsize,
    #[allow(dead_code)]
    max_concurrent_batches: usize,
}

impl AsyncBatchConfig {
    pub fn new(batch_size: NonZeroUsize) -> Self {
        AsyncBatchConfig {
            batch_size,
            max_concurrent_batches: 0,
        }
    }

    /// 计算需要的批次数量
    /// quantity
    pub fn calculate_batch_count(&self, total_items: usize) -> usize {
        if total_items == 0 {
            return 0;
        }

        let total = NonZeroUsize::new(total_items).expect("项目总数应非零");
        // Rust 1.92.0: 使用 div_ceil 计算批次数量
        total.div_ceil(self.batch_size).get()
    }
}

// ==================== 3. 迭代器方法特化在异步迭代中的应用 ====================

/// 使用特化的迭代器比较方法比较异步任务列表
/// method async task
///
/// Rust 1.92.0: Iterator::eq 为 TrustedLen 迭代器特化，性能更好
pub fn compare_async_task_lists<T: PartialEq>(
    list1: &[TaskItem<T>],
    list2: &[TaskItem<T>],
) -> bool {
    // Rust 1.92.0: 特化的迭代器比较方法，性能更好
    list1.iter().eq(list2.iter())
}

/// 使用迭代器特化检查异步任务状态
/// async task state
pub fn check_async_task_states<T>(tasks: &[TaskItem<T>], expected_ids: &[u64]) -> bool {
    let actual_ids: Vec<u64> = tasks.iter().map(|t| t.id).collect();
    // Rust 1.92.0: 特化的迭代器比较
    actual_ids.iter().eq(expected_ids.iter())
}

// ==================== 4. 综合应用示例 ====================

/// 演示 Rust 1.92.0 特性在异步编程中的应用
/// demonstration Rust 1.92.0 feature in async in application
pub async fn demonstrate_rust_192_async_features() {
    println!("\n=== Rust 1.92.0 异步编程特性演示 ===\n");

    // 1. rotate_right 演示
    println!("1. rotate_right 在异步任务队列中的应用:");
    let mut queue = AsyncTaskQueue::new();
    queue.push(TaskItem {
        id: 1,
        priority: 10,
        data: "task1",
    });
    queue.push(TaskItem {
        id: 2,
        priority: 20,
        data: "task2",
    });
    queue.push(TaskItem {
        id: 3,
        priority: 30,
        data: "task3",
    });

    println!(
        "   原始队列: {:?}",
        queue.tasks.iter().map(|t| t.id).collect::<Vec<_>>()
    );

    queue.rotate(1);
    println!(
        "   轮转后: {:?}",
        queue.tasks.iter().map(|t| t.id).collect::<Vec<_>>()
    );

    // 2. NonZero::div_ceil 演示
    println!("\n2. NonZero::div_ceil 在异步池计算中的应用:");
    let tasks_per_worker = NonZeroUsize::new(5).expect("每工作线程任务数应非零");
    let total_tasks = 23;
    let pool_size = calculate_async_pool_size(total_tasks, tasks_per_worker);
    println!("   总任务数: {}", total_tasks);
    println!("   每 worker 任务数: {}", tasks_per_worker);
    println!("   需要的 worker 数: {}", pool_size);

    let allocator = AsyncResourceAllocator::new(1024, NonZeroUsize::new(64).expect("块大小应非零"));
    println!("   总资源: 1024 units");
    println!("   每任务资源: 64 units");
    println!("   最大并发任务数: {}", allocator.max_concurrent_tasks());

    // 3. 迭代器特化演示
    println!("\n3. 迭代器方法特化在异步迭代中的应用:");
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
    let list2 = list1.clone();
    println!(
        "   任务列表相等: {}",
        compare_async_task_lists(&list1, &list2)
    );

    let expected_ids = vec![1, 2];
    println!(
        "   ID 列表匹配: {}",
        check_async_task_states(&list1, &expected_ids)
    );

    // 4. 异步调度器演示
    println!("\n4. 异步任务调度器:");
    let scheduler = AsyncTaskScheduler::new(1);
    scheduler
        .add_task(TaskItem {
            id: 1,
            priority: 10,
            data: "async_task1",
        })
        .await;
    scheduler
        .add_task(TaskItem {
            id: 2,
            priority: 20,
            data: "async_task2",
        })
        .await;

    scheduler.schedule().await;
    if let Some(task) = scheduler.next_task().await {
        println!(
            "   获取到的任务: ID={}, Priority={}",
            task.id, task.priority
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
#[cfg_attr(miri, ignore)]
    async fn test_async_task_queue_rotate() {
        let mut queue = AsyncTaskQueue::new();
        queue.push(TaskItem {
            id: 1,
            priority: 10,
            data: "task1",
        });
        queue.push(TaskItem {
            id: 2,
            priority: 20,
            data: "task2",
        });

        queue.rotate(1);
        let first = queue.pop().expect("队列不应为空");
        assert_eq!(first.id, 2);
    }

    #[test]
    fn test_async_pool_size() {
        let tasks_per_worker = NonZeroUsize::new(5).expect("每工作线程任务数应非零");
        assert_eq!(calculate_async_pool_size(23, tasks_per_worker), 5);
        assert_eq!(calculate_async_pool_size(25, tasks_per_worker), 5);
        assert_eq!(calculate_async_pool_size(26, tasks_per_worker), 6);
    }

    #[test]
    fn test_async_resource_allocator() {
        let allocator = AsyncResourceAllocator::new(1024, NonZeroUsize::new(64).expect("块大小应非零"));
        assert_eq!(allocator.max_concurrent_tasks(), 16);
    }

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
        let list2 = list1.clone();
        assert!(compare_async_task_lists(&list1, &list2));
    }
}
