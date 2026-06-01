//! Rust 1.92.0 线程特性实现模块
//! Rust 1.92.0 thread feature module
//! ## 主要功能
//! ## main functionality
//! ### 1. 线程池任务管理
//! ### 1. thread pool task
//! ### 2. 线程资源分配
//! ### 2. thread
//! - `calculate_thread_pool_size`: 计算线程池大小
//! ### 3. 并发安全初始化
//! ### 3. concurrency
//! ### 4. 统计和监控
//! ### 4. and
//! - `get_stats()`: 获取统计信息
//! - `get_stats()`:
//! - `get_stats()`: Get统计信息
//! - `get_all_tasks()`: 获取所有任务
//! - `get_all_tasks()`: all task
//! - `get_all_tasks()`: Get所有task
//! - `remove_task()`: 移除指定任务
//! - `remove_task()`: task
//! - `remove_task()`: 移除指定task
//! # 文件信息
//! #
//! - 文件: rust_192_features.rs
//! - 创建日期: 2025-12-11
//! - date : 2025-12-11
//! - 版本: 1.2
//! - this : 1.2
//! - 版this: 1.2
//! - 最后更新: 2025-12-11
//! - finally : 2025-12-11
use std::collections::VecDeque;
use std::mem::MaybeUninit;
use std::num::NonZeroUsize;
use std::sync::{Arc, Mutex};

// ==================== 1. MaybeUninit 在并发编程中的应用 ====================

pub struct ThreadSafeUninitBuffer<T> {
    buffer: Vec<MaybeUninit<T>>,
}

impl<T> ThreadSafeUninitBuffer<T> {
    /// 创建指定大小的未初始化缓冲区
    /// buffering
    pub fn new(size: usize) -> Self {
        let mut buffer = Vec::with_capacity(size);
        unsafe {
            buffer.set_len(size);
        }
        ThreadSafeUninitBuffer { buffer }
    }

    /// 在指定位置初始化数据
    /// in position
    ///
    /// 调用者必须确保：
    /// must ：
    /// - `index` 在有效范围内（0 <= index < capacity）
    /// - 该位置之前未被初始化，或已正确清理
    /// - this position 's before is ，or
    /// - 不会并发调用此方法
    /// - concurrency this method
    pub unsafe fn init_at(&mut self, index: usize, value: T) {
        self.buffer[index].write(value);
    }

    /// 获取已初始化的引用
    /// reference
    /// Get已Initializereference
    ///
    /// 调用者必须确保：
    /// must ：
    /// - `index` 在有效范围内（0 <= index < capacity）
    /// - 该位置已通过 `init_at` 正确初始化
    /// - this position `init_at`
    /// - 返回的引用在有效生命周期内不会被释放
    /// - reference in effective lifetime inside is
    pub unsafe fn get(&self, index: usize) -> &T {
        unsafe { self.buffer[index].assume_init_ref() }
    }

    /// 获取可变引用
    /// reference
    /// Get可变reference
    ///
    /// 调用者必须确保：
    /// must ：
    /// - `index` 在有效范围内（0 <= index < capacity）
    /// - 该位置已通过 `init_at` 正确初始化
    /// - this position `init_at`
    /// - 返回的可变引用在有效生命周期内不会被释放
    /// - reference in effective lifetime inside is
    /// - 不会与其他引用产生数据竞争
    /// - rather than reference
    pub unsafe fn get_mut(&mut self, index: usize) -> &mut T {
        unsafe { self.buffer[index].assume_init_mut() }
    }

    /// 获取缓冲区大小
    /// buffering
    pub fn len(&self) -> usize {
        self.buffer.len()
    }

    /// 检查缓冲区是否为空
    /// buffering as
    pub fn is_empty(&self) -> bool {
        self.buffer.is_empty()
    }

    /// 检查指定索引是否在有效范围内
    /// in effective scope inside
    pub fn is_valid_index(&self, index: usize) -> bool {
        index < self.buffer.len()
    }
}

/// 线程池中的任务项
/// thread pool in task
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ThreadTask {
    pub id: u64,
    pub priority: u8,
}

impl ThreadTask {
    /// 创建一个新的任务
    /// task
    pub fn new(id: u64, priority: u8) -> Self {
        ThreadTask { id, priority }
    }

    /// 创建一个高优先级任务
    /// task
    pub fn high_priority(id: u64) -> Self {
        ThreadTask { id, priority: 255 }
    }

    /// 创建一个中优先级任务
    /// in task
    pub fn medium_priority(id: u64) -> Self {
        ThreadTask { id, priority: 128 }
    }

    /// 创建一个低优先级任务
    /// task
    pub fn low_priority(id: u64) -> Self {
        ThreadTask { id, priority: 0 }
    }

    /// 检查是否为高优先级任务
    /// as task
    pub fn is_high_priority(&self) -> bool {
        self.priority >= 200
    }

    /// 检查是否为低优先级任务
    /// as task
    pub fn is_low_priority(&self) -> bool {
        self.priority < 50
    }
}

pub struct ThreadPoolQueue {
    tasks: Vec<MaybeUninit<ThreadTask>>,
    initialized_count: usize,
}

impl ThreadPoolQueue {
    pub fn new(capacity: usize) -> Self {
        let mut tasks = Vec::with_capacity(capacity);
        unsafe {
            tasks.set_len(capacity);
        }
        ThreadPoolQueue {
            tasks,
            initialized_count: 0,
        }
    }

    /// 添加任务（线程安全，需要外部同步）
    /// task （thread-safe ，outside synchronous ）
    ///
    /// 调用者必须确保：
    /// must ：
    /// - 在单线程环境中调用，或已提供外部同步机制
    /// - in thread environment in ，or outside synchronous mechanism
    /// - `initialized_count` 小于 `tasks` 长度
    /// - 不会并发调用此方法
    /// - concurrency this method
    pub unsafe fn push(&mut self, task: ThreadTask) {
        if self.initialized_count < self.tasks.len() {
            self.tasks[self.initialized_count].write(task);
            self.initialized_count += 1;
        }
    }

    /// 获取任务（需要外部同步）
    /// task （outside synchronous ）
    ///
    /// 调用者必须确保：
    /// must ：
    /// - 在单线程环境中调用，或已提供外部同步机制
    /// - in thread environment in ，or outside synchronous mechanism
    /// - 不会并发调用此方法
    /// - concurrency this method
    pub unsafe fn pop(&mut self) -> Option<ThreadTask> {
        if self.initialized_count > 0 {
            self.initialized_count -= 1;
            Some(unsafe { self.tasks[self.initialized_count].assume_init_read() })
        } else {
            None
        }
    }
}

// ==================== 2. rotate_right 在线程池管理中的应用 ====================

/// 使用 rotate_right 实现线程池任务轮转
/// rotate_right thread pool task
pub struct ThreadPoolTaskQueue {
    tasks: VecDeque<ThreadTask>,
}

impl ThreadPoolTaskQueue {
    pub fn new() -> Self {
        ThreadPoolTaskQueue {
            tasks: VecDeque::new(),
        }
    }

    /// 轮转任务队列
    /// task
    /// # 参数
    /// # parameter
    pub fn rotate(&mut self, positions: usize) {
        if self.tasks.is_empty() {
            return;
        }

        // 如果轮转位置大于队列长度，取模
        let len = self.tasks.len();
        let actual_positions = if positions > len {
            positions % len
        } else {
            positions
        };

        // 转换为 Vec 以便使用 rotate_right
        let mut vec: Vec<ThreadTask> = self.tasks.drain(..).collect();
        vec.rotate_right(actual_positions);
        self.tasks = vec.into_iter().collect();
    }

    pub fn push(&mut self, task: ThreadTask) {
        self.tasks.push_back(task);
    }

    pub fn pop(&mut self) -> Option<ThreadTask> {
        self.tasks.pop_front()
    }

    pub fn len(&self) -> usize {
        self.tasks.len()
    }

    pub fn is_empty(&self) -> bool {
        self.tasks.is_empty()
    }

    /// 获取队列中的所有任务（用于测试和演示）
    /// in all task （and demonstration ）
    pub fn iter(&self) -> impl Iterator<Item = &ThreadTask> {
        self.tasks.iter()
    }

    /// 清空队列
    pub fn clear(&mut self) {
        self.tasks.clear();
    }

    /// 查看队列头部的任务（不移除）
    /// task （）
    pub fn peek(&self) -> Option<&ThreadTask> {
        self.tasks.front()
    }

    /// 查看队列头部的任务（可变引用）
    /// task （reference ）
    pub fn peek_mut(&mut self) -> Option<&mut ThreadTask> {
        self.tasks.front_mut()
    }

    /// 批量添加任务
    /// task
    pub fn push_batch(&mut self, tasks: impl IntoIterator<Item = ThreadTask>) {
        for task in tasks {
            self.tasks.push_back(task);
        }
    }

    /// 按优先级排序任务（高优先级在前）
    /// ordering task （in before ）
    /// 按优先级orderingtask（高优先级inbefore）
    pub fn sort_by_priority(&mut self) {
        let mut vec: Vec<ThreadTask> = self.tasks.drain(..).collect();
        vec.sort_by_key(|a| std::cmp::Reverse(a.priority));
        self.tasks = vec.into_iter().collect();
    }

    /// 按优先级排序任务（低优先级在前）
    /// ordering task （in before ）
    /// 按优先级orderingtask（低优先级inbefore）
    pub fn sort_by_priority_asc(&mut self) {
        let mut vec: Vec<ThreadTask> = self.tasks.drain(..).collect();
        vec.sort_by_key(|a| a.priority);
        self.tasks = vec.into_iter().collect();
    }

    /// 按任务 ID 排序
    /// task ID ordering
    /// 按task ID ordering
    pub fn sort_by_id(&mut self) {
        let mut vec: Vec<ThreadTask> = self.tasks.drain(..).collect();
        vec.sort_by_key(|t| t.id);
        self.tasks = vec.into_iter().collect();
    }

    /// 获取队列容量
    pub fn capacity(&self) -> usize {
        self.tasks.capacity()
    }
}

impl Default for ThreadPoolTaskQueue {
    fn default() -> Self {
        Self::new()
    }
}

/// 线程池管理器
/// thread pool
pub struct ThreadPoolManager {
    queue: Arc<Mutex<ThreadPoolTaskQueue>>,
}

impl ThreadPoolManager {
    pub fn new() -> Self {
        ThreadPoolManager {
            queue: Arc::new(Mutex::new(ThreadPoolTaskQueue::new())),
        }
    }

    /// 执行一轮任务轮转（线程安全）
    /// task （thread-safe ）
    pub fn rotate(&self) {
        let mut queue = self.queue.lock().expect("获取队列锁不应失败");
        if queue.len() > 1 {
            queue.rotate(1);
        }
    }

    /// 添加任务（线程安全）
    /// task （thread-safe ）
    /// 添加task（thread-safe）
    pub fn add_task(&self, task: ThreadTask) {
        let mut queue = self.queue.lock().expect("获取队列锁不应失败");
        queue.push(task);
    }

    /// 获取下一个任务（线程安全）
    /// under task （thread-safe ）
    pub fn next_task(&self) -> Option<ThreadTask> {
        let mut queue = self.queue.lock().expect("获取队列锁不应失败");
        queue.pop()
    }

    /// 获取队列中的任务数量（线程安全）
    /// in task quantity （thread-safe ）
    /// Get队列intaskquantity（thread-safe）
    pub fn task_count(&self) -> usize {
        let queue = self.queue.lock().expect("获取队列锁不应失败");
        queue.len()
    }

    /// 检查队列是否为空（线程安全）
    /// as （thread-safe ）
    pub fn is_empty(&self) -> bool {
        let queue = self.queue.lock().expect("获取队列锁不应失败");
        queue.is_empty()
    }

    /// 清空队列（线程安全）
    /// （thread-safe ）
    pub fn clear(&self) {
        let mut queue = self.queue.lock().expect("获取队列锁不应失败");
        queue.clear();
    }

    /// 批量添加任务（线程安全）
    /// task （thread-safe ）
    /// 批量添加task（thread-safe）
    pub fn add_tasks_batch(&self, tasks: impl IntoIterator<Item = ThreadTask>) {
        let mut queue = self.queue.lock().expect("获取队列锁不应失败");
        queue.push_batch(tasks);
    }

    /// 按优先级排序任务（线程安全）
    /// ordering task （thread-safe ）
    /// 按优先级orderingtask（thread-safe）
    pub fn sort_by_priority(&self) {
        let mut queue = self.queue.lock().expect("获取队列锁不应失败");
        queue.sort_by_priority();
    }

    /// 获取线程池统计信息
    /// thread pool
    pub fn get_stats(&self) -> ThreadPoolStats {
        let queue = self.queue.lock().expect("获取队列锁不应失败");
        let tasks: Vec<_> = queue.iter().collect();

        let total_tasks = tasks.len();
        let high_priority_tasks = tasks.iter().filter(|t| t.is_high_priority()).count();
        let low_priority_tasks = tasks.iter().filter(|t| t.is_low_priority()).count();
        let medium_priority_tasks = total_tasks - high_priority_tasks - low_priority_tasks;

        let average_priority = if total_tasks > 0 {
            tasks.iter().map(|t| t.priority as f64).sum::<f64>() / total_tasks as f64
        } else {
            0.0
        };

        ThreadPoolStats {
            total_tasks,
            high_priority_tasks,
            medium_priority_tasks,
            low_priority_tasks,
            average_priority,
        }
    }

    /// 获取所有任务（用于调试和监控）
    /// all task （and ）
    pub fn get_all_tasks(&self) -> Vec<ThreadTask> {
        let queue = self.queue.lock().expect("获取队列锁不应失败");
        queue.iter().cloned().collect()
    }

    /// 移除指定 ID 的任务
    /// ID task
    pub fn remove_task(&self, task_id: u64) -> bool {
        let mut queue = self.queue.lock().expect("获取队列锁不应失败");
        let mut tasks: Vec<ThreadTask> = queue.iter().cloned().collect();
        let original_len = tasks.len();
        tasks.retain(|t| t.id != task_id);
        let removed = tasks.len() < original_len;

        if removed {
            queue.clear();
            queue.push_batch(tasks);
        }

        removed
    }
}

/// 线程池统计信息
/// thread pool
#[derive(Debug, Clone)]
pub struct ThreadPoolStats {
    pub total_tasks: usize,
    pub high_priority_tasks: usize,
    pub medium_priority_tasks: usize,
    pub low_priority_tasks: usize,
    pub average_priority: f64,
}

impl Default for ThreadPoolManager {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 3. NonZero::div_ceil 在线程数量计算中的应用 ====================

/// # 示例
/// # example
/// // 归档模块示例
/// // module example
pub fn calculate_thread_pool_size(total_tasks: usize, tasks_per_thread: NonZeroUsize) -> usize {
    if total_tasks == 0 {
        return 0;
    }

    let total = NonZeroUsize::new(total_tasks).expect("任务总数应非零");
    // Rust 1.92.0: 使用 div_ceil 计算需要的线程数
    total.div_ceil(tasks_per_thread).get()
}

/// 创建默认的线程资源分配器（基于 CPU 核心数）
/// thread （ CPU core ）
/// # 示例
/// # example
/// // 归档模块示例
/// // module example
pub fn create_default_resource_allocator() -> ThreadResourceAllocator {
    let num_cpus = num_cpus::get();
    ThreadResourceAllocator::new(
        num_cpus,
        NonZeroUsize::new(1).expect("CPU 数应非零"), // 默认每线程 1 个 CPU
    )
}

/// 创建默认的线程调度配置
/// thread scheduling
/// # 示例
/// # example
/// // 归档模块示例
/// // module example
pub fn create_default_scheduling_config() -> ThreadSchedulingConfig {
    ThreadSchedulingConfig::new(
        NonZeroUsize::new(2).expect("线程数应非零"), // 最小 2 个线程
        16,                                          // 最大 16 个线程
    )
}

/// 批量创建任务
/// task
/// 批量Createtask
/// # 示例
/// # example
/// // 归档模块示例
/// // module example
pub fn create_tasks_batch<I, F>(ids: I, priority_fn: F) -> Vec<ThreadTask>
where
    I: IntoIterator<Item = u64>,
    F: Fn(u64) -> u8,
{
    ids.into_iter()
        .map(|id| ThreadTask::new(id, priority_fn(id)))
        .collect()
}

/// 创建高优先级任务批次
/// task
/// # 示例
/// # example
/// // 归档模块示例
/// // module example
pub fn create_high_priority_tasks<I>(ids: I) -> Vec<ThreadTask>
where
    I: IntoIterator<Item = u64>,
{
    ids.into_iter().map(ThreadTask::high_priority).collect()
}

/// 创建低优先级任务批次
/// task
/// # 示例
/// # example
/// // 归档模块示例
/// // module example
pub fn create_low_priority_tasks<I>(ids: I) -> Vec<ThreadTask>
where
    I: IntoIterator<Item = u64>,
{
    ids.into_iter().map(ThreadTask::low_priority).collect()
}

/// 从任务列表创建线程池管理器并添加所有任务
/// from task thread pool and all task
/// # 示例
/// # example
/// // 归档模块示例
/// // module example
/// let tasks = vec![
///     ThreadTask::new(1, 10),
///     ThreadTask::new(2, 20),
/// ];
/// let manager = create_manager_with_tasks(tasks);
/// assert_eq!(manager.task_count(), 2);
/// ```
pub fn create_manager_with_tasks(tasks: Vec<ThreadTask>) -> ThreadPoolManager {
    let manager = ThreadPoolManager::new();
    manager.add_tasks_batch(tasks);
    manager
}

/// 使用 div_ceil 实现线程资源分配器
/// div_ceil thread
pub struct ThreadResourceAllocator {
    total_cpus: usize,
    cpus_per_thread: NonZeroUsize,
}

impl ThreadResourceAllocator {
    pub fn new(total_cpus: usize, cpus_per_thread: NonZeroUsize) -> Self {
        ThreadResourceAllocator {
            total_cpus,
            cpus_per_thread,
        }
    }

    /// 计算可以创建的最大线程数
    /// can maximum thread
    pub fn max_threads(&self) -> usize {
        if self.total_cpus == 0 {
            return 0;
        }

        let total = NonZeroUsize::new(self.total_cpus).expect("CPU 总数应非零");
        // Rust 1.92.0: 使用 div_ceil 计算最大线程数
        total.div_ceil(self.cpus_per_thread).get()
    }

    /// 获取总 CPU 核心数
    /// CPU core
    pub fn total_cpus(&self) -> usize {
        self.total_cpus
    }

    /// 获取每线程 CPU 数
    /// thread CPU
    /// Get每thread CPU 数
    pub fn cpus_per_thread(&self) -> NonZeroUsize {
        self.cpus_per_thread
    }

    /// 检查是否有足够的资源
    pub fn has_sufficient_resources(&self, required_threads: usize) -> bool {
        self.max_threads() >= required_threads
    }

    /// 计算可用线程数（考虑已使用的线程）
    /// thread （thread ）
    pub fn available_threads(&self, used_threads: usize) -> usize {
        self.max_threads().saturating_sub(used_threads)
    }
}

/// 线程调度配置
/// thread scheduling
pub struct ThreadSchedulingConfig {
    min_threads: NonZeroUsize,
    max_threads: usize,
}

impl ThreadSchedulingConfig {
    pub fn new(min_threads: NonZeroUsize, max_threads: usize) -> Self {
        ThreadSchedulingConfig {
            min_threads,
            max_threads,
        }
    }

    /// 根据任务数量计算需要的线程数
    /// according to task quantity thread
    pub fn calculate_threads_for_tasks(&self, task_count: usize) -> usize {
        if task_count == 0 {
            return self.min_threads.get();
        }

        let tasks = NonZeroUsize::new(task_count).expect("任务数应非零");
        let calculated = tasks.div_ceil(self.min_threads).get();
        calculated.min(self.max_threads)
    }

    /// 获取最小线程数
    /// minimum thread
    pub fn min_threads(&self) -> NonZeroUsize {
        self.min_threads
    }

    /// 获取最大线程数
    /// maximum thread
    pub fn max_threads(&self) -> usize {
        self.max_threads
    }

    /// 检查线程数是否在有效范围内
    /// thread in effective scope inside
    pub fn is_valid_thread_count(&self, thread_count: usize) -> bool {
        thread_count >= self.min_threads.get() && thread_count <= self.max_threads
    }

    /// 根据任务数量和建议的每线程任务数计算线程数
    /// according to task quantity and thread task thread
    pub fn calculate_threads_with_tasks_per_thread(
        &self,
        task_count: usize,
        tasks_per_thread: NonZeroUsize,
    ) -> usize {
        if task_count == 0 {
            return self.min_threads.get();
        }
        let calculated = calculate_thread_pool_size(task_count, tasks_per_thread);
        calculated.max(self.min_threads.get()).min(self.max_threads)
    }
}

// ==================== 4. 综合应用示例 ====================

/// 演示 Rust 1.92.0 线程特性
/// demonstration Rust 1.92.0 thread feature
pub fn demonstrate_rust_192_thread_features() {
    println!("\n=== Rust 1.92.0 线程特性演示 ===\n");

    // 1. rotate_right 演示
    println!("1. rotate_right 在线程池管理中的应用:");
    let mut queue = ThreadPoolTaskQueue::new();
    queue.push(ThreadTask {
        id: 1,
        priority: 10,
    });
    queue.push(ThreadTask {
        id: 2,
        priority: 20,
    });
    queue.push(ThreadTask {
        id: 3,
        priority: 30,
    });

    println!(
        "   原始队列: {:?}",
        queue.iter().map(|t| t.id).collect::<Vec<_>>()
    );

    queue.rotate(1);
    println!(
        "   轮转后: {:?}",
        queue.iter().map(|t| t.id).collect::<Vec<_>>()
    );

    // 2. NonZero::div_ceil 演示
    println!("\n2. NonZero::div_ceil 在线程数量计算中的应用:");
    let tasks_per_thread = NonZeroUsize::new(5).expect("每线程任务数应非零");
    let total_tasks = 23;
    let pool_size = calculate_thread_pool_size(total_tasks, tasks_per_thread);
    println!("   总任务数: {}", total_tasks);
    println!("   每线程任务数: {}", tasks_per_thread);
    println!("   需要的线程数: {}", pool_size);

    let allocator = ThreadResourceAllocator::new(16, NonZeroUsize::new(2).expect("线程数应非零"));
    println!("   CPU 核心数: 16");
    println!("   每线程 CPU: 2");
    println!("   最大线程数: {}", allocator.max_threads());

    let config = ThreadSchedulingConfig::new(NonZeroUsize::new(2).expect("最小线程数应非零"), 10);
    println!("   最小线程数: 2");
    println!("   最大线程数: 10");
    println!(
        "   23 个任务需要线程数: {}",
        config.calculate_threads_for_tasks(23)
    );

    // 3. MaybeUninit 演示
    println!("\n3. MaybeUninit 在并发编程中的应用:");
    let mut buffer = ThreadSafeUninitBuffer::<i32>::new(10);
    unsafe {
        buffer.init_at(0, 42);
        buffer.init_at(1, 84);
        println!("   初始化位置 0: {}", *buffer.get(0));
        println!("   初始化位置 1: {}", *buffer.get(1));
    }

    // 4. 线程池管理器演示
    println!("\n4. 线程池管理器:");
    let manager = ThreadPoolManager::new();
    manager.add_task(ThreadTask {
        id: 1,
        priority: 10,
    });
    manager.add_task(ThreadTask {
        id: 2,
        priority: 20,
    });

    manager.rotate();
    if let Some(task) = manager.next_task() {
        println!(
            "   获取到的任务: ID={}, Priority={}",
            task.id, task.priority
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_thread_pool_queue_rotate() {
        let mut queue = ThreadPoolTaskQueue::new();
        queue.push(ThreadTask {
            id: 1,
            priority: 10,
        });
        queue.push(ThreadTask {
            id: 2,
            priority: 20,
        });

        queue.rotate(1);
        let first = queue.pop().expect("队列不应为空");
        assert_eq!(first.id, 2);
    }

    #[test]
    fn test_thread_pool_size() {
        let tasks_per_thread = NonZeroUsize::new(5).unwrap();
        assert_eq!(calculate_thread_pool_size(23, tasks_per_thread), 5);
        assert_eq!(calculate_thread_pool_size(25, tasks_per_thread), 5);
        assert_eq!(calculate_thread_pool_size(26, tasks_per_thread), 6);
    }

    #[test]
    fn test_thread_resource_allocator() {
        let allocator = ThreadResourceAllocator::new(16, NonZeroUsize::new(2).unwrap());
        assert_eq!(allocator.max_threads(), 8);
    }

    #[test]
    fn test_thread_scheduling_config() {
        let config = ThreadSchedulingConfig::new(NonZeroUsize::new(2).unwrap(), 10);
        assert_eq!(config.calculate_threads_for_tasks(0), 2);
        assert_eq!(config.calculate_threads_for_tasks(23), 10);
        assert_eq!(config.calculate_threads_for_tasks(5), 3);
    }

    #[test]
    fn test_thread_safe_uninit_buffer() {
        let mut buffer = ThreadSafeUninitBuffer::<i32>::new(5);
        unsafe {
            buffer.init_at(0, 42);
            assert_eq!(*buffer.get(0), 42);
        }
    }
}
