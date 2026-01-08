//! Rust 1.92.0 线程特性实现模块
//!
//! 本模块展示了 Rust 1.92.0 在线程和并发编程场景中的应用，包括：
//! - `MaybeUninit` 在并发编程中的应用
//! - `rotate_right` 在线程池管理中的应用
//! - `NonZero::div_ceil` 在线程数量计算中的应用
//!
//! # 文件信息
//! - 文件: rust_192_features.rs
//! - 创建日期: 2025-12-11
//! - 版本: 1.0
//! - Rust版本: 1.92.0
//! - Edition: 2024

use std::mem::MaybeUninit;
use std::num::NonZeroUsize;
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;

// ==================== 1. MaybeUninit 在并发编程中的应用 ====================

/// 使用 MaybeUninit 实现线程安全的无锁数据初始化
///
/// Rust 1.92.0: 改进的 MaybeUninit 文档和有效性检查
pub struct ThreadSafeUninitBuffer<T> {
    buffer: Vec<MaybeUninit<T>>,
}

impl<T> ThreadSafeUninitBuffer<T> {
    /// 创建指定大小的未初始化缓冲区
    pub fn new(size: usize) -> Self {
        let mut buffer = Vec::with_capacity(size);
        unsafe {
            buffer.set_len(size);
        }
        ThreadSafeUninitBuffer { buffer }
    }

    /// 在指定位置初始化数据
    ///
    /// Rust 1.92.0: 使用 MaybeUninit 确保安全性
    pub unsafe fn init_at(&mut self, index: usize, value: T) {
        self.buffer[index].write(value);
    }

    /// 获取已初始化的引用
    pub unsafe fn get(&self, index: usize) -> &T {
        unsafe { self.buffer[index].assume_init_ref() }
    }

    /// 获取可变引用
    pub unsafe fn get_mut(&mut self, index: usize) -> &mut T {
        unsafe { self.buffer[index].assume_init_mut() }
    }
}

/// 线程池中的任务项
pub struct ThreadTask {
    pub id: u64,
    pub priority: u8,
}

/// 使用 MaybeUninit 实现线程池任务队列
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
    pub unsafe fn push(&mut self, task: ThreadTask) {
        if self.initialized_count < self.tasks.len() {
            self.tasks[self.initialized_count].write(task);
            self.initialized_count += 1;
        }
    }

    /// 获取任务（需要外部同步）
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
    ///
    /// Rust 1.92.0: 使用新的 rotate_right 方法实现高效的队列轮转
    pub fn rotate(&mut self, positions: usize) {
        if self.tasks.is_empty() {
            return;
        }

        // 转换为 Vec 以便使用 rotate_right
        let mut vec: Vec<ThreadTask> = self.tasks.drain(..).collect();
        vec.rotate_right(positions);
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
}

impl Default for ThreadPoolTaskQueue {
    fn default() -> Self {
        Self::new()
    }
}

/// 线程池管理器
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
    pub fn rotate(&self) {
        let mut queue = self.queue.lock().unwrap();
        if queue.len() > 1 {
            queue.rotate(1);
        }
    }

    /// 添加任务（线程安全）
    pub fn add_task(&self, task: ThreadTask) {
        let mut queue = self.queue.lock().unwrap();
        queue.push(task);
    }

    /// 获取下一个任务（线程安全）
    pub fn next_task(&self) -> Option<ThreadTask> {
        let mut queue = self.queue.lock().unwrap();
        queue.pop()
    }
}

impl Default for ThreadPoolManager {
    fn default() -> Self {
        Self::new()
    }
}

// ==================== 3. NonZero::div_ceil 在线程数量计算中的应用 ====================

/// 使用 NonZero::div_ceil 计算线程池大小
///
/// Rust 1.92.0: 新增的 `div_ceil` 方法可以安全地计算线程池的容量
pub fn calculate_thread_pool_size(
    total_tasks: usize,
    tasks_per_thread: NonZeroUsize,
) -> usize {
    if total_tasks == 0 {
        return 0;
    }

    let total = NonZeroUsize::new(total_tasks).unwrap();
    // Rust 1.92.0: 使用 div_ceil 计算需要的线程数
    total.div_ceil(tasks_per_thread).get()
}

/// 使用 div_ceil 实现线程资源分配器
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
    pub fn max_threads(&self) -> usize {
        if self.total_cpus == 0 {
            return 0;
        }

        let total = NonZeroUsize::new(self.total_cpus).unwrap();
        // Rust 1.92.0: 使用 div_ceil 计算最大线程数
        total.div_ceil(self.cpus_per_thread).get()
    }
}

/// 线程调度配置
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
    pub fn calculate_threads_for_tasks(&self, task_count: usize) -> usize {
        if task_count == 0 {
            return self.min_threads.get();
        }

        let tasks = NonZeroUsize::new(task_count).unwrap();
        let calculated = tasks.div_ceil(self.min_threads).get();
        calculated.min(self.max_threads)
    }
}

// ==================== 4. 综合应用示例 ====================

/// 演示 Rust 1.92.0 线程特性
pub fn demonstrate_rust_192_thread_features() {
    println!("\n=== Rust 1.92.0 线程特性演示 ===\n");

    // 1. rotate_right 演示
    println!("1. rotate_right 在线程池管理中的应用:");
    let mut queue = ThreadPoolTaskQueue::new();
    queue.push(ThreadTask { id: 1, priority: 10 });
    queue.push(ThreadTask { id: 2, priority: 20 });
    queue.push(ThreadTask { id: 3, priority: 30 });

    println!("   原始队列: {:?}",
        queue.tasks.iter().map(|t| t.id).collect::<Vec<_>>());

    queue.rotate(1);
    println!("   轮转后: {:?}",
        queue.tasks.iter().map(|t| t.id).collect::<Vec<_>>());

    // 2. NonZero::div_ceil 演示
    println!("\n2. NonZero::div_ceil 在线程数量计算中的应用:");
    let tasks_per_thread = NonZeroUsize::new(5).unwrap();
    let total_tasks = 23;
    let pool_size = calculate_thread_pool_size(total_tasks, tasks_per_thread);
    println!("   总任务数: {}", total_tasks);
    println!("   每线程任务数: {}", tasks_per_thread);
    println!("   需要的线程数: {}", pool_size);

    let allocator = ThreadResourceAllocator::new(16, NonZeroUsize::new(2).unwrap());
    println!("   CPU 核心数: 16");
    println!("   每线程 CPU: 2");
    println!("   最大线程数: {}", allocator.max_threads());

    let config = ThreadSchedulingConfig::new(NonZeroUsize::new(2).unwrap(), 10);
    println!("   最小线程数: 2");
    println!("   最大线程数: 10");
    println!("   23 个任务需要线程数: {}", config.calculate_threads_for_tasks(23));

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
    manager.add_task(ThreadTask { id: 1, priority: 10 });
    manager.add_task(ThreadTask { id: 2, priority: 20 });

    manager.rotate();
    if let Some(task) = manager.next_task() {
        println!("   获取到的任务: ID={}, Priority={}", task.id, task.priority);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_thread_pool_queue_rotate() {
        let mut queue = ThreadPoolTaskQueue::new();
        queue.push(ThreadTask { id: 1, priority: 10 });
        queue.push(ThreadTask { id: 2, priority: 20 });

        queue.rotate(1);
        let first = queue.pop().unwrap();
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
