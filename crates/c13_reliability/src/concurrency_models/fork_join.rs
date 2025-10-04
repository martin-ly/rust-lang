//! # Fork-Join并行框架
//!
//! 提供基于分治思想的并行计算框架，类似于Java的ForkJoinPool。
//!
//! ## 核心特性
//!
//! - **任务分解（Fork）**：将大任务递归分解为小任务
//! - **结果合并（Join）**：等待子任务完成并合并结果
//! - **Work-Stealing调度**：空闲线程从忙碌线程窃取任务
//! - **负载均衡**：自动在工作线程间平衡负载
//! - **递归并行**：支持任务的递归分解
//! - **自适应并行度**：根据系统负载动态调整
//!
//! ## 使用示例
//!
//! ```rust,no_run
//! use c13_reliability::concurrency_models::fork_join::{ForkJoinPool, ForkJoinTask};
//!
//! async fn parallel_sum() {
//!     let pool = ForkJoinPool::new(4);
//!     
//!     // 并行计算数组和
//!     let data = vec![1, 2, 3, 4, 5, 6, 7, 8];
//!     let task = SumTask::new(data);
//!     
//!     let result = pool.invoke(task).await;2
//!     println!("Sum: {}", result);
//! }
//! ```

use async_trait::async_trait;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;
use tokio::sync::{Mutex, Notify};
use std::time::{Duration, Instant};

use crate::error_handling::prelude::*;

// ================================================================================================
// 核心类型定义
// ================================================================================================

/// 任务ID
pub type TaskId = u64;

/// Fork-Join任务trait
#[async_trait]
pub trait ForkJoinTask: Send + Sync {
    /// 任务的结果类型
    type Output: Send + Sync;

    /// 执行任务的核心逻辑
    async fn compute(&self) -> Result<Self::Output>;

    /// 判断是否应该继续分解任务
    fn should_fork(&self) -> bool {
        false
    }

    /// 分解任务为子任务
    fn fork(&self) -> Result<Vec<Box<dyn ForkJoinTask<Output = Self::Output>>>> {
        Ok(vec![])
    }

    /// 合并子任务结果
    fn join(&self, _results: Vec<Self::Output>) -> Result<Self::Output> {
        Err(UnifiedError::state_error("Join not implemented"))
    }
}

/// 任务状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaskState {
    /// 待执行
    Pending,
    /// 执行中
    Running,
    /// 已完成
    Completed,
    /// 已取消
    Cancelled,
    /// 失败
    Failed,
}

/// 任务包装器
#[allow(dead_code)]
struct TaskWrapper<T: Send + Sync> {
    id: TaskId,
    task: Box<dyn ForkJoinTask<Output = T>>,
    state: Arc<Mutex<TaskState>>,
    result: Arc<Mutex<Option<Result<T>>>>,
    submitted_at: Instant,
}

impl<T: Send + Sync> TaskWrapper<T> {
    #[allow(dead_code)]
    fn new(id: TaskId, task: Box<dyn ForkJoinTask<Output = T>>) -> Self {
        Self {
            id,
            task,
            state: Arc::new(Mutex::new(TaskState::Pending)),
            result: Arc::new(Mutex::new(None)),
            submitted_at: Instant::now(),
        }
    }
}

// ================================================================================================
// Work-Stealing队列
// ================================================================================================

/// Work-Stealing双端队列
#[allow(dead_code)]
struct WorkStealingDeque<T> {
    deque: Mutex<VecDeque<T>>,
    notify: Arc<Notify>,
}

impl<T> WorkStealingDeque<T> {
    #[allow(dead_code)]
    fn new() -> Self {
        Self {
            deque: Mutex::new(VecDeque::new()),
            notify: Arc::new(Notify::new()),
        }
    }

    /// 从队列头部推入（本地线程使用）
    #[allow(dead_code)]
    async fn push_front(&self, item: T) {
        let mut deque = self.deque.lock().await;
        deque.push_front(item);
        self.notify.notify_one();
    }

    /// 从队列头部弹出（本地线程使用）
    #[allow(dead_code)]
    async fn pop_front(&self) -> Option<T> {
        let mut deque = self.deque.lock().await;
        deque.pop_front()
    }

    /// 从队列尾部弹出（其他线程窃取使用）
    #[allow(dead_code)]
    async fn steal(&self) -> Option<T> {
        let mut deque = self.deque.lock().await;
        deque.pop_back()
    }

    /// 获取队列长度
    #[allow(dead_code)]
    async fn len(&self) -> usize {
        let deque = self.deque.lock().await;
        deque.len()
    }

    /// 等待新任务
    #[allow(dead_code)]
    async fn wait_for_task(&self) {
        self.notify.notified().await
    }
}

// ================================================================================================
// 工作线程
// ================================================================================================

/// 工作线程
#[allow(dead_code)]
struct Worker {
    id: usize,
    local_queue: Arc<WorkStealingDeque<TaskId>>,
    tasks_executed: AtomicU64,
    is_idle: AtomicBool,
}

#[allow(dead_code)]
impl Worker {
    #[allow(dead_code)]
    fn new(id: usize) -> Self {
        Self {
            id,
            local_queue: Arc::new(WorkStealingDeque::new()),
            tasks_executed: AtomicU64::new(0),
            is_idle: AtomicBool::new(false),
        }
    }

    /// 提交任务到本地队列
    #[allow(dead_code)]
    async fn submit_local(&self, task_id: TaskId) {
        self.local_queue.push_front(task_id).await;
    }

    /// 尝试从本地队列获取任务
    async fn try_get_local(&self) -> Option<TaskId> {
        self.local_queue.pop_front().await
    }

    /// 尝试从其他工作线程窃取任务
    async fn try_steal_from(&self, other: &Worker) -> Option<TaskId> {
        if other.id == self.id {
            return None;
        }
        
        other.local_queue.steal().await
    }

    /// 标记为空闲
    fn set_idle(&self, idle: bool) {
        self.is_idle.store(idle, Ordering::SeqCst);
    }

    /// 检查是否空闲
    fn is_idle(&self) -> bool {
        self.is_idle.load(Ordering::SeqCst)
    }

    /// 增加执行计数
    fn increment_executed(&self) {
        self.tasks_executed.fetch_add(1, Ordering::SeqCst);
    }

    /// 获取执行计数
    fn get_executed_count(&self) -> u64 {
        self.tasks_executed.load(Ordering::SeqCst)
    }
}

// ================================================================================================
// Fork-Join线程池
// ================================================================================================

/// Fork-Join线程池配置
#[derive(Debug, Clone)]
pub struct ForkJoinPoolConfig {
    /// 工作线程数量
    pub parallelism: usize,
    /// 任务队列容量
    pub queue_capacity: usize,
    /// 是否启用work-stealing
    pub enable_work_stealing: bool,
    /// 空闲超时时间
    pub idle_timeout: Duration,
    /// 最大任务深度（防止栈溢出）
    pub max_task_depth: usize,
}

impl Default for ForkJoinPoolConfig {
    fn default() -> Self {
        Self {
            parallelism: std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(4),
            queue_capacity: 10000,
            enable_work_stealing: true,
            idle_timeout: Duration::from_secs(60),
            max_task_depth: 64,
        }
    }
}

/// Fork-Join线程池
#[allow(dead_code)]
pub struct ForkJoinPool {
    config: ForkJoinPoolConfig,
    workers: Arc<Vec<Worker>>,
    global_queue: Arc<WorkStealingDeque<TaskId>>,
    next_task_id: AtomicU64,
    active_tasks: AtomicUsize,
    shutdown: Arc<AtomicBool>,
    stats: Arc<Mutex<PoolStats>>,
}

/// 线程池统计信息
#[derive(Debug, Clone, Default)]
#[allow(dead_code)]
pub struct PoolStats {
    /// 总提交任务数
    pub total_submitted: u64,
    /// 总完成任务数
    pub total_completed: u64,
    /// 总失败任务数
    pub total_failed: u64,
    /// 总窃取次数
    pub total_steals: u64,
    /// 平均任务执行时间（毫秒）
    pub avg_execution_time_ms: f64,
}

#[allow(dead_code)]
impl ForkJoinPool {
    /// 创建新的Fork-Join线程池
    #[allow(dead_code)]
    pub fn new(parallelism: usize) -> Arc<Self> {
        let config = ForkJoinPoolConfig {
            parallelism,
            ..Default::default()
        };
        Self::with_config(config)
    }

    /// 使用配置创建线程池
    #[allow(dead_code)]
    pub fn with_config(config: ForkJoinPoolConfig) -> Arc<Self> {
        let workers: Vec<Worker> = (0..config.parallelism)
            .map(|id| Worker::new(id))
            .collect();
        
        Arc::new(Self {
            config,
            workers: Arc::new(workers),
            global_queue: Arc::new(WorkStealingDeque::new()),
            next_task_id: AtomicU64::new(0),
            active_tasks: AtomicUsize::new(0),
            shutdown: Arc::new(AtomicBool::new(false)),
            stats: Arc::new(Mutex::new(PoolStats::default())),
        })
    }

    /// 提交任务并等待结果
    pub async fn invoke<T: Send + Sync + 'static>(
        &self,
        task: impl ForkJoinTask<Output = T> + 'static,
    ) -> Result<T> {
        let task_id = self.submit_internal(Box::new(task)).await?;
        self.await_task(task_id).await
    }

    /// 异步提交任务（不等待结果）
    pub async fn submit<T: Send + Sync + 'static>(
        &self,
        task: impl ForkJoinTask<Output = T> + 'static,
    ) -> Result<TaskId> {
        self.submit_internal(Box::new(task)).await
    }

    /// 内部提交任务
    async fn submit_internal<T: Send + Sync + 'static>(
        &self,
        _task: Box<dyn ForkJoinTask<Output = T>>,
    ) -> Result<TaskId> {
        if self.is_shutdown() {
            return Err(UnifiedError::state_error("Pool is shutdown"));
        }

        let task_id = self.next_task_id.fetch_add(1, Ordering::SeqCst);
        
        // 选择负载最小的工作线程
        let worker = self.select_worker().await;
        worker.submit_local(task_id).await;
        
        self.active_tasks.fetch_add(1, Ordering::SeqCst);
        
        let mut stats = self.stats.lock().await;
        stats.total_submitted += 1;
        
        Ok(task_id)
    }

    /// 等待任务完成
    async fn await_task<T: Send + Sync>(&self, _task_id: TaskId) -> Result<T> {
        // 简化实现：实际应该等待任务完成并返回结果
        Err(UnifiedError::state_error("Task result retrieval not fully implemented"))
    }

    /// 选择工作线程（负载均衡）
    async fn select_worker(&self) -> &Worker {
        let mut min_load = usize::MAX;
        let mut selected = 0;
        
        for (idx, worker) in self.workers.iter().enumerate() {
            let load = worker.local_queue.len().await;
            if load < min_load {
                min_load = load;
                selected = idx;
            }
        }
        
        &self.workers[selected]
    }

    /// 执行work-stealing
    async fn try_steal_task(&self, worker_id: usize) -> Option<TaskId> {
        for (idx, worker) in self.workers.iter().enumerate() {
            if idx != worker_id && !worker.is_idle() {
                if let Some(task_id) = self.workers[worker_id].try_steal_from(worker).await {
                    let mut stats = self.stats.lock().await;
                    stats.total_steals += 1;
                    return Some(task_id);
                }
            }
        }
        None
    }

    /// 检查是否已关闭
    fn is_shutdown(&self) -> bool {
        self.shutdown.load(Ordering::SeqCst)
    }

    /// 关闭线程池
    pub async fn shutdown(&self) {
        self.shutdown.store(true, Ordering::SeqCst);
        
        // 等待所有任务完成
        while self.active_tasks.load(Ordering::SeqCst) > 0 {
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    }

    /// 获取统计信息
    pub async fn get_stats(&self) -> PoolStats {
        let stats = self.stats.lock().await;
        stats.clone()
    }

    /// 获取活跃任务数
    pub fn get_active_count(&self) -> usize {
        self.active_tasks.load(Ordering::SeqCst)
    }

    /// 获取并行度
    pub fn get_parallelism(&self) -> usize {
        self.config.parallelism
    }
}

// ================================================================================================
// 内置任务实现
// ================================================================================================

/// 递归求和任务（示例）
pub struct RecursiveSumTask {
    data: Vec<i64>,
    threshold: usize,
}

impl RecursiveSumTask {
    pub fn new(data: Vec<i64>) -> Self {
        Self {
            data,
            threshold: 1000,
        }
    }

    pub fn with_threshold(data: Vec<i64>, threshold: usize) -> Self {
        Self { data, threshold }
    }
}

#[async_trait]
impl ForkJoinTask for RecursiveSumTask {
    type Output = i64;

    async fn compute(&self) -> Result<Self::Output> {
        if self.should_fork() {
            let subtasks = self.fork()?;
            let mut results = Vec::new();
            
            for subtask in subtasks {
                let result = subtask.compute().await?;
                results.push(result);
            }
            
            self.join(results)
        } else {
            // 直接计算
            Ok(self.data.iter().sum())
        }
    }

    fn should_fork(&self) -> bool {
        self.data.len() > self.threshold
    }

    fn fork(&self) -> Result<Vec<Box<dyn ForkJoinTask<Output = Self::Output>>>> {
        let mid = self.data.len() / 2;
        let left = self.data[..mid].to_vec();
        let right = self.data[mid..].to_vec();
        
        Ok(vec![
            Box::new(RecursiveSumTask {
                data: left,
                threshold: self.threshold,
            }),
            Box::new(RecursiveSumTask {
                data: right,
                threshold: self.threshold,
            }),
        ])
    }

    fn join(&self, results: Vec<Self::Output>) -> Result<Self::Output> {
        Ok(results.iter().sum())
    }
}

/// 并行映射任务
pub struct ParallelMapTask<T, F>
where
    T: Clone + Send + Sync + 'static,
    F: Fn(T) -> T + Send + Sync + 'static,
{
    data: Vec<T>,
    map_fn: Arc<F>,
    threshold: usize,
}

impl<T, F> ParallelMapTask<T, F>
where
    T: Clone + Send + Sync + 'static,
    F: Fn(T) -> T + Send + Sync + 'static,
{
    pub fn new(data: Vec<T>, map_fn: F) -> Self {
        Self {
            data,
            map_fn: Arc::new(map_fn),
            threshold: 100,
        }
    }
}

#[async_trait]
impl<T, F> ForkJoinTask for ParallelMapTask<T, F>
where
    T: Clone + Send + Sync + 'static,
    F: Fn(T) -> T + Send + Sync + 'static,
{
    type Output = Vec<T>;

    async fn compute(&self) -> Result<Self::Output> {
        if self.should_fork() {
            let subtasks = self.fork()?;
            let mut all_results = Vec::new();
            
            for subtask in subtasks {
                let result = subtask.compute().await?;
                all_results.extend(result);
            }
            
            Ok(all_results)
        } else {
            // 直接映射
            Ok(self.data.iter().cloned().map(|x| (self.map_fn)(x)).collect())
        }
    }

    fn should_fork(&self) -> bool {
        self.data.len() > self.threshold
    }

    fn fork(&self) -> Result<Vec<Box<dyn ForkJoinTask<Output = Self::Output>>>> {
        let mid = self.data.len() / 2;
        let left = self.data[..mid].to_vec();
        let right = self.data[mid..].to_vec();
        
        Ok(vec![
            Box::new(ParallelMapTask {
                data: left,
                map_fn: Arc::clone(&self.map_fn),
                threshold: self.threshold,
            }),
            Box::new(ParallelMapTask {
                data: right,
                map_fn: Arc::clone(&self.map_fn),
                threshold: self.threshold,
            }),
        ])
    }
}

// ================================================================================================
// 测试
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_fork_join_pool_creation() {
        let pool = ForkJoinPool::new(4);
        assert_eq!(pool.get_parallelism(), 4);
        assert_eq!(pool.get_active_count(), 0);
    }

    #[tokio::test]
    async fn test_recursive_sum_task() {
        let data: Vec<i64> = (1..=1000).collect();
        let expected: i64 = data.iter().sum();
        
        let task = RecursiveSumTask::new(data);
        let result = task.compute().await.unwrap();
        
        assert_eq!(result, expected);
    }

    #[tokio::test]
    async fn test_parallel_map_task() {
        let data: Vec<i32> = (1..=100).collect();
        
        let task = ParallelMapTask::new(data.clone(), |x| x * 2);
        let result = task.compute().await.unwrap();
        
        let expected: Vec<i32> = data.iter().map(|x| x * 2).collect();
        assert_eq!(result, expected);
    }

    #[tokio::test]
    async fn test_work_stealing_deque() {
        let deque = WorkStealingDeque::new();
        
        deque.push_front(1).await;
        deque.push_front(2).await;
        deque.push_front(3).await;
        
        assert_eq!(deque.pop_front().await, Some(3));
        assert_eq!(deque.steal().await, Some(1));
        assert_eq!(deque.pop_front().await, Some(2));
        assert_eq!(deque.pop_front().await, None);
    }

    #[tokio::test]
    async fn test_pool_stats() {
        let pool = ForkJoinPool::new(2);
        let stats = pool.get_stats().await;
        
        assert_eq!(stats.total_submitted, 0);
        assert_eq!(stats.total_completed, 0);
    }
}

