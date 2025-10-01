//! 异步模型和消息队列背压模型
//! 
//! 本模块实现了现代异步编程模型，包括：
//! - 异步运行时模型
//! - 背压控制模型
//! - 流量控制模型
//! - 消息队列模型
//! - 异步状态机模型
//! - 协程调度模型
//! 
//! 充分利用 Rust 1.90 的异步改进和新特性

use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex, RwLock};
use std::time::{Duration, Instant};
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
use std::future::Future;
use serde::{Deserialize, Serialize};
use crate::error::ModelError;

#[cfg(feature = "tokio-adapter")]
use tokio::sync::Semaphore;
#[cfg(feature = "tokio-adapter")]
use tokio::time::sleep;

/// 异步模型的结果类型
pub type AsyncResult<T> = Result<T, ModelError>;

/// 异步运行时类型
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum RuntimeType {
    /// 单线程运行时
    SingleThreaded,
    /// 多线程运行时
    MultiThreaded { worker_threads: usize },
    /// 当前线程运行时
    CurrentThread,
    /// 自定义运行时
    Custom(String),
}

/// 异步任务状态
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum TaskState {
    /// 待执行
    Pending,
    /// 正在执行
    Running,
    /// 已完成
    Completed,
    /// 已取消
    Cancelled,
    /// 执行失败
    Failed(String),
}

/// 异步任务优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum TaskPriority {
    Low = 0,
    Normal = 1,
    High = 2,
    Critical = 3,
}

/// 异步任务元数据
#[derive(Debug, Clone)]
pub struct TaskMetadata {
    pub id: String,
    pub name: String,
    pub priority: TaskPriority,
    pub state: TaskState,
    pub created_at: Instant,
    pub started_at: Option<Instant>,
    pub completed_at: Option<Instant>,
    pub execution_time: Option<Duration>,
    pub retry_count: u32,
    pub max_retries: u32,
}

impl TaskMetadata {
    pub fn new(id: String, name: String, priority: TaskPriority) -> Self {
        Self {
            id,
            name,
            priority,
            state: TaskState::Pending,
            created_at: Instant::now(),
            started_at: None,
            completed_at: None,
            execution_time: None,
            retry_count: 0,
            max_retries: 3,
        }
    }
    
    pub fn start(&mut self) {
        self.state = TaskState::Running;
        self.started_at = Some(Instant::now());
    }
    
    pub fn complete(&mut self) {
        self.state = TaskState::Completed;
        let now = Instant::now();
        self.completed_at = Some(now);
        if let Some(started) = self.started_at {
            self.execution_time = Some(now - started);
        }
    }
    
    pub fn fail(&mut self, error: String) {
        self.state = TaskState::Failed(error);
        let now = Instant::now();
        self.completed_at = Some(now);
        if let Some(started) = self.started_at {
            self.execution_time = Some(now - started);
        }
    }
    
    pub fn cancel(&mut self) {
        self.state = TaskState::Cancelled;
        self.completed_at = Some(Instant::now());
    }
    
    pub fn should_retry(&self) -> bool {
        matches!(self.state, TaskState::Failed(_)) && self.retry_count < self.max_retries
    }
    
    pub fn increment_retry(&mut self) {
        self.retry_count += 1;
        self.state = TaskState::Pending;
    }
}

/// 背压策略
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum BackpressureStrategy {
    /// 丢弃最新消息
    DropNewest,
    /// 丢弃最旧消息
    DropOldest,
    /// 阻塞发送者
    Block,
    /// 缓冲到磁盘
    BufferToDisk,
    /// 拒绝新消息
    Reject,
    /// 动态调整
    Adaptive,
}

/// 流量控制配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FlowControlConfig {
    /// 最大缓冲区大小
    pub max_buffer_size: usize,
    /// 背压阈值（缓冲区使用率）
    pub backpressure_threshold: f64,
    /// 背压策略
    pub strategy: BackpressureStrategy,
    /// 批处理大小
    pub batch_size: usize,
    /// 批处理超时
    pub batch_timeout: Duration,
    /// 重试配置
    pub retry_config: RetryConfig,
}

impl Default for FlowControlConfig {
    fn default() -> Self {
        Self {
            max_buffer_size: 1000,
            backpressure_threshold: 0.8,
            strategy: BackpressureStrategy::Block,
            batch_size: 10,
            batch_timeout: Duration::from_millis(100),
            retry_config: RetryConfig::default(),
        }
    }
}

/// 重试配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryConfig {
    pub max_retries: u32,
    pub initial_delay: Duration,
    pub max_delay: Duration,
    pub backoff_multiplier: f64,
    pub jitter: bool,
}

impl Default for RetryConfig {
    fn default() -> Self {
        Self {
            max_retries: 3,
            initial_delay: Duration::from_millis(100),
            max_delay: Duration::from_secs(30),
            backoff_multiplier: 2.0,
            jitter: true,
        }
    }
}

/// 消息队列统计信息
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct QueueMetrics {
    pub total_messages: u64,
    pub processed_messages: u64,
    pub failed_messages: u64,
    pub dropped_messages: u64,
    pub current_queue_size: usize,
    pub max_queue_size: usize,
    pub average_processing_time: Duration,
    pub throughput_per_second: f64,
    pub backpressure_events: u64,
}

impl QueueMetrics {
    pub fn update_processing_time(&mut self, duration: Duration) {
        let total_time = self.average_processing_time.as_nanos() as f64 * self.processed_messages as f64;
        self.processed_messages += 1;
        let new_total = total_time + duration.as_nanos() as f64;
        self.average_processing_time = Duration::from_nanos((new_total / self.processed_messages as f64) as u64);
    }
    
    pub fn calculate_throughput(&mut self, window_duration: Duration) {
        if window_duration.as_secs_f64() > 0.0 {
            self.throughput_per_second = self.processed_messages as f64 / window_duration.as_secs_f64();
        }
    }
    
    pub fn buffer_utilization(&self) -> f64 {
        if self.max_queue_size > 0 {
            self.current_queue_size as f64 / self.max_queue_size as f64
        } else {
            0.0
        }
    }
}

/// 异步消息
#[derive(Debug, Clone)]
pub struct AsyncMessage<T> {
    pub id: String,
    pub payload: T,
    pub priority: TaskPriority,
    pub created_at: Instant,
    pub retry_count: u32,
    pub max_retries: u32,
    pub timeout: Option<Duration>,
}

impl<T> AsyncMessage<T> {
    pub fn new(payload: T) -> Self {
        Self {
            id: uuid::Uuid::new_v4().to_string(),
            payload,
            priority: TaskPriority::Normal,
            created_at: Instant::now(),
            retry_count: 0,
            max_retries: 3,
            timeout: None,
        }
    }
    
    pub fn with_priority(mut self, priority: TaskPriority) -> Self {
        self.priority = priority;
        self
    }
    
    pub fn with_timeout(mut self, timeout: Duration) -> Self {
        self.timeout = Some(timeout);
        self
    }
    
    pub fn with_retries(mut self, max_retries: u32) -> Self {
        self.max_retries = max_retries;
        self
    }
    
    pub fn is_expired(&self) -> bool {
        if let Some(timeout) = self.timeout {
            self.created_at.elapsed() > timeout
        } else {
            false
        }
    }
    
    pub fn should_retry(&self) -> bool {
        self.retry_count < self.max_retries
    }
    
    pub fn increment_retry(&mut self) {
        self.retry_count += 1;
    }
}

/// 异步消息队列
#[derive(Debug)]
pub struct AsyncMessageQueue<T> {
    buffer: Arc<Mutex<VecDeque<AsyncMessage<T>>>>,
    config: FlowControlConfig,
    metrics: Arc<RwLock<QueueMetrics>>,
    wakers: Arc<Mutex<Vec<Waker>>>,
    is_closed: Arc<Mutex<bool>>,
}

impl<T> AsyncMessageQueue<T>
where
    T: Clone + Send + 'static,
{
    pub fn new(config: FlowControlConfig) -> Self {
        let mut metrics = QueueMetrics::default();
        metrics.max_queue_size = config.max_buffer_size;
        
        Self {
            buffer: Arc::new(Mutex::new(VecDeque::new())),
            config,
            metrics: Arc::new(RwLock::new(metrics)),
            wakers: Arc::new(Mutex::new(Vec::new())),
            is_closed: Arc::new(Mutex::new(false)),
        }
    }
    
    /// 发送消息（异步）
    pub async fn send(&self, message: AsyncMessage<T>) -> AsyncResult<()> {
        if *self.is_closed.lock().unwrap() {
            return Err(ModelError::AsyncError("Queue is closed".to_string()));
        }
        
        // 检查背压
        let should_apply_backpressure = {
            let buffer = self.buffer.lock().unwrap();
            let utilization = buffer.len() as f64 / self.config.max_buffer_size as f64;
            utilization >= self.config.backpressure_threshold
        };
        
        if should_apply_backpressure {
            self.handle_backpressure(&message).await?;
        }
        
        // 添加消息到缓冲区
        {
            let mut buffer = self.buffer.lock().unwrap();
            
            // 检查容量
            if buffer.len() >= self.config.max_buffer_size {
                match self.config.strategy {
                    BackpressureStrategy::DropNewest => {
                        self.update_metrics(|m| m.dropped_messages += 1);
                        return Ok(());
                    }
                    BackpressureStrategy::DropOldest => {
                        buffer.pop_front();
                        self.update_metrics(|m| m.dropped_messages += 1);
                    }
                    BackpressureStrategy::Reject => {
                        return Err(ModelError::AsyncError("Queue is full".to_string()));
                    }
                    _ => {
                        // 其他策略在 handle_backpressure 中处理
                    }
                }
            }
            
            // 按优先级插入
            let insert_pos = buffer
                .iter()
                .position(|m| m.priority < message.priority)
                .unwrap_or(buffer.len());
            
            buffer.insert(insert_pos, message);
            
            self.update_metrics(|m| {
                m.total_messages += 1;
                m.current_queue_size = buffer.len();
            });
        }
        
        // 唤醒等待的接收者
        self.wake_receivers();
        
        Ok(())
    }
    
    /// 接收消息（异步）
    pub async fn receive(&self) -> AsyncResult<AsyncMessage<T>> {
        loop {
            // 尝试从缓冲区获取消息
            if let Some(message) = self.try_receive()? {
                return Ok(message);
            }
            
            // 如果队列已关闭且为空，返回错误
            if *self.is_closed.lock().unwrap() {
                return Err(ModelError::AsyncError("Queue is closed and empty".to_string()));
            }
            
            // 等待新消息
            ReceiveFuture::new(self).await?;
        }
    }
    
    /// 尝试接收消息（非阻塞）
    pub fn try_receive(&self) -> AsyncResult<Option<AsyncMessage<T>>> {
        let mut buffer = self.buffer.lock().unwrap();
        
        // 清理过期消息
        while let Some(front) = buffer.front() {
            if front.is_expired() {
                buffer.pop_front();
                self.update_metrics(|m| {
                    m.dropped_messages += 1;
                    m.current_queue_size = buffer.len();
                });
            } else {
                break;
            }
        }
        
        if let Some(message) = buffer.pop_front() {
            self.update_metrics(|m| {
                m.processed_messages += 1;
                m.current_queue_size = buffer.len();
            });
            Ok(Some(message))
        } else {
            Ok(None)
        }
    }
    
    /// 批量接收消息
    pub async fn receive_batch(&self, max_size: usize) -> AsyncResult<Vec<AsyncMessage<T>>> {
        let mut batch = Vec::new();
        let batch_size = max_size.min(self.config.batch_size);
        
        // 首先尝试获取一个消息（阻塞）
        let first_message = self.receive().await?;
        batch.push(first_message);
        
        // 然后尝试获取更多消息（非阻塞）
        for _ in 1..batch_size {
            if let Some(message) = self.try_receive()? {
                batch.push(message);
            } else {
                break;
            }
        }
        
        Ok(batch)
    }
    
    /// 关闭队列
    pub fn close(&self) {
        *self.is_closed.lock().unwrap() = true;
        self.wake_receivers();
    }
    
    /// 获取队列统计信息
    pub fn metrics(&self) -> QueueMetrics {
        self.metrics.read().unwrap().clone()
    }
    
    /// 获取队列大小
    pub fn len(&self) -> usize {
        self.buffer.lock().unwrap().len()
    }
    
    /// 检查队列是否为空
    pub fn is_empty(&self) -> bool {
        self.buffer.lock().unwrap().is_empty()
    }
    
    /// 检查队列是否已关闭
    pub fn is_closed(&self) -> bool {
        *self.is_closed.lock().unwrap()
    }
    
    // 私有辅助方法
    async fn handle_backpressure(&self, _message: &AsyncMessage<T>) -> AsyncResult<()> {
        self.update_metrics(|m| m.backpressure_events += 1);
        
        match self.config.strategy {
            BackpressureStrategy::Block => {
                // 等待缓冲区有空间
                while {
                    let buffer = self.buffer.lock().unwrap();
                    buffer.len() >= self.config.max_buffer_size
                } {
                    #[cfg(feature = "tokio-adapter")]
                    tokio::task::yield_now().await;
                    #[cfg(not(feature = "tokio-adapter"))]
                    std::thread::yield_now();
                }
            }
            BackpressureStrategy::BufferToDisk => {
                // 简化实现：记录到日志
                eprintln!("Backpressure: would buffer to disk");
            }
            BackpressureStrategy::Adaptive => {
                // 动态调整批处理大小
                let utilization = {
                    let buffer = self.buffer.lock().unwrap();
                    buffer.len() as f64 / self.config.max_buffer_size as f64
                };
                
                if utilization > 0.9 {
                    #[cfg(feature = "tokio-adapter")]
                    sleep(Duration::from_millis(10)).await;
                }
            }
            _ => {} // 其他策略在调用处处理
        }
        
        Ok(())
    }
    
    fn wake_receivers(&self) {
        let mut wakers = self.wakers.lock().unwrap();
        for waker in wakers.drain(..) {
            waker.wake();
        }
    }
    
    fn update_metrics<F>(&self, f: F)
    where
        F: FnOnce(&mut QueueMetrics),
    {
        if let Ok(mut metrics) = self.metrics.write() {
            f(&mut metrics);
        }
    }
}

impl<T> Clone for AsyncMessageQueue<T> {
    fn clone(&self) -> Self {
        Self {
            buffer: Arc::clone(&self.buffer),
            config: self.config.clone(),
            metrics: Arc::clone(&self.metrics),
            wakers: Arc::clone(&self.wakers),
            is_closed: Arc::clone(&self.is_closed),
        }
    }
}

/// 接收消息的 Future
struct ReceiveFuture<'a, T> {
    queue: &'a AsyncMessageQueue<T>,
}

impl<'a, T> ReceiveFuture<'a, T> {
    fn new(queue: &'a AsyncMessageQueue<T>) -> Self {
        Self { queue }
    }
}

impl<'a, T> Future for ReceiveFuture<'a, T> {
    type Output = AsyncResult<()>;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        // 检查是否有消息可用
        if !self.queue.buffer.lock().unwrap().is_empty() {
            return Poll::Ready(Ok(()));
        }
        
        // 检查队列是否已关闭
        if *self.queue.is_closed.lock().unwrap() {
            return Poll::Ready(Err(ModelError::AsyncError("Queue is closed".to_string())));
        }
        
        // 注册 waker
        self.queue.wakers.lock().unwrap().push(cx.waker().clone());
        
        Poll::Pending
    }
}

/// 异步任务调度器
#[allow(dead_code)]
#[derive(Debug)]
pub struct AsyncTaskScheduler {
    tasks: Arc<RwLock<HashMap<String, TaskMetadata>>>,
    pending_tasks: Arc<Mutex<VecDeque<String>>>,
    running_tasks: Arc<RwLock<HashSet<String>>>,
    max_concurrent_tasks: usize,
    #[cfg(feature = "tokio-adapter")]
    semaphore: Arc<Semaphore>,
}

use std::collections::HashSet;

impl AsyncTaskScheduler {
    pub fn new(max_concurrent_tasks: usize) -> Self {
        Self {
            tasks: Arc::new(RwLock::new(HashMap::new())),
            pending_tasks: Arc::new(Mutex::new(VecDeque::new())),
            running_tasks: Arc::new(RwLock::new(HashSet::new())),
            max_concurrent_tasks,
            #[cfg(feature = "tokio-adapter")]
            semaphore: Arc::new(Semaphore::new(max_concurrent_tasks)),
        }
    }
    
    /// 提交任务
    pub async fn submit_task<F, Fut, T>(
        &self,
        name: String,
        priority: TaskPriority,
        task: F,
    ) -> AsyncResult<T>
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = AsyncResult<T>> + Send + 'static,
        T: Send + 'static,
    {
        let task_id = uuid::Uuid::new_v4().to_string();
        let metadata = TaskMetadata::new(task_id.clone(), name, priority);
        
        // 添加任务元数据
        self.tasks.write().unwrap().insert(task_id.clone(), metadata);
        
        // 添加到待执行队列
        {
            let mut pending = self.pending_tasks.lock().unwrap();
            // 按优先级插入
            let insert_pos = pending
                .iter()
                .position(|id| {
                    if let Some(task_meta) = self.tasks.read().unwrap().get(id) {
                        task_meta.priority < priority
                    } else {
                        true
                    }
                })
                .unwrap_or(pending.len());
            pending.insert(insert_pos, task_id.clone());
        }
        
        // 执行任务
        self.execute_task(task_id, task).await
    }
    
    /// 执行任务
    async fn execute_task<F, Fut, T>(
        &self,
        task_id: String,
        task: F,
    ) -> AsyncResult<T>
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = AsyncResult<T>> + Send + 'static,
        T: Send + 'static,
    {
        // 等待执行槽位
        #[cfg(feature = "tokio-adapter")]
        let _permit = self.semaphore.acquire().await.map_err(|e| {
            ModelError::AsyncError(format!("Failed to acquire semaphore: {}", e))
        })?;
        
        // 更新任务状态
        if let Some(metadata) = self.tasks.write().unwrap().get_mut(&task_id) {
            metadata.start();
        }
        
        // 添加到运行中任务
        self.running_tasks.write().unwrap().insert(task_id.clone());
        
        // 执行任务
        let start_time = Instant::now();
        let result = task().await;
        let execution_time = start_time.elapsed();
        
        // 更新任务状态
        {
            let mut tasks = self.tasks.write().unwrap();
            if let Some(metadata) = tasks.get_mut(&task_id) {
                match &result {
                    Ok(_) => metadata.complete(),
                    Err(e) => metadata.fail(e.to_string()),
                }
                metadata.execution_time = Some(execution_time);
            }
        }
        
        // 从运行中任务移除
        self.running_tasks.write().unwrap().remove(&task_id);
        
        result
    }
    
    /// 取消任务
    pub fn cancel_task(&self, task_id: &str) -> AsyncResult<()> {
        if let Some(metadata) = self.tasks.write().unwrap().get_mut(task_id) {
            if matches!(metadata.state, TaskState::Pending | TaskState::Running) {
                metadata.cancel();
                
                // 从待执行队列移除
                let mut pending = self.pending_tasks.lock().unwrap();
                if let Some(pos) = pending.iter().position(|id| id == task_id) {
                    pending.remove(pos);
                }
                
                Ok(())
            } else {
                Err(ModelError::AsyncError("Task cannot be cancelled".to_string()))
            }
        } else {
            Err(ModelError::AsyncError("Task not found".to_string()))
        }
    }
    
    /// 获取任务状态
    pub fn get_task_status(&self, task_id: &str) -> Option<TaskMetadata> {
        self.tasks.read().unwrap().get(task_id).cloned()
    }
    
    /// 获取所有任务状态
    pub fn get_all_tasks(&self) -> Vec<TaskMetadata> {
        self.tasks.read().unwrap().values().cloned().collect()
    }
    
    /// 获取运行中的任务数量
    pub fn running_task_count(&self) -> usize {
        self.running_tasks.read().unwrap().len()
    }
    
    /// 获取待执行的任务数量
    pub fn pending_task_count(&self) -> usize {
        self.pending_tasks.lock().unwrap().len()
    }
    
    /// 清理已完成的任务
    pub fn cleanup_completed_tasks(&self) {
        let mut tasks = self.tasks.write().unwrap();
        tasks.retain(|_, metadata| {
            !matches!(
                metadata.state,
                TaskState::Completed | TaskState::Cancelled | TaskState::Failed(_)
            )
        });
    }
}

/// 异步状态机
#[derive(Debug, Clone)]
pub struct AsyncStateMachine<S, E> 
where
    S: Clone + Eq + std::hash::Hash,
    E: Clone + Eq + std::hash::Hash,
{
    current_state: S,
    transitions: HashMap<(S, E), S>,
    state_handlers: HashMap<S, String>, // 简化：使用字符串表示处理器
}

impl<S, E> AsyncStateMachine<S, E>
where
    S: Clone + Eq + std::hash::Hash + Send + 'static + std::fmt::Debug,
    E: Clone + Eq + std::hash::Hash + Send + 'static,
{
    pub fn new(initial_state: S) -> Self {
        Self {
            current_state: initial_state,
            transitions: HashMap::new(),
            state_handlers: HashMap::new(),
        }
    }
    
    /// 添加状态转换
    pub fn add_transition(&mut self, from: S, event: E, to: S) {
        self.transitions.insert((from, event), to);
    }
    
    /// 添加状态处理器
    pub fn add_state_handler(&mut self, state: S, handler: String) {
        self.state_handlers.insert(state, handler);
    }
    
    /// 处理事件
    pub async fn handle_event(&mut self, event: E) -> AsyncResult<()> {
        let key = (self.current_state.clone(), event);
        
        if let Some(next_state) = self.transitions.get(&key) {
            let old_state = self.current_state.clone();
            self.current_state = next_state.clone();
            
            // 执行状态处理器
            if let Some(_handler) = self.state_handlers.get(&self.current_state) {
                // 这里可以执行实际的异步处理逻辑
                #[cfg(feature = "tokio-adapter")]
                tokio::task::yield_now().await;
            }
            
            println!("State transition: {:?} -> {:?}", old_state, self.current_state);
            Ok(())
        } else {
            Err(ModelError::AsyncError(format!(
                "No transition defined for current state and event"
            )))
        }
    }
    
    /// 获取当前状态
    pub fn current_state(&self) -> &S {
        &self.current_state
    }
    
    /// 检查是否可以处理事件
    pub fn can_handle_event(&self, event: &E) -> bool {
        let key = (self.current_state.clone(), event.clone());
        self.transitions.contains_key(&key)
    }
}

/// 协程池
#[derive(Debug)]
pub struct CoroutinePool {
    pool_size: usize,
    active_coroutines: Arc<RwLock<usize>>,
    #[cfg(feature = "tokio-adapter")]
    semaphore: Arc<Semaphore>,
}

impl CoroutinePool {
    pub fn new(pool_size: usize) -> Self {
        Self {
            pool_size,
            active_coroutines: Arc::new(RwLock::new(0)),
            #[cfg(feature = "tokio-adapter")]
            semaphore: Arc::new(Semaphore::new(pool_size)),
        }
    }
    
    /// 执行协程
    pub async fn execute<F, Fut, T>(&self, coroutine: F) -> AsyncResult<T>
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = AsyncResult<T>> + Send + 'static,
        T: Send + 'static,
    {
        // 等待可用槽位
        #[cfg(feature = "tokio-adapter")]
        let _permit = self.semaphore.acquire().await.map_err(|e| {
            ModelError::AsyncError(format!("Failed to acquire coroutine slot: {}", e))
        })?;
        
        // 增加活跃协程计数
        *self.active_coroutines.write().unwrap() += 1;
        
        // 执行协程
        let result = coroutine().await;
        
        // 减少活跃协程计数
        *self.active_coroutines.write().unwrap() -= 1;
        
        result
    }
    
    /// 获取活跃协程数量
    pub fn active_count(&self) -> usize {
        *self.active_coroutines.read().unwrap()
    }
    
    /// 获取池大小
    pub fn pool_size(&self) -> usize {
        self.pool_size
    }
    
    /// 检查是否有可用槽位
    pub fn has_available_slot(&self) -> bool {
        self.active_count() < self.pool_size
    }
}

/// 异步模型引擎
#[allow(dead_code)]
#[derive(Debug)]
pub struct AsyncModelEngine {
    runtime_type: RuntimeType,
    task_scheduler: AsyncTaskScheduler,
    coroutine_pool: CoroutinePool,
    message_queues: Arc<RwLock<HashMap<String, Box<dyn std::any::Any + Send + Sync>>>>,
}

impl AsyncModelEngine {
    pub fn new(runtime_type: RuntimeType, max_concurrent_tasks: usize) -> Self {
        Self {
            runtime_type,
            task_scheduler: AsyncTaskScheduler::new(max_concurrent_tasks),
            coroutine_pool: CoroutinePool::new(max_concurrent_tasks),
            message_queues: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 创建消息队列
    pub fn create_message_queue<T>(&self, name: String, config: FlowControlConfig) -> AsyncMessageQueue<T>
    where
        T: Clone + Send + Sync + 'static,
    {
        let queue = AsyncMessageQueue::new(config);
        
        // 存储队列引用（简化实现）
        self.message_queues.write().unwrap().insert(
            name,
            Box::new(queue.clone()),
        );
        
        queue
    }
    
    /// 提交任务到调度器
    pub async fn submit_task<F, Fut, T>(
        &self,
        name: String,
        priority: TaskPriority,
        task: F,
    ) -> AsyncResult<T>
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = AsyncResult<T>> + Send + 'static,
        T: Send + 'static,
    {
        self.task_scheduler.submit_task(name, priority, task).await
    }
    
    /// 执行协程
    pub async fn execute_coroutine<F, Fut, T>(&self, coroutine: F) -> AsyncResult<T>
    where
        F: FnOnce() -> Fut + Send + 'static,
        Fut: Future<Output = AsyncResult<T>> + Send + 'static,
        T: Send + 'static,
    {
        self.coroutine_pool.execute(coroutine).await
    }
    
    /// 获取运行时信息
    pub fn runtime_info(&self) -> RuntimeInfo {
        RuntimeInfo {
            runtime_type: self.runtime_type.clone(),
            active_tasks: self.task_scheduler.running_task_count(),
            pending_tasks: self.task_scheduler.pending_task_count(),
            active_coroutines: self.coroutine_pool.active_count(),
            total_coroutine_slots: self.coroutine_pool.pool_size(),
            message_queue_count: self.message_queues.read().unwrap().len(),
        }
    }
}

/// 运行时信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RuntimeInfo {
    pub runtime_type: RuntimeType,
    pub active_tasks: usize,
    pub pending_tasks: usize,
    pub active_coroutines: usize,
    pub total_coroutine_slots: usize,
    pub message_queue_count: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    #[cfg(feature = "tokio-adapter")]
    async fn test_async_message_queue() {
        let config = FlowControlConfig::default();
        let queue = AsyncMessageQueue::new(config);
        
        // 发送消息
        let message = AsyncMessage::new("test message".to_string());
        queue.send(message).await.unwrap();
        
        // 接收消息
        let received = queue.receive().await.unwrap();
        assert_eq!(received.payload, "test message");
        
        // 检查队列为空
        assert!(queue.is_empty());
    }
    
    #[tokio::test]
    #[cfg(feature = "tokio-adapter")]
    async fn test_task_scheduler() {
        let scheduler = AsyncTaskScheduler::new(2);
        
        let result = scheduler.submit_task(
            "test_task".to_string(),
            TaskPriority::Normal,
            || async { Ok("task result".to_string()) },
        ).await.unwrap();
        
        assert_eq!(result, "task result");
    }
    
    #[tokio::test]
    #[cfg(feature = "tokio-adapter")]
    async fn test_async_state_machine() {
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        enum State {
            Idle,
            Running,
            Completed,
        }
        
        #[derive(Debug, Clone, PartialEq, Eq, Hash)]
        enum Event {
            Start,
            Finish,
        }
        
        let mut fsm = AsyncStateMachine::new(State::Idle);
        fsm.add_transition(State::Idle, Event::Start, State::Running);
        fsm.add_transition(State::Running, Event::Finish, State::Completed);
        
        assert_eq!(*fsm.current_state(), State::Idle);
        
        fsm.handle_event(Event::Start).await.unwrap();
        assert_eq!(*fsm.current_state(), State::Running);
        
        fsm.handle_event(Event::Finish).await.unwrap();
        assert_eq!(*fsm.current_state(), State::Completed);
    }
    
    #[tokio::test]
    #[cfg(feature = "tokio-adapter")]
    async fn test_coroutine_pool() {
        let pool = CoroutinePool::new(2);
        
        let result = pool.execute(|| async {
            Ok("coroutine result".to_string())
        }).await.unwrap();
        
        assert_eq!(result, "coroutine result");
    }
    
    #[test]
    fn test_backpressure_strategies() {
        let mut config = FlowControlConfig::default();
        config.strategy = BackpressureStrategy::DropNewest;
        
        assert_eq!(config.strategy, BackpressureStrategy::DropNewest);
        
        config.strategy = BackpressureStrategy::Block;
        assert_eq!(config.strategy, BackpressureStrategy::Block);
    }
    
    #[test]
    fn test_task_metadata() {
        let mut metadata = TaskMetadata::new(
            "test_id".to_string(),
            "test_task".to_string(),
            TaskPriority::High,
        );
        
        assert_eq!(metadata.state, TaskState::Pending);
        
        metadata.start();
        assert_eq!(metadata.state, TaskState::Running);
        assert!(metadata.started_at.is_some());
        
        metadata.complete();
        assert_eq!(metadata.state, TaskState::Completed);
        assert!(metadata.completed_at.is_some());
        assert!(metadata.execution_time.is_some());
    }
    
    #[test]
    fn test_token_bucket() {
        let bucket = TokenBucket::new(10.0, 100);
        assert_eq!(bucket.tokens(), 100);
        
        assert!(bucket.try_acquire(50).is_ok());
        assert_eq!(bucket.tokens(), 50);
        
        assert!(bucket.try_acquire(60).is_err());
        assert_eq!(bucket.tokens(), 50);
    }
    
    #[test]
    fn test_leaky_bucket() {
        let bucket = LeakyBucket::new(10.0, 100);
        assert_eq!(bucket.size(), 0);
        
        assert!(bucket.try_add(50).is_ok());
        assert_eq!(bucket.size(), 50);
    }
}

// ========== 高级流量控制算法 ==========

/// 令牌桶算法 (Token Bucket)
/// 
/// 用于流量整形和限流，允许一定程度的突发流量
/// 
/// # 特点
/// - 允许突发流量（桶内有足够令牌时）
/// - 平滑限流（令牌以恒定速率补充）
/// - 灵活配置（桶容量和令牌生成速率）
#[derive(Debug, Clone)]
pub struct TokenBucket {
    /// 令牌生成速率 (tokens/second)
    rate: f64,
    /// 桶容量（最大令牌数）
    capacity: usize,
    /// 当前令牌数
    tokens: Arc<Mutex<f64>>,
    /// 上次更新时间
    last_update: Arc<Mutex<Instant>>,
}

impl TokenBucket {
    /// 创建新的令牌桶
    pub fn new(rate: f64, capacity: usize) -> Self {
        Self {
            rate,
            capacity,
            tokens: Arc::new(Mutex::new(capacity as f64)),
            last_update: Arc::new(Mutex::new(Instant::now())),
        }
    }
    
    /// 尝试获取指定数量的令牌
    pub fn try_acquire(&self, count: usize) -> AsyncResult<()> {
        self.refill()?;
        
        let mut tokens = self.tokens.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock tokens: {}", e)))?;
        
        if *tokens >= count as f64 {
            *tokens -= count as f64;
            Ok(())
        } else {
            Err(ModelError::RateLimitExceeded(format!(
                "Insufficient tokens: need {}, have {:.2}",
                count, *tokens
            )))
        }
    }
    
    /// 阻塞等待直到获取到令牌
    #[cfg(feature = "tokio-adapter")]
    pub async fn acquire(&self, count: usize) -> AsyncResult<()> {
        loop {
            match self.try_acquire(count) {
                Ok(()) => return Ok(()),
                Err(_) => {
                    // 计算需要等待的时间
                    let wait_time = self.calculate_wait_time(count)?;
                    sleep(wait_time).await;
                }
            }
        }
    }
    
    /// 补充令牌
    fn refill(&self) -> AsyncResult<()> {
        let now = Instant::now();
        let mut last_update = self.last_update.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock last_update: {}", e)))?;
        
        let elapsed = now.duration_since(*last_update).as_secs_f64();
        let new_tokens = elapsed * self.rate;
        
        if new_tokens > 0.0 {
            let mut tokens = self.tokens.lock()
                .map_err(|e| ModelError::LockError(format!("Failed to lock tokens: {}", e)))?;
            
            *tokens = (*tokens + new_tokens).min(self.capacity as f64);
            *last_update = now;
        }
        
        Ok(())
    }
    
    /// 计算等待时间
    fn calculate_wait_time(&self, count: usize) -> AsyncResult<Duration> {
        let tokens = self.tokens.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock tokens: {}", e)))?;
        
        let deficit = (count as f64 - *tokens).max(0.0);
        let wait_secs = deficit / self.rate;
        
        Ok(Duration::from_secs_f64(wait_secs))
    }
    
    /// 获取当前令牌数
    pub fn tokens(&self) -> usize {
        self.tokens.lock()
            .map(|t| *t as usize)
            .unwrap_or(0)
    }
    
    /// 获取桶容量
    pub fn capacity(&self) -> usize {
        self.capacity
    }
    
    /// 获取令牌生成速率
    pub fn rate(&self) -> f64 {
        self.rate
    }
}

/// 漏桶算法 (Leaky Bucket)
/// 
/// 用于流量整形，强制恒定的输出速率
/// 
/// # 特点
/// - 平滑输出流量
/// - 不允许突发（严格限流）
/// - 简单易实现
#[derive(Debug, Clone)]
pub struct LeakyBucket {
    /// 漏出速率 (items/second)
    leak_rate: f64,
    /// 桶容量
    capacity: usize,
    /// 当前桶内数据量
    size: Arc<Mutex<usize>>,
    /// 上次漏出时间
    last_leak: Arc<Mutex<Instant>>,
}

impl LeakyBucket {
    /// 创建新的漏桶
    pub fn new(leak_rate: f64, capacity: usize) -> Self {
        Self {
            leak_rate,
            capacity,
            size: Arc::new(Mutex::new(0)),
            last_leak: Arc::new(Mutex::new(Instant::now())),
        }
    }
    
    /// 尝试添加数据到桶中
    pub fn try_add(&self, count: usize) -> AsyncResult<()> {
        self.leak()?;
        
        let mut size = self.size.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock size: {}", e)))?;
        
        if *size + count <= self.capacity {
            *size += count;
            Ok(())
        } else {
            Err(ModelError::RateLimitExceeded(format!(
                "Bucket overflow: capacity {}, current {}, trying to add {}",
                self.capacity, *size, count
            )))
        }
    }
    
    /// 阻塞等待直到可以添加数据
    #[cfg(feature = "tokio-adapter")]
    pub async fn add(&self, count: usize) -> AsyncResult<()> {
        loop {
            match self.try_add(count) {
                Ok(()) => return Ok(()),
                Err(_) => {
                    // 等待一段时间让桶漏出
                    let wait_time = self.calculate_wait_time(count)?;
                    sleep(wait_time).await;
                }
            }
        }
    }
    
    /// 漏出数据
    fn leak(&self) -> AsyncResult<()> {
        let now = Instant::now();
        let mut last_leak = self.last_leak.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock last_leak: {}", e)))?;
        
        let elapsed = now.duration_since(*last_leak).as_secs_f64();
        let leaked = (elapsed * self.leak_rate) as usize;
        
        if leaked > 0 {
            let mut size = self.size.lock()
                .map_err(|e| ModelError::LockError(format!("Failed to lock size: {}", e)))?;
            
            *size = size.saturating_sub(leaked);
            *last_leak = now;
        }
        
        Ok(())
    }
    
    /// 计算等待时间
    fn calculate_wait_time(&self, count: usize) -> AsyncResult<Duration> {
        let size = self.size.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock size: {}", e)))?;
        
        let overflow = (*size + count).saturating_sub(self.capacity);
        let wait_secs = overflow as f64 / self.leak_rate;
        
        Ok(Duration::from_secs_f64(wait_secs))
    }
    
    /// 获取当前桶内数据量
    pub fn size(&self) -> usize {
        self.size.lock()
            .map(|s| *s)
            .unwrap_or(0)
    }
    
    /// 获取桶容量
    pub fn capacity(&self) -> usize {
        self.capacity
    }
    
    /// 获取漏出速率
    pub fn leak_rate(&self) -> f64 {
        self.leak_rate
    }
}

/// 滑动窗口限流器
/// 
/// 用于精确的时间窗口内的请求限制
#[derive(Debug, Clone)]
pub struct SlidingWindowRateLimiter {
    /// 窗口大小
    window_size: Duration,
    /// 最大请求数
    max_requests: usize,
    /// 请求时间戳队列
    timestamps: Arc<Mutex<VecDeque<Instant>>>,
}

impl SlidingWindowRateLimiter {
    /// 创建新的滑动窗口限流器
    pub fn new(window_size: Duration, max_requests: usize) -> Self {
        Self {
            window_size,
            max_requests,
            timestamps: Arc::new(Mutex::new(VecDeque::new())),
        }
    }
    
    /// 尝试获取许可
    pub fn try_acquire(&self) -> AsyncResult<()> {
        let now = Instant::now();
        let window_start = now - self.window_size;
        
        let mut timestamps = self.timestamps.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock timestamps: {}", e)))?;
        
        // 移除窗口外的时间戳
        while let Some(ts) = timestamps.front() {
            if *ts < window_start {
                timestamps.pop_front();
            } else {
                break;
            }
        }
        
        // 检查是否超过限制
        if timestamps.len() < self.max_requests {
            timestamps.push_back(now);
            Ok(())
        } else {
            Err(ModelError::RateLimitExceeded(format!(
                "Rate limit exceeded: {} requests in {:?}",
                timestamps.len(), self.window_size
            )))
        }
    }
    
    /// 获取当前窗口内的请求数
    pub fn current_count(&self) -> usize {
        let now = Instant::now();
        let window_start = now - self.window_size;
        
        self.timestamps.lock()
            .map(|mut ts| {
                while let Some(t) = ts.front() {
                    if *t < window_start {
                        ts.pop_front();
                    } else {
                        break;
                    }
                }
                ts.len()
            })
            .unwrap_or(0)
    }
}

/// 自适应限流器
/// 
/// 根据系统负载动态调整限流策略
#[derive(Debug, Clone)]
pub struct AdaptiveRateLimiter {
    /// 基础速率
    base_rate: f64,
    /// 当前速率
    current_rate: Arc<Mutex<f64>>,
    /// 最小速率
    min_rate: f64,
    /// 最大速率
    max_rate: f64,
    /// 成功计数
    success_count: Arc<Mutex<usize>>,
    /// 失败计数
    failure_count: Arc<Mutex<usize>>,
    /// 调整间隔
    adjustment_interval: Duration,
    /// 上次调整时间
    last_adjustment: Arc<Mutex<Instant>>,
}

impl AdaptiveRateLimiter {
    /// 创建新的自适应限流器
    pub fn new(base_rate: f64, min_rate: f64, max_rate: f64, adjustment_interval: Duration) -> Self {
        Self {
            base_rate,
            current_rate: Arc::new(Mutex::new(base_rate)),
            min_rate,
            max_rate,
            success_count: Arc::new(Mutex::new(0)),
            failure_count: Arc::new(Mutex::new(0)),
            adjustment_interval,
            last_adjustment: Arc::new(Mutex::new(Instant::now())),
        }
    }
    
    /// 记录成功
    pub fn record_success(&self) -> AsyncResult<()> {
        let mut count = self.success_count.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock success_count: {}", e)))?;
        *count += 1;
        self.adjust_rate()?;
        Ok(())
    }
    
    /// 记录失败
    pub fn record_failure(&self) -> AsyncResult<()> {
        let mut count = self.failure_count.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock failure_count: {}", e)))?;
        *count += 1;
        self.adjust_rate()?;
        Ok(())
    }
    
    /// 调整速率
    fn adjust_rate(&self) -> AsyncResult<()> {
        let now = Instant::now();
        let mut last_adjustment = self.last_adjustment.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock last_adjustment: {}", e)))?;
        
        if now.duration_since(*last_adjustment) < self.adjustment_interval {
            return Ok(());
        }
        
        let success = *self.success_count.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock success_count: {}", e)))?;
        let failure = *self.failure_count.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock failure_count: {}", e)))?;
        
        let total = success + failure;
        if total == 0 {
            return Ok(());
        }
        
        let success_rate = success as f64 / total as f64;
        let mut current_rate = self.current_rate.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock current_rate: {}", e)))?;
        
        // 根据成功率调整速率
        if success_rate > 0.95 {
            // 成功率高，增加速率
            *current_rate = (*current_rate * 1.1).min(self.max_rate);
        } else if success_rate < 0.85 {
            // 成功率低，降低速率
            *current_rate = (*current_rate * 0.9).max(self.min_rate);
        }
        
        // 重置计数器
        *self.success_count.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock success_count: {}", e)))? = 0;
        *self.failure_count.lock()
            .map_err(|e| ModelError::LockError(format!("Failed to lock failure_count: {}", e)))? = 0;
        *last_adjustment = now;
        
        Ok(())
    }
    
    /// 获取当前速率
    pub fn current_rate(&self) -> f64 {
        self.current_rate.lock()
            .map(|r| *r)
            .unwrap_or(self.base_rate)
    }
}
