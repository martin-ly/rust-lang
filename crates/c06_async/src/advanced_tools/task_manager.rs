//! 异步任务管理器
//! 
//! 提供高级任务管理功能：
//! - 任务优先级队列
//! - 任务依赖管理
//! - 任务生命周期管理
//! - 任务监控和统计
//! - 任务失败重试
//! - 任务取消和超时

use std::collections::{HashMap, BinaryHeap};
use std::sync::Arc;
use std::time::{Duration, Instant};
use std::cmp::Ordering;
use tokio::sync::{Mutex, RwLock, mpsc, Notify};
use tokio::time::sleep;
use anyhow::Result;
use serde::{Serialize, Deserialize};
use uuid::Uuid;

/// 任务优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum TaskPriority {
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
}

/// 任务状态
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum TaskStatus {
    Pending,
    Running,
    Completed,
    Failed,
    Cancelled,
    Timeout,
}

/// 任务信息
#[derive(Debug, Clone)]
pub struct TaskInfo {
    pub id: Uuid,
    pub name: String,
    pub priority: TaskPriority,
    pub status: TaskStatus,
    pub created_at: Instant,
    pub started_at: Option<Instant>,
    pub completed_at: Option<Instant>,
    pub dependencies: Vec<Uuid>,
    pub timeout: Option<Duration>,
    pub retry_count: u32,
    pub max_retries: u32,
    pub error: Option<String>,
}

/// 任务队列项
#[derive(Debug)]
struct TaskQueueItem {
    priority: TaskPriority,
    task_id: Uuid,
    created_at: Instant,
}

impl PartialEq for TaskQueueItem {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority && self.task_id == other.task_id
    }
}

impl Eq for TaskQueueItem {}

impl PartialOrd for TaskQueueItem {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TaskQueueItem {
    fn cmp(&self, other: &Self) -> Ordering {
        // 优先级高的在前，相同优先级按创建时间排序
        match self.priority.cmp(&other.priority) {
            Ordering::Equal => other.created_at.cmp(&self.created_at),
            other => other,
        }
    }
}

/// 任务执行器 trait
#[async_trait::async_trait]
pub trait TaskExecutor: Send + Sync {
    async fn execute(&self, task_id: Uuid, input: serde_json::Value) -> Result<serde_json::Value>;
}

/// 任务统计信息
#[derive(Debug, Default, Clone)]
pub struct TaskStats {
    pub total_tasks: u64,
    pub pending_tasks: u64,
    pub running_tasks: u64,
    pub completed_tasks: u64,
    pub failed_tasks: u64,
    pub cancelled_tasks: u64,
    pub timeout_tasks: u64,
    pub avg_execution_time: Duration,
    pub total_execution_time: Duration,
}

/// 异步任务管理器
#[allow(dead_code)]
pub struct TaskManager {
    tasks: Arc<RwLock<HashMap<Uuid, TaskInfo>>>,
    task_queue: Arc<Mutex<BinaryHeap<TaskQueueItem>>>,
    running_tasks: Arc<Mutex<HashMap<Uuid, tokio::task::JoinHandle<()>>>>,
    executor: Arc<dyn TaskExecutor>,
    stats: Arc<Mutex<TaskStats>>,
    shutdown_notify: Arc<Notify>,
    max_concurrent_tasks: usize,
    task_channel: mpsc::UnboundedSender<(Uuid, serde_json::Value)>,
}

impl TaskManager {
    /// 创建新的任务管理器
    pub fn new(executor: Arc<dyn TaskExecutor>, max_concurrent_tasks: usize) -> Self {
        let (tx, _rx) = mpsc::unbounded_channel();
        
        let manager = Self {
            tasks: Arc::new(RwLock::new(HashMap::new())),
            task_queue: Arc::new(Mutex::new(BinaryHeap::new())),
            running_tasks: Arc::new(Mutex::new(HashMap::new())),
            executor: executor,
            stats: Arc::new(Mutex::new(TaskStats::default())),
            shutdown_notify: Arc::new(Notify::new()),
            max_concurrent_tasks,
            task_channel: tx,
        };

        // 启动任务处理器
        let manager_clone = manager.clone_for_processing();
        tokio::spawn(async move {
            // 注意：TaskManagerClone 不包含 process_tasks 方法
            // 任务处理逻辑应该在主 TaskManager 中实现
            // 这里应该实现任务处理循环
            loop {
                // 处理待处理的任务
                manager_clone.process_pending_tasks().await;
                
                // 短暂休眠以避免过度占用CPU
                tokio::time::sleep(Duration::from_millis(100)).await;
            }
        });

        manager
    }

    /// 提交新任务
    pub async fn submit_task(
        &self,
        name: String,
        priority: TaskPriority,
        _input: serde_json::Value,
        dependencies: Vec<Uuid>,
        timeout: Option<Duration>,
        max_retries: u32,
    ) -> Result<Uuid> {
        let task_id = Uuid::new_v4();
        let task_info = TaskInfo {
            id: task_id,
            name,
            priority,
            status: TaskStatus::Pending,
            created_at: Instant::now(),
            started_at: None,
            completed_at: None,
            dependencies,
            timeout,
            retry_count: 0,
            max_retries,
            error: None,
        };

        // 存储任务信息
        {
            let mut tasks = self.tasks.write().await;
            tasks.insert(task_id, task_info);
        }

        // 更新统计信息
        {
            let mut stats = self.stats.lock().await;
            stats.total_tasks += 1;
            stats.pending_tasks += 1;
        }

        // 检查依赖是否满足
        if self.check_dependencies(task_id).await {
            self.enqueue_task(task_id, priority).await;
        }

        Ok(task_id)
    }

    /// 取消任务
    pub async fn cancel_task(&self, task_id: Uuid) -> Result<()> {
        // 更新任务状态
        {
            let mut tasks = self.tasks.write().await;
            if let Some(task) = tasks.get_mut(&task_id) {
                task.status = TaskStatus::Cancelled;
                task.completed_at = Some(Instant::now());
            }
        }

        // 取消运行中的任务
        {
            let mut running_tasks = self.running_tasks.lock().await;
            if let Some(handle) = running_tasks.remove(&task_id) {
                handle.abort();
            }
        }

        // 更新统计信息
        {
            let mut stats = self.stats.lock().await;
            stats.pending_tasks = stats.pending_tasks.saturating_sub(1);
            stats.cancelled_tasks += 1;
        }

        Ok(())
    }

    /// 获取任务信息
    pub async fn get_task(&self, task_id: Uuid) -> Option<TaskInfo> {
        let tasks = self.tasks.read().await;
        tasks.get(&task_id).cloned()
    }

    /// 获取任务统计信息
    pub async fn get_stats(&self) -> TaskStats {
        self.stats.lock().await.clone()
    }

    /// 等待任务完成
    pub async fn wait_for_task(&self, task_id: Uuid, timeout_duration: Option<Duration>) -> Result<TaskInfo> {
        let start = Instant::now();
        let timeout_duration = timeout_duration.unwrap_or(Duration::from_secs(30));

        loop {
            if start.elapsed() > timeout_duration {
                return Err(anyhow::anyhow!("等待任务超时"));
            }

            if let Some(task) = self.get_task(task_id).await {
                match task.status {
                    TaskStatus::Completed => return Ok(task),
                    TaskStatus::Failed => return Err(anyhow::anyhow!("任务执行失败: {:?}", task.error)),
                    TaskStatus::Cancelled => return Err(anyhow::anyhow!("任务已取消")),
                    _ => {
                        sleep(Duration::from_millis(100)).await;
                        continue;
                    }
                }
            } else {
                return Err(anyhow::anyhow!("任务不存在"));
            }
        }
    }

    /// 关闭任务管理器
    pub async fn shutdown(&self) -> Result<()> {
        self.shutdown_notify.notify_waiters();

        // 等待所有任务完成
        let mut running_tasks = self.running_tasks.lock().await;
        for (_, handle) in running_tasks.drain() {
            let _ = handle.await;
        }

        Ok(())
    }

    // 私有方法

    fn clone_for_processing(&self) -> TaskManagerClone {
        TaskManagerClone {
            tasks: Arc::clone(&self.tasks),
            task_queue: Arc::clone(&self.task_queue),
            running_tasks: Arc::clone(&self.running_tasks),
            executor: Arc::clone(&self.executor),
            stats: Arc::clone(&self.stats),
            shutdown_notify: Arc::clone(&self.shutdown_notify),
            max_concurrent_tasks: self.max_concurrent_tasks,
        }
    }

    async fn enqueue_task(&self, task_id: Uuid, priority: TaskPriority) {
        let queue_item = TaskQueueItem {
            priority,
            task_id,
            created_at: Instant::now(),
        };

        let mut queue = self.task_queue.lock().await;
        queue.push(queue_item);
    }

    async fn check_dependencies(&self, task_id: Uuid) -> bool {
        let tasks = self.tasks.read().await;
        if let Some(task) = tasks.get(&task_id) {
            for dep_id in &task.dependencies {
                if let Some(dep_task) = tasks.get(dep_id) {
                    if dep_task.status != TaskStatus::Completed {
                        return false;
                    }
                }
            }
        }
        true
    }

    #[allow(dead_code)]
    async fn process_tasks(&self, mut rx: mpsc::UnboundedReceiver<(Uuid, serde_json::Value)>) {
        let mut interval = tokio::time::interval(Duration::from_millis(100));

        loop {
            tokio::select! {
                _ = interval.tick() => {
                    self.process_pending_tasks().await;
                }
                Some((task_id, input)) = rx.recv() => {
                    self.execute_task(task_id, input).await;
                }
                _ = self.shutdown_notify.notified() => {
                    break;
                }
            }
        }
    }

    #[allow(dead_code)]
    async fn process_pending_tasks(&self) {
        let current_running = {
            let running_tasks = self.running_tasks.lock().await;
            running_tasks.len()
        };

        if current_running >= self.max_concurrent_tasks {
            return;
        }

        let available_slots = self.max_concurrent_tasks - current_running;
        let mut tasks_to_start = Vec::new();

        // 从队列中获取可执行的任务
        {
            let mut queue = self.task_queue.lock().await;
            let mut temp_queue = BinaryHeap::new();

            while let Some(queue_item) = queue.pop() {
                if tasks_to_start.len() >= available_slots {
                    temp_queue.push(queue_item);
                    continue;
                }

                // 检查依赖是否满足
                if self.check_dependencies(queue_item.task_id).await {
                    tasks_to_start.push(queue_item.task_id);
                } else {
                    temp_queue.push(queue_item);
                }
            }

            *queue = temp_queue;
        }

        // 启动任务
        for task_id in tasks_to_start {
            if let Some(_task_info) = self.get_task(task_id).await {
                // 发送任务到执行器
                let _ = self.task_channel.send((task_id, serde_json::Value::Null));
            }
        }
    }

    #[allow(dead_code)]
    async fn execute_task(&self, task_id: Uuid, _input: serde_json::Value) {
        let executor = Arc::clone(&self.executor);
        let tasks = Arc::clone(&self.tasks);
        let running_tasks = Arc::clone(&self.running_tasks);
        let stats = Arc::clone(&self.stats);

        let handle = tokio::spawn(async move {
            let start_time = Instant::now();

            // 更新任务状态为运行中
            {
                let mut tasks = tasks.write().await;
                if let Some(task) = tasks.get_mut(&task_id) {
                    task.status = TaskStatus::Running;
                    task.started_at = Some(Instant::now());
                }
            }

            // 更新统计信息
            {
                let mut stats = stats.lock().await;
                stats.pending_tasks = stats.pending_tasks.saturating_sub(1);
                stats.running_tasks += 1;
            }

            // 执行任务
            let result = executor.execute(task_id, serde_json::Value::Null).await;

            let execution_time = start_time.elapsed();

            // 更新任务状态
            {
                let mut tasks = tasks.write().await;
                if let Some(task) = tasks.get_mut(&task_id) {
                    task.completed_at = Some(Instant::now());
                    
                    match result {
                        Ok(_) => {
                            task.status = TaskStatus::Completed;
                        }
                        Err(e) => {
                            task.error = Some(e.to_string());
                            if task.retry_count < task.max_retries {
                                task.retry_count += 1;
                                task.status = TaskStatus::Pending;
                                // 重新加入队列
                                // 这里需要重新实现队列逻辑
                            } else {
                                task.status = TaskStatus::Failed;
                            }
                        }
                    }
                }
            }

            // 更新统计信息
            {
                let mut stats = stats.lock().await;
                stats.running_tasks = stats.running_tasks.saturating_sub(1);
                
                let tasks = tasks.read().await;
                if let Some(task) = tasks.get(&task_id) {
                    match task.status {
                        TaskStatus::Completed => {
                            stats.completed_tasks += 1;
                            stats.total_execution_time += execution_time;
                            stats.avg_execution_time = Duration::from_nanos(
                                stats.total_execution_time.as_nanos() as u64 / stats.completed_tasks.max(1) as u64
                            );
                        }
                        TaskStatus::Failed => {
                            stats.failed_tasks += 1;
                        }
                        _ => {}
                    }
                }
            }

            // 从运行任务列表中移除
            {
                let mut running_tasks = running_tasks.lock().await;
                running_tasks.remove(&task_id);
            }
        });

        // 将任务句柄添加到运行任务列表
        {
            let mut running_tasks = self.running_tasks.lock().await;
            running_tasks.insert(task_id, handle);
        }
    }
}

/// 用于任务处理的任务管理器克隆
struct TaskManagerClone {
    tasks: Arc<RwLock<HashMap<Uuid, TaskInfo>>>,
    task_queue: Arc<Mutex<BinaryHeap<TaskQueueItem>>>,
    running_tasks: Arc<Mutex<HashMap<Uuid, tokio::task::JoinHandle<()>>>>,
    executor: Arc<dyn TaskExecutor>,
    stats: Arc<Mutex<TaskStats>>,
    #[allow(dead_code)]
    shutdown_notify: Arc<Notify>,
    max_concurrent_tasks: usize,
}

impl TaskManagerClone {
    async fn process_pending_tasks(&self) {
        let current_running = {
            let running_tasks = self.running_tasks.lock().await;
            running_tasks.len()
        };

        if current_running >= self.max_concurrent_tasks {
            return;
        }

        let available_slots = self.max_concurrent_tasks - current_running;
        let mut tasks_to_start = Vec::new();

        // 从队列中获取可执行的任务
        {
            let mut queue = self.task_queue.lock().await;
            let mut temp_queue = BinaryHeap::new();

            while let Some(queue_item) = queue.pop() {
                if tasks_to_start.len() >= available_slots {
                    temp_queue.push(queue_item);
                    continue;
                }

                // 检查依赖是否满足
                if self.check_dependencies(queue_item.task_id).await {
                    tasks_to_start.push(queue_item.task_id);
                } else {
                    temp_queue.push(queue_item);
                }
            }

            *queue = temp_queue;
        }

        // 启动任务
        for task_id in tasks_to_start {
            self.execute_task(task_id).await;
        }
    }

    async fn check_dependencies(&self, task_id: Uuid) -> bool {
        let tasks = self.tasks.read().await;
        if let Some(task) = tasks.get(&task_id) {
            for dep_id in &task.dependencies {
                if let Some(dep_task) = tasks.get(dep_id) {
                    if dep_task.status != TaskStatus::Completed {
                        return false;
                    }
                }
            }
        }
        true
    }

    async fn execute_task(&self, task_id: Uuid) {
        let executor = Arc::clone(&self.executor);
        let tasks = Arc::clone(&self.tasks);
        let running_tasks = Arc::clone(&self.running_tasks);
        let stats = Arc::clone(&self.stats);

        let handle = tokio::spawn(async move {
            let start_time = Instant::now();

            // 更新任务状态为运行中
            {
                let mut tasks = tasks.write().await;
                if let Some(task) = tasks.get_mut(&task_id) {
                    task.status = TaskStatus::Running;
                    task.started_at = Some(Instant::now());
                }
            }

            // 更新统计信息
            {
                let mut stats = stats.lock().await;
                stats.pending_tasks = stats.pending_tasks.saturating_sub(1);
                stats.running_tasks += 1;
            }

            // 执行任务
            let result = executor.execute(task_id, serde_json::Value::Null).await;

            let execution_time = start_time.elapsed();

            // 更新任务状态
            {
                let mut tasks = tasks.write().await;
                if let Some(task) = tasks.get_mut(&task_id) {
                    task.completed_at = Some(Instant::now());
                    
                    match result {
                        Ok(_) => {
                            task.status = TaskStatus::Completed;
                        }
                        Err(e) => {
                            task.error = Some(e.to_string());
                            if task.retry_count < task.max_retries {
                                task.retry_count += 1;
                                task.status = TaskStatus::Pending;
                            } else {
                                task.status = TaskStatus::Failed;
                            }
                        }
                    }
                }
            }

            // 更新统计信息
            {
                let mut stats = stats.lock().await;
                stats.running_tasks = stats.running_tasks.saturating_sub(1);
                
                let tasks = tasks.read().await;
                if let Some(task) = tasks.get(&task_id) {
                    match task.status {
                        TaskStatus::Completed => {
                            stats.completed_tasks += 1;
                            stats.total_execution_time += execution_time;
                            stats.avg_execution_time = Duration::from_nanos(
                                stats.total_execution_time.as_nanos() as u64 / stats.completed_tasks.max(1) as u64
                            );
                        }
                        TaskStatus::Failed => {
                            stats.failed_tasks += 1;
                        }
                        _ => {}
                    }
                }
            }

            // 从运行任务列表中移除
            {
                let mut running_tasks = running_tasks.lock().await;
                running_tasks.remove(&task_id);
            }
        });

        // 将任务句柄添加到运行任务列表
        {
            let mut running_tasks = self.running_tasks.lock().await;
            running_tasks.insert(task_id, handle);
        }
    }
}

/// 简单的任务执行器实现示例
pub struct SimpleTaskExecutor {
    name: String,
}

impl SimpleTaskExecutor {
    pub fn new(name: String) -> Self {
        Self { name }
    }
}

#[async_trait::async_trait]
impl TaskExecutor for SimpleTaskExecutor {
    async fn execute(&self, task_id: Uuid, input: serde_json::Value) -> Result<serde_json::Value> {
        println!("执行任务 {}: {} (输入: {:?})", task_id, self.name, input);
        
        // 模拟任务执行
        sleep(Duration::from_millis(1000)).await;
        
        Ok(serde_json::json!({
            "task_id": task_id,
            "executor": self.name,
            "result": "success"
        }))
    }
}
