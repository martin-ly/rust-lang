//! # 异步特性 / Async Features
//!
//! Rust 1.89 在异步编程方面进行了重要改进，包括更好的异步运行时支持、
//! 改进的异步语法和更高效的异步执行。
//!
//! Rust 1.89 has made important improvements in async programming, including
//! better async runtime support, improved async syntax, and more efficient
//! async execution.

use std::future::Future;
use std::pin::Pin;
// use std::task::{Context, Poll};
use futures::stream::StreamExt;
use std::time::Duration;
use tokio::time::sleep;

/// 异步工作流执行器 / Async Workflow Executor
///
/// 提供高效的异步工作流执行功能。
/// Provides efficient async workflow execution functionality.
#[allow(dead_code)]
pub struct AsyncWorkflowExecutor {
    max_concurrent_tasks: usize,
    task_queue: tokio::sync::mpsc::UnboundedSender<AsyncTask>,
}

/// 异步任务 / Async Task
#[allow(dead_code)]
pub struct AsyncTask {
    id: String,
    future: Pin<Box<dyn Future<Output = TaskResult> + Send + 'static>>,
    priority: TaskPriority,
}

/// 任务优先级 / Task Priority
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum TaskPriority {
    Low = 0,
    Normal = 1,
    High = 2,
    Critical = 3,
}

/// 任务统计信息 / Task Statistics
#[derive(Debug, Clone)]
pub struct TaskStatistics {
    pub total_tasks: usize,
    pub completed_tasks: usize,
    pub failed_tasks: usize,
    pub running_tasks: usize,
    pub average_execution_time: Duration,
}

/// 工作流任务 / Workflow Task
#[derive(Debug, Clone)]
pub struct WorkflowTask {
    pub id: String,
    pub name: String,
    pub priority: TaskPriority,
    pub timeout: Duration,
    pub retry_count: u32,
    pub max_retries: u32,
    pub dependencies: Vec<String>,
    pub payload: serde_json::Value,
}

impl WorkflowTask {
    /// 执行任务 / Execute task
    pub async fn execute(&self) -> TaskResult {
        // 模拟任务执行 / Simulate task execution
        tokio::time::sleep(Duration::from_millis(100)).await;
        TaskResult::Success(self.payload.clone())
    }
}

/// 任务结果 / Task Result
#[derive(Debug, Clone)]
pub enum TaskResult {
    Success(serde_json::Value),
    Error(String),
    Timeout,
    Cancelled,
}

impl AsyncWorkflowExecutor {
    /// 创建新的异步执行器 / Create new async executor
    pub fn new(max_concurrent_tasks: usize) -> Self {
        let (task_sender, _task_receiver) = tokio::sync::mpsc::unbounded_channel();

        Self {
            max_concurrent_tasks,
            task_queue: task_sender,
        }
    }

    /// 提交异步任务 / Submit async task
    pub async fn submit_task<F>(
        &self,
        id: String,
        future: F,
        priority: TaskPriority,
    ) -> Result<(), AsyncExecutorError>
    where
        F: Future<Output = TaskResult> + Send + 'static,
    {
        let task = AsyncTask {
            id,
            future: Box::pin(future),
            priority,
        };

        self.task_queue
            .send(task)
            .map_err(|_| AsyncExecutorError::TaskQueueFull)?;

        Ok(())
    }

    /// 执行异步工作流 / Execute async workflow
    pub async fn execute_workflow<F, T>(&self, workflow: F) -> Result<T, AsyncExecutorError>
    where
        F: Future<Output = Result<T, AsyncExecutorError>> + Send + 'static,
        T: Send + 'static,
    {
        workflow.await
    }

    /// 获取任务统计信息 / Get task statistics
    pub async fn get_task_statistics(&self) -> TaskStatistics {
        TaskStatistics {
            total_tasks: 0,
            completed_tasks: 0,
            failed_tasks: 0,
            running_tasks: 0,
            average_execution_time: std::time::Duration::from_millis(0),
        }
    }
}

/// 异步工作流构建器 / Async Workflow Builder
pub struct AsyncWorkflowBuilder {
    tasks: Vec<AsyncTaskDefinition>,
    dependencies: Vec<TaskDependency>,
}

/// 异步任务定义 / Async Task Definition
pub struct AsyncTaskDefinition {
    id: String,
    function:
        Box<dyn Fn() -> Pin<Box<dyn Future<Output = TaskResult> + Send + 'static>> + Send + Sync>,
    priority: TaskPriority,
    timeout: Option<Duration>,
}

/// 任务依赖 / Task Dependency
pub struct TaskDependency {
    task_id: String,
    depends_on: Vec<String>,
}

impl AsyncWorkflowBuilder {
    /// 创建新的构建器 / Create new builder
    pub fn new() -> Self {
        Self {
            tasks: Vec::new(),
            dependencies: Vec::new(),
        }
    }

    /// 添加任务 / Add task
    pub fn add_task<F>(mut self, id: String, function: F, priority: TaskPriority) -> Self
    where
        F: Fn() -> Pin<Box<dyn Future<Output = TaskResult> + Send + 'static>>
            + Send
            + Sync
            + 'static,
    {
        let task = AsyncTaskDefinition {
            id: id.clone(),
            function: Box::new(function),
            priority,
            timeout: None,
        };

        self.tasks.push(task);
        self
    }

    /// 添加依赖 / Add dependency
    pub fn add_dependency(mut self, task_id: String, depends_on: Vec<String>) -> Self {
        let dependency = TaskDependency {
            task_id,
            depends_on,
        };

        self.dependencies.push(dependency);
        self
    }

    /// 设置超时 / Set timeout
    pub fn with_timeout(mut self, task_id: String, timeout: Duration) -> Self {
        if let Some(task) = self.tasks.iter_mut().find(|t| t.id == task_id) {
            task.timeout = Some(timeout);
        }
        self
    }

    /// 构建工作流 / Build workflow
    pub fn build(self) -> AsyncWorkflow {
        AsyncWorkflow {
            tasks: self.tasks,
            dependencies: self.dependencies,
        }
    }
}

/// 异步工作流 / Async Workflow
pub struct AsyncWorkflow {
    tasks: Vec<AsyncTaskDefinition>,
    dependencies: Vec<TaskDependency>,
}

impl AsyncWorkflow {
    /// 执行工作流 / Execute workflow
    pub async fn execute(self) -> Result<WorkflowResult, AsyncExecutorError> {
        let mut results = std::collections::HashMap::new();
        let mut completed_tasks = std::collections::HashSet::new();

        // 按优先级排序任务 / Sort tasks by priority
        let mut sorted_tasks = self.tasks;
        sorted_tasks.sort_by(|a, b| b.priority.cmp(&a.priority));

        for task in sorted_tasks {
            // 检查依赖 / Check dependencies
            if let Some(dependency) = self.dependencies.iter().find(|d| d.task_id == task.id) {
                for dep_id in &dependency.depends_on {
                    if !completed_tasks.contains(dep_id) {
                        return Err(AsyncExecutorError::DependencyNotMet(dep_id.clone()));
                    }
                }
            }

            // 执行任务 / Execute task
            let result = if let Some(timeout) = task.timeout {
                tokio::time::timeout(timeout, (task.function)())
                    .await
                    .unwrap_or(TaskResult::Timeout)
            } else {
                (task.function)().await
            };

            results.insert(task.id.clone(), result);
            completed_tasks.insert(task.id);
        }

        Ok(WorkflowResult { results })
    }
}

/// 工作流结果 / Workflow Result
#[derive(Debug, Clone)]
pub struct WorkflowResult {
    results: std::collections::HashMap<String, TaskResult>,
}

impl WorkflowResult {
    /// 获取任务结果 / Get task result
    pub fn get_task_result(&self, task_id: &str) -> Option<&TaskResult> {
        self.results.get(task_id)
    }

    /// 获取所有结果 / Get all results
    pub fn get_all_results(&self) -> &std::collections::HashMap<String, TaskResult> {
        &self.results
    }

    /// 检查是否成功 / Check if successful
    pub fn is_successful(&self) -> bool {
        self.results
            .values()
            .all(|result| matches!(result, TaskResult::Success(_)))
    }
}

/// 异步流处理器 / Async Stream Processor
pub struct AsyncStreamProcessor<T> {
    buffer_size: usize,
    _phantom: std::marker::PhantomData<T>,
}

impl<T> AsyncStreamProcessor<T>
where
    T: Send + 'static,
{
    /// 创建新的流处理器 / Create new stream processor
    pub fn new(buffer_size: usize) -> Self {
        Self {
            buffer_size,
            _phantom: std::marker::PhantomData,
        }
    }

    /// 处理流 / Process stream
    pub async fn process_stream<F, R>(
        &self,
        stream: impl futures::Stream<Item = T> + Send + 'static,
        processor: F,
    ) -> Result<Vec<R>, AsyncExecutorError>
    where
        F: Fn(T) -> Pin<Box<dyn Future<Output = R> + Send + 'static>> + Send + Sync + 'static,
        R: Send + 'static,
    {
        let mut results = Vec::new();
        let mut stream = Box::pin(stream);

        while let Some(item) = stream.next().await {
            let result = processor(item).await;
            results.push(result);

            if results.len() >= self.buffer_size {
                // 处理缓冲区 / Process buffer
                tokio::task::yield_now().await;
            }
        }

        Ok(results)
    }
}

/// 异步错误 / Async Error
#[derive(Debug, thiserror::Error)]
pub enum AsyncExecutorError {
    #[error("任务队列已满 / Task queue is full")]
    TaskQueueFull,

    #[error("依赖未满足 / Dependency not met: {0}")]
    DependencyNotMet(String),

    #[error("任务执行失败 / Task execution failed: {0}")]
    TaskExecutionFailed(String),

    #[error("工作流执行超时 / Workflow execution timeout")]
    WorkflowTimeout,

    #[error("异步运行时错误 / Async runtime error: {0}")]
    RuntimeError(String),
}

/// 异步工具函数 / Async Utility Functions
pub mod utils {
    use super::*;

    /// 异步重试 / Async retry
    pub async fn retry_async<F, T, E>(
        mut operation: F,
        max_retries: usize,
        delay: Duration,
    ) -> Result<T, E>
    where
        F: FnMut() -> Pin<Box<dyn Future<Output = Result<T, E>> + Send + 'static>>,
        E: Clone,
    {
        let mut last_error = None;

        for attempt in 0..=max_retries {
            match operation().await {
                Ok(result) => return Ok(result),
                Err(error) => {
                    last_error = Some(error.clone());
                    if attempt < max_retries {
                        sleep(delay).await;
                    }
                }
            }
        }

        Err(last_error.unwrap())
    }

    /// 异步超时 / Async timeout
    pub async fn timeout_async<F, T>(future: F, timeout: Duration) -> Result<T, AsyncExecutorError>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        tokio::time::timeout(timeout, future)
            .await
            .map_err(|_| AsyncExecutorError::WorkflowTimeout)
    }

    /// 异步批处理 / Async batch processing
    pub async fn batch_process<T, R, F>(
        items: Vec<T>,
        batch_size: usize,
        processor: F,
    ) -> Result<Vec<R>, AsyncExecutorError>
    where
        T: Clone + Send + 'static,
        R: Send + 'static,
        F: Fn(
                Vec<T>,
            )
                -> Pin<Box<dyn Future<Output = Result<Vec<R>, AsyncExecutorError>> + Send + 'static>>
            + Send
            + Sync
            + 'static,
    {
        let mut results = Vec::new();

        for chunk in items.chunks(batch_size) {
            let batch = chunk.to_vec();
            let batch_results = processor(batch).await?;
            results.extend(batch_results);
        }

        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::stream;

    #[test]
    fn test_async_workflow_builder() {
        let workflow = AsyncWorkflowBuilder::new()
            .add_task(
                "task1".to_string(),
                || {
                    Box::pin(async {
                        TaskResult::Success(serde_json::json!({"result": "success"}))
                    })
                },
                TaskPriority::High,
            )
            .add_task(
                "task2".to_string(),
                || {
                    Box::pin(async {
                        TaskResult::Success(serde_json::json!({"result": "success"}))
                    })
                },
                TaskPriority::Normal,
            )
            .add_dependency("task2".to_string(), vec!["task1".to_string()])
            .build();

        assert_eq!(workflow.tasks.len(), 2);
        assert_eq!(workflow.dependencies.len(), 1);
    }

    #[tokio::test]
    async fn test_async_workflow_execution() {
        let workflow = AsyncWorkflowBuilder::new()
            .add_task(
                "task1".to_string(),
                || {
                    Box::pin(async {
                        TaskResult::Success(serde_json::json!({"result": "success"}))
                    })
                },
                TaskPriority::High,
            )
            .build();

        let result = workflow.execute().await.unwrap();
        assert!(result.is_successful());
    }

    #[tokio::test]
    async fn test_async_stream_processor() {
        let processor = AsyncStreamProcessor::<i32>::new(10);
        let stream = stream::iter(vec![1, 2, 3, 4, 5]);

        let results = processor
            .process_stream(stream, |item| Box::pin(async move { item * 2 }))
            .await
            .unwrap();

        assert_eq!(results, vec![2, 4, 6, 8, 10]);
    }

    #[tokio::test]
    async fn test_async_utils() {
        let result = utils::retry_async(
            || Box::pin(async { Ok::<i32, String>(42) }),
            3,
            Duration::from_millis(10),
        )
        .await
        .unwrap();

        assert_eq!(result, 42);
    }
}
