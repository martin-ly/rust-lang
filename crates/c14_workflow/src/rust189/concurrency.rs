//! # 并发特性 / Concurrency Features
//!
//! Rust 1.89 在并发编程方面进行了重要改进，包括更好的并发原语、
//! 改进的同步机制和更高效的并发执行。
//!
//! Rust 1.89 has made important improvements in concurrent programming, including
//! better concurrency primitives, improved synchronization mechanisms, and more
//! efficient concurrent execution.

use std::collections::HashMap;
use std::pin::Pin;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use tokio::sync::{Barrier, RwLock, Semaphore};
use tokio::task::JoinHandle;

/// 并发工作流执行器 / Concurrent Workflow Executor
///
/// 提供高效的并发工作流执行功能。
/// Provides efficient concurrent workflow execution functionality.
#[allow(dead_code)]
pub struct ConcurrentWorkflowExecutor {
    max_concurrent_workflows: usize,
    semaphore: Arc<Semaphore>,
    active_workflows: Arc<AtomicUsize>,
    workflow_registry: Arc<RwLock<HashMap<String, WorkflowDefinition>>>,
}

/// 工作流定义 / Workflow Definition
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct WorkflowDefinition {
    pub id: String,
    pub name: String,
    pub steps: Vec<WorkflowStep>,
    pub dependencies: Vec<WorkflowDependency>,
}

/// 工作流步骤 / Workflow Step
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct WorkflowStep {
    pub id: String,
    pub name: String,
    pub function: String,
    pub timeout: Option<std::time::Duration>,
    pub retry_count: usize,
}

/// 工作流依赖 / Workflow Dependency
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct WorkflowDependency {
    pub step_id: String,
    pub depends_on: Vec<String>,
}

impl ConcurrentWorkflowExecutor {
    /// 创建新的并发执行器 / Create new concurrent executor
    pub fn new(max_concurrent_workflows: usize) -> Self {
        Self {
            max_concurrent_workflows,
            semaphore: Arc::new(Semaphore::new(max_concurrent_workflows)),
            active_workflows: Arc::new(AtomicUsize::new(0)),
            workflow_registry: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// 注册工作流 / Register workflow
    pub async fn register_workflow(
        &self,
        definition: WorkflowDefinition,
    ) -> Result<(), ConcurrentExecutorError> {
        let mut registry = self.workflow_registry.write().await;
        registry.insert(definition.id.clone(), definition);
        Ok(())
    }

    /// 执行工作流 / Execute workflow
    pub async fn execute_workflow(
        &self,
        workflow_id: String,
    ) -> Result<WorkflowResult, ConcurrentExecutorError> {
        let _permit = self
            .semaphore
            .acquire()
            .await
            .map_err(|_| ConcurrentExecutorError::SemaphoreAcquisitionFailed)?;

        self.active_workflows.fetch_add(1, Ordering::SeqCst);

        let result = self.execute_workflow_internal(workflow_id).await;

        self.active_workflows.fetch_sub(1, Ordering::SeqCst);

        result
    }

    /// 内部工作流执行 / Internal workflow execution
    async fn execute_workflow_internal(
        &self,
        workflow_id: String,
    ) -> Result<WorkflowResult, ConcurrentExecutorError> {
        let definition = {
            let registry = self.workflow_registry.read().await;
            registry
                .get(&workflow_id)
                .ok_or_else(|| ConcurrentExecutorError::WorkflowNotFound(workflow_id.clone()))?
                .clone()
        };

        let mut step_results = HashMap::new();
        let mut completed_steps = std::collections::HashSet::new();

        // 按依赖关系排序步骤 / Sort steps by dependencies
        let sorted_steps = self.topological_sort(&definition.steps, &definition.dependencies)?;

        for step in sorted_steps {
            // 检查依赖 / Check dependencies
            if let Some(dependency) = definition
                .dependencies
                .iter()
                .find(|d| d.step_id == step.id)
            {
                for dep_id in &dependency.depends_on {
                    if !completed_steps.contains(dep_id) {
                        return Err(ConcurrentExecutorError::DependencyNotMet(dep_id.clone()));
                    }
                }
            }

            // 执行步骤 / Execute step
            let result = self.execute_step(&step).await?;
            step_results.insert(step.id.clone(), result);
            completed_steps.insert(step.id);
        }

        Ok(WorkflowResult {
            workflow_id,
            step_results,
            status: WorkflowStatus::Completed,
        })
    }

    /// 执行步骤 / Execute step
    async fn execute_step(
        &self,
        step: &WorkflowStep,
    ) -> Result<StepResult, ConcurrentExecutorError> {
        let start_time = std::time::Instant::now();

        // 模拟步骤执行 / Simulate step execution
        let result = if let Some(timeout) = step.timeout {
            tokio::time::timeout(timeout, self.simulate_step_execution(&step.function))
                .await
                .map_err(|_| ConcurrentExecutorError::StepTimeout(step.id.clone()))?
        } else {
            self.simulate_step_execution(&step.function).await
        };

        let execution_time = start_time.elapsed();

        Ok(StepResult {
            step_id: step.id.clone(),
            result,
            execution_time,
            status: StepStatus::Completed,
        })
    }

    /// 模拟步骤执行 / Simulate step execution
    async fn simulate_step_execution(&self, function: &str) -> serde_json::Value {
        // 模拟异步执行 / Simulate async execution
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;

        serde_json::json!({
            "function": function,
            "result": "success",
            "timestamp": chrono::Utc::now().to_rfc3339()
        })
    }

    /// 拓扑排序 / Topological sort
    fn topological_sort(
        &self,
        steps: &[WorkflowStep],
        dependencies: &[WorkflowDependency],
    ) -> Result<Vec<WorkflowStep>, ConcurrentExecutorError> {
        let mut sorted = Vec::new();
        let mut visited = std::collections::HashSet::new();
        let mut temp_visited = std::collections::HashSet::new();

        fn visit(
            step_id: &str,
            steps: &[WorkflowStep],
            dependencies: &[WorkflowDependency],
            sorted: &mut Vec<WorkflowStep>,
            visited: &mut std::collections::HashSet<String>,
            temp_visited: &mut std::collections::HashSet<String>,
        ) -> Result<(), ConcurrentExecutorError> {
            if temp_visited.contains(step_id) {
                return Err(ConcurrentExecutorError::CircularDependency(
                    step_id.to_string(),
                ));
            }

            if visited.contains(step_id) {
                return Ok(());
            }

            temp_visited.insert(step_id.to_string());

            // 访问依赖 / Visit dependencies
            if let Some(dependency) = dependencies.iter().find(|d| d.step_id == step_id) {
                for dep_id in &dependency.depends_on {
                    visit(dep_id, steps, dependencies, sorted, visited, temp_visited)?;
                }
            }

            temp_visited.remove(step_id);
            visited.insert(step_id.to_string());

            // 添加步骤到排序结果 / Add step to sorted result
            if let Some(step) = steps.iter().find(|s| s.id == step_id) {
                sorted.push(step.clone());
            }

            Ok(())
        }

        for step in steps {
            if !visited.contains(&step.id) {
                visit(
                    &step.id,
                    steps,
                    dependencies,
                    &mut sorted,
                    &mut visited,
                    &mut temp_visited,
                )?;
            }
        }

        Ok(sorted)
    }

    /// 获取活跃工作流数量 / Get active workflow count
    pub fn get_active_workflow_count(&self) -> usize {
        self.active_workflows.load(Ordering::SeqCst)
    }

    /// 获取可用许可证数量 / Get available permit count
    pub fn get_available_permits(&self) -> usize {
        self.semaphore.available_permits()
    }
}

/// 工作流结果 / Workflow Result
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct WorkflowResult {
    pub workflow_id: String,
    pub step_results: HashMap<String, StepResult>,
    pub status: WorkflowStatus,
}

/// 步骤结果 / Step Result
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct StepResult {
    pub step_id: String,
    pub result: serde_json::Value,
    pub execution_time: std::time::Duration,
    pub status: StepStatus,
}

/// 工作流状态 / Workflow Status
#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
pub enum WorkflowStatus {
    Pending,
    Running,
    Completed,
    Failed,
    Cancelled,
}

/// 步骤状态 / Step Status
#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
pub enum StepStatus {
    Pending,
    Running,
    Completed,
    Failed,
    Skipped,
}

/// 并发屏障 / Concurrent Barrier
#[derive(Clone)]
#[allow(dead_code)]
pub struct ConcurrentBarrier {
    barrier: Arc<Barrier>,
    participant_count: usize,
}

impl ConcurrentBarrier {
    /// 创建新的屏障 / Create new barrier
    pub fn new(participant_count: usize) -> Self {
        Self {
            barrier: Arc::new(Barrier::new(participant_count)),
            participant_count,
        }
    }

    /// 等待屏障 / Wait for barrier
    pub async fn wait(&self) -> Result<(), ConcurrentExecutorError> {
        self.barrier.wait().await;
        Ok(())
    }

    /// 获取参与者数量 / Get participant count
    pub fn get_participant_count(&self) -> usize {
        self.participant_count
    }
}

/// 并发任务池 / Concurrent Task Pool
#[allow(dead_code)]
pub struct ConcurrentTaskPool {
    max_tasks: usize,
    semaphore: Arc<Semaphore>,
    task_counter: Arc<AtomicUsize>,
}

impl ConcurrentTaskPool {
    /// 创建新的任务池 / Create new task pool
    pub fn new(max_tasks: usize) -> Self {
        Self {
            max_tasks,
            semaphore: Arc::new(Semaphore::new(max_tasks)),
            task_counter: Arc::new(AtomicUsize::new(0)),
        }
    }

    /// 提交任务 / Submit task
    pub async fn submit_task<F, T>(&self, task: F) -> Result<JoinHandle<T>, ConcurrentExecutorError>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        let _permit = self
            .semaphore
            .acquire()
            .await
            .map_err(|_| ConcurrentExecutorError::SemaphoreAcquisitionFailed)?;

        let _task_id = self.task_counter.fetch_add(1, Ordering::SeqCst);

        let handle = tokio::spawn(async move {
            let result = task.await;
            result
        });

        Ok(handle)
    }

    /// 获取活跃任务数量 / Get active task count
    pub fn get_active_task_count(&self) -> usize {
        self.task_counter.load(Ordering::SeqCst)
    }

    /// 获取可用许可证数量 / Get available permit count
    pub fn get_available_permits(&self) -> usize {
        self.semaphore.available_permits()
    }
}

/// 并发错误 / Concurrent Error
#[derive(Debug, thiserror::Error)]
#[allow(dead_code)]
pub enum ConcurrentExecutorError {
    #[error("工作流未找到 / Workflow not found: {0}")]
    WorkflowNotFound(String),

    #[error("依赖未满足 / Dependency not met: {0}")]
    DependencyNotMet(String),

    #[error("循环依赖 / Circular dependency: {0}")]
    CircularDependency(String),

    #[error("步骤超时 / Step timeout: {0}")]
    StepTimeout(String),

    #[error("信号量获取失败 / Semaphore acquisition failed")]
    SemaphoreAcquisitionFailed,

    #[error("并发执行错误 / Concurrent execution error: {0}")]
    ExecutionError(String),
}

/// 并发工具函数 / Concurrent Utility Functions
pub mod utils {
    use super::*;

    /// 并发执行多个任务 / Execute multiple tasks concurrently
    #[allow(dead_code)]
    pub async fn execute_concurrently<T, F>(
        tasks: Vec<F>,
        max_concurrent: usize,
    ) -> Result<Vec<T>, ConcurrentExecutorError>
    where
        T: Send + 'static,
        F: Future<Output = T> + Send + 'static,
    {
        let semaphore = Arc::new(Semaphore::new(max_concurrent));
        let mut handles = Vec::new();

        for task in tasks {
            let semaphore_clone = semaphore.clone();
            let handle = tokio::spawn(async move {
                let permit = semaphore_clone
                    .acquire()
                    .await
                    .map_err(|_| ConcurrentExecutorError::SemaphoreAcquisitionFailed)
                    .unwrap();
                let result = task.await;
                drop(permit);
                result
            });

            handles.push(handle);
        }

        let mut results = Vec::new();
        for handle in handles {
            let result = handle
                .await
                .map_err(|e| ConcurrentExecutorError::ExecutionError(e.to_string()))?;
            results.push(result);
        }

        Ok(results)
    }

    /// 并发映射 / Concurrent map
    pub async fn map_concurrently<T, U, F>(
        items: Vec<T>,
        mapper: F,
        max_concurrent: usize,
    ) -> Result<Vec<U>, ConcurrentExecutorError>
    where
        T: Send + 'static,
        U: Send + 'static,
        F: Fn(T) -> Pin<Box<dyn Future<Output = U> + Send + 'static>> + Send + Sync + 'static,
    {
        let tasks = items.into_iter().map(|item| mapper(item)).collect();
        execute_concurrently(tasks, max_concurrent).await
    }

    /// 并发过滤 / Concurrent filter
    pub async fn filter_concurrently<T, F>(
        items: Vec<T>,
        predicate: F,
        max_concurrent: usize,
    ) -> Result<Vec<T>, ConcurrentExecutorError>
    where
        T: Send + 'static,
        F: Fn(&T) -> Pin<Box<dyn Future<Output = bool> + Send + 'static>>
            + Send
            + Sync
            + Clone
            + 'static,
    {
        let tasks = items
            .into_iter()
            .map(|item| {
                let predicate = predicate.clone();
                async move {
                    if predicate(&item).await {
                        Some(item)
                    } else {
                        None
                    }
                }
            })
            .collect();

        let results = execute_concurrently(tasks, max_concurrent).await?;
        Ok(results.into_iter().flatten().collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_concurrent_workflow_executor() {
        let executor = ConcurrentWorkflowExecutor::new(5);

        let definition = WorkflowDefinition {
            id: "test_workflow".to_string(),
            name: "Test Workflow".to_string(),
            steps: vec![
                WorkflowStep {
                    id: "step1".to_string(),
                    name: "Step 1".to_string(),
                    function: "test_function_1".to_string(),
                    timeout: None,
                    retry_count: 0,
                },
                WorkflowStep {
                    id: "step2".to_string(),
                    name: "Step 2".to_string(),
                    function: "test_function_2".to_string(),
                    timeout: None,
                    retry_count: 0,
                },
            ],
            dependencies: vec![WorkflowDependency {
                step_id: "step2".to_string(),
                depends_on: vec!["step1".to_string()],
            }],
        };

        executor.register_workflow(definition).await.unwrap();

        let result = executor
            .execute_workflow("test_workflow".to_string())
            .await
            .unwrap();
        assert_eq!(result.status, WorkflowStatus::Completed);
        assert_eq!(result.step_results.len(), 2);
    }

    #[tokio::test]
    async fn test_concurrent_barrier() {
        let barrier = ConcurrentBarrier::new(3);
        let barrier_clone = barrier.clone();

        let handle1 = tokio::spawn(async move {
            barrier_clone.wait().await.unwrap();
        });

        let barrier_clone = barrier.clone();
        let handle2 = tokio::spawn(async move {
            barrier_clone.wait().await.unwrap();
        });

        let barrier_clone = barrier.clone();
        let handle3 = tokio::spawn(async move {
            barrier_clone.wait().await.unwrap();
        });

        handle1.await.unwrap();
        handle2.await.unwrap();
        handle3.await.unwrap();
    }

    #[tokio::test]
    async fn test_concurrent_task_pool() {
        let pool = ConcurrentTaskPool::new(2);

        let handle1 = pool.submit_task(async { 1 }).await.unwrap();
        let handle2 = pool.submit_task(async { 2 }).await.unwrap();

        let result1 = handle1.await.unwrap();
        let result2 = handle2.await.unwrap();

        assert_eq!(result1, 1);
        assert_eq!(result2, 2);
    }

    #[tokio::test]
    async fn test_concurrent_utils() {
        let items = vec![1, 2, 3, 4, 5];

        let results = utils::map_concurrently(items, |item| Box::pin(async move { item * 2 }), 3)
            .await
            .unwrap();

        assert_eq!(results, vec![2, 4, 6, 8, 10]);
    }
}
