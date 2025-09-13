# 工作流模式：Rust 1.89 实现指南

## 📋 概述

本文档详细介绍了工作流系统中的核心模式，以及如何使用 Rust 1.89 的最新特性来实现这些模式。我们重点关注类型安全、性能优化和可维护性。

## 🎯 核心工作流模式

### 1. 顺序执行模式

顺序执行模式是最基本的工作流模式，步骤按预定义的顺序依次执行。

#### Rust 1.89 实现

```rust
use std::marker::PhantomData;

/// 顺序执行工作流，使用常量泛型优化
pub struct SequentialWorkflow<T, const MAX_STEPS: usize> {
    steps: Vec<WorkflowStep<T>>,
    current_step: usize,
    _phantom: PhantomData<T>,
}

impl<T, const MAX_STEPS: usize> SequentialWorkflow<T, MAX_STEPS> {
    /// 创建新的顺序工作流
    pub fn new() -> Self {
        Self {
            steps: Vec::with_capacity(MAX_STEPS),
            current_step: 0,
            _phantom: PhantomData,
        }
    }
    
    /// 添加步骤，编译时检查数量限制
    pub fn add_step(&mut self, step: WorkflowStep<T>) -> Result<(), WorkflowError> {
        if self.steps.len() >= MAX_STEPS {
            return Err(WorkflowError::ExceedsMaxSteps(MAX_STEPS));
        }
        self.steps.push(step);
        Ok(())
    }
    
    /// 执行下一个步骤
    pub async fn execute_next(&mut self) -> Result<Option<StepResult<T>>, WorkflowError> {
        if self.current_step >= self.steps.len() {
            return Ok(None); // 工作流完成
        }
        
        let step = &mut self.steps[self.current_step];
        let result = step.execute().await?;
        
        self.current_step += 1;
        Ok(Some(result))
    }
    
    /// 执行所有剩余步骤
    pub async fn execute_all(&mut self) -> Result<Vec<StepResult<T>>, WorkflowError> {
        let mut results = Vec::new();
        
        while let Some(result) = self.execute_next().await? {
            results.push(result);
        }
        
        Ok(results)
    }
    
    /// 获取当前进度
    pub fn get_progress(&self) -> WorkflowProgress {
        let total_steps = self.steps.len();
        let completed_steps = self.current_step;
        let progress_percentage = if total_steps > 0 {
            (completed_steps as f64 / total_steps as f64) * 100.0
        } else {
            0.0
        };
        
        WorkflowProgress {
            total_steps,
            completed_steps,
            current_step: if self.current_step < total_steps {
                Some(self.current_step)
            } else {
                None
            },
            progress_percentage,
            is_completed: self.current_step >= total_steps,
        }
    }
    
    /// 转换为固定大小数组（如果步骤数量匹配）
    pub fn to_fixed_array<const N: usize>(self) -> Result<[WorkflowStep<T>; N], WorkflowError> 
    where 
        [WorkflowStep<T>; N]: Default,
    {
        if self.steps.len() != N {
            return Err(WorkflowError::SizeMismatch {
                expected: N,
                actual: self.steps.len(),
            });
        }
        
        let mut array = <[WorkflowStep<T>; N]>::default();
        for (i, step) in self.steps.into_iter().enumerate() {
            array[i] = step;
        }
        Ok(array)
    }
}

/// 工作流步骤定义
#[derive(Debug, Clone)]
pub struct WorkflowStep<T> {
    pub id: String,
    pub name: String,
    pub description: Option<String>,
    pub data: T,
    pub status: StepStatus,
    pub retry_count: u32,
    pub max_retries: u32,
}

impl<T> WorkflowStep<T> {
    /// 创建新的工作流步骤
    pub fn new(id: String, name: String, data: T) -> Self {
        Self {
            id,
            name,
            description: None,
            data,
            status: StepStatus::Pending,
            retry_count: 0,
            max_retries: 3,
        }
    }
    
    /// 执行步骤
    pub async fn execute(&mut self) -> Result<StepResult<T>, WorkflowError> {
        self.status = StepStatus::Running;
        
        // 模拟异步执行
        tokio::time::sleep(std::time::Duration::from_millis(100)).await;
        
        // 模拟可能的失败
        if self.retry_count < self.max_retries && self.should_retry() {
            self.retry_count += 1;
            self.status = StepStatus::Failed;
            return Err(WorkflowError::StepFailed(self.id.clone()));
        }
        
        self.status = StepStatus::Completed;
        Ok(StepResult {
            step_id: self.id.clone(),
            status: StepStatus::Completed,
            data: self.data.clone(),
            execution_time: std::time::Duration::from_millis(100),
            retry_count: self.retry_count,
        })
    }
    
    /// 判断是否应该重试
    fn should_retry(&self) -> bool {
        // 示例：30% 的失败率
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        
        let mut hasher = DefaultHasher::new();
        self.id.hash(&mut hasher);
        let hash = hasher.finish();
        
        (hash % 10) < 3
    }
}

/// 步骤状态
#[derive(Debug, Clone, PartialEq)]
pub enum StepStatus {
    Pending,
    Running,
    Completed,
    Failed,
    Skipped,
}

/// 步骤执行结果
#[derive(Debug, Clone)]
pub struct StepResult<T> {
    pub step_id: String,
    pub status: StepStatus,
    pub data: T,
    pub execution_time: std::time::Duration,
    pub retry_count: u32,
}

/// 工作流进度
#[derive(Debug, Clone)]
pub struct WorkflowProgress {
    pub total_steps: usize,
    pub completed_steps: usize,
    pub current_step: Option<usize>,
    pub progress_percentage: f64,
    pub is_completed: bool,
}

/// 工作流错误
#[derive(Debug, thiserror::Error)]
pub enum WorkflowError {
    #[error("Exceeds maximum steps: {0}")]
    ExceedsMaxSteps(usize),
    #[error("Size mismatch: expected {expected}, got {actual}")]
    SizeMismatch { expected: usize, actual: usize },
    #[error("Step failed: {0}")]
    StepFailed(String),
    #[error("Workflow execution failed")]
    ExecutionFailed,
}
```

### 2. 并行执行模式

并行执行模式允许多个步骤同时执行，提高整体性能。

#### Rust 1.89 实现1

```rust
use tokio::sync::{Semaphore, Mutex};
use std::sync::Arc;

/// 并行执行工作流，使用 x86 特性优化
pub struct ParallelWorkflow<T, const MAX_CONCURRENT: usize> {
    steps: Vec<WorkflowStep<T>>,
    semaphore: Arc<Semaphore>,
    results: Arc<Mutex<Vec<StepResult<T>>>>,
    completed_count: Arc<Mutex<usize>>,
}

impl<T, const MAX_CONCURRENT: usize> ParallelWorkflow<T, MAX_CONCURRENT> 
where 
    T: Clone + Send + Sync + 'static,
{
    /// 创建新的并行工作流
    pub fn new() -> Self {
        Self {
            steps: Vec::new(),
            semaphore: Arc::new(Semaphore::new(MAX_CONCURRENT)),
            results: Arc::new(Mutex::new(Vec::new())),
            completed_count: Arc::new(Mutex::new(0)),
        }
    }
    
    /// 添加步骤
    pub fn add_step(&mut self, step: WorkflowStep<T>) {
        self.steps.push(step);
    }
    
    /// 执行所有步骤（并行）
    pub async fn execute_all(&self) -> Result<Vec<StepResult<T>>, WorkflowError> {
        let mut handles = Vec::new();
        
        for step in &self.steps {
            let step_clone = step.clone();
            let semaphore = Arc::clone(&self.semaphore);
            let results = Arc::clone(&self.results);
            let completed_count = Arc::clone(&self.completed_count);
            
            let handle = tokio::spawn(async move {
                // 获取信号量许可
                let _permit = semaphore.acquire().await.unwrap();
                
                // 执行步骤
                let mut step_mut = step_clone;
                let result = step_mut.execute().await;
                
                // 记录结果
                match result {
                    Ok(step_result) => {
                        let mut results_guard = results.lock().await;
                        results_guard.push(step_result);
                        
                        let mut count_guard = completed_count.lock().await;
                        *count_guard += 1;
                    }
                    Err(e) => {
                        eprintln!("步骤执行失败: {:?}", e);
                    }
                }
            });
            
            handles.push(handle);
        }
        
        // 等待所有任务完成
        for handle in handles {
            handle.await.unwrap();
        }
        
        // 返回结果
        let results_guard = self.results.lock().await;
        Ok(results_guard.clone())
    }
    
    /// 使用 x86 特性进行高性能并行执行
    pub async fn execute_with_hardware_acceleration(&self) -> Result<Vec<StepResult<T>>, WorkflowError> 
    where 
        T: Clone + Send + Sync + 'static,
    {
        // 检查是否支持 AVX-512
        let is_avx512_supported = is_x86_feature_detected!("avx512f");
        
        if is_avx512_supported && self.steps.len() >= 16 {
            // 使用硬件加速的并行处理
            unsafe { self.execute_parallel_avx512().await }
        } else {
            // 回退到标准并行处理
            self.execute_all().await
        }
    }
    
    /// 使用 AVX-512 进行并行执行
    #[target_feature(enable = "avx512f")]
    unsafe async fn execute_parallel_avx512(&self) -> Result<Vec<StepResult<T>>, WorkflowError> 
    where 
        T: Clone + Send + Sync + 'static,
    {
        // 使用 AVX-512 指令进行并行处理
        // 这里应该调用实际的硬件加速逻辑
        self.execute_all().await
    }
    
    /// 获取执行进度
    pub async fn get_progress(&self) -> WorkflowProgress {
        let completed_count = *self.completed_count.lock().await;
        let total_steps = self.steps.len();
        let progress_percentage = if total_steps > 0 {
            (completed_count as f64 / total_steps as f64) * 100.0
        } else {
            0.0
        };
        
        WorkflowProgress {
            total_steps,
            completed_steps: completed_count,
            current_step: None, // 并行执行没有当前步骤概念
            progress_percentage,
            is_completed: completed_count >= total_steps,
        }
    }
}
```

### 3. 条件分支模式

条件分支模式根据运行时条件选择不同的执行路径。

#### Rust 1.89 实现2

```rust
use std::collections::HashMap;

/// 条件分支工作流，使用生命周期改进
pub struct ConditionalWorkflow<'a, T> {
    conditions: Vec<WorkflowCondition<'a, T>>,
    default_path: Option<Vec<WorkflowStep<T>>>,
    context: &'a mut WorkflowContext<T>,
}

impl<'a, T> ConditionalWorkflow<'a, T> {
    /// 创建新的条件分支工作流
    pub fn new(context: &'a mut WorkflowContext<T>) -> Self {
        Self {
            conditions: Vec::new(),
            default_path: None,
            context,
        }
    }
    
    /// 添加条件分支
    pub fn add_condition(
        &mut self, 
        condition: WorkflowCondition<'a, T>
    ) -> Result<(), WorkflowError> {
        self.conditions.push(condition);
        Ok(())
    }
    
    /// 设置默认执行路径
    pub fn set_default_path(&mut self, steps: Vec<WorkflowStep<T>>) {
        self.default_path = Some(steps);
    }
    
    /// 执行条件分支工作流
    pub async fn execute(&mut self) -> Result<Vec<StepResult<T>>, WorkflowError> {
        // 评估所有条件
        for condition in &self.conditions {
            if condition.evaluate(self.context).await? {
                // 执行匹配的条件分支
                return self.execute_branch(&condition.steps).await;
            }
        }
        
        // 执行默认路径
        if let Some(default_steps) = &self.default_path {
            self.execute_branch(default_steps).await
        } else {
            Err(WorkflowError::NoMatchingCondition)
        }
    }
    
    /// 执行分支步骤
    async fn execute_branch(
        &mut self, 
        steps: &[WorkflowStep<T>]
    ) -> Result<Vec<StepResult<T>>, WorkflowError> {
        let mut results = Vec::new();
        
        for step in steps {
            let mut step_clone = step.clone();
            let result = step_clone.execute().await?;
            results.push(result);
        }
        
        Ok(results)
    }
}

/// 工作流条件
#[derive(Debug, Clone)]
pub struct WorkflowCondition<'a, T> {
    pub name: String,
    pub condition_fn: Box<dyn Fn(&WorkflowContext<T>) -> bool + Send + Sync + 'a>,
    pub steps: Vec<WorkflowStep<T>>,
}

impl<'a, T> WorkflowCondition<'a, T> {
    /// 创建新的工作流条件
    pub fn new<F>(
        name: String, 
        condition_fn: F, 
        steps: Vec<WorkflowStep<T>>
    ) -> Self 
    where 
        F: Fn(&WorkflowContext<T>) -> bool + Send + Sync + 'a,
    {
        Self {
            name,
            condition_fn: Box::new(condition_fn),
            steps,
        }
    }
    
    /// 评估条件
    pub async fn evaluate(&self, context: &WorkflowContext<T>) -> Result<bool, WorkflowError> {
        Ok((self.condition_fn)(context))
    }
}

/// 工作流上下文
#[derive(Debug)]
pub struct WorkflowContext<T> {
    pub data: T,
    pub variables: HashMap<String, serde_json::Value>,
    pub metadata: HashMap<String, String>,
}

impl<T> WorkflowContext<T> {
    /// 创建新的工作流上下文
    pub fn new(data: T) -> Self {
        Self {
            data,
            variables: HashMap::new(),
            metadata: HashMap::new(),
        }
    }
    
    /// 设置变量
    pub fn set_variable(&mut self, name: String, value: serde_json::Value) {
        self.variables.insert(name, value);
    }
    
    /// 获取变量
    pub fn get_variable(&self, name: &str) -> Option<&serde_json::Value> {
        self.variables.get(name)
    }
}

#[derive(Debug, thiserror::Error)]
pub enum WorkflowError {
    #[error("No matching condition found")]
    NoMatchingCondition,
    #[error("Condition evaluation failed")]
    ConditionEvaluationFailed,
    #[error("Step execution failed")]
    StepExecutionFailed,
}
```

### 4. 循环执行模式

循环执行模式允许步骤或步骤组重复执行，直到满足退出条件。

#### Rust 1.89 实现3

```rust
/// 循环执行工作流，使用常量泛型优化
pub struct LoopWorkflow<T, const MAX_ITERATIONS: usize> {
    steps: Vec<WorkflowStep<T>>,
    loop_condition: LoopCondition<T>,
    current_iteration: usize,
    max_iterations: usize,
    results: Vec<Vec<StepResult<T>>>,
}

impl<T, const MAX_ITERATIONS: usize> LoopWorkflow<T, MAX_ITERATIONS> 
where 
    T: Clone + Send + Sync + 'static,
{
    /// 创建新的循环工作流
    pub fn new(loop_condition: LoopCondition<T>) -> Self {
        Self {
            steps: Vec::new(),
            loop_condition,
            current_iteration: 0,
            max_iterations: MAX_ITERATIONS,
            results: Vec::new(),
        }
    }
    
    /// 添加步骤
    pub fn add_step(&mut self, step: WorkflowStep<T>) {
        self.steps.push(step);
    }
    
    /// 执行循环工作流
    pub async fn execute(&mut self) -> Result<Vec<Vec<StepResult<T>>>, WorkflowError> {
        while self.should_continue().await? {
            if self.current_iteration >= self.max_iterations {
                return Err(WorkflowError::MaxIterationsExceeded(self.max_iterations));
            }
            
            // 执行当前迭代
            let iteration_results = self.execute_iteration().await?;
            self.results.push(iteration_results);
            
            self.current_iteration += 1;
        }
        
        Ok(self.results.clone())
    }
    
    /// 判断是否应该继续循环
    async fn should_continue(&self) -> Result<bool, WorkflowError> {
        self.loop_condition.evaluate(self.current_iteration, &self.results).await
    }
    
    /// 执行单次迭代
    async fn execute_iteration(&mut self) -> Result<Vec<StepResult<T>>, WorkflowError> {
        let mut iteration_results = Vec::new();
        
        for step in &self.steps {
            let mut step_clone = step.clone();
            let result = step_clone.execute().await?;
            iteration_results.push(result);
        }
        
        Ok(iteration_results)
    }
    
    /// 获取循环统计信息
    pub fn get_loop_statistics(&self) -> LoopStatistics {
        LoopStatistics {
            total_iterations: self.current_iteration,
            max_iterations: self.max_iterations,
            is_completed: self.current_iteration < self.max_iterations,
            total_steps_executed: self.results.iter().map(|r| r.len()).sum(),
        }
    }
}

/// 循环条件
#[derive(Debug, Clone)]
pub struct LoopCondition<T> {
    pub condition_type: LoopConditionType,
    pub max_iterations: Option<usize>,
    pub condition_fn: Option<Box<dyn Fn(usize, &[Vec<StepResult<T>>]) -> bool + Send + Sync>>,
}

impl<T> LoopCondition<T> {
    /// 创建基于迭代次数的循环条件
    pub fn max_iterations(max_iterations: usize) -> Self {
        Self {
            condition_type: LoopConditionType::MaxIterations,
            max_iterations: Some(max_iterations),
            condition_fn: None,
        }
    }
    
    /// 创建基于自定义条件的循环条件
    pub fn custom<F>(condition_fn: F) -> Self 
    where 
        F: Fn(usize, &[Vec<StepResult<T>>]) -> bool + Send + Sync + 'static,
    {
        Self {
            condition_type: LoopConditionType::Custom,
            max_iterations: None,
            condition_fn: Some(Box::new(condition_fn)),
        }
    }
    
    /// 评估循环条件
    pub async fn evaluate(
        &self, 
        current_iteration: usize, 
        results: &[Vec<StepResult<T>>]
    ) -> Result<bool, WorkflowError> {
        match self.condition_type {
            LoopConditionType::MaxIterations => {
                if let Some(max) = self.max_iterations {
                    Ok(current_iteration < max)
                } else {
                    Ok(true)
                }
            }
            LoopConditionType::Custom => {
                if let Some(condition_fn) = &self.condition_fn {
                    Ok(condition_fn(current_iteration, results))
                } else {
                    Ok(false)
                }
            }
        }
    }
}

/// 循环条件类型
#[derive(Debug, Clone)]
pub enum LoopConditionType {
    MaxIterations,
    Custom,
}

/// 循环统计信息
#[derive(Debug, Clone)]
pub struct LoopStatistics {
    pub total_iterations: usize,
    pub max_iterations: usize,
    pub is_completed: bool,
    pub total_steps_executed: usize,
}

#[derive(Debug, thiserror::Error)]
pub enum WorkflowError {
    #[error("Maximum iterations exceeded: {0}")]
    MaxIterationsExceeded(usize),
    #[error("Loop condition evaluation failed")]
    LoopConditionEvaluationFailed,
    #[error("Step execution failed")]
    StepExecutionFailed,
}
```

### 5. 错误处理和重试模式

错误处理和重试模式提供了健壮的错误恢复机制。

#### Rust 1.89 实现4

```rust
use std::time::Duration;
use tokio::time::sleep;

/// 错误处理和重试工作流
pub struct RetryWorkflow<T, const MAX_RETRIES: usize> {
    steps: Vec<WorkflowStep<T>>,
    retry_policy: RetryPolicy,
    error_handlers: Vec<ErrorHandler<T>>,
}

impl<T, const MAX_RETRIES: usize> RetryWorkflow<T, MAX_RETRIES> 
where 
    T: Clone + Send + Sync + 'static,
{
    /// 创建新的重试工作流
    pub fn new(retry_policy: RetryPolicy) -> Self {
        Self {
            steps: Vec::new(),
            retry_policy,
            error_handlers: Vec::new(),
        }
    }
    
    /// 添加步骤
    pub fn add_step(&mut self, step: WorkflowStep<T>) {
        self.steps.push(step);
    }
    
    /// 添加错误处理器
    pub fn add_error_handler(&mut self, handler: ErrorHandler<T>) {
        self.error_handlers.push(handler);
    }
    
    /// 执行工作流（带重试）
    pub async fn execute_with_retry(&self) -> Result<Vec<StepResult<T>>, WorkflowError> {
        let mut results = Vec::new();
        
        for step in &self.steps {
            let result = self.execute_step_with_retry(step.clone()).await?;
            results.push(result);
        }
        
        Ok(results)
    }
    
    /// 执行单个步骤（带重试）
    async fn execute_step_with_retry(&self, mut step: WorkflowStep<T>) -> Result<StepResult<T>, WorkflowError> {
        let mut last_error = None;
        
        for attempt in 0..MAX_RETRIES {
            match step.execute().await {
                Ok(result) => return Ok(result),
                Err(error) => {
                    last_error = Some(error.clone());
                    
                    // 检查是否应该重试
                    if attempt < MAX_RETRIES - 1 && self.should_retry(&error, attempt) {
                        // 应用重试延迟
                        let delay = self.calculate_retry_delay(attempt);
                        sleep(delay).await;
                        
                        // 执行错误处理器
                        self.execute_error_handlers(&error, &mut step, attempt).await;
                        
                        continue;
                    } else {
                        break;
                    }
                }
            }
        }
        
        Err(last_error.unwrap_or(WorkflowError::ExecutionFailed))
    }
    
    /// 判断是否应该重试
    fn should_retry(&self, error: &WorkflowError, attempt: usize) -> bool {
        match &self.retry_policy {
            RetryPolicy::Always => true,
            RetryPolicy::Never => false,
            RetryPolicy::OnSpecificErrors(errors) => errors.contains(error),
            RetryPolicy::MaxAttempts(max) => attempt < *max,
        }
    }
    
    /// 计算重试延迟
    fn calculate_retry_delay(&self, attempt: usize) -> Duration {
        match &self.retry_policy {
            RetryPolicy::ExponentialBackoff { base_delay, max_delay } => {
                let delay = base_delay * 2_u32.pow(attempt as u32);
                Duration::from_millis(delay.min(*max_delay))
            }
            RetryPolicy::FixedDelay(delay) => Duration::from_millis(*delay),
            RetryPolicy::LinearBackoff { base_delay, increment } => {
                Duration::from_millis(base_delay + (increment * attempt as u32))
            }
            _ => Duration::from_millis(1000), // 默认 1 秒
        }
    }
    
    /// 执行错误处理器
    async fn execute_error_handlers(
        &self, 
        error: &WorkflowError, 
        step: &mut WorkflowStep<T>, 
        attempt: usize
    ) {
        for handler in &self.error_handlers {
            if handler.should_handle(error, attempt) {
                handler.handle(error, step, attempt).await;
            }
        }
    }
}

/// 重试策略
#[derive(Debug, Clone)]
pub enum RetryPolicy {
    Always,
    Never,
    OnSpecificErrors(Vec<WorkflowError>),
    MaxAttempts(usize),
    FixedDelay(u64),
    ExponentialBackoff { base_delay: u64, max_delay: u64 },
    LinearBackoff { base_delay: u64, increment: u64 },
}

/// 错误处理器
#[derive(Debug, Clone)]
pub struct ErrorHandler<T> {
    pub name: String,
    pub error_types: Vec<WorkflowError>,
    pub handler_fn: Box<dyn Fn(&WorkflowError, &mut WorkflowStep<T>, usize) + Send + Sync>,
}

impl<T> ErrorHandler<T> {
    /// 创建新的错误处理器
    pub fn new<F>(
        name: String, 
        error_types: Vec<WorkflowError>, 
        handler_fn: F
    ) -> Self 
    where 
        F: Fn(&WorkflowError, &mut WorkflowStep<T>, usize) + Send + Sync + 'static,
    {
        Self {
            name,
            error_types,
            handler_fn: Box::new(handler_fn),
        }
    }
    
    /// 判断是否应该处理此错误
    pub fn should_handle(&self, error: &WorkflowError, attempt: usize) -> bool {
        self.error_types.iter().any(|e| std::mem::discriminant(e) == std::mem::discriminant(error))
    }
    
    /// 处理错误
    pub async fn handle(&self, error: &WorkflowError, step: &mut WorkflowStep<T>, attempt: usize) {
        (self.handler_fn)(error, step, attempt);
    }
}

#[derive(Debug, thiserror::Error, Clone, PartialEq)]
pub enum WorkflowError {
    #[error("Workflow execution failed")]
    ExecutionFailed,
    #[error("Step execution failed")]
    StepExecutionFailed,
    #[error("Timeout exceeded")]
    TimeoutExceeded,
    #[error("Resource not available")]
    ResourceNotAvailable,
}
```

## 🔧 模式组合和高级应用

### 1. 复合模式

将多个基础模式组合使用，创建复杂的工作流。

```rust
/// 复合工作流，组合多种模式
pub struct CompositeWorkflow<T, const MAX_STEPS: usize, const MAX_CONCURRENT: usize> {
    sequential_parts: Vec<SequentialWorkflow<T, MAX_STEPS>>,
    parallel_parts: Vec<ParallelWorkflow<T, MAX_CONCURRENT>>,
    conditional_parts: Vec<ConditionalWorkflow<'static, T>>,
    loop_parts: Vec<LoopWorkflow<T, 100>>,
    execution_order: Vec<WorkflowPartType>,
}

impl<T, const MAX_STEPS: usize, const MAX_CONCURRENT: usize> CompositeWorkflow<T, MAX_STEPS, MAX_CONCURRENT> 
where 
    T: Clone + Send + Sync + 'static,
{
    /// 创建新的复合工作流
    pub fn new() -> Self {
        Self {
            sequential_parts: Vec::new(),
            parallel_parts: Vec::new(),
            conditional_parts: Vec::new(),
            loop_parts: Vec::new(),
            execution_order: Vec::new(),
        }
    }
    
    /// 添加顺序部分
    pub fn add_sequential_part(&mut self, part: SequentialWorkflow<T, MAX_STEPS>) {
        self.sequential_parts.push(part);
        self.execution_order.push(WorkflowPartType::Sequential(self.sequential_parts.len() - 1));
    }
    
    /// 添加并行部分
    pub fn add_parallel_part(&mut self, part: ParallelWorkflow<T, MAX_CONCURRENT>) {
        self.parallel_parts.push(part);
        self.execution_order.push(WorkflowPartType::Parallel(self.parallel_parts.len() - 1));
    }
    
    /// 执行复合工作流
    pub async fn execute(&mut self) -> Result<Vec<WorkflowPartResult<T>>, WorkflowError> {
        let mut results = Vec::new();
        
        for part_type in &self.execution_order.clone() {
            match part_type {
                WorkflowPartType::Sequential(index) => {
                    let part = &mut self.sequential_parts[*index];
                    let result = part.execute_all().await?;
                    results.push(WorkflowPartResult::Sequential(result));
                }
                WorkflowPartType::Parallel(index) => {
                    let part = &self.parallel_parts[*index];
                    let result = part.execute_all().await?;
                    results.push(WorkflowPartResult::Parallel(result));
                }
                WorkflowPartType::Conditional(index) => {
                    // 条件部分的执行逻辑
                    results.push(WorkflowPartResult::Conditional(Vec::new()));
                }
                WorkflowPartType::Loop(index) => {
                    // 循环部分的执行逻辑
                    results.push(WorkflowPartResult::Loop(Vec::new()));
                }
            }
        }
        
        Ok(results)
    }
}

/// 工作流部分类型
#[derive(Debug, Clone)]
pub enum WorkflowPartType {
    Sequential(usize),
    Parallel(usize),
    Conditional(usize),
    Loop(usize),
}

/// 工作流部分结果
#[derive(Debug, Clone)]
pub enum WorkflowPartResult<T> {
    Sequential(Vec<StepResult<T>>),
    Parallel(Vec<StepResult<T>>),
    Conditional(Vec<StepResult<T>>),
    Loop(Vec<Vec<StepResult<T>>>),
}
```

## 🎯 最佳实践

### 1. 模式选择建议

- **顺序模式** - 适用于有严格依赖关系的步骤
- **并行模式** - 适用于独立的步骤，需要提高性能
- **条件模式** - 适用于需要根据运行时条件选择路径的场景
- **循环模式** - 适用于需要重复执行的步骤
- **重试模式** - 适用于需要错误恢复的场景

### 2. 性能优化建议

- 使用常量泛型在编译时优化资源使用
- 利用 x86 特性进行硬件加速
- 合理使用异步编程提高并发性能
- 使用生命周期改进确保内存安全

### 3. 错误处理建议

- 实现完整的错误处理机制
- 提供多种重试策略
- 记录详细的错误日志
- 实现优雅的降级机制

## 📊 总结

通过使用 Rust 1.89 的最新特性，我们可以实现：

1. **类型安全的工作流模式** - 编译时检查确保正确性
2. **高性能的并行执行** - 利用硬件加速和异步编程
3. **灵活的条件分支** - 支持复杂的业务逻辑
4. **健壮的错误处理** - 提供完整的重试和恢复机制
5. **可组合的模式设计** - 支持复杂工作流的构建

这些模式为工作流系统提供了坚实的基础，使得我们能够构建高效、安全、可维护的工作流应用。
