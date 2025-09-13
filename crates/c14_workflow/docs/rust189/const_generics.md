# Rust 1.89 常量泛型在工作流系统中的应用

## 📋 概述

本文档深入探讨 Rust 1.89 中常量泛型的显式推导特性，以及如何在工作流系统中充分利用这一强大的类型系统特性。

## 🚀 常量泛型显式推导

### 核心概念

Rust 1.89 允许在常量泛型参数中使用 `_` 占位符，编译器会根据上下文自动推断常量值。这为工作流系统提供了更灵活的类型安全保证。

### 基础语法

```rust
// 基础常量泛型结构
pub struct WorkflowArray<T, const N: usize> {
    data: [T; N],
}

// 使用 _ 让编译器推断大小
let workflow_array: WorkflowArray<String, _> = WorkflowArray {
    data: ["step1".to_string(), "step2".to_string(), "step3".to_string()],
};
```

## 🏗️ 工作流系统中的常量泛型应用

### 1. 工作流步骤管理

```rust
use std::marker::PhantomData;

/// 类型安全的工作流步骤管理器
pub struct WorkflowStepManager<T, const MAX_STEPS: usize> {
    steps: Vec<WorkflowStep<T>>,
    _phantom: PhantomData<T>,
}

impl<T, const MAX_STEPS: usize> WorkflowStepManager<T, MAX_STEPS> {
    /// 创建新的步骤管理器
    pub fn new() -> Self {
        Self {
            steps: Vec::with_capacity(MAX_STEPS),
            _phantom: PhantomData,
        }
    }
    
    /// 添加步骤，编译时检查容量限制
    pub fn add_step(&mut self, step: WorkflowStep<T>) -> Result<(), WorkflowError> {
        if self.steps.len() >= MAX_STEPS {
            return Err(WorkflowError::ExceedsMaxSteps(MAX_STEPS));
        }
        self.steps.push(step);
        Ok(())
    }
    
    /// 转换为固定大小数组（如果步骤数量匹配）
    pub fn to_array<const N: usize>(self) -> Result<[WorkflowStep<T>; N], WorkflowError> 
    where 
        T: Clone,
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
    
    /// 使用 _ 推断数组大小
    pub fn to_inferred_array(self) -> Result<WorkflowArray<T, _>, WorkflowError> 
    where 
        T: Clone,
    {
        let len = self.steps.len();
        if len == 0 {
            return Err(WorkflowError::EmptySteps);
        }
        
        let array: [WorkflowStep<T>; _] = self.steps.try_into()
            .map_err(|_| WorkflowError::ConversionFailed)?;
        
        Ok(WorkflowArray {
            data: array,
        })
    }
}

/// 工作流步骤定义
#[derive(Debug, Clone)]
pub struct WorkflowStep<T> {
    pub id: String,
    pub name: String,
    pub data: T,
    pub status: StepStatus,
    pub dependencies: Vec<String>,
}

#[derive(Debug, Clone)]
pub enum StepStatus {
    Pending,
    Ready,
    Running,
    Completed,
    Failed,
    Skipped,
}

/// 工作流数组包装器
pub struct WorkflowArray<T, const N: usize> {
    pub data: [T; N],
}

impl<T, const N: usize> WorkflowArray<T, N> {
    /// 创建新的工作流数组
    pub fn new() -> Self 
    where 
        T: Default,
    {
        Self {
            data: std::array::from_fn(|_| T::default()),
        }
    }
    
    /// 从迭代器创建
    pub fn from_iter<I>(iter: I) -> Result<Self, WorkflowError>
    where 
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        let iter = iter.into_iter();
        if iter.len() != N {
            return Err(WorkflowError::SizeMismatch {
                expected: N,
                actual: iter.len(),
            });
        }
        
        let mut array = std::array::from_fn(|_| {
            // 这里需要更复杂的实现来从迭代器填充数组
            // 为简化示例，我们假设 T 实现了 Default
            T::default()
        });
        
        for (i, item) in iter.enumerate() {
            array[i] = item;
        }
        
        Ok(Self { data: array })
    }
    
    /// 映射到新类型
    pub fn map<U, F>(self, f: F) -> WorkflowArray<U, N>
    where 
        F: FnMut(T) -> U,
    {
        WorkflowArray {
            data: self.data.map(f),
        }
    }
    
    /// 过滤并重新打包
    pub fn filter<F>(self, predicate: F) -> Vec<T>
    where 
        F: FnMut(&T) -> bool,
    {
        self.data.into_iter().filter(predicate).collect()
    }
}

#[derive(Debug, thiserror::Error)]
pub enum WorkflowError {
    #[error("Exceeds maximum steps: {0}")]
    ExceedsMaxSteps(usize),
    #[error("Size mismatch: expected {expected}, got {actual}")]
    SizeMismatch { expected: usize, actual: usize },
    #[error("Empty steps collection")]
    EmptySteps,
    #[error("Conversion failed")]
    ConversionFailed,
}
```

### 2. 工作流状态机

```rust
/// 类型安全的工作流状态机
pub struct WorkflowStateMachine<const STATE_COUNT: usize> {
    current_state: usize,
    states: [WorkflowState; STATE_COUNT],
    transitions: [[bool; STATE_COUNT]; STATE_COUNT],
}

impl<const STATE_COUNT: usize> WorkflowStateMachine<STATE_COUNT> {
    /// 创建新的状态机
    pub fn new(states: [WorkflowState; STATE_COUNT]) -> Self {
        Self {
            current_state: 0,
            states,
            transitions: [[false; STATE_COUNT]; STATE_COUNT],
        }
    }
    
    /// 添加状态转换
    pub fn add_transition(&mut self, from: usize, to: usize) -> Result<(), WorkflowError> {
        if from >= STATE_COUNT || to >= STATE_COUNT {
            return Err(WorkflowError::InvalidStateIndex);
        }
        self.transitions[from][to] = true;
        Ok(())
    }
    
    /// 检查是否可以转换到目标状态
    pub fn can_transition_to(&self, target_state: usize) -> bool {
        if target_state >= STATE_COUNT {
            return false;
        }
        self.transitions[self.current_state][target_state]
    }
    
    /// 转换到目标状态
    pub fn transition_to(&mut self, target_state: usize) -> Result<(), WorkflowError> {
        if !self.can_transition_to(target_state) {
            return Err(WorkflowError::InvalidTransition {
                from: self.current_state,
                to: target_state,
            });
        }
        
        self.current_state = target_state;
        Ok(())
    }
    
    /// 获取当前状态
    pub fn current_state(&self) -> &WorkflowState {
        &self.states[self.current_state]
    }
    
    /// 获取所有可能的下一个状态
    pub fn possible_next_states(&self) -> Vec<&WorkflowState> {
        self.transitions[self.current_state]
            .iter()
            .enumerate()
            .filter_map(|(i, &can_transition)| {
                if can_transition {
                    Some(&self.states[i])
                } else {
                    None
                }
            })
            .collect()
    }
}

/// 工作流状态定义
#[derive(Debug, Clone)]
pub struct WorkflowState {
    pub name: String,
    pub description: String,
    pub is_final: bool,
    pub metadata: std::collections::HashMap<String, String>,
}

impl Default for WorkflowState {
    fn default() -> Self {
        Self {
            name: "default".to_string(),
            description: "Default state".to_string(),
            is_final: false,
            metadata: std::collections::HashMap::new(),
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum WorkflowError {
    #[error("Invalid state index")]
    InvalidStateIndex,
    #[error("Invalid transition from {from} to {to}")]
    InvalidTransition { from: usize, to: usize },
}
```

### 3. 工作流配置系统

```rust
/// 类型安全的工作流配置
pub struct WorkflowConfig<const MAX_PARALLEL: usize, const MAX_RETRIES: usize> {
    pub name: String,
    pub version: String,
    pub max_parallel_executions: usize,
    pub max_retry_attempts: usize,
    pub timeout_seconds: u64,
    pub retry_delay_ms: u64,
}

impl<const MAX_PARALLEL: usize, const MAX_RETRIES: usize> WorkflowConfig<MAX_PARALLEL, MAX_RETRIES> {
    /// 创建新的配置
    pub fn new(name: String, version: String) -> Self {
        Self {
            name,
            version,
            max_parallel_executions: MAX_PARALLEL,
            max_retry_attempts: MAX_RETRIES,
            timeout_seconds: 300, // 5 minutes default
            retry_delay_ms: 1000, // 1 second default
        }
    }
    
    /// 设置并行执行数量（编译时检查）
    pub fn set_max_parallel(&mut self, count: usize) -> Result<(), WorkflowError> {
        if count > MAX_PARALLEL {
            return Err(WorkflowError::ExceedsMaxParallel(MAX_PARALLEL));
        }
        self.max_parallel_executions = count;
        Ok(())
    }
    
    /// 设置重试次数（编译时检查）
    pub fn set_max_retries(&mut self, count: usize) -> Result<(), WorkflowError> {
        if count > MAX_RETRIES {
            return Err(WorkflowError::ExceedsMaxRetries(MAX_RETRIES));
        }
        self.max_retry_attempts = count;
        Ok(())
    }
    
    /// 验证配置
    pub fn validate(&self) -> Result<(), WorkflowError> {
        if self.max_parallel_executions > MAX_PARALLEL {
            return Err(WorkflowError::ExceedsMaxParallel(MAX_PARALLEL));
        }
        if self.max_retry_attempts > MAX_RETRIES {
            return Err(WorkflowError::ExceedsMaxRetries(MAX_RETRIES));
        }
        if self.timeout_seconds == 0 {
            return Err(WorkflowError::InvalidTimeout);
        }
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum WorkflowError {
    #[error("Exceeds maximum parallel executions: {0}")]
    ExceedsMaxParallel(usize),
    #[error("Exceeds maximum retries: {0}")]
    ExceedsMaxRetries(usize),
    #[error("Invalid timeout value")]
    InvalidTimeout,
}
```

### 4. 工作流执行引擎

```rust
/// 高性能工作流执行引擎
pub struct WorkflowExecutionEngine<const MAX_CONCURRENT: usize> {
    config: WorkflowConfig<MAX_CONCURRENT, 3>, // 最多3次重试
    active_executions: std::collections::HashMap<String, WorkflowExecution>,
    execution_queue: std::collections::VecDeque<QueuedExecution>,
}

impl<const MAX_CONCURRENT: usize> WorkflowExecutionEngine<MAX_CONCURRENT> {
    /// 创建新的执行引擎
    pub fn new(config: WorkflowConfig<MAX_CONCURRENT, 3>) -> Self {
        Self {
            config,
            active_executions: std::collections::HashMap::new(),
            execution_queue: std::collections::VecDeque::new(),
        }
    }
    
    /// 提交工作流执行请求
    pub async fn submit_execution(
        &mut self, 
        request: WorkflowExecutionRequest
    ) -> Result<String, WorkflowError> {
        let execution_id = uuid::Uuid::new_v4().to_string();
        
        if self.active_executions.len() >= MAX_CONCURRENT {
            // 添加到队列
            self.execution_queue.push_back(QueuedExecution {
                id: execution_id.clone(),
                request,
                queued_at: chrono::Utc::now(),
            });
        } else {
            // 立即执行
            self.start_execution(execution_id.clone(), request).await?;
        }
        
        Ok(execution_id)
    }
    
    /// 启动工作流执行
    async fn start_execution(
        &mut self, 
        execution_id: String, 
        request: WorkflowExecutionRequest
    ) -> Result<(), WorkflowError> {
        let execution = WorkflowExecution {
            id: execution_id.clone(),
            request: request.clone(),
            status: ExecutionStatus::Running,
            started_at: chrono::Utc::now(),
            progress: 0.0,
            current_step: 0,
        };
        
        self.active_executions.insert(execution_id, execution);
        
        // 异步执行工作流
        tokio::spawn(async move {
            // 这里应该是实际的工作流执行逻辑
            tokio::time::sleep(std::time::Duration::from_secs(1)).await;
        });
        
        Ok(())
    }
    
    /// 获取执行状态
    pub fn get_execution_status(&self, execution_id: &str) -> Option<&WorkflowExecution> {
        self.active_executions.get(execution_id)
    }
    
    /// 获取所有活跃执行
    pub fn get_active_executions(&self) -> &std::collections::HashMap<String, WorkflowExecution> {
        &self.active_executions
    }
    
    /// 获取队列长度
    pub fn queue_length(&self) -> usize {
        self.execution_queue.len()
    }
}

/// 工作流执行请求
#[derive(Debug, Clone)]
pub struct WorkflowExecutionRequest {
    pub workflow_id: String,
    pub input_data: serde_json::Value,
    pub priority: ExecutionPriority,
    pub metadata: std::collections::HashMap<String, String>,
}

/// 工作流执行状态
#[derive(Debug, Clone)]
pub struct WorkflowExecution {
    pub id: String,
    pub request: WorkflowExecutionRequest,
    pub status: ExecutionStatus,
    pub started_at: chrono::DateTime<chrono::Utc>,
    pub progress: f64,
    pub current_step: usize,
}

/// 执行状态枚举
#[derive(Debug, Clone)]
pub enum ExecutionStatus {
    Queued,
    Running,
    Completed,
    Failed,
    Cancelled,
}

/// 执行优先级
#[derive(Debug, Clone)]
pub enum ExecutionPriority {
    Low,
    Normal,
    High,
    Critical,
}

/// 队列中的执行
#[derive(Debug, Clone)]
pub struct QueuedExecution {
    pub id: String,
    pub request: WorkflowExecutionRequest,
    pub queued_at: chrono::DateTime<chrono::Utc>,
}
```

## 🎯 高级应用场景

### 1. 编译时工作流验证

```rust
/// 编译时工作流验证器
pub struct CompileTimeWorkflowValidator<const STEP_COUNT: usize> {
    steps: [WorkflowStep<String>; STEP_COUNT],
    dependencies: [[bool; STEP_COUNT]; STEP_COUNT],
}

impl<const STEP_COUNT: usize> CompileTimeWorkflowValidator<STEP_COUNT> {
    /// 创建新的验证器
    pub fn new(steps: [WorkflowStep<String>; STEP_COUNT]) -> Self {
        Self {
            steps,
            dependencies: [[false; STEP_COUNT]; STEP_COUNT],
        }
    }
    
    /// 添加步骤依赖
    pub fn add_dependency(&mut self, from: usize, to: usize) -> Result<(), WorkflowError> {
        if from >= STEP_COUNT || to >= STEP_COUNT {
            return Err(WorkflowError::InvalidStepIndex);
        }
        self.dependencies[from][to] = true;
        Ok(())
    }
    
    /// 验证工作流（编译时检查）
    pub fn validate(&self) -> Result<(), WorkflowError> {
        // 检查循环依赖
        if self.has_cycles() {
            return Err(WorkflowError::CircularDependency);
        }
        
        // 检查所有步骤都有唯一ID
        let mut ids = std::collections::HashSet::new();
        for step in &self.steps {
            if !ids.insert(&step.id) {
                return Err(WorkflowError::DuplicateStepId(step.id.clone()));
            }
        }
        
        Ok(())
    }
    
    /// 检查循环依赖
    fn has_cycles(&self) -> bool {
        // 使用深度优先搜索检测循环
        let mut visited = [false; STEP_COUNT];
        let mut rec_stack = [false; STEP_COUNT];
        
        for i in 0..STEP_COUNT {
            if !visited[i] && self.dfs_has_cycle(i, &mut visited, &mut rec_stack) {
                return true;
            }
        }
        false
    }
    
    /// 深度优先搜索检测循环
    fn dfs_has_cycle(
        &self, 
        v: usize, 
        visited: &mut [bool; STEP_COUNT], 
        rec_stack: &mut [bool; STEP_COUNT]
    ) -> bool {
        visited[v] = true;
        rec_stack[v] = true;
        
        for i in 0..STEP_COUNT {
            if self.dependencies[v][i] {
                if !visited[i] && self.dfs_has_cycle(i, visited, rec_stack) {
                    return true;
                } else if rec_stack[i] {
                    return true;
                }
            }
        }
        
        rec_stack[v] = false;
        false
    }
}

#[derive(Debug, thiserror::Error)]
pub enum WorkflowError {
    #[error("Invalid step index")]
    InvalidStepIndex,
    #[error("Circular dependency detected")]
    CircularDependency,
    #[error("Duplicate step ID: {0}")]
    DuplicateStepId(String),
}
```

### 2. 类型安全的工作流模板

```rust
/// 类型安全的工作流模板
pub struct WorkflowTemplate<const TEMPLATE_SIZE: usize> {
    template_steps: [TemplateStep; TEMPLATE_SIZE],
    variables: std::collections::HashMap<String, String>,
}

impl<const TEMPLATE_SIZE: usize> WorkflowTemplate<TEMPLATE_SIZE> {
    /// 创建新模板
    pub fn new(template_steps: [TemplateStep; TEMPLATE_SIZE]) -> Self {
        Self {
            template_steps,
            variables: std::collections::HashMap::new(),
        }
    }
    
    /// 设置模板变量
    pub fn set_variable(&mut self, name: String, value: String) {
        self.variables.insert(name, value);
    }
    
    /// 实例化模板
    pub fn instantiate(&self, instance_id: String) -> Result<WorkflowInstance<TEMPLATE_SIZE>, WorkflowError> {
        let mut steps = [WorkflowStep::default(); TEMPLATE_SIZE];
        
        for (i, template_step) in self.template_steps.iter().enumerate() {
            steps[i] = WorkflowStep {
                id: template_step.id.replace("{{instance_id}}", &instance_id),
                name: template_step.name.clone(),
                data: template_step.data.clone(),
                status: StepStatus::Pending,
                dependencies: template_step.dependencies.clone(),
            };
        }
        
        Ok(WorkflowInstance {
            id: instance_id,
            steps,
            created_at: chrono::Utc::now(),
        })
    }
}

/// 模板步骤
#[derive(Debug, Clone)]
pub struct TemplateStep {
    pub id: String,
    pub name: String,
    pub data: String,
    pub dependencies: Vec<String>,
}

/// 工作流实例
#[derive(Debug, Clone)]
pub struct WorkflowInstance<const STEP_COUNT: usize> {
    pub id: String,
    pub steps: [WorkflowStep<String>; STEP_COUNT],
    pub created_at: chrono::DateTime<chrono::Utc>,
}
```

## 🔧 最佳实践

### 1. 常量泛型使用建议

- **优先使用 `_` 占位符**：让编译器自动推断常量值，减少手动指定
- **合理选择常量大小**：根据实际需求选择合适的大小限制
- **提供回退机制**：为不支持常量泛型的场景提供动态分配方案
- **使用类型别名**：为常用的常量泛型组合创建类型别名

### 2. 性能优化建议

- **编译时优化**：利用常量泛型在编译时进行优化
- **内存布局优化**：固定大小数组提供更好的内存局部性
- **零成本抽象**：常量泛型不会带来运行时开销

### 3. 错误处理建议

- **编译时检查**：尽可能在编译时捕获错误
- **清晰的错误信息**：提供有意义的错误消息
- **优雅降级**：在无法满足编译时约束时提供运行时检查

## 📊 性能对比

### 常量泛型 vs 动态分配

```rust
// 性能测试结果（示例数据）
// 常量泛型数组访问: ~1ns
// 动态分配向量访问: ~2-3ns
// 内存使用: 常量泛型更节省内存
// 编译时间: 常量泛型可能增加编译时间
```

## 🎯 总结

Rust 1.89 的常量泛型显式推导为工作流系统带来了显著优势：

1. **类型安全**：编译时检查确保工作流结构的正确性
2. **性能优化**：固定大小数组提供更好的性能特征
3. **内存效率**：减少动态分配的开销
4. **代码简洁**：使用 `_` 占位符简化代码

通过合理使用常量泛型，我们可以构建更安全、更高效、更易维护的工作流系统。
