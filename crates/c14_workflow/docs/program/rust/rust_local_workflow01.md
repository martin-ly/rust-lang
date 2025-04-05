# 本地工作流系统设计与实现

## 目录

- [本地工作流系统设计与实现](#本地工作流系统设计与实现)
  - [目录](#目录)
  - [思维导图](#思维导图)
  - [1. 引言](#1-引言)
    - [1.1 背景与需求](#11-背景与需求)
  - [2. 工作流概念模型](#2-工作流概念模型)
    - [2.1 工作流定义](#21-工作流定义)
    - [2.2 核心概念](#22-核心概念)
  - [3. 形式化模型](#3-形式化模型)
    - [3.1 数学表示](#31-数学表示)
    - [3.2 状态转换系统](#32-状态转换系统)
  - [4. 系统架构](#4-系统架构)
    - [4.1 总体架构](#41-总体架构)
    - [4.2 核心组件](#42-核心组件)
  - [5. 核心组件实现](#5-核心组件实现)
    - [5.1 工作流定义](#51-工作流定义)
    - [5.2 执行引擎](#52-执行引擎)
    - [5.3 存储与持久化](#53-存储与持久化)
  - [6. 工作流执行与监控](#6-工作流执行与监控)
    - [6.1 调度与执行策略](#61-调度与执行策略)
    - [6.2 监控与日志系统](#62-监控与日志系统)
    - [6.3 故障恢复机制](#63-故障恢复机制)
  - [7. 云端同步机制](#7-云端同步机制)
    - [7.1 同步接口](#71-同步接口)
    - [7.2 版本控制与增量同步](#72-版本控制与增量同步)
    - [7.3 数据一致性保障](#73-数据一致性保障)
  - [8. 总结与展望](#8-总结与展望)
    - [8.1 系统总体集成](#81-系统总体集成)
    - [8.2 系统高级特性](#82-系统高级特性)
    - [8.3 应用场景](#83-应用场景)
    - [8.4 未来展望](#84-未来展望)

## 思维导图

```text
本地工作流系统
├── 概念模型
│   ├── 工作流定义
│   ├── 任务模型
│   ├── 依赖关系
│   └── 状态管理
├── 形式化模型
│   ├── 有向无环图表示
│   ├── 状态转换系统
│   └── 数据流规范
├── 系统架构
│   ├── 核心引擎
│   ├── 存储层
│   ├── 执行层
│   └── 同步层
├── 组件实现
│   ├── 工作流定义
│   ├── 执行引擎
│   ├── 调度器
│   ├── 任务处理器
│   └── 状态追踪器
├── 执行与监控
│   ├── 执行策略
│   ├── 日志系统
│   ├── 指标收集
│   └── 故障恢复
└── 云端同步
    ├── 数据一致性
    ├── 冲突解决
    ├── 版本控制
    └── 增量同步
```

## 1. 引言

本地工作流系统是一种能够在本地环境中定义、执行和管理复杂处理流程的框架。在许多场景下，我们需要在离线环境中运行工作流，或者在处理敏感数据时避免将数据发送到云端。本文将详细探讨本地工作流系统的设计原理、形式化模型，并给出基于Rust语言的实现方案。

### 1.1 背景与需求

本地工作流系统需要满足以下核心需求：

- 支持编排复杂的任务依赖关系
- 管理数据流和控制流
- 提供状态追踪和查询能力
- 支持与云端工作流的无缝集成
- 保证工作流执行的可靠性和可重现性

## 2. 工作流概念模型

### 2.1 工作流定义

工作流是由一系列相互关联的任务组成的有向无环图(DAG)，每个任务代表一个独立的计算单元，任务之间通过依赖关系连接。

### 2.2 核心概念

- **任务(Task)**: 工作流中的基本执行单元
- **依赖(Dependency)**: 任务之间的前后执行关系
- **数据流(DataFlow)**: 任务间传递的数据
- **状态(State)**: 任务和工作流的执行状态
- **执行器(Executor)**: 负责执行任务的组件

## 3. 形式化模型

### 3.1 数学表示

工作流可以形式化为一个三元组 \(T, D, S\)，其中：

- \(T\) 是任务集合 \(T = \{t_1, t_2, ..., t_n\}\)
- \(D\) 是依赖关系集合 \(D \subseteq T \times T\)，\((t_i, t_j) \in D\) 表示任务 \(t_j\) 依赖于任务 \(t_i\)
- \(S\) 是状态转换函数 \(S: T \times State \rightarrow State\)

### 3.2 状态转换系统

每个任务可以处于以下状态之一：

- PENDING: 等待执行
- RUNNING: 正在执行
- SUCCEEDED: 执行成功
- FAILED: 执行失败
- SKIPPED: 被跳过执行

工作流的执行可以被建模为一个状态转换系统，符合特定的转换规则。

## 4. 系统架构

### 4.1 总体架构

```text
+------------------+        +---------------+
|  工作流定义模块   |------->|  验证与解析模块 |
+------------------+        +---------------+
                                   |
                                   v
+------------------+        +---------------+        +-----------------+
|   存储与持久化    |<------>|  执行引擎核心  |------->|  任务执行器池   |
+------------------+        +---------------+        +-----------------+
                                   ^                        |
                                   |                        v
+------------------+        +---------------+        +-----------------+
|   云端同步模块    |<------>|  状态管理模块  |<-------|  监控与日志模块  |
+------------------+        +---------------+        +-----------------+
```

### 4.2 核心组件

1. **工作流定义模块**: 提供API用于定义工作流结构
2. **验证与解析模块**: 确保工作流定义的正确性
3. **执行引擎核心**: 负责调度和执行工作流
4. **任务执行器池**: 执行具体任务的组件集合
5. **状态管理模块**: 追踪和管理工作流状态
6. **存储与持久化**: 保存工作流定义和执行记录
7. **监控与日志模块**: 收集执行指标和日志
8. **云端同步模块**: 与云端工作流系统交互

## 5. 核心组件实现

### 5.1 工作流定义

```rust
use std::collections::HashMap;
use uuid::Uuid;
use chrono::{DateTime, Utc};
use serde::{Serialize, Deserialize};

/// 任务状态枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum TaskState {
    Pending,
    Running,
    Succeeded,
    Failed,
    Skipped,
}

/// 任务定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Task {
    pub id: String,
    pub name: String,
    pub command: String,
    pub dependencies: Vec<String>,
    pub state: TaskState,
    pub retry_policy: RetryPolicy,
    pub timeout_seconds: Option<u64>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    pub metadata: HashMap<String, String>,
}

/// 重试策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RetryPolicy {
    pub max_retries: u32,
    pub backoff_seconds: u32,
}

/// 工作流定义
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Workflow {
    pub id: String,
    pub name: String,
    pub description: String,
    pub tasks: HashMap<String, Task>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    pub metadata: HashMap<String, String>,
}

impl Workflow {
    /// 创建新的工作流
    pub fn new(name: &str, description: &str) -> Self {
        let now = Utc::now();
        Workflow {
            id: Uuid::new_v4().to_string(),
            name: name.to_string(),
            description: description.to_string(),
            tasks: HashMap::new(),
            created_at: now,
            updated_at: now,
            metadata: HashMap::new(),
        }
    }

    /// 添加任务到工作流
    pub fn add_task(&mut self, task: Task) -> Result<(), String> {
        // 验证任务依赖关系，防止循环依赖
        for dep_id in &task.dependencies {
            if !self.tasks.contains_key(dep_id) {
                return Err(format!("Dependency {} not found", dep_id));
            }
        }
        
        self.tasks.insert(task.id.clone(), task);
        self.updated_at = Utc::now();
        Ok(())
    }

    /// 验证工作流是否有效
    pub fn validate(&self) -> Result<(), String> {
        // 检查是否存在循环依赖
        if let Err(e) = self.check_cyclic_dependencies() {
            return Err(e);
        }
        
        // 其他验证...
        
        Ok(())
    }

    /// 检查是否存在循环依赖
    fn check_cyclic_dependencies(&self) -> Result<(), String> {
        // 使用深度优先搜索检测循环
        let mut visited = HashMap::new();
        let mut rec_stack = HashMap::new();
        
        for task_id in self.tasks.keys() {
            if !visited.contains_key(task_id) {
                if self.is_cyclic_util(task_id, &mut visited, &mut rec_stack) {
                    return Err("Cyclic dependency detected".to_string());
                }
            }
        }
        
        Ok(())
    }

    fn is_cyclic_util(
        &self, 
        task_id: &str, 
        visited: &mut HashMap<String, bool>,
        rec_stack: &mut HashMap<String, bool>
    ) -> bool {
        visited.insert(task_id.to_string(), true);
        rec_stack.insert(task_id.to_string(), true);
        
        if let Some(task) = self.tasks.get(task_id) {
            for dep_id in &task.dependencies {
                if !visited.contains_key(dep_id) {
                    if self.is_cyclic_util(dep_id, visited, rec_stack) {
                        return true;
                    }
                } else if rec_stack.get(dep_id) == Some(&true) {
                    return true;
                }
            }
        }
        
        rec_stack.insert(task_id.to_string(), false);
        false
    }
}
```

### 5.2 执行引擎

```rust
use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;
use tokio::time::{timeout, Duration};
use async_trait::async_trait;

use crate::workflow::{Workflow, Task, TaskState};

/// 任务处理器特质
#[async_trait]
pub trait TaskHandler: Send + Sync {
    async fn handle(&self, task: &Task) -> Result<(), String>;
}

/// 默认命令行任务处理器
pub struct CommandTaskHandler;

#[async_trait]
impl TaskHandler for CommandTaskHandler {
    async fn handle(&self, task: &Task) -> Result<(), String> {
        println!("Executing task: {}", task.name);
        
        let output = tokio::process::Command::new("sh")
            .arg("-c")
            .arg(&task.command)
            .output()
            .await
            .map_err(|e| format!("Failed to execute command: {}", e))?;
            
        if output.status.success() {
            Ok(())
        } else {
            let stderr = String::from_utf8_lossy(&output.stderr);
            Err(format!("Command failed: {}", stderr))
        }
    }
}

/// 工作流执行引擎
pub struct WorkflowEngine {
    task_handlers: HashMap<String, Box<dyn TaskHandler>>,
    pub workflow_state: Arc<Mutex<HashMap<String, TaskState>>>,
}

impl WorkflowEngine {
    /// 创建新的工作流执行引擎
    pub fn new() -> Self {
        let mut engine = WorkflowEngine {
            task_handlers: HashMap::new(),
            workflow_state: Arc::new(Mutex::new(HashMap::new())),
        };
        
        // 注册默认的命令处理器
        engine.register_handler("command", Box::new(CommandTaskHandler));
        
        engine
    }
    
    /// 注册任务处理器
    pub fn register_handler(&mut self, handler_type: &str, handler: Box<dyn TaskHandler>) {
        self.task_handlers.insert(handler_type.to_string(), handler);
    }
    
    /// 执行工作流
    pub async fn execute(&self, workflow: &Workflow) -> Result<(), String> {
        // 验证工作流
        workflow.validate()?;
        
        // 初始化工作流状态
        {
            let mut state = self.workflow_state.lock().unwrap();
            for (id, _) in &workflow.tasks {
                state.insert(id.clone(), TaskState::Pending);
            }
        }
        
        // 构建依赖图和入度表
        let mut dependencies = HashMap::new();
        let mut in_degree = HashMap::new();
        
        for (id, task) in &workflow.tasks {
            dependencies.insert(id.clone(), task.dependencies.clone());
            in_degree.insert(id.clone(), task.dependencies.len());
        }
        
        // 查找入度为0的任务（没有依赖的任务）
        let mut queue = VecDeque::new();
        for (id, degree) in &in_degree {
            if *degree == 0 {
                queue.push_back(id.clone());
            }
        }
        
        // 创建任务执行通道
        let (tx, mut rx) = mpsc::channel(32);
        
        // 启动执行循环
        let state_arc = self.workflow_state.clone();
        
        tokio::spawn(async move {
            while let Some((task_id, result)) = rx.recv().await {
                let mut state = state_arc.lock().unwrap();
                
                // 更新任务状态
                match result {
                    Ok(()) => {
                        state.insert(task_id.clone(), TaskState::Succeeded);
                    }
                    Err(_) => {
                        state.insert(task_id.clone(), TaskState::Failed);
                    }
                }
                
                // 更新依赖关系
                for (id, deps) in &dependencies {
                    if deps.contains(&task_id) {
                        if let Some(degree) = in_degree.get_mut(id) {
                            *degree -= 1;
                            if *degree == 0 {
                                queue.push_back(id.clone());
                            }
                        }
                    }
                }
            }
        });
        
        // 执行工作流
        while let Some(task_id) = queue.pop_front() {
            let task = workflow.tasks.get(&task_id).unwrap().clone();
            
            // 检查所有依赖是否成功
            let mut can_execute = true;
            {
                let state = self.workflow_state.lock().unwrap();
                for dep_id in &task.dependencies {
                    if state.get(dep_id) != Some(&TaskState::Succeeded) {
                        can_execute = false;
                        break;
                    }
                }
            }
            
            if !can_execute {
                // 跳过此任务
                let mut state = self.workflow_state.lock().unwrap();
                state.insert(task_id.clone(), TaskState::Skipped);
                continue;
            }
            
            // 更新任务状态为运行中
            {
                let mut state = self.workflow_state.lock().unwrap();
                state.insert(task_id.clone(), TaskState::Running);
            }
            
            // 获取任务处理器
            let handler = self.task_handlers.get("command").unwrap();
            
            // 克隆发送端
            let tx = tx.clone();
            let task_id_clone = task_id.clone();
            
            // 异步执行任务
            tokio::spawn(async move {
                let result = if let Some(timeout_secs) = task.timeout_seconds {
                    match timeout(Duration::from_secs(timeout_secs), handler.handle(&task)).await {
                        Ok(r) => r,
                        Err(_) => Err("Task timed out".to_string()),
                    }
                } else {
                    handler.handle(&task).await
                };
                
                // 发送执行结果
                let _ = tx.send((task_id_clone, result)).await;
            });
        }
        
        Ok(())
    }
}
```

### 5.3 存储与持久化

```rust
use std::path::Path;
use std::fs::{self, File};
use std::io::{Read, Write};
use serde::{Serialize, Deserialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

use crate::workflow::{Workflow, Task, TaskState};

/// 工作流执行记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowExecution {
    pub id: String,
    pub workflow_id: String,
    pub workflow_name: String,
    pub start_time: DateTime<Utc>,
    pub end_time: Option<DateTime<Utc>>,
    pub task_states: Vec<TaskExecutionState>,
    pub status: ExecutionStatus,
}

/// 任务执行状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaskExecutionState {
    pub task_id: String,
    pub task_name: String,
    pub state: TaskState,
    pub start_time: Option<DateTime<Utc>>,
    pub end_time: Option<DateTime<Utc>>,
    pub error_message: Option<String>,
    pub retries: u32,
}

/// 执行状态枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExecutionStatus {
    Running,
    Completed,
    Failed,
    Cancelled,
}

/// 存储接口特质
pub trait WorkflowStorage: Send + Sync {
    fn save_workflow(&self, workflow: &Workflow) -> Result<(), String>;
    fn load_workflow(&self, id: &str) -> Result<Workflow, String>;
    fn list_workflows(&self) -> Result<Vec<Workflow>, String>;
    fn delete_workflow(&self, id: &str) -> Result<(), String>;
    
    fn save_execution(&self, execution: &WorkflowExecution) -> Result<(), String>;
    fn load_execution(&self, id: &str) -> Result<WorkflowExecution, String>;
    fn list_executions(&self, workflow_id: &str) -> Result<Vec<WorkflowExecution>, String>;
}

/// 文件系统存储实现
pub struct FileSystemStorage {
    workflows_dir: String,
    executions_dir: String,
}

impl FileSystemStorage {
    pub fn new(base_dir: &str) -> Self {
        let workflows_dir = format!("{}/workflows", base_dir);
        let executions_dir = format!("{}/executions", base_dir);
        
        // 确保目录存在
        fs::create_dir_all(&workflows_dir).expect("Failed to create workflows directory");
        fs::create_dir_all(&executions_dir).expect("Failed to create executions directory");
        
        FileSystemStorage {
            workflows_dir,
            executions_dir,
        }
    }
    
    fn workflow_path(&self, id: &str) -> String {
        format!("{}/{}.json", self.workflows_dir, id)
    }
    
    fn execution_path(&self, id: &str) -> String {
        format!("{}/{}.json", self.executions_dir, id)
    }
}

impl WorkflowStorage for FileSystemStorage {
    fn save_workflow(&self, workflow: &Workflow) -> Result<(), String> {
        let path = self.workflow_path(&workflow.id);
        let json = serde_json::to_string_pretty(workflow)
            .map_err(|e| format!("Failed to serialize workflow: {}", e))?;
            
        let mut file = File::create(path)
            .map_err(|e| format!("Failed to create workflow file: {}", e))?;
            
        file.write_all(json.as_bytes())
            .map_err(|e| format!("Failed to write workflow data: {}", e))?;
            
        Ok(())
    }
    
    fn load_workflow(&self, id: &str) -> Result<Workflow, String> {
        let path = self.workflow_path(id);
        let mut file = File::open(path)
            .map_err(|e| format!("Failed to open workflow file: {}", e))?;
            
        let mut contents = String::new();
        file.read_to_string(&mut contents)
            .map_err(|e| format!("Failed to read workflow file: {}", e))?;
            
        serde_json::from_str(&contents)
            .map_err(|e| format!("Failed to deserialize workflow: {}", e))
    }
    
    fn list_workflows(&self) -> Result<Vec<Workflow>, String> {
        let mut workflows = Vec::new();
        
        for entry in fs::read_dir(&self.workflows_dir)
            .map_err(|e| format!("Failed to read workflows directory: {}", e))? {
                
            let entry = entry
                .map_err(|e| format!("Failed to read directory entry: {}", e))?;
                
            let path = entry.path();
            if path.is_file() && path.extension().map_or(false, |ext| ext == "json") {
                if let Some(file_stem) = path.file_stem() {
                    if let Some(id) = file_stem.to_str() {
                        let workflow = self.load_workflow(id)?;
                        workflows.push(workflow);
                    }
                }
            }
        }
        
        Ok(workflows)
    }
    
    fn delete_workflow(&self, id: &str) -> Result<(), String> {
        let path = self.workflow_path(id);
        fs::remove_file(path)
            .map_err(|e| format!("Failed to delete workflow file: {}", e))
    }
    
    fn save_execution(&self, execution: &WorkflowExecution) -> Result<(), String> {
        let path = self.execution_path(&execution.id);
        let json = serde_json::to_string_pretty(execution)
            .map_err(|e| format!("Failed to serialize execution: {}", e))?;
            
        let mut file = File::create(path)
            .map_err(|e| format!("Failed to create execution file: {}", e))?;
            
        file.write_all(json.as_bytes())
            .map_err(|e| format!("Failed to write execution data: {}", e))?;
            
        Ok(())
    }
    
    fn load_execution(&self, id: &str) -> Result<WorkflowExecution, String> {
        let path = self.execution_path(id);
        let mut file = File::open(path)
            .map_err(|e| format!("Failed to open execution file: {}", e))?;
            
        let mut contents = String::new();
        file.read_to_string(&mut contents)
            .map_err(|e| format!("Failed to read execution file: {}", e))?;
            
        serde_json::from_str(&contents)
            .map_err(|e| format!("Failed to deserialize execution: {}", e))
    }
    
    fn list_executions(&self, workflow_id: &str) -> Result<Vec<WorkflowExecution>, String> {
        let mut executions = Vec::new();
        
        for entry in fs::read_dir(&self.executions_dir)
            .map_err(|e| format!("Failed to read executions directory: {}", e))? {
                
            let entry = entry
                .map_err(|e| format!("Failed to read directory entry: {}", e))?;
                
            let path = entry.path();
            if path.is_file() && path.extension().map_or(false, |ext| ext == "json") {
                if let Some(file_stem) = path.file_stem() {
                    if let Some(id) = file_stem.to_str() {
                        let execution = self.load_execution(id)?;
                        if execution.workflow_id == workflow_id {
                            executions.push(execution);
                        }
                    }
                }
            }
        }
        
        // 按开始时间排序
        executions.sort_by(|a, b| a.start_time.cmp(&b.start_time));
        
        Ok(executions)
    }
}
```

## 6. 工作流执行与监控

### 6.1 调度与执行策略

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;
use tokio::task::JoinSet;
use chrono::Utc;
use async_trait::async_trait;

use crate::workflow::{Workflow, Task, TaskState};
use crate::storage::{WorkflowStorage, WorkflowExecution, TaskExecutionState, ExecutionStatus};
use crate::engine::WorkflowEngine;

/// 调度策略特质
#[async_trait]
pub trait SchedulingStrategy: Send + Sync {
    async fn schedule_tasks(
        &self, 
        workflow: &Workflow, 
        ready_tasks: Vec<&Task>
    ) -> Vec<&Task>;
}

/// 默认的调度策略（先进先出）
pub struct FifoStrategy;

#[async_trait]
impl SchedulingStrategy for FifoStrategy {
    async fn schedule_tasks(
        &self, 
        _workflow: &Workflow, 
        ready_tasks: Vec<&Task>
    ) -> Vec<&Task> {
        // 简单地按照提供的顺序返回任务
        ready_tasks
    }
}

/// 资源感知的调度策略
pub struct ResourceAwareStrategy {
    resource_limits: HashMap<String, usize>,
    current_usage: Arc<Mutex<HashMap<String, usize>>>,
}

impl ResourceAwareStrategy {
    pub fn new(resource_limits: HashMap<String, usize>) -> Self {
        ResourceAwareStrategy {
            resource_limits,
            current_usage: Arc::new(Mutex::new(HashMap::new())),
        }
    }
}

#[async_trait]
impl SchedulingStrategy for ResourceAwareStrategy {
    async fn schedule_tasks(
        &self, 
        workflow: &Workflow, 
        ready_tasks: Vec<&Task>
    ) -> Vec<&Task> {
        let mut scheduled_tasks = Vec::new();
        let mut current_usage = self.current_usage.lock().unwrap();
        
        for task in ready_tasks {
            // 检查每个资源是否超出限制
            let mut can_schedule = true;
            
            // 这里假设任务元数据中包含资源需求
            for (resource, limit) in &self.resource_limits {
                if let Some(requirement) = task.metadata.get(resource) {
                    if let Ok(req_amount) = requirement.parse::<usize>() {
                        let current = *current_usage.get(resource).unwrap_or(&0);
                        if current + req_amount > *limit {
                            can_schedule = false;
                            break;
                        }
                    }
                }
            }
            
            if can_schedule {
                // 更新资源使用情况
                for (resource, _) in &self.resource_limits {
                    if let Some(requirement) = task.metadata.get(resource) {
                        if let Ok(req_amount) = requirement.parse::<usize>() {
                            let entry = current_usage.entry(resource.clone()).or_insert(0);
                            *entry += req_amount;
                        }
                    }
                }
                
                scheduled_tasks.push(task);
            }
        }
        
        scheduled_tasks
    }
}

/// 工作流调度器
pub struct WorkflowScheduler<S: WorkflowStorage> {
    engine: Arc<WorkflowEngine>,
    storage: Arc<S>,
    strategy: Box<dyn SchedulingStrategy>,
}

impl<S: WorkflowStorage + 'static> WorkflowScheduler<S> {
    pub fn new(engine: Arc<WorkflowEngine>, storage: Arc<S>, strategy: Box<dyn SchedulingStrategy>) -> Self {
        WorkflowScheduler {
            engine,
            storage,
            strategy,
        }
    }
    
    /// 启动工作流执行
    pub async fn run_workflow(&self, workflow_id: &str) -> Result<String, String> {
        // 加载工作流
        let workflow = self.storage.load_workflow(workflow_id)?;
        
        // 创建执行记录
        let execution_id = uuid::Uuid::new_v4().to_string();
        let mut execution = WorkflowExecution {
            id: execution_id.clone(),
            workflow_id: workflow.id.clone(),
            workflow_name: workflow.name.clone(),
            start_time: Utc::now(),
            end_time: None,
            task_states: Vec::new(),
            status: ExecutionStatus::Running,
        };
        
        // 初始化任务状态
        for (id, task) in &workflow.tasks {
            execution.task_states.push(TaskExecutionState {
                task_id: id.clone(),
                task_name: task.name.clone(),
                state: TaskState::Pending,
                start_time: None,
                end_time: None,
                error_message: None,
                retries: 0,
            });
        }
        
        // 保存初始执行记录
        self.storage.save_execution(&execution)?;
        
        // 异步执行工作流
        let engine = self.engine.clone();
        let storage = self.storage.clone();
        let workflow_clone = workflow.clone();
        let execution_id_clone = execution_id.clone();
        
        tokio::spawn(async move {
            // 执行工作流
            let result = engine.execute(&workflow_clone).await;
            
            // 更新执行状态
            let mut execution = match storage.load_execution(&execution_id_clone) {
                Ok(exec) => exec,
                Err(_) => return,
            };
            
            execution.end_time = Some(Utc::now());
            execution.status = match result {
                Ok(_) => ExecutionStatus::Completed,
                Err(_) => ExecutionStatus::Failed,
            };
            
            // 从引擎获取最终任务状态
            let state_map = engine.workflow_state.lock().unwrap().clone();
            for task_state in &mut execution.task_states {
                if let Some(state) = state_map.get(&task_state.task_id) {
                    task_state.state = *state;
                }
            }
            
            let _ = storage.save_execution(&execution);
        });
        
        Ok(execution_id)
    }
    
    /// 获取执行状态
    pub fn get_execution_status(&self, execution_id: &str) -> Result<ExecutionStatus, String> {
        let execution = self.storage.load_execution(execution_id)?;
        Ok(execution.status)
    }
    
    /// 取消执行
    pub async fn cancel_execution(&self, execution_id: &str) -> Result<(), String> {
        // 加载执行记录
        let mut execution = self.storage.load_execution(execution_id)?;
        
        // 只能取消运行中的工作流
        if execution.status != ExecutionStatus::Running {
            return Err("Cannot cancel execution that is not running".to_string());
        }
        
        // 更新状态
        execution.status = ExecutionStatus::Cancelled;
        execution.end_time = Some(Utc::now());
        
        // 保存更新后的执行记录
        self.storage.save_execution(&execution)?;
        
        // 实际取消逻辑需要更复杂的实现
        // 这里仅作为示例
        
        Ok(())
    }
}
```

### 6.2 监控与日志系统

```rust
use std::sync::{Arc, Mutex};
use chrono::{DateTime, Utc};
use serde::{Serialize, Deserialize};
use std::collections::HashMap;
use tokio::sync::broadcast;

/// 日志级别枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum LogLevel {
    Debug,
    Info,
    Warning,
    Error,
}

/// 工作流日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowLogEntry {
    pub timestamp: DateTime<Utc>,
    pub workflow_id: String,
    pub execution_id: Option<String>,
    pub task_id: Option<String>,
    pub level: LogLevel,
    pub message: String,
}

/// 工作流指标条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MetricEntry {
    pub timestamp: DateTime<Utc>,
    pub workflow_id: String,
    pub execution_id: Option<String>,
    pub task_id: Option<String>,
    pub name: String,
    pub value: f64,
    pub tags: HashMap<String, String>,
}

/// 监控接口
pub trait MonitoringBackend: Send + Sync {
    fn log(&self, entry: WorkflowLogEntry);
    fn record_metric(&self, metric: MetricEntry);
}

/// 内存监控后端实现
pub struct InMemoryMonitoring {
    logs: Arc<Mutex<Vec<WorkflowLogEntry>>>,
    metrics: Arc<Mutex<Vec<MetricEntry>>>,
    log_sender: broadcast::Sender<WorkflowLogEntry>,
    metric_sender: broadcast::Sender<MetricEntry>,
}

impl InMemoryMonitoring {
    pub fn new() -> Self {
        let (log_sender, _) = broadcast::channel(1000);
        let (metric_sender, _) = broadcast::channel(1000);
        
        InMemoryMonitoring {
            logs: Arc::new(Mutex::new(Vec::new())),
            metrics: Arc::new(Mutex::new(Vec::new())),
            log_sender,
            metric_sender,
        }
    }
    
    pub fn subscribe_logs(&self) -> broadcast::Receiver<WorkflowLogEntry> {
        self.log_sender.subscribe()
    }
    
    pub fn subscribe_metrics(&self) -> broadcast::Receiver<MetricEntry> {
        self.metric_sender.subscribe()
    }
    
    pub fn get_logs(
        &self, 
        workflow_id: Option<&str>, 
        execution_id: Option<&str>, 
        task_id: Option<&str>, 
        level: Option<LogLevel>,
        limit: usize
    ) -> Vec<WorkflowLogEntry> {
        let logs = self.logs.lock().unwrap();
        
        logs.iter()
           .filter(|log| {
               (workflow_id.is_none() || Some(log.workflow_id.as_str()) == workflow_id) &&
               (execution_id.is_none() || log.execution_id.as_ref().map(|s| s.as_str()) == execution_id) &&
               (task_id.is_none() || log.task_id.as_ref().map(|s| s.as_str()) == task_id) &&
               (level.is_none() || Some(log.level) == level)
           })
           .rev() // 最新的日志优先
           .take(limit)
           .cloned()
           .collect()
    }
    
    pub fn get_metrics(
        &self,
        workflow_id: Option<&str>,
        execution_id: Option<&str>,
        task_id: Option<&str>,
        metric_name: Option<&str>,
        limit: usize
    ) -> Vec<MetricEntry> {
        let metrics = self.metrics.lock().unwrap();
        
        metrics.iter()
              .filter(|metric| {
                  (workflow_id.is_none() || Some(metric.workflow_id.as_str()) == workflow_id) &&
                  (execution_id.is_none() || metric.execution_id.as_ref().map(|s| s.as_str()) == execution_id) &&
                  (task_id.is_none() || metric.task_id.as_ref().map(|s| s.as_str()) == task_id) &&
                  (metric_name.is_none() || Some(metric.name.as_str()) == metric_name)
              })
              .rev() // 最新的指标优先
              .take(limit)
              .cloned()
              .collect()
    }
}

impl MonitoringBackend for InMemoryMonitoring {
    fn log(&self, entry: WorkflowLogEntry) {
        // 添加到内存存储
        {
            let mut logs = self.logs.lock().unwrap();
            logs.push(entry.clone());
            
            // 限制日志数量，避免内存无限增长
            if logs.len() > 10000 {
                logs.remove(0);
            }
        }
        
        // 广播日志事件
        let _ = self.log_sender.send(entry);
    }
    
    fn record_metric(&self, metric: MetricEntry) {
        // 添加到内存存储
        {
            let mut metrics = self.metrics.lock().unwrap();
            metrics.push(metric.clone());
            
            // 限制指标数量，避免内存无限增长
            if metrics.len() > 10000 {
                metrics.remove(0);
            }
        }
        
        // 广播指标事件
        let _ = self.metric_sender.send(metric);
    }
}
```

### 6.3 故障恢复机制

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::time::{sleep, Duration};
use uuid::Uuid;
use chrono::Utc;
use serde::{Serialize, Deserialize};

use crate::workflow::{Workflow, Task, TaskState};
use crate::storage::{WorkflowStorage, WorkflowExecution, ExecutionStatus};
use crate::engine::WorkflowEngine;
use crate::monitoring::{WorkflowLogEntry, LogLevel, MonitoringBackend};

/// 工作流检查点
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowCheckpoint {
    pub id: String,
    pub execution_id: String,
    pub workflow_id: String,
    pub timestamp: chrono::DateTime<Utc>,
    pub task_states: HashMap<String, TaskState>,
    pub task_outputs: HashMap<String, String>,
}

/// 故障恢复管理器
pub struct RecoveryManager<S: WorkflowStorage, M: MonitoringBackend> {
    storage: Arc<S>,
    monitoring: Arc<M>,
    checkpoints: Arc<Mutex<HashMap<String, WorkflowCheckpoint>>>,
    engine: Arc<WorkflowEngine>,
}

impl<S: WorkflowStorage + 'static, M: MonitoringBackend + 'static> RecoveryManager<S, M> {
    pub fn new(storage: Arc<S>, monitoring: Arc<M>, engine: Arc<WorkflowEngine>) -> Self {
        RecoveryManager {
            storage,
            monitoring,
            checkpoints: Arc::new(Mutex::new(HashMap::new())),
            engine,
        }
    }
    
    /// 创建工作流检查点
    pub fn create_checkpoint(&self, execution_id: &str) -> Result<String, String> {
        // 加载执行记录
        let execution = self.storage.load_execution(execution_id)?;
        
        // 只能为正在运行的工作流创建检查点
        if execution.status != ExecutionStatus::Running {
            return Err("Cannot create checkpoint for non-running workflow".to_string());
        }
        
        // 获取当前任务状态
        let task_states = {
            let state_map = self.engine.workflow_state.lock().unwrap();
            state_map.clone()
        };
        
        // 创建检查点
        let checkpoint = WorkflowCheckpoint {
            id: Uuid::new_v4().to_string(),
            execution_id: execution_id.to_string(),
            workflow_id: execution.workflow_id,
            timestamp: Utc::now(),
            task_states,
            task_outputs: HashMap::new(), // 这里需要额外实现获取任务输出的逻辑
        };
        
        // 保存检查点
        {
            let mut checkpoints = self.checkpoints.lock().unwrap();
            checkpoints.insert(checkpoint.id.clone(), checkpoint.clone());
        }
        
        // 记录日志
        self.monitoring.log(WorkflowLogEntry {
            timestamp: Utc::now(),
            workflow_id: checkpoint.workflow_id.clone(),
            execution_id: Some(execution_id.to_string()),
            task_id: None,
            level: LogLevel::Info,
            message: format!("Created checkpoint: {}", checkpoint.id),
        });
        
        Ok(checkpoint.id)
    }
    
    /// 从检查点恢复执行
    pub async fn recover_from_checkpoint(&self, checkpoint_id: &str) -> Result<String, String> {
        // 获取检查点
        let checkpoint = {
            let checkpoints = self.checkpoints.lock().unwrap();
            checkpoints.get(checkpoint_id).cloned().ok_or_else(|| "Checkpoint not found".to_string())?
        };
        
        // 加载原始工作流
        let workflow = self.storage.load_workflow(&checkpoint.workflow_id)?;
        
        // 创建新的执行记录
        let execution_id = Uuid::new_v4().to_string();
        let execution = WorkflowExecution {
            id: execution_id.clone(),
            workflow_id: workflow.id.clone(),
            workflow_name: workflow.name.clone(),
            start_time: Utc::now(),
            end_time: None,
            task_states: Vec::new(), // 将在恢复过程中填充
            status: ExecutionStatus::Running,
        };
        
        // 保存新的执行记录
        self.storage.save_execution(&execution)?;
        
        // 记录日志
        self.monitoring.log(WorkflowLogEntry {
            timestamp: Utc::now(),
            workflow_id: workflow.id.clone(),
            execution_id: Some(execution_id.clone()),
            task_id: None,
            level: LogLevel::Info,
            message: format!("Recovering from checkpoint: {}", checkpoint_id),
        });
        
        // 启动恢复过程
        let engine = self.engine.clone();
        let storage = self.storage.clone();
        let monitoring = self.monitoring.clone();
        let workflow_clone = workflow.clone();
        let checkpoint_clone = checkpoint.clone();
        let execution_id_clone = execution_id.clone();
        
        tokio::spawn(async move {
            // 恢复任务状态
            {
                let mut state_map = engine.workflow_state.lock().unwrap();
                for (task_id, state) in &checkpoint_clone.task_states {
                    state_map.insert(task_id.clone(), *state);
                }
            }
            
            // 继续执行工作流（这里需要实现特定的恢复逻辑）
            // ...
            
            // 示例：模拟恢复过程
            sleep(Duration::from_secs(1)).await;
            
            // 更新执行状态
            let mut execution = match storage.load_execution(&execution_id_clone) {
                Ok(exec) => exec,
                Err(_) => return,
            };
            
            execution.end_time = Some(Utc::now());
            execution.status = ExecutionStatus::Completed;
            
            let _ = storage.save_execution(&execution);
            
            // 记录恢复完成日志
            monitoring.log(WorkflowLogEntry {
                timestamp: Utc::now(),
                workflow_id: workflow_clone.id.clone(),
                execution_id: Some(execution_id_clone),
                task_id: None,
                level: LogLevel::Info,
                message: "Recovery completed".to_string(),
            });
        });
        
        Ok(execution_id)
    }
}
```

## 7. 云端同步机制

### 7.1 同步接口

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use async_trait::async_trait;
use serde::{Serialize, Deserialize};
use chrono::{DateTime, Utc};

use crate::workflow::{Workflow, Task};
use crate::storage::{WorkflowStorage, WorkflowExecution};

/// 同步行为枚举
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SyncAction {
    Upload,
    Download,
    Merge,
}

/// 同步状态
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SyncStatus {
    pub id: String,
    pub workflow_id: String,
    pub last_synced: Option<DateTime<Utc>>,
    pub last_action: Option<SyncAction>,
    pub status: String,
    pub error_message: Option<String>,
}

/// 冲突解决策略
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConflictResolution {
    UseLocal,
    UseRemote,
    ManualMerge,
}

/// 云端同步接口
#[async_trait]
pub trait CloudSync: Send + Sync {
    async fn upload_workflow(&self, workflow_id: &str) -> Result<SyncStatus, String>;
    async fn download_workflow(&self, workflow_id: &str) -> Result<SyncStatus, String>;
    async fn sync_workflow(&self, workflow_id: &str, resolution: ConflictResolution) -> Result<SyncStatus, String>;
    async fn list_remote_workflows(&self) -> Result<Vec<WorkflowSummary>, String>;
    async fn get_sync_status(&self, workflow_id: &str) -> Result<SyncStatus, String>;
}

/// 工作流摘要
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowSummary {
    pub id: String,
    pub name: String,
    pub version: String,
    pub last_modified: DateTime<Utc>,
}

/// REST API 云端同步实现
pub struct RestApiCloudSync<S: WorkflowStorage> {
    storage: Arc<S>,
    api_url: String,
    api_key: String,
    sync_status: Arc<Mutex<HashMap<String, SyncStatus>>>,
}

impl<S: WorkflowStorage + 'static> RestApiCloudSync<S> {
    pub fn new(storage: Arc<S>, api_url: &str, api_key: &str) -> Self {
        RestApiCloudSync {
            storage,
            api_url: api_url.to_string(),
            api_key: api_key.to_string(),
            sync_status: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    fn update_sync_status(
        &self, 
        workflow_id: &str, 
        action: SyncAction, 
        status: &str, 
        error: Option<String>
    ) -> SyncStatus {
        let status = SyncStatus {
            id: uuid::Uuid::new_v4().to_string(),
            workflow_id: workflow_id.to_string(),
            last_synced: Some(Utc::now()),
            last_action: Some(action),
            status: status.to_string(),
            error_message: error,
        };
        
        let mut statuses = self.sync_status.lock().unwrap();
        statuses.insert(workflow_id.to_string(), status.clone());
        
        status
    }
}

#[async_trait]
impl<S: WorkflowStorage + 'static> CloudSync for RestApiCloudSync<S> {
    async fn upload_workflow(&self, workflow_id: &str) -> Result<SyncStatus, String> {
        // 加载工作流
        let workflow = self.storage.load_workflow(workflow_id)?;
        
        // 序列化工作流
        let workflow_json = serde_json::to_string(&workflow)
            .map_err(|e| format!("Failed to serialize workflow: {}", e))?;
            
        // 构建请求
        let client = reqwest::Client::new();
        let url = format!("{}/workflows/{}", self.api_url, workflow_id);
        
        // 发送请求
        let response = client.put(&url)
            .header("Authorization", format!("Bearer {}", self.api_key))
            .header("Content-Type", "application/json")
            .body(workflow_json)
            .send()
            .await
            .map_err(|e| format!("Failed to send request: {}", e))?;
            
        // 处理响应
        if response.status().is_success() {
            Ok(self.update_sync_status(workflow_id, SyncAction::Upload, "success", None))
        } else {
            let error = format!("Failed to upload workflow: {}", response.status());
            Ok(self.update_sync_status(workflow_id, SyncAction::Upload, "failed", Some(error)))
        }
    }
    
    async fn download_workflow(&self, workflow_id: &str) -> Result<SyncStatus, String> {
        // 构建请求
        let client = reqwest::Client::new();
        let url = format!("{}/workflows/{}", self.api_url, workflow_id);
        
        // 发送请求
        let response = client.get(&url)
            .header("Authorization", format!("Bearer {}", self.api_key))
            .send()
            .await
            .map_err(|e| format!("Failed to send request: {}", e))?;
            
        // 处理响应
        if response.status().is_success() {
            let workflow: Workflow = response.json()
                .await
                .map_err(|e| format!("Failed to parse workflow: {}", e))?;
                
            // 保存工作流
            self.storage.save_workflow(&workflow)?;
            
            Ok(self.update_sync_status(workflow_id, SyncAction::Download, "success", None))
        } else {
            let error = format!("Failed to download workflow: {}", response.status());
            Ok(self.update_sync_status(workflow_id, SyncAction::Download, "failed", Some(error)))
        }
    }
    
    async fn sync_workflow(&self, workflow_id: &str, resolution: ConflictResolution) -> Result<SyncStatus, String> {
        // 加载本地工作流
        let local_workflow = self.storage.load_workflow(workflow_id)?;
        
        // 获取远程工作流
        let client = reqwest::Client::new();
        let url = format!("{}/workflows/{}", self.api_url, workflow_id);
        
        let response = client.get(&url)
            .header("Authorization", format!("Bearer {}", self.api_key))
            .send()
            .await
            .map_err(|e| format!("Failed to send request: {}", e))?;
            
        if !response.status().is_success() {
            // 远程不存在，直接上传
            return self.upload_workflow(workflow_id).await;
        }
        
        let remote_workflow: Workflow = response.json()
            .await
            .map_err(|e| format!("Failed to parse workflow: {}", e))?;
            
        // 检查冲突
        if local_workflow.updated_at == remote_workflow.updated_at {
            // 无冲突，不需同步
            return Ok(self.update_sync_status(workflow_id, SyncAction::Merge, "no_change", None));
        }
        
        // 根据冲突解决策略处理
        match resolution {
            ConflictResolution::UseLocal => {
                self.upload_workflow(workflow_id).await
            },
            ConflictResolution::UseRemote => {
                // 直接使用远程版本
                self.storage.save_workflow(&remote_workflow)?;
                Ok(self.update_sync_status(workflow_id, SyncAction::Download, "success", None))
            },
            ConflictResolution::ManualMerge => {
                // 这里需要实现复杂的合并逻辑
                // 简化示例：合并元数据，保留最新的任务定义
                let mut merged_workflow = local_workflow.clone();
                
                // 合并元数据
                for (key, value) in &remote_workflow.metadata {
                    if !merged_workflow.metadata.contains_key(key) {
                        merged_workflow.metadata.insert(key.clone(), value.clone());
                    }
                }
                
                // 合并任务（这里简化处理，实际应用需要更复杂的合并逻辑）
                for (id, remote_task) in &remote_workflow.tasks {
                    if let Some(local_task) = merged_workflow.tasks.get(id) {
                        if remote_task.updated_at > local_task.updated_at {
                            merged_workflow.tasks.insert(id.clone(), remote_task.clone());
                        }
                    } else {
                        merged_workflow.tasks.insert(id.clone(), remote_task.clone());
                    }
                }
                
                // 更新时间戳
                merged_workflow.updated_at = Utc::now();
                
                // 保存合并后的工作流
                self.storage.save_workflow(&merged_workflow)?;
                
                // 上传合并结果
                let workflow_json = serde_json::to_string(&merged_workflow)
                    .map_err(|e| format!("Failed to serialize workflow: {}", e))?;
                    
                let response = client.put(&url)
                    .header("Authorization", format!("Bearer {}", self.api_key))
                    .header("Content-Type", "application/json")
                    .body(workflow_json)
                    .send()
                    .await
                    .map_err(|e| format!("Failed to send request: {}", e))?;
                    
                if response.status().is_success() {
                    Ok(self.update_sync_status(workflow_id, SyncAction::Merge, "success", None))
                } else {
                    let error = format!("Failed to upload merged workflow: {}", response.status());
                    Ok(self.update_sync_status(workflow_id, SyncAction::Merge, "failed", Some(error)))
                }
            }
        }
    }
    
    async fn list_remote_workflows(&self) -> Result<Vec<WorkflowSummary>, String> {
        // 构建请求
        let client = reqwest::Client::new();
        let url = format!("{}/workflows", self.api_url);
        
        // 发送请求
        let response = client.get(&url)
            .header("Authorization", format!("Bearer {}", self.api_key))
            .send()
            .await
            .map_err(|e| format!("Failed to send request: {}", e))?;
            
        // 处理响应
        if response.status().is_success() {
            let workflows: Vec<WorkflowSummary> = response.json()
                .await
                .map_err(|e| format!("Failed to parse workflow list: {}", e))?;
                
            Ok(workflows)
        } else {
            Err(format!("Failed to list workflows: {}", response.status()))
        }
    }
    
    async fn get_sync_status(&self, workflow_id: &str) -> Result<SyncStatus, String> {
        let statuses = self.sync_status.lock().unwrap();
        
        if let Some(status) = statuses.get(workflow_id) {
            Ok(status.clone())
        } else {
            Ok(SyncStatus {
                id: uuid::Uuid::new_v4().to_string(),
                workflow_id: workflow_id.to_string(),
                last_synced: None,
                last_action: None,
                status: "never_synced".to_string(),
                error_message: None,
            })
        }
    }
}
```

### 7.2 版本控制与增量同步

```rust
use std::collections::{HashMap, HashSet};
use serde::{Serialize, Deserialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;

use crate::workflow::{Workflow, Task};

/// 工作流版本信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct WorkflowVersion {
    pub id: String,
    pub workflow_id: String,
    pub version: u32,
    pub created_at: DateTime<Utc>,
    pub comment: String,
    pub changes: Vec<ChangeRecord>,
}

/// 变更记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ChangeRecord {
    pub type_: ChangeType,
    pub entity_type: EntityType,
    pub entity_id: String,
    pub field: Option<String>,
    pub old_value: Option<String>,
    pub new_value: Option<String>,
}

/// 变更类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChangeType {
    Added,
    Removed,
    Modified,
}

/// 实体类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum EntityType {
    Workflow,
    Task,
    Dependency,
    Metadata,
}

/// 版本控制器
pub struct VersionControl {
    versions: HashMap<String, Vec<WorkflowVersion>>,
}

impl VersionControl {
    pub fn new() -> Self {
        VersionControl {
            versions: HashMap::new(),
        }
    }
    
    /// 创建新版本
    pub fn create_version(&mut self, old_workflow: Option<&Workflow>, new_workflow: &Workflow, comment: &str) -> WorkflowVersion {
        let workflow_id = new_workflow.id.clone();
        
        // 获取版本列表，如果不存在则创建
        let versions = self.versions.entry(workflow_id.clone()).or_insert_with(Vec::new);
        
        // 确定新版本号
        let version = if versions.is_empty() { 1 } else { versions.last().unwrap().version + 1 };
        
        // 计算变更
        let changes = if let Some(old) = old_workflow {
            self.compute_changes(old, new_workflow)
        } else {
            // 首次创建，所有内容都是新增的
            let mut changes = vec![
                ChangeRecord {
                    type_: ChangeType::Added,
                    entity_type: EntityType::Workflow,
                    entity_id: workflow_id.clone(),
                    field: None,
                    old_value: None,
                    new_value: None,
                }
            ];
            
            // 添加所有任务为新增
            for (id, task) in &new_workflow.tasks {
                changes.push(ChangeRecord {
                    type_: ChangeType::Added,
### 7.2 版本控制与增量同步（续）

```rust
                    type_: ChangeType::Added,
                    entity_type: EntityType::Task,
                    entity_id: id.clone(),
                    field: None,
                    old_value: None,
                    new_value: Some(task.name.clone()),
                });
            }
            
            changes
        };
        
        // 创建版本记录
        let version_record = WorkflowVersion {
            id: Uuid::new_v4().to_string(),
            workflow_id,
            version,
            created_at: Utc::now(),
            comment: comment.to_string(),
            changes,
        };
        
        // 保存版本
        versions.push(version_record.clone());
        
        version_record
    }
    
    /// 获取工作流的版本历史
    pub fn get_versions(&self, workflow_id: &str) -> Vec<WorkflowVersion> {
        self.versions.get(workflow_id).cloned().unwrap_or_default()
    }
    
    /// 计算两个工作流版本之间的变更
    fn compute_changes(&self, old: &Workflow, new: &Workflow) -> Vec<ChangeRecord> {
        let mut changes = Vec::new();
        
        // 检查工作流属性变更
        if old.name != new.name {
            changes.push(ChangeRecord {
                type_: ChangeType::Modified,
                entity_type: EntityType::Workflow,
                entity_id: new.id.clone(),
                field: Some("name".to_string()),
                old_value: Some(old.name.clone()),
                new_value: Some(new.name.clone()),
            });
        }
        
        if old.description != new.description {
            changes.push(ChangeRecord {
                type_: ChangeType::Modified,
                entity_type: EntityType::Workflow,
                entity_id: new.id.clone(),
                field: Some("description".to_string()),
                old_value: Some(old.description.clone()),
                new_value: Some(new.description.clone()),
            });
        }
        
        // 检查元数据变更
        let old_meta_keys: HashSet<_> = old.metadata.keys().collect();
        let new_meta_keys: HashSet<_> = new.metadata.keys().collect();
        
        // 添加的元数据
        for key in new_meta_keys.difference(&old_meta_keys) {
            changes.push(ChangeRecord {
                type_: ChangeType::Added,
                entity_type: EntityType::Metadata,
                entity_id: key.to_string(),
                field: None,
                old_value: None,
                new_value: new.metadata.get(*key).cloned(),
            });
        }
        
        // 删除的元数据
        for key in old_meta_keys.difference(&new_meta_keys) {
            changes.push(ChangeRecord {
                type_: ChangeType::Removed,
                entity_type: EntityType::Metadata,
                entity_id: key.to_string(),
                field: None,
                old_value: old.metadata.get(*key).cloned(),
                new_value: None,
            });
        }
        
        // 修改的元数据
        for key in old_meta_keys.intersection(&new_meta_keys) {
            let old_value = old.metadata.get(*key).unwrap();
            let new_value = new.metadata.get(*key).unwrap();
            
            if old_value != new_value {
                changes.push(ChangeRecord {
                    type_: ChangeType::Modified,
                    entity_type: EntityType::Metadata,
                    entity_id: key.to_string(),
                    field: None,
                    old_value: Some(old_value.clone()),
                    new_value: Some(new_value.clone()),
                });
            }
        }
        
        // 检查任务变更
        let old_task_ids: HashSet<_> = old.tasks.keys().collect();
        let new_task_ids: HashSet<_> = new.tasks.keys().collect();
        
        // 添加的任务
        for id in new_task_ids.difference(&old_task_ids) {
            let task = new.tasks.get(*id).unwrap();
            changes.push(ChangeRecord {
                type_: ChangeType::Added,
                entity_type: EntityType::Task,
                entity_id: id.to_string(),
                field: None,
                old_value: None,
                new_value: Some(task.name.clone()),
            });
        }
        
        // 删除的任务
        for id in old_task_ids.difference(&new_task_ids) {
            let task = old.tasks.get(*id).unwrap();
            changes.push(ChangeRecord {
                type_: ChangeType::Removed,
                entity_type: EntityType::Task,
                entity_id: id.to_string(),
                field: None,
                old_value: Some(task.name.clone()),
                new_value: None,
            });
        }
        
        // 修改的任务
        for id in old_task_ids.intersection(&new_task_ids) {
            let old_task = old.tasks.get(*id).unwrap();
            let new_task = new.tasks.get(*id).unwrap();
            
            // 检查任务名称变更
            if old_task.name != new_task.name {
                changes.push(ChangeRecord {
                    type_: ChangeType::Modified,
                    entity_type: EntityType::Task,
                    entity_id: id.to_string(),
                    field: Some("name".to_string()),
                    old_value: Some(old_task.name.clone()),
                    new_value: Some(new_task.name.clone()),
                });
            }
            
            // 检查任务命令变更
            if old_task.command != new_task.command {
                changes.push(ChangeRecord {
                    type_: ChangeType::Modified,
                    entity_type: EntityType::Task,
                    entity_id: id.to_string(),
                    field: Some("command".to_string()),
                    old_value: Some(old_task.command.clone()),
                    new_value: Some(new_task.command.clone()),
                });
            }
            
            // 检查依赖变更
            let old_deps: HashSet<_> = old_task.dependencies.iter().collect();
            let new_deps: HashSet<_> = new_task.dependencies.iter().collect();
            
            // 添加的依赖
            for dep in new_deps.difference(&old_deps) {
                changes.push(ChangeRecord {
                    type_: ChangeType::Added,
                    entity_type: EntityType::Dependency,
                    entity_id: format!("{}-{}", id, dep),
                    field: None,
                    old_value: None,
                    new_value: Some(dep.to_string()),
                });
            }
            
            // 删除的依赖
            for dep in old_deps.difference(&new_deps) {
                changes.push(ChangeRecord {
                    type_: ChangeType::Removed,
                    entity_type: EntityType::Dependency,
                    entity_id: format!("{}-{}", id, dep),
                    field: None,
                    old_value: Some(dep.to_string()),
                    new_value: None,
                });
            }
        }
        
        changes
    }
    
    /// 获取特定版本的工作流
    pub fn get_workflow_at_version(&self, workflow_id: &str, version: u32) -> Option<Workflow> {
        let versions = self.versions.get(workflow_id)?;
        
        // 找到目标版本之前的所有版本
        let applicable_versions: Vec<_> = versions.iter()
            .filter(|v| v.version <= version)
            .collect();
            
        if applicable_versions.is_empty() {
            return None;
        }
        
        // 从初始版本开始重建工作流
        let mut workflow = Workflow::new("", "");
        workflow.id = workflow_id.to_string();
        
        for version in applicable_versions {
            self.apply_changes(&mut workflow, &version.changes);
        }
        
        Some(workflow)
    }
    
    /// 应用变更到工作流
    fn apply_changes(&self, workflow: &mut Workflow, changes: &[ChangeRecord]) {
        for change in changes {
            match (change.entity_type, change.type_) {
                (EntityType::Workflow, ChangeType::Modified) => {
                    if let (Some(field), Some(new_value)) = (&change.field, &change.new_value) {
                        match field.as_str() {
                            "name" => workflow.name = new_value.clone(),
                            "description" => workflow.description = new_value.clone(),
                            _ => {}
                        }
                    }
                },
                (EntityType::Metadata, ChangeType::Added) | (EntityType::Metadata, ChangeType::Modified) => {
                    if let Some(new_value) = &change.new_value {
                        workflow.metadata.insert(change.entity_id.clone(), new_value.clone());
                    }
                },
                (EntityType::Metadata, ChangeType::Removed) => {
                    workflow.metadata.remove(&change.entity_id);
                },
                (EntityType::Task, ChangeType::Added) => {
                    // 简化处理：创建空任务，实际应用中需要更完整的任务信息
                    let task = Task {
                        id: change.entity_id.clone(),
                        name: change.new_value.clone().unwrap_or_default(),
                        command: String::new(),
                        dependencies: Vec::new(),
                        state: crate::workflow::TaskState::Pending,
                        retry_policy: crate::workflow::RetryPolicy {
                            max_retries: 0,
                            backoff_seconds: 0,
                        },
                        timeout_seconds: None,
                        created_at: Utc::now(),
                        updated_at: Utc::now(),
                        metadata: HashMap::new(),
                    };
                    workflow.tasks.insert(change.entity_id.clone(), task);
                },
                (EntityType::Task, ChangeType::Removed) => {
                    workflow.tasks.remove(&change.entity_id);
                },
                (EntityType::Task, ChangeType::Modified) => {
                    if let (Some(field), Some(new_value), Some(task)) = (
                        &change.field, 
                        &change.new_value,
                        workflow.tasks.get_mut(&change.entity_id)
                    ) {
                        match field.as_str() {
                            "name" => task.name = new_value.clone(),
                            "command" => task.command = new_value.clone(),
                            _ => {}
                        }
                        task.updated_at = Utc::now();
                    }
                },
                (EntityType::Dependency, ChangeType::Added) => {
                    // 解析依赖ID格式 "{task_id}-{dep_id}"
                    let parts: Vec<_> = change.entity_id.split('-').collect();
                    if parts.len() == 2 {
                        let task_id = parts[0];
                        let dep_id = change.new_value.clone().unwrap_or_else(|| parts[1].to_string());
                        
                        if let Some(task) = workflow.tasks.get_mut(task_id) {
                            if !task.dependencies.contains(&dep_id) {
                                task.dependencies.push(dep_id);
                                task.updated_at = Utc::now();
                            }
                        }
                    }
                },
                (EntityType::Dependency, ChangeType::Removed) => {
                    // 解析依赖ID格式 "{task_id}-{dep_id}"
                    let parts: Vec<_> = change.entity_id.split('-').collect();
                    if parts.len() == 2 {
                        let task_id = parts[0];
                        let dep_id = change.old_value.clone().unwrap_or_else(|| parts[1].to_string());
                        
                        if let Some(task) = workflow.tasks.get_mut(task_id) {
                            task.dependencies.retain(|d| *d != dep_id);
                            task.updated_at = Utc::now();
                        }
                    }
                },
                _ => {}
            }
        }
        
        workflow.updated_at = Utc::now();
    }
}
```

### 7.3 数据一致性保障

```rust
use std::sync::{Arc, Mutex};
use std::collections::HashMap;
use tokio::time::{sleep, Duration};
use chrono::Utc;
use serde::{Serialize, Deserialize};

use crate::workflow::Workflow;
use crate::storage::WorkflowStorage;
use crate::cloud::{CloudSync, SyncStatus, ConflictResolution};

/// 同步记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SyncRecord {
    pub workflow_id: String,
    pub local_hash: String,
    pub remote_hash: String,
    pub last_sync: chrono::DateTime<Utc>,
}

/// 同步管理器
pub struct SyncManager<S: WorkflowStorage, C: CloudSync> {
    storage: Arc<S>,
    cloud_sync: Arc<C>,
    sync_records: Arc<Mutex<HashMap<String, SyncRecord>>>,
    auto_sync_interval: Duration,
}

impl<S: WorkflowStorage + 'static, C: CloudSync + 'static> SyncManager<S, C> {
    pub fn new(storage: Arc<S>, cloud_sync: Arc<C>, auto_sync_interval_secs: u64) -> Self {
        SyncManager {
            storage,
            cloud_sync,
            sync_records: Arc::new(Mutex::new(HashMap::new())),
            auto_sync_interval: Duration::from_secs(auto_sync_interval_secs),
        }
    }
    
    /// 启动自动同步
    pub fn start_auto_sync(&self) {
        let storage = self.storage.clone();
        let cloud_sync = self.cloud_sync.clone();
        let sync_records = self.sync_records.clone();
        let interval = self.auto_sync_interval;
        
        tokio::spawn(async move {
            loop {
                sleep(interval).await;
                
                // 获取所有工作流
                let workflows = match storage.list_workflows() {
                    Ok(wfs) => wfs,
                    Err(_) => continue,
                };
                
                for workflow in workflows {
                    // 对每个工作流尝试同步
                    let workflow_id = workflow.id.clone();
                    let local_hash = compute_workflow_hash(&workflow);
                    
                    // 检查是否需要同步
                    let needs_sync = {
                        let records = sync_records.lock().unwrap();
                        match records.get(&workflow_id) {
                            Some(record) => record.local_hash != local_hash,
                            None => true, // 没有同步记录，需要同步
                        }
                    };
                    
                    if needs_sync {
                        // 执行同步
                        let result = cloud_sync.sync_workflow(&workflow_id, ConflictResolution::ManualMerge).await;
                        
                        if let Ok(status) = result {
                            if status.status == "success" {
                                // 同步成功，更新记录
                                let mut records = sync_records.lock().unwrap();
                                
                                // 重新加载同步后的工作流以获取最新状态
                                if let Ok(updated_workflow) = storage.load_workflow(&workflow_id) {
                                    let remote_hash = local_hash.clone(); // 简化：假设同步后本地和远程哈希相同
                                    
                                    records.insert(workflow_id.clone(), SyncRecord {
                                        workflow_id,
                                        local_hash,
                                        remote_hash,
                                        last_sync: Utc::now(),
                                    });
                                }
                            }
                        }
                    }
                }
            }
        });
    }
    
    /// 手动同步工作流
    pub async fn sync_workflow(&self, workflow_id: &str) -> Result<SyncStatus, String> {
        // 加载工作流
        let workflow = self.storage.load_workflow(workflow_id)?;
        let local_hash = compute_workflow_hash(&workflow);
        
        // 执行同步
        let result = self.cloud_sync.sync_workflow(workflow_id, ConflictResolution::ManualMerge).await?;
        
        if result.status == "success" {
            // 同步成功，更新记录
            let mut records = self.sync_records.lock().unwrap();
            
            // 重新加载同步后的工作流
            let updated_workflow = self.storage.load_workflow(workflow_id)?;
            let remote_hash = compute_workflow_hash(&updated_workflow);
            
            records.insert(workflow_id.to_string(), SyncRecord {
                workflow_id: workflow_id.to_string(),
                local_hash,
                remote_hash,
                last_sync: Utc::now(),
            });
        }
        
        Ok(result)
    }
    
    /// 获取同步状态
    pub fn get_sync_record(&self, workflow_id: &str) -> Option<SyncRecord> {
        let records = self.sync_records.lock().unwrap();
        records.get(workflow_id).cloned()
    }
    
    /// 检查工作流是否已同步
    pub fn is_synchronized(&self, workflow_id: &str) -> bool {
        let records = self.sync_records.lock().unwrap();
        
        if let Some(record) = records.get(workflow_id) {
            // 加载工作流
            if let Ok(workflow) = self.storage.load_workflow(workflow_id) {
                let current_hash = compute_workflow_hash(&workflow);
                return current_hash == record.local_hash && current_hash == record.remote_hash;
            }
        }
        
        false
    }
}

/// 计算工作流哈希值
fn compute_workflow_hash(workflow: &Workflow) -> String {
    // 简化实现：使用serde_json序列化后计算SHA-256哈希
    use sha2::{Sha256, Digest};
    
    let json = serde_json::to_string(workflow).unwrap_or_default();
    let mut hasher = Sha256::new();
    hasher.update(json.as_bytes());
    
    format!("{:x}", hasher.finalize())
}
```

## 8. 总结与展望

### 8.1 系统总体集成

本地工作流系统通过精心设计的模块化架构，提供了强大的工作流定义、执行和监控能力。主要组件包括：

1. **核心工作流模型**：提供了形式化的工作流表示，包括任务、依赖、状态模型等
2. **执行引擎**：负责工作流的调度和执行，支持各种执行策略
3. **存储层**：持久化工作流定义和执行记录，确保数据可靠性
4. **监控系统**：追踪工作流执行状态，提供日志和指标收集
5. **云端同步**：实现本地与云端工作流的无缝集成

### 8.2 系统高级特性

1. **可扩展性**：基于特质（trait）的设计使系统各组件易于扩展
2. **可靠性**：故障恢复机制确保工作流执行的可靠性
3. **一致性**：版本控制和冲突解决机制保证数据一致性
4. **灵活性**：支持各种调度策略和任务处理器

### 8.3 应用场景

1. **离线数据处理**：在无网络环境下执行复杂的数据处理流程
2. **敏感数据处理**：处理不宜上传至云端的敏感数据
3. **本地开发测试**：开发和测试工作流，然后再部署到生产环境
4. **边缘计算**：在边缘设备上运行工作流，减少与中心服务器的通信

### 8.4 未来展望

1. **分布式执行**：支持跨多个本地节点分布式执行工作流
2. **机器学习集成**：内置对机器学习工作流的支持
3. **图形化界面**：提供直观的工作流设计和监控界面
4. **实时处理**：支持流式数据的实时处理工作流
5. **智能调度**：基于资源利用率和任务特性的智能调度算法

本地工作流系统是构建可靠、高效的自动化处理流程的基础，随着边缘计算和隐私保护需求的增长，其重要性将进一步提升。通过持续改进和扩展，系统将能够应对更广泛的应用场景和复杂需求。
