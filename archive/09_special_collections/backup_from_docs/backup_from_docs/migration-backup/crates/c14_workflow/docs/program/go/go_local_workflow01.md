# 本地工作流设计与实现

## 目录

- [本地工作流设计与实现](#本地工作流设计与实现)
  - [目录](#目录)
  - [思维导图](#思维导图)
  - [1. 引言](#1-引言)
  - [2. 工作流概念模型](#2-工作流概念模型)
    - [2.1 核心概念](#21-核心概念)
    - [2.2 工作流形式模型](#22-工作流形式模型)
    - [2.3 工作流状态转换](#23-工作流状态转换)
  - [3. 本地工作流设计](#3-本地工作流设计)
    - [3.1 设计目标](#31-设计目标)
    - [3.2 架构设计](#32-架构设计)
    - [3.3 数据持久化](#33-数据持久化)
    - [3.4 云端同步机制](#34-云端同步机制)
  - [4. 代码实现](#4-代码实现)
    - [4.1 核心数据结构](#41-核心数据结构)
    - [4.2 工作流引擎](#42-工作流引擎)
  - [4.3 执行器](#43-执行器)
    - [4.4 数据流管理](#44-数据流管理)
    - [4.5 控制流实现](#45-控制流实现)
    - [4.6 持久化实现](#46-持久化实现)
    - [4.7 云端同步](#47-云端同步)
  - [5. 使用示例](#5-使用示例)
  - [6. 总结与展望](#6-总结与展望)
    - [6.1 设计概述](#61-设计概述)
    - [6.2 理论基础](#62-理论基础)
    - [6.3 实现挑战](#63-实现挑战)
    - [6.4 未来扩展](#64-未来扩展)
    - [6.5 结论](#65-结论)
    - [7. 附录： 本地工作流设计与实现 - 思维导图（文本格式）](#7-附录-本地工作流设计与实现---思维导图文本格式)
  - [4.2节和4.3节存在的问题修正](#42节和43节存在的问题修正)
    - [4.2 工作流引擎 (问题修正)](#42-工作流引擎-问题修正)
    - [4.3 执行器 (问题修正)](#43-执行器-问题修正)
  - [本地工作流系统架构图（文本格式）](#本地工作流系统架构图文本格式)
  - [系统组件间的数据流动](#系统组件间的数据流动)
  - [核心交互流程](#核心交互流程)

## 思维导图

```text
本地工作流设计与实现
├── 核心概念
│   ├── 任务(Task)
│   ├── 工作流(Workflow)
│   ├── 执行器(Executor)
│   ├── 数据流(DataFlow)
│   └── 控制流(ControlFlow)
├── 形式模型
│   ├── 有向无环图(DAG)表示
│   ├── 状态转换系统
│   └── 操作语义
├── 架构设计
│   ├── 工作流引擎
│   ├── 任务调度器
│   ├── 状态管理器
│   ├── 数据存储层
│   └── 云端同步层
├── 实现细节
│   ├── 核心数据结构
│   ├── 执行引擎
│   ├── 状态管理
│   ├── 持久化策略
│   └── 事件系统
└── 使用场景
    ├── 本地开发测试
    ├── 离线执行
    ├── 历史回溯
    └── 云端迁移
```

## 1. 引言

在现代软件开发和数据处理中，工作流已成为组织和自动化复杂任务的关键工具。虽然云端工作流提供了强大的可扩展性和可用性，但在许多场景下，本地工作流仍然具有不可替代的价值，如开发测试、网络受限环境、数据隐私要求等情况。

本文将从理论和实践两个角度探讨本地工作流的设计与实现，包括概念模型的形式化定义、系统架构设计，以及基于Golang的具体实现。我们的目标是构建一个既能独立运行又能与云端无缝集成的本地工作流系统。

## 2. 工作流概念模型

### 2.1 核心概念

1. **任务(Task)**: 工作流中的基本执行单元，具有明确的输入、输出和执行逻辑。
2. **工作流(Workflow)**: 多个任务按照特定依赖关系组织起来的集合，通常表示为有向无环图(DAG)。
3. **执行器(Executor)**: 负责任务的实际执行，可以是同步或异步的。
4. **数据流(DataFlow)**: 描述任务间数据传递的方式和路径。
5. **控制流(ControlFlow)**: 描述任务执行顺序和条件的规则集合。
6. **状态(State)**: 任务或工作流在特定时刻的执行情况。
7. **事件(Event)**: 工作流执行过程中发生的值得记录的活动。

### 2.2 工作流形式模型

从形式化角度，我们可以将工作流定义为一个五元组：

\[ W = (T, E, D, C, S) \]

其中：

- \(T\) 是任务集合 \(T = \{t_1, t_2, ..., t_n\}\)
- \(E\) 是执行器集合 \(E = \{e_1, e_2, ..., e_m\}\)
- \(D\) 是数据流关系，\(D \subseteq T \times T \times Type\)，表示从一个任务到另一个任务的数据传递，以及数据类型
- \(C\) 是控制流关系，\(C \subseteq T \times T \times Condition\)，表示任务间的执行依赖和条件
- \(S\) 是状态空间，记录工作流和任务的执行状态

每个任务 \(t_i\) 可以表示为：

\[ t_i = (I_i, O_i, L_i, S_i) \]

其中：

- \(I_i\) 是输入集合
- \(O_i\) 是输出集合
- \(L_i\) 是执行逻辑
- \(S_i\) 是任务状态

### 2.3 工作流状态转换

工作流的执行可以看作是一个状态转换系统。定义状态转换函数：

\[ \delta: S \times A \rightarrow S \]

其中 \(A\) 是动作集合，包括任务启动、完成、失败等。

工作流的执行过程可以表示为状态序列：

\[ s_0 \xrightarrow{a_1} s_1 \xrightarrow{a_2} s_2 \xrightarrow{a_3} ... \xrightarrow{a_n} s_n \]

其中 \(s_0\) 是初始状态，\(s_n\) 是终止状态，\(a_i\) 是状态转换动作。

## 3. 本地工作流设计

### 3.1 设计目标

1. **自足性**: 无需依赖云服务即可完整运行
2. **持久化**: 工作流定义和执行状态可靠保存
3. **可追踪**: 完整记录执行历史和状态变化
4. **可重现**: 支持历史工作流的重新执行
5. **可集成**: 与云端工作流系统兼容，支持无缝迁移
6. **高效性**: 最小化本地资源消耗
7. **扩展性**: 支持自定义执行器和任务类型

### 3.2 架构设计

本地工作流系统采用分层架构，包括：

1. **API层**: 提供工作流定义、执行、查询的接口
2. **引擎层**: 负责工作流解析、调度和状态管理
3. **执行层**: 负责具体任务的执行
4. **存储层**: 负责工作流定义和状态的持久化
5. **同步层**: 负责与云端工作流系统的数据同步

![本地工作流架构](https://placeholder-for-architecture-diagram.com)

### 3.3 数据持久化

本地工作流采用多级持久化策略：

1. **内存缓存**: 用于高频访问的工作流定义和运行时状态
2. **本地文件**: 使用结构化格式(如JSON)存储工作流定义和执行历史
3. **嵌入式数据库**: 用于更复杂的查询和索引需求
4. **快照机制**: 定期创建工作流状态快照，支持故障恢复

### 3.4 云端同步机制

本地工作流与云端的同步采用以下策略：

1. **增量同步**: 只同步发生变更的部分
2. **冲突解决**: 明确的冲突检测和解决机制
3. **离线操作**: 支持离线工作，连接恢复后自动同步
4. **版本控制**: 维护工作流定义的版本历史

## 4. 代码实现

### 4.1 核心数据结构

```go
// workflow/model.go

package workflow

import (
    "time"
    "github.com/google/uuid"
)

// TaskState 表示任务的执行状态
type TaskState string

const (
    TaskStatePending   TaskState = "PENDING"
    TaskStateRunning   TaskState = "RUNNING"
    TaskStateSucceeded TaskState = "SUCCEEDED"
    TaskStateFailed    TaskState = "FAILED"
    TaskStateCancelled TaskState = "CANCELLED"
)

// WorkflowState 表示工作流的执行状态
type WorkflowState string

const (
    WorkflowStatePending   WorkflowState = "PENDING"
    WorkflowStateRunning   WorkflowState = "RUNNING"
    WorkflowStateSucceeded WorkflowState = "SUCCEEDED"
    WorkflowStateFailed    WorkflowState = "FAILED"
    WorkflowStateCancelled WorkflowState = "CANCELLED"
)

// Task 表示工作流中的一个任务
type Task struct {
    ID          string                 `json:"id"`
    Name        string                 `json:"name"`
    Type        string                 `json:"type"`
    Config      map[string]interface{} `json:"config"`
    DependsOn   []string               `json:"dependsOn"`
    State       TaskState              `json:"state"`
    StartTime   *time.Time             `json:"startTime,omitempty"`
    EndTime     *time.Time             `json:"endTime,omitempty"`
    Inputs      map[string]interface{} `json:"inputs"`
    Outputs     map[string]interface{} `json:"outputs"`
    Error       string                 `json:"error,omitempty"`
    Retries     int                    `json:"retries"`
    MaxRetries  int                    `json:"maxRetries"`
}

// DataFlow 表示任务间的数据流
type DataFlow struct {
    SourceTaskID      string `json:"sourceTaskId"`
    SourceOutputName  string `json:"sourceOutputName"`
    TargetTaskID      string `json:"targetTaskId"`
    TargetInputName   string `json:"targetInputName"`
}

// ControlFlow 表示任务间的控制流
type ControlFlow struct {
    SourceTaskID      string                 `json:"sourceTaskId"`
    TargetTaskID      string                 `json:"targetTaskId"`
    Condition         string                 `json:"condition"`
    ConditionParams   map[string]interface{} `json:"conditionParams,omitempty"`
}

// Workflow 表示一个完整的工作流定义
type Workflow struct {
    ID          string                 `json:"id"`
    Name        string                 `json:"name"`
    Description string                 `json:"description"`
    Version     string                 `json:"version"`
    Tasks       map[string]*Task       `json:"tasks"`
    DataFlows   []*DataFlow            `json:"dataFlows"`
    ControlFlows []*ControlFlow        `json:"controlFlows"`
    State       WorkflowState          `json:"state"`
    StartTime   *time.Time             `json:"startTime,omitempty"`
    EndTime     *time.Time             `json:"endTime,omitempty"`
    CreateTime  time.Time              `json:"createTime"`
    UpdateTime  time.Time              `json:"updateTime"`
    Tags        map[string]string      `json:"tags,omitempty"`
    Metadata    map[string]interface{} `json:"metadata,omitempty"`
}

// WorkflowExecution 表示工作流的一次执行实例
type WorkflowExecution struct {
    ID              string                    `json:"id"`
    WorkflowID      string                    `json:"workflowId"`
    WorkflowVersion string                    `json:"workflowVersion"`
    State           WorkflowState             `json:"state"`
    TaskStates      map[string]TaskState      `json:"taskStates"`
    TaskResults     map[string]interface{}    `json:"taskResults"`
    StartTime       time.Time                 `json:"startTime"`
    EndTime         *time.Time                `json:"endTime,omitempty"`
    Error           string                    `json:"error,omitempty"`
    Parameters      map[string]interface{}    `json:"parameters,omitempty"`
    SyncStatus      string                    `json:"syncStatus,omitempty"`
}

// NewWorkflow 创建一个新的工作流
func NewWorkflow(name, description string) *Workflow {
    now := time.Now()
    return &Workflow{
        ID:          uuid.New().String(),
        Name:        name,
        Description: description,
        Version:     "1.0.0",
        Tasks:       make(map[string]*Task),
        DataFlows:   make([]*DataFlow, 0),
        ControlFlows: make([]*ControlFlow, 0),
        State:       WorkflowStatePending,
        CreateTime:  now,
        UpdateTime:  now,
        Tags:        make(map[string]string),
        Metadata:    make(map[string]interface{}),
    }
}

// AddTask 向工作流添加任务
func (w *Workflow) AddTask(task *Task) {
    w.Tasks[task.ID] = task
    w.UpdateTime = time.Now()
}

// NewTask 创建一个新的任务
func NewTask(name, taskType string, config map[string]interface{}) *Task {
    return &Task{
        ID:         uuid.New().String(),
        Name:       name,
        Type:       taskType,
        Config:     config,
        DependsOn:  make([]string, 0),
        State:      TaskStatePending,
        Inputs:     make(map[string]interface{}),
        Outputs:    make(map[string]interface{}),
        Retries:    0,
        MaxRetries: 3,
    }
}
```

### 4.2 工作流引擎

```go
// workflow/engine.go

package workflow

import (
    "context"
    "fmt"
    "sync"
    "time"
    
    "github.com/google/uuid"
)

// Engine 是工作流执行引擎
type Engine struct {
    store          Storage
    executors      map[string]Executor
    executions     map[string]*WorkflowExecution
    eventListeners []EventListener
    mu             sync.RWMutex
}

// Storage 定义工作流存储接口
type Storage interface {
    SaveWorkflow(workflow *Workflow) error
    GetWorkflow(id string) (*Workflow, error)
    ListWorkflows() ([]*Workflow, error)
    SaveExecution(execution *WorkflowExecution) error
    GetExecution(id string) (*WorkflowExecution, error)
    ListExecutions(workflowID string) ([]*WorkflowExecution, error)
}

// Executor 定义任务执行器接口
type Executor interface {
    Execute(ctx context.Context, task *Task) error
    CanExecute(taskType string) bool
    Abort(taskID string) error
}

// EventType 定义工作流事件类型
type EventType string

const (
    EventTaskStarted    EventType = "TASK_STARTED"
    EventTaskCompleted  EventType = "TASK_COMPLETED"
    EventTaskFailed     EventType = "TASK_FAILED"
    EventWorkflowStarted EventType = "WORKFLOW_STARTED"
    EventWorkflowCompleted EventType = "WORKFLOW_COMPLETED"
    EventWorkflowFailed    EventType = "WORKFLOW_FAILED"
)

// Event 定义工作流事件
type Event struct {
    Type       EventType              `json:"type"`
    WorkflowID string                 `json:"workflowId"`
    TaskID     string                 `json:"taskId,omitempty"`
    ExecutionID string                `json:"executionId"`
    Timestamp  time.Time              `json:"timestamp"`
    Data       map[string]interface{} `json:"data,omitempty"`
}

// EventListener 定义事件监听器接口
type EventListener interface {
    OnEvent(event *Event)
}

// NewEngine 创建工作流引擎
func NewEngine(store Storage) *Engine {
    return &Engine{
        store:      store,
        executors:  make(map[string]Executor),
        executions: make(map[string]*WorkflowExecution),
    }
}

// RegisterExecutor 注册任务执行器
func (e *Engine) RegisterExecutor(name string, executor Executor) {
    e.mu.Lock()
    defer e.mu.Unlock()
    e.executors[name] = executor
}

// AddEventListener 添加事件监听器
func (e *Engine) AddEventListener(listener EventListener) {
    e.mu.Lock()
    defer e.mu.Unlock()
    e.eventListeners = append(e.eventListeners, listener)
}

// ExecuteWorkflow 执行工作流
func (e *Engine) ExecuteWorkflow(ctx context.Context, workflowID string, params map[string]interface{}) (*WorkflowExecution, error) {
    workflow, err := e.store.GetWorkflow(workflowID)
    if err != nil {
        return nil, fmt.Errorf("获取工作流失败: %w", err)
    }
    
    execution := &WorkflowExecution{
        ID:              uuid.New().String(),
        WorkflowID:      workflowID,
        WorkflowVersion: workflow.Version,
        State:           WorkflowStateRunning,
        TaskStates:      make(map[string]TaskState),
        TaskResults:     make(map[string]interface{}),
        StartTime:       time.Now(),
        Parameters:      params,
        SyncStatus:      "LOCAL",
    }
    
    // 初始化任务状态
    for taskID, task := range workflow.Tasks {
        execution.TaskStates[taskID] = TaskStatePending
    }
    
    // 保存执行记录
    if err := e.store.SaveExecution(execution); err != nil {
        return nil, fmt.Errorf("保存执行记录失败: %w", err)
    }
    
    e.mu.Lock()
    e.executions[execution.ID] = execution
    e.mu.Unlock()
    
    // 发布工作流开始事件
    e.publishEvent(&Event{
        Type:       EventWorkflowStarted,
        WorkflowID: workflowID,
        ExecutionID: execution.ID,
        Timestamp:  time.Now(),
    })
    
    // 启动工作流执行
    go e.runWorkflow(ctx, workflow, execution)
    
    return execution, nil
}

// runWorkflow 运行工作流
func (e *Engine) runWorkflow(ctx context.Context, workflow *Workflow, execution *WorkflowExecution) {
    defer func() {
        if r := recover(); r != nil {
            execution.State = WorkflowStateFailed
            execution.Error = fmt.Sprintf("工作流执行panic: %v", r)
            e.finishExecution(execution)
        }
    }()
    
    // 构建依赖图
    taskDeps := make(map[string][]string)
    taskChildren := make(map[string][]string)
    readyTasks := make([]string, 0)
    
    for taskID, task := range workflow.Tasks {
        deps := task.DependsOn
        taskDeps[taskID] = deps
        
        if len(deps) == 0 {
            readyTasks = append(readyTasks, taskID)
        }
        
        for _, dep := range deps {
            if _, exists := taskChildren[dep]; !exists {
                taskChildren[dep] = make([]string, 0)
            }
            taskChildren[dep] = append(taskChildren[dep], taskID)
        }
    }
    
    // 任务执行计数
    var completedTasks int
    var failedTasks int
    totalTasks := len(workflow.Tasks)
    
    // 任务完成通道
    taskCompletionCh := make(chan string)
    
    // 执行就绪任务
    for len(readyTasks) > 0 && failedTasks == 0 {
        // 并行执行就绪任务
        var wg sync.WaitGroup
        currentBatch := readyTasks
        readyTasks = make([]string, 0)
        
        for _, taskID := range currentBatch {
            wg.Add(1)
            go func(id string) {
                defer wg.Done()
                task := workflow.Tasks[id]
                
                // 更新任务状态
                task.State = TaskStateRunning
                execution.TaskStates[id] = TaskStateRunning
                now := time.Now()
                task.StartTime = &now
                
                e.store.SaveExecution(execution)
                
                // 发布任务开始事件
                e.publishEvent(&Event{
                    Type:       EventTaskStarted,
                    WorkflowID: workflow.ID,
                    TaskID:     id,
                    ExecutionID: execution.ID,
                    Timestamp:  now,
                })
                
                // 查找合适的执行器
                var executor Executor
                for _, exec := range e.executors {
                    if exec.CanExecute(task.Type) {
                        executor = exec
                        break
                    }
                }
                
                if executor == nil {
                    task.State = TaskStateFailed
                    task.Error = fmt.Sprintf("没有找到适合任务类型 %s 的执行器", task.Type)
                    execution.TaskStates[id] = TaskStateFailed
                    
                    endTime := time.Now()
                    task.EndTime = &endTime
                    
                    e.publishEvent(&Event{
                        Type:       EventTaskFailed,
                        WorkflowID: workflow.ID,
                        TaskID:     id,
                        ExecutionID: execution.ID,
                        Timestamp:  endTime,
                        Data:       map[string]interface{}{"error": task.Error},
                    })
                    
                    e.store.SaveExecution(execution)
                    taskCompletionCh <- id
                    return
                }
                
                // 处理输入数据
                e.processTaskInputs(workflow, task, execution)
                
                // 执行任务
                err := executor.Execute(ctx, task)
                endTime := time.Now()
                task.EndTime = &endTime
                
                if err != nil {
                    task.State = TaskStateFailed
                    task.Error = err.Error()
                    execution.TaskStates[id] = TaskStateFailed
                    
                    e.publishEvent(&Event{
                        Type:       EventTaskFailed,
                        WorkflowID: workflow.ID,
                        TaskID:     id,
                        ExecutionID: execution.ID,
                        Timestamp:  endTime,
                        Data:       map[string]interface{}{"error": task.Error},
                    })
                } else {
                    task.State = TaskStateSucceeded
                    execution.TaskStates[id] = TaskStateSucceeded
                    execution.TaskResults[id] = task.Outputs
                    
                    e.publishEvent(&Event{
                        Type:       EventTaskCompleted,
                        WorkflowID: workflow.ID,
                        TaskID:     id,
                        ExecutionID: execution.ID,
                        Timestamp:  endTime,
                        Data:       map[string]interface{}{"outputs": task.Outputs},
                    })
                }
                
                e.store.SaveExecution(execution)
                taskCompletionCh <- id
            }(taskID)
        }
        
        // 等待当前批次的任务完成
        go func() {
            wg.Wait()
        }()
        
        // 收集完成的任务，并准备下一批次
        batchSize := len(currentBatch)
        for i := 0; i < batchSize; i++ {
            taskID := <-taskCompletionCh
            task := workflow.Tasks[taskID]
            
            if task.State == TaskStateSucceeded {
                completedTasks++
                
                // 添加后续任务到就绪队列
                if children, exists := taskChildren[taskID]; exists {
                    for _, childID := range children {
                        // 检查该子任务的所有依赖是否已完成
                        allDepsCompleted := true
                        for _, depID := range taskDeps[childID] {
                            if workflow.Tasks[depID].State != TaskStateSucceeded {
                                allDepsCompleted = false
                                break
                            }
                        }
                        
                        if allDepsCompleted {
                            readyTasks = append(readyTasks, childID)
                        }
                    }
                }
            } else if task.State == TaskStateFailed {
                failedTasks++
            }
        }
    }
    
    // 更新工作流状态
    if failedTasks > 0 {
        execution.State = WorkflowStateFailed
        execution.Error = "一个或多个任务执行失败"
        
        e.publishEvent(&Event{
            Type:       EventWorkflowFailed,
            WorkflowID: workflow.ID,
            ExecutionID: execution.ID,
            Timestamp:  time.Now(),
            Data:       map[string]interface{}{"error": execution.Error},
        })
    } else if completedTasks == totalTasks {
        execution.State = WorkflowStateSucceeded
        
        e.publishEvent(&Event{
            Type:       EventWorkflowCompleted,
            WorkflowID: workflow.ID,
            ExecutionID: execution.ID,
            Timestamp:  time.Now(),
        })
    }
    
    e.finishExecution(execution)
}

// processTaskInputs 处理任务输入
func (e *Engine) processTaskInputs(workflow *Workflow, task *Task, execution *WorkflowExecution) {
    // 处理来自其他任务的数据输入
    for _, dataFlow := range workflow.DataFlows {
        if dataFlow.TargetTaskID == task.ID {
            sourceTask := workflow.Tasks[dataFlow.SourceTaskID]
            if sourceOutput, exists := sourceTask.Outputs[dataFlow.SourceOutputName]; exists {
                task.Inputs[dataFlow.TargetInputName] = sourceOutput
            }
        }
    }
    
    // 处理工作流参数
    for inputName, inputValue := range task.Inputs {
        if strValue, ok := inputValue.(string); ok && len(strValue) > 0 && strValue[0] == '$' {
            // 参数引用格式: ${params.paramName}
            if strValue == "${params}" {
                task.Inputs[inputName] = execution.Parameters
            } else if len(strValue) > 9 && strValue[:9] == "${params." && strValue[len(strValue)-1] == '}' {
                paramName := strValue[9 : len(strValue)-1]
                if paramValue, exists := execution.Parameters[paramName]; exists {
                    task.Inputs[inputName] = paramValue
                }
            }
        }
    }
}

// finishExecution 完成工作流执行
func (e *Engine) finishExecution(execution *WorkflowExecution) {
    now := time.Now()
    execution.EndTime = &now
    
    if err := e.store.SaveExecution(execution); err != nil {
        // 记录日志
        fmt.Printf("保存执行结果失败: %v\n", err)
    }
    
    e.mu.Lock()
    delete(e.executions, execution.ID)
    e.mu.Unlock()
}

// publishEvent 发布事件
func (e *Engine) publishEvent(event *Event) {
    e.mu.RLock()
    listeners := make([]EventListener, len(e.eventListeners))
    copy(listeners, e.eventListeners)
    e.mu.RUnlock()
    
    for _, listener := range listeners {
        go listener.OnEvent(event)
    }
}

// GetExecution 获取工作流执行详情
func (e *Engine) GetExecution(executionID string) (*WorkflowExecution, error) {
    e.mu.RLock()
    if execution, exists := e.executions[executionID]; exists {
        e.mu.RUnlock()
        return execution, nil
    }
    e.mu.RUnlock()
    
    return e.store.GetExecution(executionID)
}

// StopExecution 停止工作流执行
func (e *Engine) StopExecution(executionID string) error {
    execution, err := e.GetExecution(executionID)
    if err != nil {
        return err
    }
    
    if execution.State != WorkflowStateRunning {
        return fmt.Errorf("工作流未处于运行状态")
    }
    
    // 标记为取消状
}
```

## 4.3 执行器

```go
// workflow/executor.go

package workflow

import (
    "context"
    "fmt"
    "sync"
)

// BaseExecutor 提供执行器的基本功能
type BaseExecutor struct {
    taskTypes     []string
    runningTasks  map[string]context.CancelFunc
    mu            sync.RWMutex
}

// NewBaseExecutor 创建基本执行器
func NewBaseExecutor(taskTypes []string) *BaseExecutor {
    return &BaseExecutor{
        taskTypes:    taskTypes,
        runningTasks: make(map[string]context.CancelFunc),
    }
}

// CanExecute 检查是否可以执行指定类型的任务
func (e *BaseExecutor) CanExecute(taskType string) bool {
    for _, t := range e.taskTypes {
        if t == taskType {
            return true
        }
    }
    return false
}

// Abort 中止任务执行
func (e *BaseExecutor) Abort(taskID string) error {
    e.mu.Lock()
    defer e.mu.Unlock()
    
    if cancel, exists := e.runningTasks[taskID]; exists {
        cancel()
        delete(e.runningTasks, taskID)
        return nil
    }
    
    return fmt.Errorf("任务未运行: %s", taskID)
}

// registerRunningTask 注册正在运行的任务
func (e *BaseExecutor) registerRunningTask(taskID string, cancel context.CancelFunc) {
    e.mu.Lock()
    e.runningTasks[taskID] = cancel
    e.mu.Unlock()
}

// unregisterRunningTask 取消注册正在运行的任务
func (e *BaseExecutor) unregisterRunningTask(taskID string) {
    e.mu.Lock()
    delete(e.runningTasks, taskID)
    e.mu.Unlock()
}

// ShellExecutor 执行shell命令的执行器
type ShellExecutor struct {
    *BaseExecutor
}

// NewShellExecutor 创建一个Shell执行器
func NewShellExecutor() *ShellExecutor {
    return &ShellExecutor{
        BaseExecutor: NewBaseExecutor([]string{"shell", "bash", "cmd"}),
    }
}

// Execute 执行Shell命令
func (e *ShellExecutor) Execute(ctx context.Context, task *Task) error {
    childCtx, cancel := context.WithCancel(ctx)
    e.registerRunningTask(task.ID, cancel)
    defer e.unregisterRunningTask(task.ID)
    
    command, ok := task.Config["command"].(string)
    if !ok {
        return fmt.Errorf("无效的Shell命令配置")
    }
    
    // 这里实现Shell命令的执行逻辑
    // 可以使用 os/exec 包执行命令
    
    // 模拟执行结果
    task.Outputs["exitCode"] = 0
    task.Outputs["stdout"] = "命令执行成功"
    
    return nil
}

// HTTPExecutor 执行HTTP请求的执行器
type HTTPExecutor struct {
    *BaseExecutor
}

// NewHTTPExecutor 创建HTTP执行器
func NewHTTPExecutor() *HTTPExecutor {
    return &HTTPExecutor{
        BaseExecutor: NewBaseExecutor([]string{"http", "rest"}),
    }
}

// Execute 执行HTTP请求
func (e *HTTPExecutor) Execute(ctx context.Context, task *Task) error {
    childCtx, cancel := context.WithCancel(ctx)
    e.registerRunningTask(task.ID, cancel)
    defer e.unregisterRunningTask(task.ID)
    
    url, ok := task.Config["url"].(string)
    if !ok {
        return fmt.Errorf("无效的HTTP URL配置")
    }
    
    method, _ := task.Config["method"].(string)
    if method == "" {
        method = "GET"
    }
    
    // 这里实现HTTP请求的执行逻辑
    // 可以使用 net/http 包发送请求
    
    // 模拟执行结果
    task.Outputs["statusCode"] = 200
    task.Outputs["body"] = fmt.Sprintf("成功请求 %s", url)
    
    return nil
}

// FunctionExecutor 执行Go函数的执行器
type FunctionExecutor struct {
    *BaseExecutor
    functions map[string]func(context.Context, map[string]interface{}) (map[string]interface{}, error)
}

// NewFunctionExecutor 创建函数执行器
func NewFunctionExecutor() *FunctionExecutor {
    return &FunctionExecutor{
        BaseExecutor: NewBaseExecutor([]string{"function", "golang"}),
        functions:    make(map[string]func(context.Context, map[string]interface{}) (map[string]interface{}, error)),
    }
}

// RegisterFunction 注册可执行函数
func (e *FunctionExecutor) RegisterFunction(name string, fn func(context.Context, map[string]interface{}) (map[string]interface{}, error)) {
    e.functions[name] = fn
}

// Execute 执行Go函数
func (e *FunctionExecutor) Execute(ctx context.Context, task *Task) error {
    childCtx, cancel := context.WithCancel(ctx)
    e.registerRunningTask(task.ID, cancel)
    defer e.unregisterRunningTask(task.ID)
    
    funcName, ok := task.Config["function"].(string)
    if !ok {
        return fmt.Errorf("未指定函数名")
    }
    
    fn, exists := e.functions[funcName]
    if !exists {
        return fmt.Errorf("函数未注册: %s", funcName)
    }
    
    outputs, err := fn(childCtx, task.Inputs)
    if err != nil {
        return err
    }
    
    // 将函数输出存储到任务输出
    for k, v := range outputs {
        task.Outputs[k] = v
    }
    
    return nil
}
```

### 4.4 数据流管理

```go
// workflow/dataflow.go

package workflow

import (
    "fmt"
    "reflect"
    "strings"
)

// DataType 数据类型
type DataType string

const (
    DataTypeString  DataType = "string"
    DataTypeNumber  DataType = "number"
    DataTypeBoolean DataType = "boolean"
    DataTypeObject  DataType = "object"
    DataTypeArray   DataType = "array"
    DataTypeAny     DataType = "any"
)

// DataSchema 描述数据架构
type DataSchema struct {
    Type        DataType              `json:"type"`
    Description string                `json:"description,omitempty"`
    Required    bool                  `json:"required"`
    Default     interface{}           `json:"default,omitempty"`
    Properties  map[string]DataSchema `json:"properties,omitempty"`
    Items       *DataSchema           `json:"items,omitempty"`
}

// DataPort 描述任务的数据端口（输入或输出）
type DataPort struct {
    Name        string     `json:"name"`
    Schema      DataSchema `json:"schema"`
    Description string     `json:"description,omitempty"`
}

// DataMapper 负责数据映射转换
type DataMapper struct{}

// NewDataMapper 创建数据映射器
func NewDataMapper() *DataMapper {
    return &DataMapper{}
}

// MapData 按照指定映射规则转换数据
func (dm *DataMapper) MapData(source map[string]interface{}, mapping map[string]string) (map[string]interface{}, error) {
    result := make(map[string]interface{})
    
    for targetKey, sourcePath := range mapping {
        value, err := dm.extractValue(source, sourcePath)
        if err != nil {
            return nil, err
        }
        result[targetKey] = value
    }
    
    return result, nil
}

// extractValue 根据路径从数据源提取值
func (dm *DataMapper) extractValue(source map[string]interface{}, path string) (interface{}, error) {
    if path == "" {
        return nil, fmt.Errorf("路径不能为空")
    }
    
    // 直接映射整个源对象
    if path == "." {
        return source, nil
    }
    
    // 处理路径表达式，如 "data.items[0].name"
    parts := strings.Split(path, ".")
    current := source
    
    for i, part := range parts {
        // 处理数组索引，如 "items[0]"
        idxStart := strings.Index(part, "[")
        if idxStart > 0 && part[len(part)-1] == ']' {
            fieldName := part[:idxStart]
            idxStr := part[idxStart+1 : len(part)-1]
            
            // 确保字段存在
            fieldValue, exists := current[fieldName]
            if !exists {
                return nil, fmt.Errorf("字段不存在: %s", fieldName)
            }
            
            // 确保字段是数组
            arr, ok := fieldValue.([]interface{})
            if !ok {
                return nil, fmt.Errorf("字段不是数组: %s", fieldName)
            }
            
            // 解析索引
            var idx int
            _, err := fmt.Sscanf(idxStr, "%d", &idx)
            if err != nil {
                return nil, fmt.Errorf("无效的数组索引: %s", idxStr)
            }
            
            if idx < 0 || idx >= len(arr) {
                return nil, fmt.Errorf("数组索引越界: %d", idx)
            }
            
            if i == len(parts)-1 {
                return arr[idx], nil
            }
            
            // 确保数组元素是对象
            nextObj, ok := arr[idx].(map[string]interface{})
            if !ok {
                return nil, fmt.Errorf("数组元素不是对象")
            }
            
            current = nextObj
        } else {
            // 普通字段
            if i == len(parts)-1 {
                return current[part], nil
            }
            
            nextObj, ok := current[part].(map[string]interface{})
            if !ok {
                return nil, fmt.Errorf("字段不是对象: %s", part)
            }
            
            current = nextObj
        }
    }
    
    return nil, fmt.Errorf("无效的路径: %s", path)
}

// ValidateData 验证数据是否符合架构要求
func (dm *DataMapper) ValidateData(data interface{}, schema DataSchema) error {
    return dm.validateValue(data, schema, "")
}

// validateValue 验证单个值
func (dm *DataMapper) validateValue(value interface{}, schema DataSchema, path string) error {
    // 检查 null 值
    if value == nil {
        if schema.Required {
            return fmt.Errorf("字段必需但为null: %s", path)
        }
        return nil
    }
    
    valueType := reflect.TypeOf(value)
    
    // 根据模式类型验证
    switch schema.Type {
    case DataTypeString:
        if valueType.Kind() != reflect.String {
            return fmt.Errorf("类型不匹配，期望string，得到%v: %s", valueType.Kind(), path)
        }
    
    case DataTypeNumber:
        if valueType.Kind() != reflect.Int && 
           valueType.Kind() != reflect.Int8 && 
           valueType.Kind() != reflect.Int16 && 
           valueType.Kind() != reflect.Int32 && 
           valueType.Kind() != reflect.Int64 && 
           valueType.Kind() != reflect.Float32 && 
           valueType.Kind() != reflect.Float64 {
            return fmt.Errorf("类型不匹配，期望number，得到%v: %s", valueType.Kind(), path)
        }
    
    case DataTypeBoolean:
        if valueType.Kind() != reflect.Bool {
            return fmt.Errorf("类型不匹配，期望boolean，得到%v: %s", valueType.Kind(), path)
        }
    
    case DataTypeObject:
        if valueType.Kind() != reflect.Map {
            return fmt.Errorf("类型不匹配，期望object，得到%v: %s", valueType.Kind(), path)
        }
        
        // 验证对象的属性
        objValue, _ := value.(map[string]interface{})
        if schema.Properties != nil {
            for propName, propSchema := range schema.Properties {
                propPath := path
                if propPath != "" {
                    propPath += "."
                }
                propPath += propName
                
                propValue, exists := objValue[propName]
                if !exists {
                    if propSchema.Required {
                        return fmt.Errorf("必需的属性缺失: %s", propPath)
                    }
                    continue
                }
                
                if err := dm.validateValue(propValue, propSchema, propPath); err != nil {
                    return err
                }
            }
        }
    
    case DataTypeArray:
        if valueType.Kind() != reflect.Slice && valueType.Kind() != reflect.Array {
            return fmt.Errorf("类型不匹配，期望array，得到%v: %s", valueType.Kind(), path)
        }
        
        // 验证数组元素
        if schema.Items != nil {
            arrValue, _ := value.([]interface{})
            for i, item := range arrValue {
                itemPath := fmt.Sprintf("%s[%d]", path, i)
                if err := dm.validateValue(item, *schema.Items, itemPath); err != nil {
                    return err
                }
            }
        }
    
    case DataTypeAny:
        // 任何类型都接受
        return nil
    
    default:
        return fmt.Errorf("未知的模式类型: %s", schema.Type)
    }
    
    return nil
}
```

### 4.5 控制流实现

```go
// workflow/controlflow.go

package workflow

import (
    "encoding/json"
    "fmt"
    "reflect"
    "strings"
)

// ConditionType 定义条件类型
type ConditionType string

const (
    ConditionTypeEqual        ConditionType = "equal"
    ConditionTypeNotEqual     ConditionType = "not_equal"
    ConditionTypeGreater      ConditionType = "greater"
    ConditionTypeLess         ConditionType = "less"
    ConditionTypeGreaterEqual ConditionType = "greater_equal"
    ConditionTypeLessEqual    ConditionType = "less_equal"
    ConditionTypeContains     ConditionType = "contains"
    ConditionTypeNotContains  ConditionType = "not_contains"
    ConditionTypeAnd          ConditionType = "and"
    ConditionTypeOr           ConditionType = "or"
    ConditionTypeNot          ConditionType = "not"
    ConditionTypeExpression   ConditionType = "expression"
)

// Condition 表示一个条件
type Condition struct {
    Type      ConditionType  `json:"type"`
    Field     string         `json:"field,omitempty"`
    Value     interface{}    `json:"value,omitempty"`
    Conditions []*Condition  `json:"conditions,omitempty"`
    Expression string        `json:"expression,omitempty"`
}

// ControlFlowManager 管理工作流控制流
type ControlFlowManager struct{}

// NewControlFlowManager 创建控制流管理器
func NewControlFlowManager() *ControlFlowManager {
    return &ControlFlowManager{}
}

// EvaluateCondition 计算条件表达式
func (cfm *ControlFlowManager) EvaluateCondition(cond *Condition, data map[string]interface{}) (bool, error) {
    if cond == nil {
        return true, nil
    }
    
    switch cond.Type {
    case ConditionTypeEqual:
        fieldValue, err := cfm.getFieldValue(cond.Field, data)
        if err != nil {
            return false, err
        }
        return reflect.DeepEqual(fieldValue, cond.Value), nil
    
    case ConditionTypeNotEqual:
        fieldValue, err := cfm.getFieldValue(cond.Field, data)
        if err != nil {
            return false, err
        }
        return !reflect.DeepEqual(fieldValue, cond.Value), nil
    
    case ConditionTypeGreater:
        fieldValue, err := cfm.getFieldValue(cond.Field, data)
        if err != nil {
            return false, err
        }
        return cfm.compareValues(fieldValue, cond.Value, func(a, b float64) bool { return a > b })
    
    case ConditionTypeLess:
        fieldValue, err := cfm.getFieldValue(cond.Field, data)
        if err != nil {
            return false, err
        }
        return cfm.compareValues(fieldValue, cond.Value, func(a, b float64) bool { return a < b })
    
    case ConditionTypeGreaterEqual:
        fieldValue, err := cfm.getFieldValue(cond.Field, data)
        if err != nil {
            return false, err
        }
        return cfm.compareValues(fieldValue, cond.Value, func(a, b float64) bool { return a >= b })
    
    case ConditionTypeLessEqual:
        fieldValue, err := cfm.getFieldValue(cond.Field, data)
        if err != nil {
            return false, err
        }
        return cfm.compareValues(fieldValue, cond.Value, func(a, b float64) bool { return a <= b })
    
    case ConditionTypeContains:
        fieldValue, err := cfm.getFieldValue(cond.Field, data)
        if err != nil {
            return false, err
        }
        return cfm.contains(fieldValue, cond.Value)
    
    case ConditionTypeNotContains:
        fieldValue, err := cfm.getFieldValue(cond.Field, data)
        if err != nil {
            return false, err
        }
        contains, err := cfm.contains(fieldValue, cond.Value)
        if err != nil {
            return false, err
        }
        return !contains, nil
    
    case ConditionTypeAnd:
        if cond.Conditions == nil || len(cond.Conditions) == 0 {
            return true, nil
        }
        
        for _, subCond := range cond.Conditions {
            result, err := cfm.EvaluateCondition(subCond, data)
            if err != nil {
                return false, err
            }
            if !result {
                return false, nil
            }
        }
        return true, nil
    
    case ConditionTypeOr:
        if cond.Conditions == nil || len(cond.Conditions) == 0 {
            return false, nil
        }
        
        for _, subCond := range cond.Conditions {
            result, err := cfm.EvaluateCondition(subCond, data)
            if err != nil {
                return false, err
            }
            if result {
                return true, nil
            }
        }
        return false, nil
    
    case ConditionTypeNot:
        if len(cond.Conditions) != 1 {
            return false, fmt.Errorf("NOT条件必须有且仅有一个子条件")
        }
        
        result, err := cfm.EvaluateCondition(cond.Conditions[0], data)
        if err != nil {
            return false, err
        }
        return !result, nil
    
    case ConditionTypeExpression:
        // 在实际应用中，这里可以接入一个表达式引擎
        // 目前我们只实现一个简单版本，支持基本的表达式计算
        return cfm.evaluateSimpleExpression(cond.Expression, data)
    
    default:
        return false, fmt.Errorf("不支持的条件类型: %s", cond.Type)
    }
}

// getFieldValue 从数据对象中获取指定路径的值
func (cfm *ControlFlowManager) getFieldValue(path string, data map[string]interface{}) (interface{}, error) {
    if path == "" {
        return nil, fmt.Errorf("字段路径不能为空")
    }
    
    // 处理路径表达式，如 "data.items[0].name"
    parts := strings.Split(path, ".")
    current := data
    
    for i, part := range parts {
        // 处理数组索引，如 "items[0]"
        idxStart := strings.Index(part, "[")
        if idxStart > 0 && part[len(part)-1] == ']' {
            fieldName := part[:idxStart]
            idxStr := part[idxStart+1 : len(part)-1]
            
            // 确保字段存在
            fieldValue, exists := current[fieldName]
            if !exists {
                return nil, fmt.Errorf("字段不存在: %s", fieldName)
            }
            
            // 确保字段是数组
            arr, ok := fieldValue.([]interface{})
            if !ok {
                return nil, fmt.Errorf("字段不是数组: %s", fieldName)
            }
            
            // 解析索引
            var idx int
            _, err := fmt.Sscanf(idxStr, "%d", &idx)
            if err != nil {
                return nil, fmt.Errorf("无效的数组索引: %s", idxStr)
            }
            
            if idx < 0 || idx >= len(arr) {
                return nil, fmt.Errorf("数组索引越界: %d", idx)
            }
            
            if i == len(parts)-1 {
                return arr[idx], nil
            }
            
            // 确保数组元素是对象
            nextObj, ok := arr[idx].(map[string]interface{})
            if !ok {
                return nil, fmt.Errorf("数组元素不是对象")
            }
            
            current = nextObj
        } else {
            // 普通字段
            if i == len(parts)-1 {
                return current[part], nil
            }
            
            nextObj, ok := current[part].(map[string]interface{})
            if !ok {
                return nil, fmt.Errorf("字段不是对象: %s", part)
            }
            
            current = nextObj
        }
    }
    
    return nil, fmt.Errorf("无效的路径: %s", path)
}

// compareValues 比较两个值的大小
func (cfm *ControlFlowManager) compareValues(a, b interface{}, compareFn func(float64, float64) bool) (bool, error) {
    // 尝试将值转换为数字进行比较
    var numA, numB float64
    
    switch v := a.(type) {
    case int:
        numA = float64(v)
    case int8:
        numA = float64(v)
    case int16:
        numA = float64(v)
    case int32:
        numA = float64(v)
    case int64:
        numA = float64(v)
    case float32:
        numA = float64(v)
    case float64:
        numA = v
    case json.Number:
        var err error
        numA, err = v.Float64()
        if err != nil {
            return false, fmt.Errorf("无法将值转换为数字: %v", a)
        }
    default:
        return false, fmt.Errorf("无法比较非数字类型: %T", a)
    }
    
    switch v := b.(type) {
    case int:
        numB = float64(v)
    case int8:
        numB = float64(v)
    case int16:
        numB = float64(v)
    case int32:
        numB = float64(v)
    case int64:
        numB = float64(v)
    case float32:
        numB = float64(v)
    case float64:
        numB = v
    case json.Number:
        var err error
        numB, err = v.Float64()
        if err != nil {
            return false, fmt.Errorf("无法将值转换为数字: %v", b)
        }
    default:
        return false, fmt.Errorf("无法比较非数字类型: %T", b)
    }
    
    return compareFn(numA, numB), nil
}

// contains 检查一个值是否包含另一个值
func (cfm *ControlFlowManager) contains(container, item interface{}) (bool, error) {
    switch c := container.(type) {
    case string:
        itemStr, ok := item.(string)
        if !ok {
            return false, fmt.Errorf("无法在字符串中查找非字符串类型的项")
        }
        return strings.Contains(c, itemStr), nil
    
    case []interface{}:
        for _, v := range c {
            if reflect.DeepEqual(v, item) {
                return true, nil
            }
        }
        return false, nil
    
    case map[string]interface{}:
        itemStr, ok := item.(string)
        if !ok {
            return false, fmt.Errorf("无法在对象中查找非字符串类型的键")
        }
        _, exists := c[itemStr]
        return exists, nil
    
    default:
        return false, fmt.Errorf("不支持的容器类型: %T", container)
    }
}

// evaluateSimpleExpression 评估简单表达式
func (cfm *ControlFlowManager) evaluateSimpleExpression(expr string, data map[string]interface{}) (bool, error) {
    // 这里实现简单的表达式计算逻辑
    // 在实际应用中，应该使用专门的表达式引擎
    
    // 简单实现：支持常见的等式比较，如 "foo == 'bar'" 或 "count > 5"
    expr = strings.TrimSpace(expr)
    
    // 检查常见的操作符
    for _, op := range []string{"==", "!=", ">=", "<=", ">", "<"} {
        parts := strings.Split(expr, op)
        if len(parts) == 2 {
            left := strings.TrimSpace(parts[0])
            right := strings.TrimSpace(parts[1])
            
            // 解析左值（应该是数据字段）
            leftValue, err := cfm.getFieldValue(left, data)
            if err != nil {
                return false, err
            }
            
            // 解析右值（可能是常量或数据字段）
            var rightValue interface{}
            if strings.HasPrefix(right, "'") && strings.HasSuffix(right, "'") {
                // 字符串常量
                rightValue = right[1 : len(right)-1]
            } else if strings.HasPrefix(right, "\"") && strings.HasSuffix(right, "\"") {
                // 字符串常量
                rightValue = right[1 : len(right)-1]
            } else if right == "true" {
                rightValue = true
            } else if right == "false" {
                rightValue = false
            } else if right == "null" {
                rightValue = nil
            } else {
                // 尝试解析为数字
                var num float64
                if _, err := fmt.Sscanf(right, "%f", &num); err == nil {
                    rightValue = num
                } else {
                    // 假设是数据字段
                    rightValue, err = cfm.getFieldValue(right, data)
                    if err != nil {
                        return false, err
                    }
                }
            }
            
            // 根据操作符比较值
            switch op {
            case "==":
                return reflect.DeepEqual(leftValue, rightValue), nil
            case "!=":
                return !reflect.DeepEqual(leftValue, rightValue), nil
            case ">":
                return cfm.compareValues(leftValue, rightValue, func(a, b float64) bool { return a > b })
            case "<":
                return cfm.compareValues(leftValue, rightValue, func(a, b float64) bool { return a < b })
            case ">=":
                return cfm.compareValues(leftValue, rightValue, func(a, b float64) bool { return a >= b })
            case "<=":
                return cfm.compareValues(leftValue, rightValue, func(a, b float64) bool { return a <= b })
            }
        }
    }
    
    return false, fmt.Errorf("不支持的表达式: %s", expr)
}
```

### 4.6 持久化实现

```go
// workflow/storage.go

package workflow

import (
    "encoding/json"
    "fmt"
    "io/ioutil"
    "os"
    "path/filepath"
    "sync"
    "time"
)

// FileStorage 实现基于文件的工作流存储
type FileStorage struct {
    basePath     string
    cacheTTL     time.Duration
    workflowCache map[string]*WorkflowCacheItem
    executionCache map[string]*ExecutionCacheItem
    mu           sync.RWMutex
}

// WorkflowCacheItem 表示缓存的工作流项
type WorkflowCacheItem struct {
    workflow  *Workflow
    expiresAt time.Time
}

// ExecutionCacheItem 表示缓存的执行项
type ExecutionCacheItem struct {
    execution *WorkflowExecution
    expiresAt time.Time
}

// NewFileStorage 创建文件存储实例
func NewFileStorage(basePath string) (*FileStorage, error) {
    // 确保目录存在
    if err := os.MkdirAll(filepath.Join(basePath, "workflows"), 0755); err != nil {
        return nil, fmt.Errorf("创建工作流目录失败: %w", err)
    }
    
    if err := os.MkdirAll(filepath.Join(basePath, "executions"), 0755); err != nil {
        return nil, fmt.Errorf("创建执行目录失败: %w", err)
    }
    
    return &FileStorage{
        basePath:        basePath,
        cacheTTL:        5 * time.Minute,
        workflowCache:   make(map[string]*WorkflowCacheItem),
        executionCache:  make(map[string]*ExecutionCacheItem),
    }, nil
}

// SaveWorkflow 保存工作流
func (s *FileStorage) SaveWorkflow(workflow *Workflow) error {
    if workflow == nil {
        return fmt.Errorf("工作流不能为nil")
    }
    
    // 更新修改时间
    workflow.UpdateTime = time.Now()
    
    // 序列化工作流
    data, err := json.MarshalIndent(workflow, "", "  ")
    if err != nil {
        return fmt.Errorf("序列化工作流失败: %w", err)
    }
    
    // 保存到文件
    filePath := filepath.Join(s.basePath, "workflows", workflow.ID+".json")
    if err := ioutil.WriteFile(filePath, data, 0644); err != nil {
        return fmt.Errorf("写入工作流文件失败: %w", err)
    }
    
    // 更新缓存
    s.mu.Lock()
    s.workflowCache[workflow.ID] = &WorkflowCacheItem{
        workflow:  workflow,
        expiresAt: time.Now().Add(s.cacheTTL),
    }
    s.mu.Unlock()
    
    return nil
}

// GetWorkflow 获取工作流
func (s *FileStorage) GetWorkflow(id string) (*Workflow, error) {
    // 检查缓存
    s.mu.RLock()
    if item, exists := s.workflowCache[id]; exists && time.Now().Before(item.expiresAt) {
        s.mu.RUnlock()
        return item.workflow, nil
    }
    s.mu.RUnlock()
    
    // 从文件加载
    filePath := filepath.Join(s.basePath, "workflows", id+".json")
    data, err := ioutil.ReadFile(filePath)
    if err != nil {
        if os.IsNotExist(err) {
            return nil, fmt.Errorf("工作流不存在: %s", id)
        }
        return nil, fmt.Errorf("读取工作流文件失败: %w", err)
    }
    
    // 反序列化工作流
    var workflow Workflow
    if err := json.Unmarshal(data, &workflow); err != nil {
        return nil, fmt.Errorf("反序列化工作流失败: %w", err)
    }
    
    // 更新缓存
    s.mu.Lock()
    s.workflowCache[id] = &WorkflowCacheItem{
        workflow:  &workflow,
        expiresAt: time.Now().Add(s.cacheTTL),
    }
    s.mu.Unlock()
    
    return &workflow, nil
}

// ListWorkflows 列出所有工作流
func (s *FileStorage) ListWorkflows() ([]*Workflow, error) {
    // 获取工作流目录中的所有JSON文件
    pattern := filepath.Join(s.basePath, "workflows", "*.json")
    matches, err := filepath.Glob(pattern)
    if err != nil {
        return nil, fmt.Errorf("查找工作流文件失败: %w", err)
    }
    
    workflows := make([]*Workflow, 0, len(matches))
    
    for _, filePath := range matches {
        // 从文件名提取ID
        id := filepath.Base(filePath)
        id = id[:len(id)-5] // 移除 ".json" 后缀
        
        // 获取工作流
        workflow, err := s.GetWorkflow(id)
        if err != nil {
            // 记录错误但继续
            fmt.Printf("获取工作流 %s 失败: %v\n", id, err)
            continue
        }
        
        workflows = append(workflows, workflow)
    }
    
    return workflows, nil
}

// SaveExecution 保存执行记录
func (s *FileStorage) SaveExecution(execution *WorkflowExecution) error {
    if execution == nil {
        return fmt.Errorf("执行记录不能为nil")
    }
    
    // 序列化执行记录
    data, err := json.MarshalIndent(execution, "", "  ")
    if err != nil {
        return fmt.Errorf("序列化执行记录失败: %w", err)
    }
    
    // 保存到文件
    filePath := filepath.Join(s.basePath, "executions", execution.ID+".json")
    if err := ioutil.WriteFile(filePath, data, 0644); err != nil {
        return fmt.Errorf("写入执行记录文件失败: %w", err)
    }
    
    // 更新缓存
    s.mu.Lock()
    s.executionCache[execution.ID] = &ExecutionCacheItem{
        execution: execution,
        expiresAt: time.Now().Add(s.cacheTTL),
    }
    s.mu.Unlock()
    
    return nil
}

// GetExecution 获取执行记录
func (s *FileStorage) GetExecution(id string) (*WorkflowExecution, error) {
    // 检查缓存
    s.mu.RLock()
    if item, exists := s.executionCache[id]; exists && time.Now().Before(item.expiresAt) {
        s.mu.RUnlock()
        return item.execution, nil
    }
    s.mu.RUnlock()
    
    // 从文件加载
    filePath := filepath.Join(s.basePath, "executions", id+".json")
    data, err := ioutil.ReadFile(filePath)
    if err != nil {
        if os.IsNotExist(err) {
            return nil, fmt.Errorf("执行记录不存在: %s", id)
        }
        return nil, fmt.Errorf("读取执行记录文件失败: %w", err)
    }
    
    // 反序列化执行记录
    var execution WorkflowExecution
    if err := json.Unmarshal(data, &execution); err != nil {
        return nil, fmt.Errorf("反序列化执行记录失败: %w", err)
    }
    
    // 更新缓存
    s.mu.Lock()
    s.executionCache[id] = &ExecutionCacheItem{
        execution: &execution,
        expiresAt: time.Now().Add(s.cacheTTL),
    }
    s.mu.Unlock()
    
    return &execution, nil
}

// ListExecutions 列出工作流的所有执行记录
func (s *FileStorage) ListExecutions(workflowID string) ([]*WorkflowExecution, error) {
    // 获取执行目录中的所有JSON文件
    pattern := filepath.Join(s.basePath, "executions", "*.json")
    matches, err := filepath.Glob(pattern)
    if err != nil {
        return nil, fmt.Errorf("查找执行记录文件失败: %w", err)
    }
    
    executions := make([]*WorkflowExecution, 0)
    
    for _, filePath := range matches {
        // 从文件名提取ID
        id := filepath.Base(filePath)
        id = id[:len(id)-5] // 移除 ".json" 后缀
        
        // 获取执行记录
        execution, err := s.GetExecution(id)
        if err != nil {
            // 记录错误但继续
            fmt.Printf("获取执行记录 %s 失败: %v\n", id, err)
            continue
        }
        
        // 如果指定了工作流ID，则过滤
        if workflowID != "" && execution.WorkflowID != workflowID {
            continue
        }
        
        executions = append(executions, execution)
    }
    
    return executions, nil
}

// CleanCache 清理过期的缓存项
func (s *FileStorage) CleanCache() {
    s.mu.Lock()
    defer s.mu.Unlock()
    
    now := time.Now()
    
    // 清理工作流缓存
    for id, item := range s.workflowCache {
        if now.After(item.expiresAt) {
            delete(s.workflowCache, id)
        }
    }
    
    // 清理执行记录缓存
    for id, item := range s.executionCache {
        if now.After(item.expiresAt) {
            delete(s.executionCache, id)
        }
    }
}

// SnapshotManager 负责工作流和执行记录的快照管理
type SnapshotManager struct {
    storage      *FileStorage
    snapshotDir  string
    interval     time.Duration
    stopCh       chan struct{}
    wg           sync.WaitGroup
}

// NewSnapshotManager 创建快照管理器
func NewSnapshotManager(storage *FileStorage, snapshotDir string, interval time.Duration) (*SnapshotManager, error) {
    // 确保快照目录存在
    if err := os.MkdirAll(snapshotDir, 0755); err != nil {
        return nil, fmt.Errorf("创建快照目录失败: %w", err)
    }
    
    return &SnapshotManager{
        storage:     storage,
        snapshotDir: snapshotDir,
        interval:    interval,
        stopCh:      make(chan struct{}),
    }, nil
}

// Start 启动快照管理器
func (sm *SnapshotManager) Start() {
    sm.wg.Add(1)
    go sm.run()
}

// Stop 停止快照管理器
func (sm *SnapshotManager) Stop() {
    close(sm.stopCh)
    sm.wg.Wait()
}

// run 运行快照管理
func (sm *SnapshotManager) run() {
    defer sm.wg.Done()
    
    ticker := time.NewTicker(sm.interval)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            if err := sm.createSnapshot(); err != nil {
                fmt.Printf("创建快照失败: %v\n", err)
            }
        case <-sm.stopCh:
            return
        }
    }
}

// createSnapshot 创建数据快照
func (sm *SnapshotManager) createSnapshot() error {
    // 创建时间戳目录
    timestamp := time.Now().Format("20060102_150405")
    snapshotPath := filepath.Join(sm.snapshotDir, timestamp)
    
    if err := os.MkdirAll(snapshotPath, 0755); err != nil {
        return fmt.Errorf("创建快照目录失败: %w", err)
    }
    
    // 复制工作流文件
    if err := sm.copyDirectory(
        filepath.Join(sm.storage.basePath, "workflows"),
        filepath.Join(snapshotPath, "workflows"),
    ); err != nil {
        return fmt.Errorf("复制工作流失败: %w", err)
    }
    
    // 复制执行记录文件
    if err := sm.copyDirectory(
        filepath.Join(sm.storage.basePath, "executions"),
        filepath.Join(snapshotPath, "executions"),
    ); err != nil {
        return fmt.Errorf("复制执行记录失败: %w", err)
    }
    
    fmt.Printf("创建快照成功: %s\n", snapshotPath)
    return nil
}

// copyDirectory 复制目录及其内容
func (sm *SnapshotManager) copyDirectory(src, dst string) error {
    // 确保目标目录存在
    if err := os.MkdirAll(dst, 0755); err != nil {
        return err
    }
    
    // 读取源目录
    entries, err := ioutil.ReadDir(src)
    if err != nil {
        return err
    }
    
    // 复制文件
    for _, entry := range entries {
        srcPath := filepath.Join(src, entry.Name())
        dstPath := filepath.Join(dst, entry.Name())
        
        if entry.IsDir() {
            if err := sm.copyDirectory(srcPath, dstPath); err != nil {
                return err
            }
        } else {
            if err := sm.copyFile(srcPath, dstPath); err != nil {
                return err
            }
        }
    }
    
    return nil
}

// copyFile 复制单个文件
func (sm *SnapshotManager) copyFile(src, dst string) error {
    // 读取源文件
    data, err := ioutil.ReadFile(src)
    if err != nil {
        return err
    }
    
    // 写入目标文件
    return ioutil.WriteFile(dst, data, 0644)
}
```

### 4.7 云端同步

```go
// workflow/sync.go

package workflow

import (
    "bytes"
    "encoding/json"
    "fmt"
    "net/http"
    "sync"
    "time"
)

// SyncStatus 表示同步状态
type SyncStatus string

const (
    SyncStatusPending  SyncStatus = "PENDING"
    SyncStatusSuccess  SyncStatus = "SUCCESS"
    SyncStatusFailed   SyncStatus = "FAILED"
    SyncStatusConflict SyncStatus = "CONFLICT"
)

// SyncItem 表示需要同步的项目
type SyncItem struct {
    Type      string          `json:"type"` // "workflow" 或 "execution"
    ID        string          `json:"id"`
    Data      json.RawMessage `json:"data"`
    Timestamp time.Time       `json:"timestamp"`
    Status    SyncStatus      `json:"status"`
    Error     string          `json:"error,omitempty"`
    Retries   int             `json:"retries"`
}

// SyncConfig 同步配置
type SyncConfig struct {
    Endpoint     string        `json:"endpoint"`
    APIKey       string        `json:"apiKey"`
    SyncInterval time.Duration `json:"syncInterval"`
    MaxRetries   int           `json:"maxRetries"`
}

// SyncManager 管理与云端的同步
type SyncManager struct {
    config     SyncConfig
    storage    *FileStorage
    syncQueue  []*SyncItem
    mu         sync.Mutex
    stopCh     chan struct{}
    wg         sync.WaitGroup
    httpClient *http.Client
}

// NewSyncManager 创建同步管理器
func NewSyncManager(config SyncConfig, storage *FileStorage) *SyncManager {
    return &SyncManager{
        config:     config,
        storage:    storage,
        syncQueue:  make([]*SyncItem, 0),
        stopCh:     make(chan struct{}),
        httpClient: &http.Client{Timeout: 30 * time.Second},
    }
}

// Start 启动同步管理器
func (sm *SyncManager) Start() {
    sm.wg.Add(1)
    go sm.run()
}

// Stop 停止同步管理器
func (sm *SyncManager) Stop() {
    close(sm.stopCh)
    sm.wg.Wait()
}

// QueueWorkflowSync 将工作流添加到同步队列
func (sm *SyncManager) QueueWorkflowSync(workflow *Workflow) error {
    data, err := json.Marshal(workflow)
    if err != nil {
        return fmt.Errorf("序列化工作流失败: %w", err)
    }
    
    sm.mu.Lock()
    defer sm.mu.Unlock()
    
    // 检查是否已在队列中
    for _, item := range sm.syncQueue {
        if item.Type == "workflow" && item.ID == workflow.ID {
            // 更新现有项目
            item.Data = json.RawMessage(data)
            item.Timestamp = time.Now()
            item.Status = SyncStatusPending
            item.Error = ""
            return nil
        }
    }
    
    // 添加新项目
    sm.syncQueue = append(sm.syncQueue, &SyncItem{
        Type:      "workflow",
        ID:        workflow.ID,
        Data:      json.RawMessage(data),
        Timestamp: time.Now(),
        Status:    SyncStatusPending,
    })
    
    return nil
}

// QueueExecutionSync 将执行记录添加到同步队列
func (sm *SyncManager) QueueExecutionSync(execution *WorkflowExecution) error {
    data, err := json.Marshal(execution)
    if err != nil {
        return fmt.Errorf("序列化执行记录失败: %w", err)
    }
    
    sm.mu.Lock()
    defer sm.mu.Unlock()
    
    // 检查是否已在队列中
    for _, item := range sm.syncQueue {
        if item.Type == "execution" && item.ID == execution.ID {
            // 更新现有项目
            item.Data = json.RawMessage(data)
            item.Timestamp = time.Now()
            item.Status = SyncStatusPending
            item.Error = ""
            return nil
        }
    }
    
    // 添加新项目
    sm.syncQueue = append(sm.syncQueue, &SyncItem{
        Type:      "execution",
        ID:        execution.ID,
        Data:      json.RawMessage(data),
        Timestamp: time.Now(),
        Status:    SyncStatusPending,
    })
    
    return nil
}

// run 运行同步处理
func (sm *SyncManager) run() {
    defer sm.wg.Done()
    
    ticker := time.NewTicker(sm.config.SyncInterval)
    defer ticker.Stop()
    
    for {
        select {
        case <-ticker.C:
            sm.processSync()
        case <-sm.stopCh:
            return
        }
    }
}

// processSync 处理同步队列
func (sm *SyncManager) processSync() {
    sm.mu.Lock()
    pending := make([]*SyncItem, 0)
    
    // 找出所有待同步的项目
    for _, item := range sm.syncQueue {
        if item.Status == SyncStatusPending {
            pending = append(pending, item)
        }
    }
    sm.mu.Unlock()
    
    // 无需加锁处理每个项目
    for _, item := range pending {
        sm.syncItem(item)
    }
    
    // 清理已成功同步的项目
    sm.mu.Lock()
    newQueue := make([]*SyncItem, 0)
    for _, item := range sm.syncQueue {
        if item.Status != SyncStatusSuccess {
            newQueue = append(newQueue, item)
        }
    }
    sm.syncQueue = newQueue
    sm.mu.Unlock()
}

// syncItem 同步单个项目
func (sm *SyncManager) syncItem(item *SyncItem) {
    // 构建请求URL
    url := fmt.Sprintf("%s/%s/%s", sm.config.Endpoint, item.Type, item.ID)
    
    // 创建请求
    req, err := http.NewRequest("PUT", url, bytes.NewReader(item.Data))
    if err != nil {
        sm.updateItemStatus(item, SyncStatusFailed, fmt.Sprintf("创建请求失败: %v", err))
        return
    }
    
    // 设置请求头
    req.Header.Set("Content-Type", "application/json")
    req.Header.Set("X-API-Key", sm.config.APIKey)
    
    // 发送请求
    resp, err := sm.httpClient.Do(req)
    if err != nil {
        sm.updateItemStatus(item, SyncStatusFailed, fmt.Sprintf("发送请求失败: %v", err))
        return
    }
    defer resp.Body.Close()
    
    // 检查响应状态
    if resp.StatusCode == http.StatusOK || resp.StatusCode == http.StatusCreated {
        sm.updateItemStatus(item, SyncStatusSuccess, "")
    } else if resp.StatusCode == http.StatusConflict {
        sm.updateItemStatus(item, SyncStatusConflict, "与云端数据冲突")
    } else {
        sm.updateItemStatus(item, SyncStatusFailed, fmt.Sprintf("请求失败，状态码: %d", resp.StatusCode))
    }
}

// updateItemStatus 更新项目状态
func (sm *SyncManager) updateItemStatus(item *SyncItem, status SyncStatus, errorMsg string) {
    sm.mu.Lock()
    defer sm.mu.Unlock()
    
    for _, qItem := range sm.syncQueue {
        if qItem.Type == item.Type && qItem.ID == item.ID {
            qItem.Status = status
            qItem.Error = errorMsg
            
            if status == SyncStatusFailed {
                qItem.Retries++
                
                // 如果超过最大重试次数，不再尝试
                if qItem.Retries >= sm.config.MaxRetries {
                    fmt.Printf("同步项目 %s:%s 达到最大重试次数，放弃同步\n", item.Type, item.ID)
                } else {
                    // 否则重置为待同步状态，稍后重试
                    qItem.Status = SyncStatusPending
                }
            }
            
            break
        }
    }
}

// PullFromCloud 从云端拉取数据
func (sm *SyncManager) PullFromCloud() error {
    // 拉取工作流数据
    if err := sm.pullWorkflows(); err != nil {
        return err
    }
    
    // 拉取执行记录数据
    if err := sm.pullExecutions(); err != nil {
        return err
    }
    
    return nil
}

// pullWorkflows 从云端拉取工作流
func (sm *SyncManager) pullWorkflows() error {
    url := fmt.Sprintf("%s/workflows", sm.config.Endpoint)
    
    req, err := http.NewRequest("GET", url, nil)
    if err != nil {
        return fmt.Errorf("创建请求失败: %w", err)
    }
    
    req.Header.Set("X-API-Key", sm.config.APIKey)
    
    resp, err := sm.httpClient.Do(req)
    if err != nil {
        return fmt.Errorf("发送请求失败: %w", err)
    }
    defer resp.Body.Close()
    
    if resp.StatusCode != http.StatusOK {
        return fmt.Errorf("拉取工作流失败，状态码: %d", resp.StatusCode)
    }
    
    var workflowsData struct {
        Workflows []*Workflow `json:"workflows"`
    }
    
    if err := json.NewDecoder(resp.Body).Decode(&workflowsData); err != nil {
        return fmt.Errorf("解析响应失败: %w", err)
    }
    
    // 保存工作流到本地
    for _, workflow := range workflowsData.Workflows {
        if err := sm.storage.SaveWorkflow(workflow); err != nil {
            fmt.Printf("保存工作流 %s 失败: %v\n", workflow.ID, err)
        }
    }
    
    return nil
}

// pullExecutions 从云端拉取执行记录
func (sm *SyncManager) pullExecutions() error {
    url := fmt.Sprintf("%s/executions", sm.config.Endpoint)
    
    req, err := http.NewRequest("GET", url, nil)
    if err != nil {
        return fmt.Errorf("创建请求失败: %w", err)
    }
    
    req.Header.Set("X-API-Key", sm.config.APIKey)
    
    resp, err := sm.httpClient.Do(req)
    if err != nil {
        return fmt.Errorf("发送请求失败: %w", err)
    }
    defer resp.Body.Close()
    
    if resp.StatusCode != http.StatusOK {
        return fmt.Errorf("拉取执行记录失败，状态码: %d", resp.StatusCode)
    }
    
    var executionsData struct {
        Executions []*WorkflowExecution `json:"executions"`
    }
    
    if err := json.NewDecoder(resp.Body).Decode(&executionsData); err != nil {
        return fmt.Errorf("解析响应失败: %w", err)
    }
    
    // 保存执行记录到本地
    for _, execution := range executionsData.Executions {
        if err := sm.storage.SaveExecution(execution); err != nil {
            fmt.Printf("保存执行记录 %s 失败: %v\n", execution.ID, err)
        }
    }
    
    return nil
}
```

## 5. 使用示例

```go
package main

import (
    "context"
    "fmt"
    "os"
    "os/signal"
    "syscall"
    "time"
    
    "github.com/yourorg/localworkflow/workflow"
)

func main() {
    // 创建文件存储
    storage, err := workflow.NewFileStorage("./data")
    if err != nil {
        fmt.Printf("创建存储失败: %v\n", err)
        os.Exit(1)
    }
    
    // 创建工作流引擎
    engine := workflow.NewEngine(storage)
    
    // 注册执行器
    engine.RegisterExecutor("shell", workflow.NewShellExecutor())
    engine.RegisterExecutor("http", workflow.NewHTTPExecutor())
    
    // 创建函数执行器
    funcExecutor := workflow.NewFunctionExecutor()
    
    // 注册自定义函数
    funcExecutor.RegisterFunction("processData", func(ctx context.Context, inputs map[string]interface{}) (map[string]interface{}, error) {
        // 从输入获取数据
        data, ok := inputs["data"].([]interface{})
        if !ok {
            return nil, fmt.Errorf("无效的输入数据")
        }
        
        // 处理数据
        var sum float64
        for _, item := range data {
            if num, ok := item.(float64); ok {
                sum += num
            }
        }
        
        // 返回结果
        return map[string]interface{}{
            "sum": sum,
            "average": sum / float64(len(data)),
            "count": len(data),
        }, nil
    })
    
    engine.RegisterExecutor("function", funcExecutor)
    
    // 创建事件记录器
    engine.AddEventListener(&EventLogger{})
    
    // 创建一个数据处理工作流
    workflow := createSampleWorkflow()
    
    // 保存工作流
    if err := storage.SaveWorkflow(workflow); err != nil {
        fmt.Printf("保存工作流失败: %v\n", err)
        os.Exit(1)
    }
    
    fmt.Printf("创建工作流成功: %s\n", workflow.ID)
    
    // 执行工作流
    params := map[string]interface{}{
        "inputFile": "data.json",
        "threshold": 10,
    }
    
    execution, err := engine.ExecuteWorkflow(context.Background(), workflow.ID, params)
    if err != nil {
        fmt.Printf("执行工作流失败: %v\n", err)
        os.Exit(1)
    }
    
    fmt.Printf("工作流执行已启动: %s\n", execution.ID)
    
    // 等待中断信号
    sigCh := make(chan os.Signal, 1)
    signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
    <-sigCh
    
    fmt.Println("正在关闭...")
}

// EventLogger 简单的事件日志记录器
type EventLogger struct{}

func (l *EventLogger) OnEvent(event *workflow.Event) {
    fmt.Printf("[%s] 事件: %s, 工作流: %s", event.Timestamp.Format(time.RFC3339), event.Type, event.WorkflowID)
    if event.TaskID != "" {
        fmt.Printf(", 任务: %s", event.TaskID)
    }
    fmt.Println()
}

// 创建示例工作流
func createSampleWorkflow() *workflow.Workflow {
    w := workflow.NewWorkflow("数据处理流程", "从文件读取数据，处理并发送结果")
    
    // 创建任务
    readTask := workflow.NewTask("读取数据", "shell", map[string]interface{}{
        "command": "cat ${params.inputFile}",
    })
    
    parseTask := workflow.NewTask("解析数据", "function", map[string]interface{}{
        "function": "parseJSON",
    })
    
    processTask := workflow.NewTask("处理数据", "function", map[string]interface{}{
        "function": "processData",
    })
    
    filterTask := workflow.NewTask("过滤数据", "function", map[string]interface{}{
        "function": "filterData",
    })
    
    reportTask := workflow.NewTask("生成报告", "function", map[string]interface{}{
        "function": "generateReport",
    })
    
    apiTask := workflow.NewTask("发送API", "http", map[string]interface{}{
        "url":    "https://api.example.com/submit",
        "method": "POST",
    })
    
    // 设置任务依赖关系
    parseTask.DependsOn = []string{readTask.ID}
    processTask.DependsOn = []string{parseTask.ID}
    filterTask.DependsOn = []string{processTask.ID}
    reportTask.DependsOn = []string{filterTask.ID}
    apiTask.DependsOn = []string{reportTask.ID}
    
    // 添加任务到工作流
    w.AddTask(readTask)
    w.AddTask(parseTask)
    w.AddTask(processTask)
    w.AddTask(filterTask)
    w.AddTask(reportTask)
    w.AddTask(apiTask)
    
    // 定义数据流
    w.DataFlows = append(w.DataFlows, &workflow.DataFlow{
        SourceTaskID:     readTask.ID,
        SourceOutputName: "stdout",
        TargetTaskID:     parseTask.ID,
        TargetInputName:  "rawData",
    })
    
    w.DataFlows = append(w.DataFlows, &workflow.DataFlow{
        SourceTaskID:     parseTask.ID,
        SourceOutputName: "parsedData",
        TargetTaskID:     processTask.ID,
        TargetInputName:  "data",
    })
    
    w.DataFlows = append(w.DataFlows, &workflow.DataFlow{
        SourceTaskID:     processTask.ID,
        SourceOutputName: "result",
        TargetTaskID:     filterTask.ID,
        TargetInputName:  "data",
    })
    
    w.DataFlows = append(w.DataFlows, &workflow.DataFlow{
        SourceTaskID:     filterTask.ID,
        SourceOutputName: "filteredData",
        TargetTaskID:     reportTask.ID,
        TargetInputName:  "data",
    })
    
    w.DataFlows = append(w.DataFlows, &workflow.DataFlow{
        SourceTaskID:     reportTask.ID,
        SourceOutputName: "report",
        TargetTaskID:     apiTask.ID,
        TargetInputName:  "body",
    })
    
    // 定义控制流
    w.ControlFlows = append(w.ControlFlows, &workflow.ControlFlow{
        SourceTaskID: processTask.ID,
        TargetTaskID: filterTask.ID,
        Condition:    "result.count > ${params.threshold}",
    })
    
    return w
}

// 更完整的示例程序
func completeExample() {
    // 创建文件存储
    storage, err := workflow.NewFileStorage("./data")
    if err != nil {
        fmt.Printf("创建存储失败: %v\n", err)
        os.Exit(1)
    }
    
    // 创建工作流引擎
    engine := workflow.NewEngine(storage)
    
    // 注册执行器
    engine.RegisterExecutor("shell", workflow.NewShellExecutor())
    engine.RegisterExecutor("http", workflow.NewHTTPExecutor())
    
    // 创建函数执行器
    funcExecutor := workflow.NewFunctionExecutor()
    
    // 注册自定义函数
    funcExecutor.RegisterFunction("parseJSON", func(ctx context.Context, inputs map[string]interface{}) (map[string]interface{}, error) {
        rawData, ok := inputs["rawData"].(string)
        if !ok {
            return nil, fmt.Errorf("无效的原始数据")
        }
        
        var parsedData interface{}
        if err := json.Unmarshal([]byte(rawData), &parsedData); err != nil {
            return nil, fmt.Errorf("解析JSON失败: %w", err)
        }
        
        return map[string]interface{}{
            "parsedData": parsedData,
        }, nil
    })
    
    funcExecutor.RegisterFunction("processData", func(ctx context.Context, inputs map[string]interface{}) (map[string]interface{}, error) {
        // 处理数据逻辑
        data, ok := inputs["data"].([]interface{})
        if !ok {
            return nil, fmt.Errorf("无效的输入数据")
        }
        
        var sum float64
        for _, item := range data {
            if num, ok := item.(float64); ok {
                sum += num
            }
        }
        
        return map[string]interface{}{
            "result": map[string]interface{}{
                "sum":     sum,
                "average": sum / float64(len(data)),
                "count":   len(data),
            },
        }, nil
    })
    
    funcExecutor.RegisterFunction("filterData", func(ctx context.Context, inputs map[string]interface{}) (map[string]interface{}, error) {
        // 过滤数据逻辑
        dataMap, ok := inputs["data"].(map[string]interface{})
        if !ok {
            return nil, fmt.Errorf("无效的输入数据")
        }
        
        return map[string]interface{}{
            "filteredData": dataMap,
        }, nil
    })
    
    funcExecutor.RegisterFunction("generateReport", func(ctx context.Context, inputs map[string]interface{}) (map[string]interface{}, error) {
        // 生成报告逻辑
        data, ok := inputs["data"].(map[string]interface{})
        if !ok {
            return nil, fmt.Errorf("无效的输入数据")
        }
        
        // 创建简单的HTML报告
        report := fmt.Sprintf(`
            <html>
            <head><title>数据处理报告</title></head>
            <body>
                <h1>数据处理报告</h1>
                <p>总和: %v</p>
                <p>平均值: %v</p>
                <p>数量: %v</p>
            </body>
            </html>
        `, data["sum"], data["average"], data["count"])
        
        return map[string]interface{}{
            "report": report,
        }, nil
    })
    
    engine.RegisterExecutor("function", funcExecutor)
    
    // 创建日志记录器
    logFile, err := os.OpenFile("workflow.log", os.O_CREATE|os.O_APPEND|os.O_WRONLY, 0644)
    if err != nil {
        fmt.Printf("打开日志文件失败: %v\n", err)
        os.Exit(1)
    }
    defer logFile.Close()
    
    // 创建事件记录器
    engine.AddEventListener(&FileEventLogger{
        file: logFile,
    })
    
    // 创建并保存工作流
    workflow := createSampleWorkflow()
    if err := storage.SaveWorkflow(workflow); err != nil {
        fmt.Printf("保存工作流失败: %v\n", err)
        os.Exit(1)
    }
    
    fmt.Printf("创建工作流成功: %s\n", workflow.ID)
    
    // 创建云端同步配置
    syncConfig := workflow.SyncConfig{
        Endpoint:     "https://workflow-api.example.com",
        APIKey:       "your-api-key",
        SyncInterval: 5 * time.Minute,
        MaxRetries:   3,
    }
    
    // 创建同步管理器
    syncManager := workflow.NewSyncManager(syncConfig, storage)
    syncManager.Start()
    defer syncManager.Stop()
    
    // 创建快照管理器
    snapshotManager, err := workflow.NewSnapshotManager(storage, "./snapshots", 1*time.Hour)
    if err != nil {
        fmt.Printf("创建快照管理器失败: %v\n", err)
        os.Exit(1)
    }
    snapshotManager.Start()
    defer snapshotManager.Stop()
    
    // 执行工作流
    params := map[string]interface{}{
        "inputFile": "data.json",
        "threshold": 10,
    }
    
    execution, err := engine.ExecuteWorkflow(context.Background(), workflow.ID, params)
    if err != nil {
        fmt.Printf("执行工作流失败: %v\n", err)
        os.Exit(1)
    }
    
    fmt.Printf("工作流执行已启动: %s\n", execution.ID)
    
    // 等待中断信号
    sigCh := make(chan os.Signal, 1)
    signal.Notify(sigCh, syscall.SIGINT, syscall.SIGTERM)
    <-sigCh
    
    fmt.Println("正在关闭...")
}

// FileEventLogger 将事件记录到文件
type FileEventLogger struct {
    file *os.File
    mu   sync.Mutex
}

func (l *FileEventLogger) OnEvent(event *workflow.Event) {
    l.mu.Lock()
    defer l.mu.Unlock()
    
    logEntry := fmt.Sprintf("[%s] 事件: %s, 工作流: %s", 
        event.Timestamp.Format(time.RFC3339), 
        event.Type, 
        event.WorkflowID)
    
    if event.TaskID != "" {
        logEntry += fmt.Sprintf(", 任务: %s", event.TaskID)
    }
    
    if event.Data != nil && len(event.Data) > 0 {
        dataJSON, _ := json.Marshal(event.Data)
        logEntry += fmt.Sprintf(", 数据: %s", string(dataJSON))
    }
    
    logEntry += "\n"
    
    l.file.WriteString(logEntry)
}
```

## 6. 总结与展望

### 6.1 设计概述

本文详细阐述了一个完整的本地工作流系统的设计与实现，该系统具有以下特点：

1. **完备的工作流模型**：基于有向无环图(DAG)的工作流表示，支持复杂的数据流和控制流
2. **灵活的执行机制**：支持多种执行器，满足不同类型任务的需求
3. **可靠的持久化**：通过本地文件系统和快照机制确保数据安全
4. **完整的生命周期管理**：从创建、执行、监控到历史查询的全生命周期支持
5. **云端同步能力**：支持与云端工作流系统同步，解决数据一致性问题

### 6.2 理论基础

本地工作流系统的设计基于以下理论基础：

1. **有向无环图(DAG)理论**：工作流的基本数学模型，保证任务执行的顺序性和无循环依赖
2. **状态转换系统**：描述工作流和任务的生命周期变化
3. **事件驱动架构**：通过事件机制实现系统各组件的解耦和可扩展性
4. **一致性模型**：在本地和云端之间保持数据一致性的理论保障

### 6.3 实现挑战

在实现过程中，主要面临以下挑战：

1. **控制流表达能力**：如何灵活而严谨地表达复杂的控制逻辑
2. **数据流一致性**：确保任务间数据传递的类型安全和一致性
3. **错误处理与恢复**：在任务失败时保持系统稳定并支持恢复
4. **状态持久化效率**：平衡存储开销和查询效率
5. **云端同步冲突**：解决本地与云端数据冲突的策略

### 6.4 未来扩展

本地工作流系统可以在以下方向进行扩展：

1. **更丰富的控制流模式**：支持循环、子工作流等高级控制结构
2. **更强大的表达式引擎**：增强条件表达式的能力，支持更复杂的逻辑判断
3. **分布式执行支持**：允许任务在多个本地节点上执行
4. **版本管理能力**：支持工作流定义的版本控制和回滚
5. **可视化工具**：提供工作流设计和监控的图形界面
6. **性能优化**：针对大规模工作流和数据进行性能调优

### 6.5 结论

本地工作流系统的设计与实现为企业和个人提供了一种在本地环境下管理和执行复杂任务序列的有效方案。
它既可以独立运行，又能与云端工作流系统无缝集成，为用户提供了最大的灵活性和数据安全性。

通过形式化的概念模型和严谨的系统实现，
本地工作流系统能够满足开发测试、离线处理、数据隐私以及网络受限等多种场景的需求，
成为现代软件基础设施中不可或缺的一部分。

### 7. 附录： 本地工作流设计与实现 - 思维导图（文本格式）

```text
本地工作流设计与实现
├── 核心概念
│   ├── 任务(Task)
│   │   ├── 输入/输出定义
│   │   ├── 执行逻辑
│   │   ├── 状态管理
│   │   └── 生命周期
│   ├── 工作流(Workflow)
│   │   ├── DAG结构
│   │   ├── 版本控制
│   │   ├── 状态追踪
│   │   └── 元数据管理
│   ├── 执行器(Executor)
│   │   ├── 任务类型映射
│   │   ├── 执行策略
│   │   ├── 资源管理
│   │   └── 异常处理
│   ├── 数据流(DataFlow)
│   │   ├── 类型系统
│   │   ├── 数据转换
│   │   ├── 数据校验
│   │   └── 数据序列化
│   └── 控制流(ControlFlow)
│       ├── 条件表达式
│       ├── 分支逻辑
│       ├── 状态依赖
│       └── 执行约束
├── 形式模型
│   ├── 工作流五元组定义
│   │   ├── 任务集合(T)
│   │   ├── 执行器集合(E)
│   │   ├── 数据流关系(D)
│   │   ├── 控制流关系(C)
│   │   └── 状态空间(S)
│   ├── 状态转换系统
│   │   ├── 状态定义
│   │   ├── 转换函数
│   │   ├── 状态序列
│   │   └── 终止条件
│   └── 形式化验证
│       ├── 死锁检测
│       ├── 可达性分析
│       ├── 活性验证
│       └── 安全性保障
├── 系统架构
│   ├── 分层设计
│   │   ├── API层
│   │   ├── 引擎层
│   │   ├── 执行层
│   │   ├── 存储层
│   │   └── 同步层
│   ├── 核心组件
│   │   ├── 工作流引擎
│   │   ├── 任务调度器
│   │   ├── 状态管理器
│   │   ├── 事件系统
│   │   └── 持久化管理器
│   ├── 接口设计
│   │   ├── 工作流定义接口
│   │   ├── 执行控制接口
│   │   ├── 状态查询接口
│   │   ├── 历史记录接口
│   │   └── 同步管理接口
│   └── 通信机制
│       ├── 事件传递
│       ├── 状态通知
│       ├── 数据交换
│       └── 外部集成
├── 存储与持久化
│   ├── 多级存储策略
│   │   ├── 内存缓存
│   │   ├── 本地文件
│   │   ├── 嵌入式数据库
│   │   └── 外部存储
│   ├── 数据模型
│   │   ├── 工作流定义
│   │   ├── 执行记录
│   │   ├── 任务状态
│   │   └── 事件日志
│   ├── 快照机制
│   │   ├── 增量快照
│   │   ├── 完整快照
│   │   ├── 快照调度
│   │   └── 快照恢复
│   └── 查询能力
│       ├── 历史查询
│       ├── 状态过滤
│       ├── 统计分析
│       └── 性能优化
├── 云端同步
│   ├── 同步模型
│   │   ├── 变更检测
│   │   ├── 冲突解决
│   │   ├── 数据合并
│   │   └── 一致性保证
│   ├── 同步策略
│   │   ├── 定时同步
│   │   ├── 事件触发
│   │   ├── 手动同步
│   │   └── 选择性同步
│   ├── 错误处理
│   │   ├── 重试机制
│   │   ├── 失败记录
│   │   ├── 降级策略
│   │   └── 恢复流程
│   └── 安全机制
│       ├── 身份验证
│       ├── 授权控制
│       ├── 数据加密
│       └── 审计日志
└── 实现特性
    ├── 代码模块
    │   ├── 核心定义
    │   ├── 引擎实现
    │   ├── 执行器库
    │   ├── 存储适配器
    │   └── 工具集成
    ├── 可扩展点
    │   ├── 自定义执行器
    │   ├── 存储适配器
    │   ├── 事件监听器
    │   └── 表达式引擎
    ├── 错误处理
    │   ├── 异常捕获
    │   ├── 错误传播
    │   ├── 自动重试
    │   └── 降级策略
    └── 性能优化
        ├── 并行执行
        ├── 资源控制
        ├── 缓存策略
        └── 批量处理
```

## 4.2节和4.3节存在的问题修正

### 4.2 工作流引擎 (问题修正)

```go
// workflow/engine.go

package workflow

import (
    "context"
    "fmt"
    "sync"
    "time"
    
    "github.com/google/uuid"
)

// Engine 是工作流执行引擎
type Engine struct {
    store          Storage
    executors      map[string]Executor
    executions     map[string]*WorkflowExecution
    eventListeners []EventListener
    mu             sync.RWMutex
}

// 修复：添加适当的并发控制和任务终止机制
func (e *Engine) runWorkflow(ctx context.Context, workflow *Workflow, execution *WorkflowExecution) {
    defer func() {
        if r := recover(); r != nil {
            execution.State = WorkflowStateFailed
            execution.Error = fmt.Sprintf("工作流执行panic: %v", r)
            e.finishExecution(execution)
        }
    }()
    
    // 构建依赖图
    taskDeps := make(map[string][]string)
    taskChildren := make(map[string][]string)
    readyTasks := make([]string, 0)
    
    for taskID, task := range workflow.Tasks {
        deps := task.DependsOn
        taskDeps[taskID] = deps
        
        if len(deps) == 0 {
            readyTasks = append(readyTasks, taskID)
        }
        
        for _, dep := range deps {
            if _, exists := taskChildren[dep]; !exists {
                taskChildren[dep] = make([]string, 0)
            }
            taskChildren[dep] = append(taskChildren[dep], taskID)
        }
    }
    
    // 修复：使用通道进行任务调度，更好地支持取消和超时
    taskCompletionCh := make(chan string, len(workflow.Tasks))
    taskErrorCh := make(chan error, len(workflow.Tasks))
    
    // 创建子上下文，用于控制所有任务
    workflowCtx, cancelWorkflow := context.WithCancel(ctx)
    defer cancelWorkflow()
    
    // 任务执行计数
    var completedTasks, failedTasks int
    totalTasks := len(workflow.Tasks)
    
    // 修复：添加任务运行管理映射
    runningTasks := make(map[string]context.CancelFunc)
    var tasksMutex sync.Mutex
    
    // 启动任务处理循环
    for {
        // 处理就绪任务
        for _, taskID := range readyTasks {
            taskID := taskID // 避免闭包捕获循环变量
            
            tasksMutex.Lock()
            task := workflow.Tasks[taskID]
            // 更新任务状态
            task.State = TaskStateRunning
            execution.TaskStates[taskID] = TaskStateRunning
            now := time.Now()
            task.StartTime = &now
            
            // 创建任务上下文，支持单独取消
            taskCtx, cancelTask := context.WithCancel(workflowCtx)
            runningTasks[taskID] = cancelTask
            tasksMutex.Unlock()
            
            e.store.SaveExecution(execution)
            
            // 发布任务开始事件
            e.publishEvent(&Event{
                Type:        EventTaskStarted,
                WorkflowID:  workflow.ID,
                TaskID:      taskID,
                ExecutionID: execution.ID,
                Timestamp:   now,
            })
            
            // 执行任务
            go func() {
                defer func() {
                    if r := recover(); r != nil {
                        taskErrorCh <- fmt.Errorf("任务执行panic: %v", r)
                        return
                    }
                }()
                
                // 处理任务输入
                e.processTaskInputs(workflow, task, execution)
                
                // 查找合适的执行器
                var executor Executor
                for _, exec := range e.executors {
                    if exec.CanExecute(task.Type) {
                        executor = exec
                        break
                    }
                }
                
                if executor == nil {
                    taskErrorCh <- fmt.Errorf("没有找到适合任务类型 %s 的执行器", task.Type)
                    return
                }
                
                // 执行任务
                err := executor.Execute(taskCtx, task)
                
                tasksMutex.Lock()
                delete(runningTasks, taskID)
                endTime := time.Now()
                task.EndTime = &endTime
                
                if err != nil {
                    // 任务失败
                    task.State = TaskStateFailed
                    task.Error = err.Error()
                    execution.TaskStates[taskID] = TaskStateFailed
                    
                    e.publishEvent(&Event{
                        Type:        EventTaskFailed,
                        WorkflowID:  workflow.ID,
                        TaskID:      taskID,
                        ExecutionID: execution.ID,
                        Timestamp:   endTime,
                        Data:        map[string]interface{}{"error": task.Error},
                    })
                    
                    taskErrorCh <- err
                } else {
                    // 任务成功
                    task.State = TaskStateSucceeded
                    execution.TaskStates[taskID] = TaskStateSucceeded
                    execution.TaskResults[taskID] = task.Outputs
                    
                    e.publishEvent(&Event{
                        Type:        EventTaskCompleted,
                        WorkflowID:  workflow.ID,
                        TaskID:      taskID,
                        ExecutionID: execution.ID,
                        Timestamp:   endTime,
                        Data:        map[string]interface{}{"outputs": task.Outputs},
                    })
                    
                    taskCompletionCh <- taskID
                }
                tasksMutex.Unlock()
                
                e.store.SaveExecution(execution)
            }()
        }
        
        // 重置就绪任务列表
        readyTasks = make([]string, 0)
        
        // 等待任务完成或出错
        select {
        case taskID := <-taskCompletionCh:
            // 任务成功完成
            completedTasks++
            
            // 检查是否有子任务可以执行
            if children, exists := taskChildren[taskID]; exists {
                for _, childID := range children {
                    // 检查该子任务的所有依赖是否已完成
                    allDepsCompleted := true
                    for _, depID := range taskDeps[childID] {
                        if workflow.Tasks[depID].State != TaskStateSucceeded {
                            allDepsCompleted = false
                            break
                        }
                    }
                    
                    if allDepsCompleted {
                        readyTasks = append(readyTasks, childID)
                    }
                }
            }
            
        case err := <-taskErrorCh:
            // 任务执行出错
            failedTasks++
            fmt.Printf("任务执行失败: %v\n", err)
            
            // 根据工作流配置决定是否继续执行
            // 这里采用简单策略：任何任务失败都停止工作流
            // 实际应用可能需要更复杂的策略
            if failedTasks > 0 {
                // 取消所有运行中的任务
                tasksMutex.Lock()
                for _, cancel := range runningTasks {
                    cancel()
                }
                tasksMutex.Unlock()
                
                // 更新工作流状态
                execution.State = WorkflowStateFailed
                execution.Error = "一个或多个任务执行失败"
                
                e.publishEvent(&Event{
                    Type:        EventWorkflowFailed,
                    WorkflowID:  workflow.ID,
                    ExecutionID: execution.ID,
                    Timestamp:   time.Now(),
                    Data:        map[string]interface{}{"error": execution.Error},
                })
                
                e.finishExecution(execution)
                return
            }
            
        case <-ctx.Done():
            // 外部取消或超时
            execution.State = WorkflowStateCancelled
            execution.Error = "工作流被外部取消"
            
            // 取消所有运行中的任务
            tasksMutex.Lock()
            for _, cancel := range runningTasks {
                cancel()
            }
            tasksMutex.Unlock()
            
            e.publishEvent(&Event{
                Type:        EventWorkflowFailed,
                WorkflowID:  workflow.ID,
                ExecutionID: execution.ID,
                Timestamp:   time.Now(),
                Data:        map[string]interface{}{"error": execution.Error},
            })
            
            e.finishExecution(execution)
            return
        }
        
        // 检查工作流是否完成
        if completedTasks == totalTasks {
            execution.State = WorkflowStateSucceeded
            
            e.publishEvent(&Event{
                Type:        EventWorkflowCompleted,
                WorkflowID:  workflow.ID,
                ExecutionID: execution.ID,
                Timestamp:   time.Now(),
            })
            
            e.finishExecution(execution)
            return
        }
        
        // 如果没有更多就绪任务，但工作流尚未完成，说明出现了死锁
        if len(readyTasks) == 0 && completedTasks + failedTasks < totalTasks {
            execution.State = WorkflowStateFailed
            execution.Error = "工作流陷入死锁状态"
            
            e.publishEvent(&Event{
                Type:        EventWorkflowFailed,
                WorkflowID:  workflow.ID,
                ExecutionID: execution.ID,
                Timestamp:   time.Now(),
                Data:        map[string]interface{}{"error": execution.Error},
            })
            
            e.finishExecution(execution)
            return
        }
    }
}
```

### 4.3 执行器 (问题修正)

```go
// workflow/executor.go

package workflow

import (
    "context"
    "fmt"
    "os/exec"
    "strings"
    "sync"
    "time"
)

// BaseExecutor 提供执行器的基本功能
type BaseExecutor struct {
    taskTypes     []string
    runningTasks  map[string]context.CancelFunc
    mu            sync.RWMutex
}

// NewBaseExecutor 创建基本执行器
func NewBaseExecutor(taskTypes []string) *BaseExecutor {
    return &BaseExecutor{
        taskTypes:    taskTypes,
        runningTasks: make(map[string]context.CancelFunc),
    }
}

// CanExecute 检查是否可以执行指定类型的任务
func (e *BaseExecutor) CanExecute(taskType string) bool {
    for _, t := range e.taskTypes {
        if t == taskType {
            return true
        }
    }
    return false
}

// Abort 中止任务执行
func (e *BaseExecutor) Abort(taskID string) error {
    e.mu.Lock()
    defer e.mu.Unlock()
    
    if cancel, exists := e.runningTasks[taskID]; exists {
        cancel()
        delete(e.runningTasks, taskID)
        return nil
    }
    
    return fmt.Errorf("任务未运行: %s", taskID)
}

// registerRunningTask 注册正在运行的任务
func (e *BaseExecutor) registerRunningTask(taskID string, cancel context.CancelFunc) {
    e.mu.Lock()
    e.runningTasks[taskID] = cancel
    e.mu.Unlock()
}

// unregisterRunningTask 取消注册正在运行的任务
func (e *BaseExecutor) unregisterRunningTask(taskID string) {
    e.mu.Lock()
    delete(e.runningTasks, taskID)
    e.mu.Unlock()
}

// ShellExecutor 执行shell命令的执行器
type ShellExecutor struct {
    *BaseExecutor
}

// NewShellExecutor 创建一个Shell执行器
func NewShellExecutor() *ShellExecutor {
    return &ShellExecutor{
        BaseExecutor: NewBaseExecutor([]string{"shell", "bash", "cmd"}),
    }
}

// Execute 执行Shell命令
func (e *ShellExecutor) Execute(ctx context.Context, task *Task) error {
    childCtx, cancel := context.WithCancel(ctx)
    e.registerRunningTask(task.ID, cancel)
    defer e.unregisterRunningTask(task.ID)
    
    // 解析命令
    command, ok := task.Config["command"].(string)
    if !ok {
        return fmt.Errorf("无效的Shell命令配置")
    }
    
    // 替换输入变量
    for key, value := range task.Inputs {
        placeholder := fmt.Sprintf("${input.%s}", key)
        strValue := fmt.Sprintf("%v", value)
        command = strings.Replace(command, placeholder, strValue, -1)
    }
    
    // 创建命令
    var cmd *exec.Cmd
    if strings.HasPrefix(command, "bash ") {
        cmd = exec.CommandContext(childCtx, "bash", "-c", command[5:])
    } else {
        // 根据操作系统选择shell
        shell := "sh"
        shellOption := "-c"
        cmd = exec.CommandContext(childCtx, shell, shellOption, command)
    }
    
    // 捕获输出
    outputBytes, err := cmd.CombinedOutput()
    output := string(outputBytes)
    
    // 任务完成，存储结果
    task.Outputs["exitCode"] = cmd.ProcessState.ExitCode()
    task.Outputs["stdout"] = output
    
    if err != nil {
        // 命令执行失败，但我们已经捕获了输出和退出码
        return fmt.Errorf("命令执行失败: %w, 输出: %s", err, output)
    }
    
    return nil
}

// HTTPExecutor 执行HTTP请求的执行器
type HTTPExecutor struct {
    *BaseExecutor
}

// NewHTTPExecutor 创建HTTP执行器
func NewHTTPExecutor() *HTTPExecutor {
    return &HTTPExecutor{
        BaseExecutor: NewBaseExecutor([]string{"http", "rest"}),
    }
}

// Execute 执行HTTP请求
// 修复：添加完整的HTTP请求实现
func (e *HTTPExecutor) Execute(ctx context.Context, task *Task) error {
    childCtx, cancel := context.WithCancel(ctx)
    e.registerRunningTask(task.ID, cancel)
    defer e.unregisterRunningTask(task.ID)
    
    // 获取请求配置
    url, ok := task.Config["url"].(string)
    if !ok {
        return fmt.Errorf("无效的HTTP URL配置")
    }
    
    method, _ := task.Config["method"].(string)
    if method == "" {
        method = "GET"
    }
    
    // 设置超时
    timeout := 30 * time.Second
    if timeoutVal, ok := task.Config["timeout"].(float64); ok {
        timeout = time.Duration(timeoutVal) * time.Second
    }
    
    // 创建请求上下文
    reqCtx, reqCancel := context.WithTimeout(childCtx, timeout)
    defer reqCancel()
    
    // 准备请求体
    var requestBody []byte
    if bodyData, hasBody := task.Inputs["body"]; hasBody {
        var err error
        switch v := bodyData.(type) {
        case string:
            requestBody = []byte(v)
        case []byte:
            requestBody = v
        default:
            // 尝试JSON序列化
            requestBody, err = json.Marshal(bodyData)
            if err != nil {
                return fmt.Errorf("序列化请求体失败: %w", err)
            }
        }
    }
    
    // 创建请求
    req, err := http.NewRequestWithContext(reqCtx, method, url, bytes.NewBuffer(requestBody))
    if err != nil {
        return fmt.Errorf("创建HTTP请求失败: %w", err)
    }
    
    // 设置请求头
    if headers, ok := task.Config["headers"].(map[string]interface{}); ok {
        for key, value := range headers {
            req.Header.Set(key, fmt.Sprintf("%v", value))
        }
    }
    
    // 设置Content-Type
    if len(requestBody) > 0 && req.Header.Get("Content-Type") == "" {
        req.Header.Set("Content-Type", "application/json")
    }
    
    // 发送请求
    client := &http.Client{
        Timeout: timeout,
    }
    
    resp, err := client.Do(req)
    if err != nil {
        return fmt.Errorf("执行HTTP请求失败: %w", err)
    }
    defer resp.Body.Close()
    
    // 读取响应
    responseBody, err := ioutil.ReadAll(resp.Body)
    if err != nil {
        return fmt.Errorf("读取响应失败: %w", err)
    }
    
    // 解析JSON响应（如果适用）
    var responseData interface{}
    contentType := resp.Header.Get("Content-Type")
    if strings.Contains(contentType, "application/json") {
        if err := json.Unmarshal(responseBody, &responseData); err != nil {
            // 非JSON或解析失败，使用原始响应
            responseData = string(responseBody)
        }
    } else {
        responseData = string(responseBody)
    }
    
    // 保存响应到输出
    task.Outputs["statusCode"] = resp.StatusCode
    task.Outputs["headers"] = resp.Header
    task.Outputs["body"] = responseData
    
    // 检查状态码
    if resp.StatusCode >= 400 {
        return fmt.Errorf("HTTP请求返回错误状态码: %d", resp.StatusCode)
    }
    
    return nil
}

// FunctionExecutor 执行Go函数的执行器
type FunctionExecutor struct {
    *BaseExecutor
    functions map[string]func(context.Context, map[string]interface{}) (map[string]interface{}, error)
    mu        sync.RWMutex
}

// NewFunctionExecutor 创建函数执行器
func NewFunctionExecutor() *FunctionExecutor {
    return &FunctionExecutor{
        BaseExecutor: NewBaseExecutor([]string{"function", "golang"}),
        functions:    make(map[string]func(context.Context, map[string]interface{}) (map[string]interface{}, error)),
    }
}

// RegisterFunction 注册可执行函数
func (e *FunctionExecutor) RegisterFunction(name string, fn func(context.Context, map[string]interface{}) (map[string]interface{}, error)) {
    e.mu.Lock()
    defer e.mu.Unlock()
    e.functions[name] = fn
}

// Execute 执行Go函数
func (e *FunctionExecutor) Execute(ctx context.Context, task *Task) error {
    childCtx, cancel := context.WithCancel(ctx)
    e.registerRunningTask(task.ID, cancel)
    defer e.unregisterRunningTask(task.ID)
    
    // 获取函数名
    funcName, ok := task.Config["function"].(string)
    if !ok {
        return fmt.Errorf("未指定函数名")
    }
    
    // 查找函数
    e.mu.RLock()
    fn, exists := e.functions[funcName]
    e.mu.RUnlock()
    
    if !exists {
        return fmt.Errorf("函数未注册: %s", funcName)
    }
    
    // 执行函数
    outputs, err := fn(childCtx, task.Inputs)
    if err != nil {
        return fmt.Errorf("函数执行失败: %w", err)
    }
    
    // 将函数输出存储到任务输出
    for k, v := range outputs {
        task.Outputs[k] = v
    }
    
    return nil
}
```

## 本地工作流系统架构图（文本格式）

```text
+----------------------------------+
|        应用/UI 层                |
+----------------------------------+
           |      ^
           v      |
+----------------------------------+
|            API 层                |
|----------------------------------+
| - 工作流定义API                  |
| - 工作流执行API                  |
| - 状态查询API                    |
| - 历史查询API                    |
| - 同步管理API                    |
+----------------------------------+
           |      ^
           v      |
+----------------------------------+
|           引擎层                 |
|----------------------------------+
| +------------------------------+ |
| |         工作流引擎           | |
| |------------------------------| |
| | - 工作流解析与验证           | |
| | - 任务调度与依赖管理         | |
| | - 状态管理                   | |
| | - 事件处理                   | |
| +------------------------------+ |
|              |       ^           |
|              v       |           |
| +------------------------------+ |
| |        调度管理器            | |
| |------------------------------| |
| | - 任务排队                   | |
| | - 资源分配                   | |
| | - 并发控制                   | |
| | - 超时管理                   | |
| +------------------------------+ |
+----------------------------------+
           |      ^
           v      |
+----------------------------------+
|           执行层                 |
|----------------------------------+
| +------------------------------+ |
| |       执行器注册表           | |
| +------------------------------+ |
|              |                   |
|              v                   |
| +------------+---+------------+  |
| |                |             | |
| v                v             v |
| +--------+  +--------+  +--------+
| |Shell执行|  |HTTP执行|  |函数执行|
| |器      |  |器      |  |器      |
| +--------+  +--------+  +--------+
+----------------------------------+
           |      ^
           v      |
+----------------------------------+
|          数据/控制流层           |
|----------------------------------+
| +------------------------------+ |
| |         数据映射器           | |
| +------------------------------+ |
|                                  |
| +------------------------------+ |
| |         控制流管理器         | |
| +------------------------------+ |
+----------------------------------+
           |      ^
           v      |
+----------------------------------+
|           存储层                 |
|----------------------------------+
| +------------------------------+ |
| |        存储管理器            | |
| |------------------------------| |
| | - 工作流定义持久化           | |
| | - 执行状态记录               | |
| | - 历史数据管理               | |
| | - 快照与恢复                 | |
| +------------------------------+ |
|              |                   |
|              v                   |
| +------------+------------+     |
| |                         |     |
| v                         v     |
| +--------------+  +--------------+
| | 内存缓存/    |  | 本地文件/    |
| | 缓存管理     |  | 嵌入式数据库 |
| +--------------+  +--------------+
+----------------------------------+
           |      ^
           v      |
+----------------------------------+
|           同步层                 |
|----------------------------------+
| +------------------------------+ |
| |        同步管理器            | |
| |------------------------------| |
| | - 变更检测                   | |
| | - 冲突解决                   | |
| | - 增量同步                   | |
| | - 版本控制                   | |
| +------------------------------+ |
|              |                   |
|              v                   |
| +------------------------------+ |
| |        安全管理器            | |
| |------------------------------| |
| | - 认证与授权                 | |
| | - 数据加密                   | |
| | - 安全通道                   | |
| +------------------------------+ |
+----------------------------------+
           |      ^
           v      |
+----------------------------------+
|          云端工作流系统          |
+----------------------------------+
```

## 系统组件间的数据流动

```text
[工作流定义] ---> [工作流引擎] ---> [存储管理器] ---> [持久化存储]
                      |
[执行请求] ----------> | ---> [任务调度器] ---> [执行器] ---> [任务执行]
                      |                              |
                      |                              v
[数据输入] ------------> ---> [数据映射器] <------> [任务结果]
                      |
[条件逻辑] ------------> ---> [控制流管理器] ---> [任务流控制]
                      |
                      v
[执行状态] <--- [事件系统] ---> [状态更新] ---> [存储管理器]
    |                                              |
    v                                              v
[状态查询API] <-------------------------------- [历史记录]
    |
    v
[同步管理器] <---> [云端同步] <---> [云端工作流系统]
```

## 核心交互流程

```text
1. 工作流定义与存储:
   用户 --> API层 --> 引擎层(验证) --> 存储层 --> 持久化

2. 工作流执行流程:
   用户 --> API层 --> 引擎层 
       --> 任务依赖分析 
       --> 可执行任务标识 
       --> 调度执行 
       --> 执行层(执行器选择) 
       --> 任务执行 
       --> 结果收集 
       --> 状态更新 
       --> 下一批任务处理

3. 数据流处理:
   前置任务结果 --> 数据映射 --> 当前任务输入 --> 当前任务处理 --> 输出结果

4. 控制流处理:
   前置任务结果 --> 条件评估 --> 执行路径确定 --> 任务调度

5. 状态查询与监控:
   用户 --> API层 --> 存储层 --> 查询结果返回

6. 云端同步流程:
   本地变更 --> 检测 --> 序列化 --> 冲突检查 --> 同步到云端
   云端变更 --> 检测 --> 拉取 --> 合并 --> 更新本地
```
