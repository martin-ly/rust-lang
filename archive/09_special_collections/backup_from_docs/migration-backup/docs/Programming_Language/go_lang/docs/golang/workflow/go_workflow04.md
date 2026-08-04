# Go语言实现工作流模式的形式化分析与代码实现

```text
<think>
这个请求要求我使用Go语言（Golang）来实现工作流形式上的所有模式，
并解释各种形式关系（相容性、等价性、嵌入性等）。
用户提到了23+工作流模式，
并将它们分为控制流模式、数据流模式、资源模式和异常处理模式等分类。

用户希望：

1. 分析各种工作流模式的形式模型
2. 用Golang实现这些模式或等价模型
3. 提供完整的代码实现
4. 输出为Markdown格式，含目录，可能包含思维导图
5. 不应包含外部链接，只提供文本格式

我需要使用中文回复（根据自定义指令）。

让我首先整理一下常见的工作流模式，然后用Golang实现这些模式。我会分类别进行组织。

工作流模式（基于van der Aalst等人的工作流模式研究）通常包括：

控制流模式（Control-Flow Patterns）:

1. 顺序执行（Sequence）
2. 并行分支（Parallel Split）
3. 同步（Synchronization）
4. 排他选择（Exclusive Choice）
5. 简单合并（Simple Merge）
6. 多选择（Multi-Choice）
7. 结构化同步合并（Structured Synchronizing Merge）
8. 多合并（Multi-Merge）
9. 结构化判别（Structured Discriminator）
10. 任意循环（Arbitrary Cycles）
11. 隐式终止（Implicit Termination）
12. 多实例（Multiple Instances）
13. 等等...

数据流模式（Data Patterns）:

1. 任务数据（Task Data）
2. 块数据（Block Data）
3. 范围数据（Scope Data）
4. 多实例数据（Multiple Instance Data）
5. 数据交互（Data Interaction）
6. 等等...

资源模式（Resource Patterns）:

1. 直接分配（Direct Allocation）
2. 基于角色的分配（Role-based Allocation）
3. 分离职责（Separation of Duties）
4. 基于案例的职责（Case Handling）
5. 等等...

异常处理模式（Exception Handling Patterns）:

1. 取消任务（Task Cancellation）
2. 跳过活动（Activity Skip）
3. 回滚活动（Activity Rollback）
4. 等等...

我会针对这些模式，使用Golang的特性来实现它们，包括但不限于：

- 协程（goroutines）和通道（channels）
- 接口（interfaces）和结构体（structs）
- 错误处理机制
- 同步原语（sync包）
- 上下文（context包）

然后我会分析这些实现之间的关系，包括相容性、等价性和嵌入性。
</think>
```

## 目录

- [Go语言实现工作流模式的形式化分析与代码实现](#go语言实现工作流模式的形式化分析与代码实现)
  - [目录](#目录)
  - [引言](#引言)
  - [工作流模式概述](#工作流模式概述)
  - [控制流模式](#控制流模式)
    - [顺序执行模式](#顺序执行模式)
    - [并行分支模式](#并行分支模式)
    - [同步模式](#同步模式)
    - [排他选择模式](#排他选择模式)
    - [简单合并模式](#简单合并模式)
    - [多选择模式](#多选择模式)
    - [结构化同步合并模式](#结构化同步合并模式)
    - [多合并模式](#多合并模式)
  - [数据流模式](#数据流模式)
    - [任务数据模式](#任务数据模式)
    - [管道数据模式](#管道数据模式)
    - [共享状态模式](#共享状态模式)
  - [资源模式](#资源模式)
    - [资源分配模式](#资源分配模式)
    - [资源池模式](#资源池模式)
    - [资源限制模式](#资源限制模式)
  - [异常处理模式](#异常处理模式)
    - [错误传播模式](#错误传播模式)
    - [超时控制模式](#超时控制模式)
    - [重试模式](#重试模式)
    - [回退模式](#回退模式)
  - [模式之间的关系](#模式之间的关系)
    - [相容性分析](#相容性分析)
    - [等价性分析](#等价性分析)
    - [嵌入性分析](#嵌入性分析)
  - [总结](#总结)

## 引言

工作流模式是一组描述工作流系统常见行为的设计模式，广泛应用于业务流程管理、数据处理、服务编排等场景。本文将使用Go语言实现多种工作流模式，并分析这些模式之间的形式关系，包括相容性、等价性和嵌入性。

Go语言具有并发编程友好的特性（goroutines和channels）、强大的类型系统和错误处理机制，非常适合实现各种工作流模式。

## 工作流模式概述

工作流模式大致可分为四类：

```text
工作流模式
├── 控制流模式：描述活动执行顺序和条件的模式
├── 数据流模式：描述数据如何在工作流中传递和处理的模式
├── 资源模式：描述如何分配和管理执行资源的模式
└── 异常处理模式：描述如何处理异常情况的模式
```

## 控制流模式

### 顺序执行模式

最基本的工作流模式，任务按照预定义的顺序依次执行。

```go
package workflow

// 定义工作单元接口
type Task interface {
    Execute() error
}

// 顺序执行模式
type SequentialWorkflow struct {
    tasks []Task
}

// 创建新的顺序工作流
func NewSequentialWorkflow() *SequentialWorkflow {
    return &SequentialWorkflow{
        tasks: make([]Task, 0),
    }
}

// 添加任务到工作流
func (w *SequentialWorkflow) AddTask(task Task) {
    w.tasks = append(w.tasks, task)
}

// 执行工作流
func (w *SequentialWorkflow) Execute() error {
    for _, task := range w.tasks {
        err := task.Execute()
        if err != nil {
            return err
        }
    }
    return nil
}

// 简单任务实现
type SimpleTask struct {
    name     string
    function func() error
}

func NewSimpleTask(name string, function func() error) *SimpleTask {
    return &SimpleTask{
        name:     name,
        function: function,
    }
}

func (t *SimpleTask) Execute() error {
    return t.function()
}
```

使用示例：

```go
func main() {
    workflow := NewSequentialWorkflow()
    
    // 添加三个顺序执行的任务
    workflow.AddTask(NewSimpleTask("步骤1", func() error {
        fmt.Println("执行步骤1")
        return nil
    }))
    
    workflow.AddTask(NewSimpleTask("步骤2", func() error {
        fmt.Println("执行步骤2")
        return nil
    }))
    
    workflow.AddTask(NewSimpleTask("步骤3", func() error {
        fmt.Println("执行步骤3")
        return nil
    }))
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    }
}
```

### 并行分支模式

允许多个任务并行执行的模式。在Go中，使用goroutines实现。

```go
package workflow

import (
    "sync"
)

// 并行工作流
type ParallelWorkflow struct {
    tasks []Task
}

// 创建新的并行工作流
func NewParallelWorkflow() *ParallelWorkflow {
    return &ParallelWorkflow{
        tasks: make([]Task, 0),
    }
}

// 添加任务到工作流
func (w *ParallelWorkflow) AddTask(task Task) {
    w.tasks = append(w.tasks, task)
}

// 执行工作流
func (w *ParallelWorkflow) Execute() error {
    var wg sync.WaitGroup
    errChan := make(chan error, len(w.tasks))
    
    // 启动所有任务
    for _, task := range w.tasks {
        wg.Add(1)
        go func(t Task) {
            defer wg.Done()
            if err := t.Execute(); err != nil {
                errChan <- err
            }
        }(task)
    }
    
    // 等待所有任务完成
    wg.Wait()
    close(errChan)
    
    // 检查是否有错误
    for err := range errChan {
        if err != nil {
            return err // 返回第一个遇到的错误
        }
    }
    
    return nil
}
```

使用示例：

```go
func main() {
    workflow := NewParallelWorkflow()
    
    // 添加三个并行执行的任务
    workflow.AddTask(NewSimpleTask("并行任务1", func() error {
        fmt.Println("执行并行任务1")
        time.Sleep(2 * time.Second)
        return nil
    }))
    
    workflow.AddTask(NewSimpleTask("并行任务2", func() error {
        fmt.Println("执行并行任务2")
        time.Sleep(1 * time.Second)
        return nil
    }))
    
    workflow.AddTask(NewSimpleTask("并行任务3", func() error {
        fmt.Println("执行并行任务3")
        time.Sleep(3 * time.Second)
        return nil
    }))
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    }
}
```

### 同步模式

等待多个并行任务完成后再继续执行。

```go
package workflow

import (
    "sync"
)

// 同步点
type SynchronizationPoint struct {
    previous *ParallelWorkflow
    next     *SequentialWorkflow
}

// 创建同步点
func NewSynchronizationPoint(previous *ParallelWorkflow, next *SequentialWorkflow) *SynchronizationPoint {
    return &SynchronizationPoint{
        previous: previous,
        next:     next,
    }
}

// 执行同步工作流
func (sp *SynchronizationPoint) Execute() error {
    // 执行并行部分
    if err := sp.previous.Execute(); err != nil {
        return err
    }
    
    // 所有并行任务完成后，执行顺序部分
    return sp.next.Execute()
}
```

使用示例：

```go
func main() {
    // 创建并行部分
    parallelFlow := NewParallelWorkflow()
    parallelFlow.AddTask(NewSimpleTask("并行任务1", func() error {
        fmt.Println("执行并行任务1")
        time.Sleep(2 * time.Second)
        return nil
    }))
    parallelFlow.AddTask(NewSimpleTask("并行任务2", func() error {
        fmt.Println("执行并行任务2")
        time.Sleep(1 * time.Second)
        return nil
    }))
    
    // 创建同步后的顺序部分
    sequentialFlow := NewSequentialWorkflow()
    sequentialFlow.AddTask(NewSimpleTask("同步后任务", func() error {
        fmt.Println("所有并行任务完成后执行")
        return nil
    }))
    
    // 创建同步点
    syncPoint := NewSynchronizationPoint(parallelFlow, sequentialFlow)
    
    // 执行同步工作流
    err := syncPoint.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    }
}
```

### 排他选择模式

基于条件选择一个执行路径的模式。

```go
package workflow

// 定义条件接口
type Condition interface {
    Evaluate() bool
}

// 简单条件实现
type SimpleCondition struct {
    predicate func() bool
}

func NewSimpleCondition(predicate func() bool) *SimpleCondition {
    return &SimpleCondition{predicate: predicate}
}

func (c *SimpleCondition) Evaluate() bool {
    return c.predicate()
}

// 排他选择工作流
type ExclusiveChoiceWorkflow struct {
    branches map[Condition]Task
    default_ Task
}

// 创建排他选择工作流
func NewExclusiveChoiceWorkflow() *ExclusiveChoiceWorkflow {
    return &ExclusiveChoiceWorkflow{
        branches: make(map[Condition]Task),
    }
}

// 添加条件分支
func (w *ExclusiveChoiceWorkflow) AddBranch(condition Condition, task Task) {
    w.branches[condition] = task
}

// 设置默认分支
func (w *ExclusiveChoiceWorkflow) SetDefaultBranch(task Task) {
    w.default_ = task
}

// 执行工作流
func (w *ExclusiveChoiceWorkflow) Execute() error {
    for condition, task := range w.branches {
        if condition.Evaluate() {
            return task.Execute()
        }
    }
    
    // 如果没有条件满足，执行默认分支
    if w.default_ != nil {
        return w.default_.Execute()
    }
    
    return nil
}
```

使用示例：

```go
func main() {
    workflow := NewExclusiveChoiceWorkflow()
    
    // 定义一些条件和对应的任务
    value := 15
    
    workflow.AddBranch(
        NewSimpleCondition(func() bool { return value > 20 }),
        NewSimpleTask("值大于20", func() error {
            fmt.Println("值大于20的分支被执行")
            return nil
        }),
    )
    
    workflow.AddBranch(
        NewSimpleCondition(func() bool { return value > 10 && value <= 20 }),
        NewSimpleTask("值在10到20之间", func() error {
            fmt.Println("值在10到20之间的分支被执行")
            return nil
        }),
    )
    
    workflow.SetDefaultBranch(
        NewSimpleTask("默认分支", func() error {
            fmt.Println("默认分支被执行")
            return nil
        }),
    )
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    }
}
```

### 简单合并模式

合并多个分支的执行路径，不需要同步。

```go
package workflow

// 简单合并工作流
type SimpleMergeWorkflow struct {
    incomingBranches []Task
    mergeTask        Task
}

// 创建简单合并工作流
func NewSimpleMergeWorkflow(mergeTask Task) *SimpleMergeWorkflow {
    return &SimpleMergeWorkflow{
        incomingBranches: make([]Task, 0),
        mergeTask:        mergeTask,
    }
}

// 添加输入分支
func (w *SimpleMergeWorkflow) AddIncomingBranch(task Task) {
    w.incomingBranches = append(w.incomingBranches, task)
}

// 执行特定分支然后执行合并任务
func (w *SimpleMergeWorkflow) ExecuteBranch(index int) error {
    if index < 0 || index >= len(w.incomingBranches) {
        return fmt.Errorf("分支索引 %d 超出范围", index)
    }
    
    // 执行选定的分支
    if err := w.incomingBranches[index].Execute(); err != nil {
        return err
    }
    
    // 执行合并任务
    return w.mergeTask.Execute()
}
```

使用示例：

```go
func main() {
    // 创建合并任务
    mergeTask := NewSimpleTask("合并任务", func() error {
        fmt.Println("执行合并任务")
        return nil
    })
    
    // 创建简单合并工作流
    workflow := NewSimpleMergeWorkflow(mergeTask)
    
    // 添加几个可能的输入分支
    workflow.AddIncomingBranch(NewSimpleTask("分支1", func() error {
        fmt.Println("执行分支1")
        return nil
    }))
    
    workflow.AddIncomingBranch(NewSimpleTask("分支2", func() error {
        fmt.Println("执行分支2")
        return nil
    }))
    
    workflow.AddIncomingBranch(NewSimpleTask("分支3", func() error {
        fmt.Println("执行分支3")
        return nil
    }))
    
    // 根据某些条件选择执行分支2
    branchToExecute := 1
    err := workflow.ExecuteBranch(branchToExecute)
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    }
}
```

### 多选择模式

基于条件选择多个执行路径的模式。

```go
package workflow

// 多选择工作流
type MultiChoiceWorkflow struct {
    branches map[Condition]Task
    default_ Task
}

// 创建多选择工作流
func NewMultiChoiceWorkflow() *MultiChoiceWorkflow {
    return &MultiChoiceWorkflow{
        branches: make(map[Condition]Task),
    }
}

// 添加条件分支
func (w *MultiChoiceWorkflow) AddBranch(condition Condition, task Task) {
    w.branches[condition] = task
}

// 设置默认分支
func (w *MultiChoiceWorkflow) SetDefaultBranch(task Task) {
    w.default_ = task
}

// 执行工作流
func (w *MultiChoiceWorkflow) Execute() error {
    executed := false
    var errs []error
    
    // 评估所有条件，执行满足条件的分支
    for condition, task := range w.branches {
        if condition.Evaluate() {
            executed = true
            if err := task.Execute(); err != nil {
                errs = append(errs, err)
            }
        }
    }
    
    // 如果没有条件满足，执行默认分支
    if !executed && w.default_ != nil {
        if err := w.default_.Execute(); err != nil {
            errs = append(errs, err)
        }
    }
    
    // 如果有错误，返回第一个错误
    if len(errs) > 0 {
        return errs[0]
    }
    
    return nil
}
```

使用示例：

```go
func main() {
    workflow := NewMultiChoiceWorkflow()
    
    // 定义一些条件和对应的任务
    temperature := 25
    humidity := 80
    
    workflow.AddBranch(
        NewSimpleCondition(func() bool { return temperature > 30 }),
        NewSimpleTask("高温警告", func() error {
            fmt.Println("触发高温警告")
            return nil
        }),
    )
    
    workflow.AddBranch(
        NewSimpleCondition(func() bool { return humidity > 70 }),
        NewSimpleTask("高湿度警告", func() error {
            fmt.Println("触发高湿度警告")
            return nil
        }),
    )
    
    workflow.AddBranch(
        NewSimpleCondition(func() bool { return temperature > 30 && humidity > 70 }),
        NewSimpleTask("高温高湿度警告", func() error {
            fmt.Println("触发高温高湿度综合警告")
            return nil
        }),
    )
    
    workflow.SetDefaultBranch(
        NewSimpleTask("默认分支", func() error {
            fmt.Println("正常状态，无需警告")
            return nil
        }),
    )
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    }
}
```

### 结构化同步合并模式

合并多选择模式中激活的分支，并在所有分支完成后继续。

```go
package workflow

import (
    "sync"
)

// 结构化同步合并工作流
type StructuredSyncMergeWorkflow struct {
    multiChoice *MultiChoiceWorkflow
    mergeTask   Task
}

// 创建结构化同步合并工作流
func NewStructuredSyncMergeWorkflow(mergeTask Task) *StructuredSyncMergeWorkflow {
    return &StructuredSyncMergeWorkflow{
        multiChoice: NewMultiChoiceWorkflow(),
        mergeTask:   mergeTask,
    }
}

// 添加条件分支
func (w *StructuredSyncMergeWorkflow) AddBranch(condition Condition, task Task) {
    w.multiChoice.AddBranch(condition, task)
}

// 设置默认分支
func (w *StructuredSyncMergeWorkflow) SetDefaultBranch(task Task) {
    w.multiChoice.SetDefaultBranch(task)
}

// 执行工作流
func (w *StructuredSyncMergeWorkflow) Execute() error {
    // 首先执行多选择部分
    activeBranches := make(map[Condition]bool)
    
    // 创建一个包装版本的多选择工作流，记录哪些分支被激活
    wrappedMultiChoice := &MultiChoiceWorkflow{
        branches: make(map[Condition]Task),
        default_: w.multiChoice.default_,
    }
    
    for condition, task := range w.multiChoice.branches {
        wrappedTask := NewSimpleTask("wrapped", func() error {
            err := task.Execute()
            activeBranches[condition] = true
            return err
        })
        wrappedMultiChoice.AddBranch(condition, wrappedTask)
    }
    
    // 执行多选择部分
    if err := wrappedMultiChoice.Execute(); err != nil {
        return err
    }
    
    // 执行合并任务
    return w.mergeTask.Execute()
}
```

使用示例：

```go
func main() {
    // 创建合并任务
    mergeTask := NewSimpleTask("同步合并", func() error {
        fmt.Println("所有激活的分支都已完成，执行合并任务")
        return nil
    })
    
    // 创建结构化同步合并工作流
    workflow := NewStructuredSyncMergeWorkflow(mergeTask)
    
    // 添加条件分支
    temperature := 35
    humidity := 80
    
    workflow.AddBranch(
        NewSimpleCondition(func() bool { return temperature > 30 }),
        NewSimpleTask("高温处理", func() error {
            fmt.Println("处理高温")
            time.Sleep(2 * time.Second)
            return nil
        }),
    )
    
    workflow.AddBranch(
        NewSimpleCondition(func() bool { return humidity > 70 }),
        NewSimpleTask("高湿度处理", func() error {
            fmt.Println("处理高湿度")
            time.Sleep(1 * time.Second)
            return nil
        }),
    )
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    }
}
```

### 多合并模式

合并多个分支，允许同一分支多次激活，每次激活后都触发下游任务。

```go
package workflow

import (
    "context"
    "sync"
)

// 多合并工作流
type MultiMergeWorkflow struct {
    ctx           context.Context
    cancelFunc    context.CancelFunc
    incomingPaths []chan struct{}
    mergeTask     Task
    wg            sync.WaitGroup
    done          chan struct{}
}

// 创建多合并工作流
func NewMultiMergeWorkflow(mergeTask Task) *MultiMergeWorkflow {
    ctx, cancel := context.WithCancel(context.Background())
    return &MultiMergeWorkflow{
        ctx:           ctx,
        cancelFunc:    cancel,
        incomingPaths: make([]chan struct{}, 0),
        mergeTask:     mergeTask,
        done:          make(chan struct{}),
    }
}

// 添加输入路径
func (w *MultiMergeWorkflow) AddIncomingPath() int {
    pathID := len(w.incomingPaths)
    w.incomingPaths = append(w.incomingPaths, make(chan struct{}, 100)) // 缓冲通道允许多次触发
    return pathID
}

// 启动工作流监听
func (w *MultiMergeWorkflow) Start() {
    w.wg.Add(1)
    go func() {
        defer w.wg.Done()
        
        // 创建聚合的通道
        cases := make([]reflect.SelectCase, len(w.incomingPaths)+1)
        cases[0] = reflect.SelectCase{
            Dir:  reflect.SelectRecv,
            Chan: reflect.ValueOf(w.ctx.Done()),
        }
        
        for i, ch := range w.incomingPaths {
            cases[i+1] = reflect.SelectCase{
                Dir:  reflect.SelectRecv,
                Chan: reflect.ValueOf(ch),
            }
        }
        
        for {
            chosen, _, ok := reflect.Select(cases)
            if chosen == 0 || !ok {
                // 上下文被取消或通道关闭
                return
            }
            
            // 执行合并任务
            w.mergeTask.Execute()
        }
    }()
}

// 激活指定路径
func (w *MultiMergeWorkflow) ActivatePath(pathID int) error {
    if pathID < 0 || pathID >= len(w.incomingPaths) {
        return fmt.Errorf("路径ID %d 超出范围", pathID)
    }
    
    select {
    case w.incomingPaths[pathID] <- struct{}{}:
        return nil
    default:
        return fmt.Errorf("路径 %d 缓冲区已满", pathID)
    }
}

// 停止工作流
func (w *MultiMergeWorkflow) Stop() {
    w.cancelFunc()
    w.wg.Wait()
    close(w.done)
}

// 等待工作流完成
func (w *MultiMergeWorkflow) Wait() {
    <-w.done
}
```

使用示例：

```go
func main() {
    // 创建合并任务
    mergeTask := NewSimpleTask("合并处理", func() error {
        fmt.Println("执行合并处理")
        return nil
    })
    
    // 创建多合并工作流
    workflow := NewMultiMergeWorkflow(mergeTask)
    
    // 添加三个输入路径
    path1 := workflow.AddIncomingPath()
    path2 := workflow.AddIncomingPath()
    path3 := workflow.AddIncomingPath()
    
    // 启动工作流监听
    workflow.Start()
    
    // 模拟不同路径的激活
    go func() {
        time.Sleep(1 * time.Second)
        workflow.ActivatePath(path1)
        fmt.Println("路径1被激活")
        
        time.Sleep(500 * time.Millisecond)
        workflow.ActivatePath(path2)
        fmt.Println("路径2被激活")
        
        time.Sleep(200 * time.Millisecond)
        workflow.ActivatePath(path1) // 路径1再次激活
        fmt.Println("路径1再次被激活")
        
        time.Sleep(300 * time.Millisecond)
        workflow.ActivatePath(path3)
        fmt.Println("路径3被激活")
        
        time.Sleep(2 * time.Second)
        workflow.Stop()
    }()
    
    // 等待工作流完成
    workflow.Wait()
}
```

## 数据流模式

### 任务数据模式

定义任务如何接收和传递数据的模式。

```go
package workflow

// 定义带数据的任务接口
type DataTask interface {
    Execute(data interface{}) (interface{}, error)
}

// 简单数据任务实现
type SimpleDataTask struct {
    name     string
    function func(interface{}) (interface{}, error)
}

func NewSimpleDataTask(name string, function func(interface{}) (interface{}, error)) *SimpleDataTask {
    return &SimpleDataTask{
        name:     name,
        function: function,
    }
}

func (t *SimpleDataTask) Execute(data interface{}) (interface{}, error) {
    return t.function(data)
}

// 数据流工作流
type DataFlowWorkflow struct {
    tasks []DataTask
}

// 创建数据流工作流
func NewDataFlowWorkflow() *DataFlowWorkflow {
    return &DataFlowWorkflow{
        tasks: make([]DataTask, 0),
    }
}

// 添加任务到工作流
func (w *DataFlowWorkflow) AddTask(task DataTask) {
    w.tasks = append(w.tasks, task)
}

// 执行工作流
func (w *DataFlowWorkflow) Execute(initialData interface{}) (interface{}, error) {
    data := initialData
    
    for _, task := range w.tasks {
        result, err := task.Execute(data)
        if err != nil {
            return nil, err
        }
        data = result
    }
    
    return data, nil
}
```

使用示例：

```go
func main() {
    workflow := NewDataFlowWorkflow()
    
    // 添加处理数据的任务
    workflow.AddTask(NewSimpleDataTask("解析数据", func(data interface{}) (interface{}, error) {
        inputStr, ok := data.(string)
        if !ok {
            return nil, fmt.Errorf("输入数据类型错误")
        }
        
        fmt.Println("解析数据:", inputStr)
        return inputStr + " - 已解析", nil
    }))
    
    workflow.AddTask(NewSimpleDataTask("转换数据", func(data interface{}) (interface{}, error) {
        inputStr, ok := data.(string)
        if !ok {
            return nil, fmt.Errorf("输入数据类型错误")
        }
        
        fmt.Println("转换数据:", inputStr)
        return strings.ToUpper(inputStr), nil
    }))
    
    workflow.AddTask(NewSimpleDataTask("验证数据", func(data interface{}) (interface{}, error) {
        inputStr, ok := data.(string)
        if !ok {
            return nil, fmt.Errorf("输入数据类型错误")
        }
        
        fmt.Println("验证数据:", inputStr)
        if len(inputStr) > 10 {
            return map[string]interface{}{
                "status": "valid",
                "data":   inputStr,
            }, nil
        } else {
            return map[string]interface{}{
                "status": "invalid",
                "data":   inputStr,
                "reason": "数据太短",
            }, nil
        }
    }))
    
    // 执行工作流
    initialData := "原始数据"
    result, err := workflow.Execute(initialData)
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    } else {
        fmt.Printf("工作流执行结果: %v\n", result)
    }
}
```

### 管道数据模式

使用Go通道在各任务间传递数据。

```go
package workflow

// 管道阶段接口
type PipelineStage interface {
    Process(in <-chan interface{}, out chan<- interface{})
}

// 简单管道阶段实现
type SimplePipelineStage struct {
    name     string
    function func(interface{}) interface{}
}

func NewSimplePipelineStage(name string, function func(interface{}) interface{}) *SimplePipelineStage {
    return &SimplePipelineStage{
        name:     name,
        function: function,
    }
}

func (s *SimplePipelineStage) Process(in <-chan interface{}, out chan<- interface{}) {
    for data := range in {
        result := s.function(data)
        out <- result
    }
    close(out)
}

// 管道工作流
type PipelineWorkflow struct {
    stages []PipelineStage
}

// 创建管道工作流
func NewPipelineWorkflow() *PipelineWorkflow {
    return &PipelineWorkflow{
        stages: make([]PipelineStage, 0),
    }
}

// 添加阶段到管道
func (w *PipelineWorkflow) AddStage(stage PipelineStage) {
    w.stages = append(w.stages, stage)
}

// 执行工作流
func (w *PipelineWorkflow) Execute(inputData []interface{}) []interface{} {
    if len(w.stages) == 0 {
        return inputData
    }
    
    // 创建各阶段之间的通道
    channels := make([]chan interface{}, len(w.stages)+1)
    for i := range channels {
        channels[i] = make(chan interface{}, 10)
    }
    
    // 启动各阶段的处理
    var wg sync.WaitGroup
    for i, stage := range w.stages {
        wg.Add(1)
        go func(i int, s PipelineStage) {
            defer wg.Done()
            s.Process(channels[i], channels[i+1])
        }(i, stage)
    }
    
    // 输入数据
    go func() {
        for _, data := range inputData {
            channels[0] <- data
        }
        close(channels[0])
    }()
    
    // 收集结果
    var results []interface{}
    resultChan := channels[len(channels)-1]
    for result := range resultChan {
        results = append(results, result)
    }
    
    // 等待所有阶段完成
    wg.Wait()
    
    return results
}
```

使用示例：

```go
func main() {
    pipeline := NewPipelineWorkflow()
    
    // 添加处理阶段
    pipeline.AddStage(NewSimplePipelineStage("解析", func(data interface{}) interface{} {
        str, ok := data.(string)
        if !ok {
            return nil
        }
        fmt.Println("解析:", str)
        return str + " - 已解析"
    }))
    
    pipeline.AddStage(NewSimplePipelineStage("转换", func(data interface{}) interface{} {
        str, ok := data.(string)
        if !ok {
            return nil
        }
        fmt.Println("转换:", str)
        return strings.ToUpper(str)
    }))
    
    pipeline.AddStage(NewSimplePipelineStage("过滤", func(data interface{}) interface{} {
        str, ok := data.(string)
        if !ok {
            return nil
        }
        fmt.Println("过滤:", str)
        if strings.Contains(str, "IMPORTANT") {
            return str
        }
        return nil // 过滤掉非重要数据
    }))

    // 准备输入数据
    inputData := []interface{}{
        "普通消息",
        "IMPORTANT: 系统警告",
        "日常日志",
        "IMPORTANT: 安全警报",
    }
    
    // 执行管道工作流
    results := pipeline.Execute(inputData)
    
    // 显示结果
    fmt.Println("过滤后的重要消息:")
    for _, result := range results {
        if result != nil {
            fmt.Println(result)
        }
    }
}
```

### 共享状态模式

允许工作流中的不同任务访问共享状态。

```go
package workflow

import (
    "sync"
)

// 工作流共享上下文
type WorkflowContext struct {
    mu    sync.RWMutex
    state map[string]interface{}
}

// 创建新的工作流上下文
func NewWorkflowContext() *WorkflowContext {
    return &WorkflowContext{
        state: make(map[string]interface{}),
    }
}

// 设置状态
func (c *WorkflowContext) SetState(key string, value interface{}) {
    c.mu.Lock()
    defer c.mu.Unlock()
    c.state[key] = value
}

// 获取状态
func (c *WorkflowContext) GetState(key string) (interface{}, bool) {
    c.mu.RLock()
    defer c.mu.RUnlock()
    val, exists := c.state[key]
    return val, exists
}

// 删除状态
func (c *WorkflowContext) DeleteState(key string) {
    c.mu.Lock()
    defer c.mu.Unlock()
    delete(c.state, key)
}

// 获取所有状态的快照
func (c *WorkflowContext) GetAllState() map[string]interface{} {
    c.mu.RLock()
    defer c.mu.RUnlock()
    
    snapshot := make(map[string]interface{})
    for k, v := range c.state {
        snapshot[k] = v
    }
    
    return snapshot
}

// 上下文感知任务接口
type ContextAwareTask interface {
    Execute(ctx *WorkflowContext) error
}

// 简单上下文感知任务
type SimpleContextAwareTask struct {
    name     string
    function func(*WorkflowContext) error
}

func NewSimpleContextAwareTask(name string, function func(*WorkflowContext) error) *SimpleContextAwareTask {
    return &SimpleContextAwareTask{
        name:     name,
        function: function,
    }
}

func (t *SimpleContextAwareTask) Execute(ctx *WorkflowContext) error {
    return t.function(ctx)
}

// 共享状态工作流
type SharedStateWorkflow struct {
    tasks   []ContextAwareTask
    context *WorkflowContext
}

// 创建共享状态工作流
func NewSharedStateWorkflow() *SharedStateWorkflow {
    return &SharedStateWorkflow{
        tasks:   make([]ContextAwareTask, 0),
        context: NewWorkflowContext(),
    }
}

// 添加任务
func (w *SharedStateWorkflow) AddTask(task ContextAwareTask) {
    w.tasks = append(w.tasks, task)
}

// 获取工作流上下文
func (w *SharedStateWorkflow) Context() *WorkflowContext {
    return w.context
}

// 执行工作流
func (w *SharedStateWorkflow) Execute() error {
    for _, task := range w.tasks {
        if err := task.Execute(w.context); err != nil {
            return err
        }
    }
    return nil
}
```

使用示例：

```go
func main() {
    workflow := NewSharedStateWorkflow()
    
    // 添加初始化任务
    workflow.AddTask(NewSimpleContextAwareTask("初始化", func(ctx *WorkflowContext) error {
        fmt.Println("初始化共享状态")
        ctx.SetState("count", 0)
        ctx.SetState("items", []string{})
        return nil
    }))
    
    // 添加处理任务
    workflow.AddTask(NewSimpleContextAwareTask("处理A", func(ctx *WorkflowContext) error {
        count, _ := ctx.GetState("count")
        countVal := count.(int)
        
        fmt.Printf("处理A: 当前计数 = %d\n", countVal)
        
        // 更新计数
        ctx.SetState("count", countVal+1)
        
        // 添加项目
        items, _ := ctx.GetState("items")
        itemsVal := items.([]string)
        itemsVal = append(itemsVal, "Item A")
        ctx.SetState("items", itemsVal)
        
        return nil
    }))
    
    workflow.AddTask(NewSimpleContextAwareTask("处理B", func(ctx *WorkflowContext) error {
        count, _ := ctx.GetState("count")
        countVal := count.(int)
        
        fmt.Printf("处理B: 当前计数 = %d\n", countVal)
        
        // 更新计数
        ctx.SetState("count", countVal+2)
        
        // 添加项目
        items, _ := ctx.GetState("items")
        itemsVal := items.([]string)
        itemsVal = append(itemsVal, "Item B1", "Item B2")
        ctx.SetState("items", itemsVal)
        
        // 添加新状态
        ctx.SetState("process_b_completed", true)
        
        return nil
    }))
    
    // 添加总结任务
    workflow.AddTask(NewSimpleContextAwareTask("总结", func(ctx *WorkflowContext) error {
        fmt.Println("工作流总结:")
        
        count, _ := ctx.GetState("count")
        fmt.Printf("- 最终计数: %d\n", count)
        
        items, _ := ctx.GetState("items")
        itemsVal := items.([]string)
        fmt.Printf("- 处理的项目数: %d\n", len(itemsVal))
        
        fmt.Println("- 所有项目:")
        for i, item := range itemsVal {
            fmt.Printf("  %d. %s\n", i+1, item)
        }
        
        return nil
    }))
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    }
}
```

## 资源模式

### 资源分配模式

管理有限资源的分配和释放。

```go
package workflow

import (
    "fmt"
    "sync"
    "time"
)

// 资源接口
type Resource interface {
    ID() string
    Use() error
    Release() error
}

// 简单资源实现
type SimpleResource struct {
    id       string
    inUse    bool
    mu       sync.Mutex
    useCount int
}

func NewSimpleResource(id string) *SimpleResource {
    return &SimpleResource{
        id:       id,
        inUse:    false,
        useCount: 0,
    }
}

func (r *SimpleResource) ID() string {
    return r.id
}

func (r *SimpleResource) Use() error {
    r.mu.Lock()
    defer r.mu.Unlock()
    
    if r.inUse {
        return fmt.Errorf("资源 %s 已经在使用中", r.id)
    }
    
    r.inUse = true
    r.useCount++
    return nil
}

func (r *SimpleResource) Release() error {
    r.mu.Lock()
    defer r.mu.Unlock()
    
    if !r.inUse {
        return fmt.Errorf("资源 %s 当前没有被使用", r.id)
    }
    
    r.inUse = false
    return nil
}

func (r *SimpleResource) UseCount() int {
    r.mu.Lock()
    defer r.mu.Unlock()
    return r.useCount
}

// 资源分配器
type ResourceAllocator struct {
    resources map[string]Resource
    mu        sync.Mutex
}

// 创建资源分配器
func NewResourceAllocator() *ResourceAllocator {
    return &ResourceAllocator{
        resources: make(map[string]Resource),
    }
}

// 注册资源
func (a *ResourceAllocator) RegisterResource(resource Resource) {
    a.mu.Lock()
    defer a.mu.Unlock()
    a.resources[resource.ID()] = resource
}

// 分配资源
func (a *ResourceAllocator) AllocateResource(id string) (Resource, error) {
    a.mu.Lock()
    defer a.mu.Unlock()
    
    resource, exists := a.resources[id]
    if !exists {
        return nil, fmt.Errorf("资源 %s 不存在", id)
    }
    
    if err := resource.Use(); err != nil {
        return nil, err
    }
    
    return resource, nil
}

// 释放资源
func (a *ResourceAllocator) ReleaseResource(id string) error {
    a.mu.Lock()
    defer a.mu.Unlock()
    
    resource, exists := a.resources[id]
    if !exists {
        return fmt.Errorf("资源 %s 不存在", id)
    }
    
    return resource.Release()
}

// 使用资源的任务
type ResourceTask struct {
    name          string
    resourceID    string
    allocator     *ResourceAllocator
    processFunc   func(Resource) error
}

// 创建使用资源的任务
func NewResourceTask(name string, resourceID string, allocator *ResourceAllocator, 
    processFunc func(Resource) error) *ResourceTask {
    return &ResourceTask{
        name:        name,
        resourceID:  resourceID,
        allocator:   allocator,
        processFunc: processFunc,
    }
}

// 执行任务
func (t *ResourceTask) Execute() error {
    // 分配资源
    resource, err := t.allocator.AllocateResource(t.resourceID)
    if err != nil {
        return fmt.Errorf("任务 %s 无法分配资源 %s: %v", t.name, t.resourceID, err)
    }
    
    // 确保资源最终被释放
    defer func() {
        if err := t.allocator.ReleaseResource(t.resourceID); err != nil {
            fmt.Printf("警告: 任务 %s 无法释放资源 %s: %v\n", t.name, t.resourceID, err)
        }
    }()
    
    // 使用资源执行处理
    return t.processFunc(resource)
}
```

使用示例：

```go
func main() {
    // 创建资源分配器
    allocator := NewResourceAllocator()
    
    // 注册资源
    allocator.RegisterResource(NewSimpleResource("打印机"))
    allocator.RegisterResource(NewSimpleResource("数据库连接"))
    allocator.RegisterResource(NewSimpleResource("共享内存"))
    
    // 创建任务
    task1 := NewResourceTask("打印文档", "打印机", allocator, func(r Resource) error {
        fmt.Printf("任务1正在使用%s\n", r.ID())
        time.Sleep(2 * time.Second)
        fmt.Printf("任务1完成使用%s\n", r.ID())
        return nil
    })
    
    task2 := NewResourceTask("数据库查询", "数据库连接", allocator, func(r Resource) error {
        fmt.Printf("任务2正在使用%s\n", r.ID())
        time.Sleep(1 * time.Second)
        fmt.Printf("任务2完成使用%s\n", r.ID())
        return nil
    })
    
    task3 := NewResourceTask("打印报告", "打印机", allocator, func(r Resource) error {
        fmt.Printf("任务3正在使用%s\n", r.ID())
        time.Sleep(3 * time.Second)
        fmt.Printf("任务3完成使用%s\n", r.ID())
        return nil
    })
    
    // 创建顺序工作流
    workflow := NewSequentialWorkflow()
    workflow.AddTask(task1)
    workflow.AddTask(task2)
    workflow.AddTask(task3)
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    }
    
    // 检查资源使用情况
    res := allocator.resources["打印机"].(*SimpleResource)
    fmt.Printf("打印机使用次数: %d\n", res.UseCount())
}
```

### 资源池模式

管理一个同质化资源池，允许多个客户端并发使用有限的资源。

```go
package workflow

import (
    "errors"
    "fmt"
    "sync"
    "time"
)

// 资源池项
type PoolItem struct {
    id        int
    available bool
}

// 资源池
type ResourcePool struct {
    items     []*PoolItem
    mutex     sync.Mutex
    semaphore chan struct{}
}

// 创建新的资源池
func NewResourcePool(size int) *ResourcePool {
    items := make([]*PoolItem, size)
    for i := 0; i < size; i++ {
        items[i] = &PoolItem{
            id:        i,
            available: true,
        }
    }
    
    return &ResourcePool{
        items:     items,
        semaphore: make(chan struct{}, size),
    }
}

// 初始化资源池信号量
func (p *ResourcePool) Initialize() {
    for i := 0; i < len(p.items); i++ {
        p.semaphore <- struct{}{}
    }
}

// 获取资源
func (p *ResourcePool) Acquire() (*PoolItem, error) {
    // 尝试从信号量获取令牌
    select {
    case <-p.semaphore:
        // 获取到令牌，找一个可用资源
        p.mutex.Lock()
        defer p.mutex.Unlock()
        
        for _, item := range p.items {
            if item.available {
                item.available = false
                return item, nil
            }
        }
        
        // 理论上不应该到这里，因为信号量控制了可用资源数量
        return nil, errors.New("无可用资源")
    case <-time.After(5 * time.Second):
        return nil, errors.New("获取资源超时")
    }
}

// 释放资源
func (p *ResourcePool) Release(item *PoolItem) {
    p.mutex.Lock()
    defer p.mutex.Unlock()
    
    // 确保资源属于本池
    for _, poolItem := range p.items {
        if poolItem.id == item.id {
            if !poolItem.available {
                poolItem.available = true
                // 释放信号量令牌
                p.semaphore <- struct{}{}
            }
            return
        }
    }
}

// 使用资源池的任务
type PooledResourceTask struct {
    name      string
    pool      *ResourcePool
    processor func(*PoolItem) error
}

// 创建使用资源池的任务
func NewPooledResourceTask(name string, pool *ResourcePool, processor func(*PoolItem) error) *PooledResourceTask {
    return &PooledResourceTask{
        name:      name,
        pool:      pool,
        processor: processor,
    }
}

// 执行任务
func (t *PooledResourceTask) Execute() error {
    // 获取资源
    item, err := t.pool.Acquire()
    if err != nil {
        return fmt.Errorf("任务 %s 无法获取资源: %v", t.name, err)
    }
    
    // 确保资源最终被释放
    defer t.pool.Release(item)
    
    // 使用资源执行处理
    return t.processor(item)
}
```

使用示例：

```go
func main() {
    // 创建资源池
    pool := NewResourcePool(3) // 3个资源的池
    pool.Initialize()
    
    // 创建并行工作流
    workflow := NewParallelWorkflow()
    
    // 添加多个使用资源池的任务
    for i := 1; i <= 5; i++ {
        taskID := i
        task := NewPooledResourceTask(
            fmt.Sprintf("任务%d", taskID),
            pool,
            func(item *PoolItem) error {
                fmt.Printf("任务%d获取到资源%d\n", taskID, item.id)
                // 模拟工作
                time.Sleep(time.Duration(1+taskID%3) * time.Second)
                fmt.Printf("任务%d完成使用资源%d\n", taskID, item.id)
                return nil
            },
        )
        workflow.AddTask(task)
    }
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    } else {
        fmt.Println("所有任务都已完成")
    }
}
```

### 资源限制模式

限制工作流中可以并发执行的任务数量。

```go
package workflow

import (
    "sync"
)

// 带限制的并行工作流
type LimitedParallelWorkflow struct {
    tasks       []Task
    concurrency int
}

// 创建新的带限制的并行工作流
func NewLimitedParallelWorkflow(concurrency int) *LimitedParallelWorkflow {
    if concurrency <= 0 {
        concurrency = 1
    }
    
    return &LimitedParallelWorkflow{
        tasks:       make([]Task, 0),
        concurrency: concurrency,
    }
}

// 添加任务到工作流
func (w *LimitedParallelWorkflow) AddTask(task Task) {
    w.tasks = append(w.tasks, task)
}

// 执行工作流
func (w *LimitedParallelWorkflow) Execute() error {
    var wg sync.WaitGroup
    errChan := make(chan error, len(w.tasks))
    semaphore := make(chan struct{}, w.concurrency)
    
    for _, task := range w.tasks {
        // 获取信号量
        semaphore <- struct{}{}
        
        wg.Add(1)
        go func(t Task) {
            defer func() {
                // 释放信号量
                <-semaphore
                wg.Done()
            }()
            
            if err := t.Execute(); err != nil {
                errChan <- err
            }
        }(task)
    }
    
    // 等待所有任务完成
    wg.Wait()
    close(errChan)
    
    // 检查是否有错误
    for err := range errChan {
        if err != nil {
            return err // 返回第一个遇到的错误
        }
    }
    
    return nil
}
```

使用示例：

```go
func main() {
    // 创建限制最多2个并发的工作流
    workflow := NewLimitedParallelWorkflow(2)
    
    // 添加5个任务
    for i := 1; i <= 5; i++ {
        id := i
        task := NewSimpleTask(fmt.Sprintf("任务%d", id), func() error {
            fmt.Printf("开始执行任务%d\n", id)
            time.Sleep(time.Duration(2) * time.Second)
            fmt.Printf("完成执行任务%d\n", id)
            return nil
        })
        workflow.AddTask(task)
    }
    
    // 记录开始时间
    startTime := time.Now()
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    }
    
    // 计算总执行时间
    elapsedTime := time.Since(startTime)
    fmt.Printf("工作流执行完成，耗时: %v\n", elapsedTime)
}
```

## 异常处理模式

### 错误传播模式

在工作流中处理和传播错误。

```go
package workflow

import (
    "fmt"
)

// 错误处理函数类型
type ErrorHandler func(error) error

// 带错误处理的任务
type ErrorHandlingTask struct {
    task         Task
    errorHandler ErrorHandler
}

// 创建带错误处理的任务
func NewErrorHandlingTask(task Task, handler ErrorHandler) *ErrorHandlingTask {
    return &ErrorHandlingTask{
        task:         task,
        errorHandler: handler,
    }
}

// 执行任务
func (t *ErrorHandlingTask) Execute() error {
    err := t.task.Execute()
    if err != nil && t.errorHandler != nil {
        return t.errorHandler(err)
    }
    return err
}

// 带错误处理的工作流
type ErrorHandlingWorkflow struct {
    tasks         []Task
    errorHandler  ErrorHandler
    continueOnErr bool
}

// 创建带错误处理的工作流
func NewErrorHandlingWorkflow(errorHandler ErrorHandler, continueOnErr bool) *ErrorHandlingWorkflow {
    return &ErrorHandlingWorkflow{
        tasks:         make([]Task, 0),
        errorHandler:  errorHandler,
        continueOnErr: continueOnErr,
    }
}

// 添加任务
func (w *ErrorHandlingWorkflow) AddTask(task Task) {
    w.tasks = append(w.tasks, task)
}

// 执行工作流
func (w *ErrorHandlingWorkflow) Execute() error {
    var lastErr error
    
    for _, task := range w.tasks {
        err := task.Execute()
        if err != nil {
            if w.errorHandler != nil {
                // 使用错误处理器处理错误
                lastErr = w.errorHandler(err)
            } else {
                lastErr = err
            }
            
            // 如果不继续执行，则立即返回
            if !w.continueOnErr {
                return lastErr
            }
        }
    }
    
    return lastErr
}
```

使用示例：

```go
func main() {
    // 创建全局错误处理器
    globalErrorHandler := func(err error) error {
        fmt.Printf("全局处理错误: %v\n", err)
        // 决定是转换错误还是传递原始错误
        return fmt.Errorf("已处理的错误: %w", err)
    }
    
    // 创建允许错误时继续执行的工作流
    workflow := NewErrorHandlingWorkflow(globalErrorHandler, true)
    
    // 添加任务
    workflow.AddTask(NewSimpleTask("任务1", func() error {
        fmt.Println("执行任务1")
        return nil
    }))
    
    // 添加会失败的任务，带特定错误处理
    failingTask := NewSimpleTask("任务2", func() error {
        fmt.Println("执行任务2")
        return fmt.Errorf("任务2失败")
    })
    
    // 任务特定的错误处理
    specificErrorHandler := func(err error) error {
        fmt.Printf("特定处理任务2错误: %v\n", err)
        // 可以决定吞掉错误
        return nil
    }
    
    workflow.AddTask(NewErrorHandlingTask(failingTask, specificErrorHandler))
    
    // 添加正常任务
    workflow.AddTask(NewSimpleTask("任务3", func() error {
        fmt.Println("执行任务3")
        return nil
    }))
    
    // 添加另一个会失败的任务，使用全局错误处理
    workflow.AddTask(NewSimpleTask("任务4", func() error {
        fmt.Println("执行任务4")
        return fmt.Errorf("任务4失败")
    }))
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行完成，最终错误: %v\n", err)
    } else {
        fmt.Println("工作流执行成功完成")
    }
}
```

### 超时控制模式

给任务执行设置时间限制。

```go
package workflow

import (
    "context"
    "fmt"
    "time"
)

// 带超时的任务
type TimeoutTask struct {
    task    Task
    timeout time.Duration
}

// 创建带超时的任务
func NewTimeoutTask(task Task, timeout time.Duration) *TimeoutTask {
    return &TimeoutTask{
        task:    task,
        timeout: timeout,
    }
}

// 执行带超时控制的任务
func (t *TimeoutTask) Execute() error {
    // 创建带取消的上下文
    ctx, cancel := context.WithTimeout(context.Background(), t.timeout)
    defer cancel()
    
    // 创建错误通道
    done := make(chan error, 1)
    
    // 在goroutine中执行实际任务
    go func() {
        done <- t.task.Execute()
    }()
    
    // 等待任务完成或超时
    select {
    case err := <-done:
        return err
    case <-ctx.Done():
        return fmt.Errorf("任务执行超时: %v", ctx.Err())
    }
}

// 带超时控制的工作流
type TimeoutWorkflow struct {
    tasks   []Task
    timeout time.Duration
}

// 创建带超时控制的工作流
func NewTimeoutWorkflow(timeout time.Duration) *TimeoutWorkflow {
    return &TimeoutWorkflow{
        tasks:   make([]Task, 0),
        timeout: timeout,
    }
}

// 添加任务
func (w *TimeoutWorkflow) AddTask(task Task) {
    w.tasks = append(w.tasks, task)
}

// 执行工作流
func (w *TimeoutWorkflow) Execute() error {
    // 创建带取消的上下文
    ctx, cancel := context.WithTimeout(context.Background(), w.timeout)
    defer cancel()
    
    // 创建错误通道
    done := make(chan error, 1)
    
    // 在goroutine中执行工作流
    go func() {
        var err error
        for _, task := range w.tasks {
            if err = task.Execute(); err != nil {
                break
            }
        }
        done <- err
    }()
    
    // 等待工作流完成或超时
    select {
    case err := <-done:
        return err
    case <-ctx.Done():
        return fmt.Errorf("工作流执行超时: %v", ctx.Err())
    }
}
```

使用示例：

```go
func main() {
    // 创建带超时的工作流
    workflow := NewTimeoutWorkflow(5 * time.Second)
    
    // 添加几个任务
    workflow.AddTask(NewSimpleTask("任务1", func() error {
        fmt.Println("执行任务1")
        time.Sleep(1 * time.Second)
        return nil
    }))
    
    // 添加一个带自己超时的任务
    longTask := NewSimpleTask("耗时任务", func() error {
        fmt.Println("开始执行耗时任务")
        time.Sleep(3 * time.Second)
        fmt.Println("完成执行耗时任务")
        return nil
    })
    timeoutTask := NewTimeoutTask(longTask, 2*time.Second)
    workflow.AddTask(timeoutTask)
    
    // 添加可能不会执行的任务
    workflow.AddTask(NewSimpleTask("任务3", func() error {
        fmt.Println("执行任务3")
        return nil
    }))
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    } else {
        fmt.Println("工作流执行成功完成")
    }
}
```

### 重试模式

当任务失败时自动重试。

```go
package workflow

import (
    "fmt"
    "time"
)

// 重试策略接口
type RetryStrategy interface {
    // 决定是否应该重试
    ShouldRetry(attempt int, err error) bool
    // 获取下次重试前的等待时间
    NextDelay(attempt int) time.Duration
}

// 简单重试策略实现
type SimpleRetryStrategy struct {
    maxAttempts int
    baseDelay   time.Duration
    maxDelay    time.Duration
}

// 创建简单重试策略
func NewSimpleRetryStrategy(maxAttempts int, baseDelay, maxDelay time.Duration) *SimpleRetryStrategy {
    return &SimpleRetryStrategy{
        maxAttempts: maxAttempts,
        baseDelay:   baseDelay,
        maxDelay:    maxDelay,
    }
}

// 决定是否应该重试
func (s *SimpleRetryStrategy) ShouldRetry(attempt int, err error) bool {
    return attempt < s.maxAttempts
}

// 获取下次重试前的等待时间（指数退避）
func (s *SimpleRetryStrategy) NextDelay(attempt int) time.Duration {
    // 计算指数退避延迟
    delay := s.baseDelay * time.Duration(1<<uint(attempt))
    
    // 确保不超过最大延迟
    if delay > s.maxDelay {
        delay = s.maxDelay
    }
    
    return delay
}

// 带重试的任务
type RetryTask struct {
    task           Task
    retryStrategy  RetryStrategy
}

// 创建带重试的任务
func NewRetryTask(task Task, strategy RetryStrategy) *RetryTask {
    return &RetryTask{
        task:          task,
        retryStrategy: strategy,
    }
}

// 执行带重试的任务
func (t *RetryTask) Execute() error {
    var lastErr error
    
    for attempt := 0; ; attempt++ {
        // 执行任务
        err := t.task.Execute()
        if err == nil {
            return nil // 成功执行
        }
        
        lastErr = err
        
        // 检查是否应该重试
        if !t.retryStrategy.ShouldRetry(attempt, err) {
            break
        }
        
        // 获取重试延迟时间
        delay := t.retryStrategy.NextDelay(attempt)
        fmt.Printf("任务执行失败，将在 %v 后重试（尝试 %d）: %v\n", delay, attempt+1, err)
        
        // 等待重试
        time.Sleep(delay)
    }
    
    return fmt.Errorf("达到最大重试次数，最后错误: %w", lastErr)
}
```

使用示例：

```go
func main() {
    // 创建重试策略：最多尝试3次，初始延迟100毫秒，最大延迟1秒
    retryStrategy := NewSimpleRetryStrategy(3, 100*time.Millisecond, 1*time.Second)
    
    // 创建一个会失败几次的任务
    failingTask := NewSimpleTask("不稳定任务", func() error {
        // 生成随机数来模拟偶尔失败
        if time.Now().UnixNano()%3 != 0 {
            return fmt.Errorf("任务临时失败")
        }
        fmt.Println("任务成功执行")
        return nil
    })
    
    // 创建带重试的任务
    retryTask := NewRetryTask(failingTask, retryStrategy)
    
    // 创建工作流
    workflow := NewSequentialWorkflow()
    workflow.AddTask(NewSimpleTask("预处理", func() error {
        fmt.Println("执行预处理")
        return nil
    }))
    workflow.AddTask(retryTask)
    workflow.AddTask(NewSimpleTask("后处理", func() error {
        fmt.Println("执行后处理")
        return nil
    }))
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    } else {
        fmt.Println("工作流执行成功完成")
    }
}
```

### 回退模式

当主要任务失败时执行备选方案。

```go
package workflow

// 回退任务
type FallbackTask struct {
    primaryTask   Task
    fallbackTask  Task
}

// 创建回退任务
func NewFallbackTask(primaryTask, fallbackTask Task) *FallbackTask {
    return &FallbackTask{
        primaryTask:  primaryTask,
        fallbackTask: fallbackTask,
    }
}

// 执行任务
func (t *FallbackTask) Execute() error {
    // 尝试执行主要任务
    err := t.primaryTask.Execute()
    if err == nil {
        return nil // 主要任务成功
    }
    
    // 主要任务失败，尝试回退任务
    fmt.Printf("主要任务失败: %v，执行回退任务\n", err)
    return t.fallbackTask.Execute()
}

// 带回退的工作流
type FallbackWorkflow struct {
    primaryWorkflow   Task
    fallbackWorkflow  Task
}

// 创建带回退的工作流
func NewFallbackWorkflow(primaryWorkflow, fallbackWorkflow Task) *FallbackWorkflow {
    return &FallbackWorkflow{
        primaryWorkflow:  primaryWorkflow,
        fallbackWorkflow: fallbackWorkflow,
    }
}

// 执行工作流
func (w *FallbackWorkflow) Execute() error {
    // 尝试执行主要工作流
    err := w.primaryWorkflow.Execute()
    if err == nil {
        return nil // 主要工作流成功
    }
    
    // 主要工作流失败，尝试回退工作流
    fmt.Printf("主要工作流失败: %v，执行回退工作流\n", err)
    return w.fallbackWorkflow.Execute()
}
```

使用示例：

```go
func main() {
    // 创建一个可能失败的主要任务
    primaryTask := NewSimpleTask("主要数据库操作", func() error {
        fmt.Println("尝试连接主数据库...")
        // 模拟失败
        return fmt.Errorf("主数据库连接失败")
    })
    
    // 创建回退任务
    fallbackTask := NewSimpleTask("备用数据库操作", func() error {
        fmt.Println("连接备用数据库...")
        // 模拟成功
        fmt.Println("备用数据库操作成功")
        return nil
    })
    
    // 创建带回退的任务
    task := NewFallbackTask(primaryTask, fallbackTask)
    
    // 创建工作流
    workflow := NewSequentialWorkflow()
    workflow.AddTask(NewSimpleTask("准备", func() error {
        fmt.Println("准备数据...")
        return nil
    }))
    workflow.AddTask(task)
    workflow.AddTask(NewSimpleTask("完成", func() error {
        fmt.Println("操作

<think>我需要继续完成上一个响应中的异常处理模式部分，并且完成模式之间的关系分析部分，包括相容性、等价性和嵌入性的分析。

从上次的响应中，我正在描述异常处理模式中的回退模式的使用示例，但是最后一部分被截断了。我将继续完成这部分，然后进入模式之间的关系分析。</think># Go语言实现工作流模式的形式化分析与代码实现（续）

## 异常处理模式（续）

### 回退模式（续）

使用示例（续）：

```go
func main() {
    // 前面的代码...
    
    workflow.AddTask(NewSimpleTask("完成", func() error {
        fmt.Println("操作完成")
        return nil
    }))
    
    // 执行工作流
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    } else {
        fmt.Println("工作流执行成功完成")
    }
    
    // 创建一个更复杂的场景：带回退的工作流
    
    // 定义主工作流
    primaryWorkflow := NewSequentialWorkflow()
    primaryWorkflow.AddTask(NewSimpleTask("主流程步骤1", func() error {
        fmt.Println("执行主流程步骤1")
        return nil
    }))
    primaryWorkflow.AddTask(NewSimpleTask("主流程步骤2", func() error {
        fmt.Println("执行主流程步骤2")
        return fmt.Errorf("主流程在步骤2失败")
    }))
    
    // 定义回退工作流
    fallbackWorkflow := NewSequentialWorkflow()
    fallbackWorkflow.AddTask(NewSimpleTask("备用流程步骤1", func() error {
        fmt.Println("执行备用流程步骤1")
        return nil
    }))
    fallbackWorkflow.AddTask(NewSimpleTask("备用流程步骤2", func() error {
        fmt.Println("执行备用流程步骤2")
        return nil
    }))
    
    // 创建带回退的工作流
    complexWorkflow := NewFallbackWorkflow(primaryWorkflow, fallbackWorkflow)
    
    // 执行复杂工作流
    fmt.Println("\n执行带回退的复杂工作流:")
    err = complexWorkflow.Execute()
    if err != nil {
        fmt.Printf("复杂工作流执行失败: %v\n", err)
    } else {
        fmt.Println("复杂工作流执行成功完成")
    }
}
```

## 模式之间的关系

### 相容性分析

相容性指的是不同工作流模式是否可以共存和组合使用，而不会引起冲突或者破坏各自的语义。

```go
// 模式相容性分析
/*
1. 控制流模式的相容性:
   - 顺序执行模式与几乎所有其他模式都相容
   - 并行分支模式与同步模式高度相容，通常一起使用
   - 排他选择模式与简单合并模式相容，可以成对使用
   - 多选择模式与结构化同步合并模式相容，可以成对使用
   - 多合并模式可以与任何能产生多个分支的模式一起使用

2. 数据流模式的相容性:
   - 任务数据模式与几乎所有其他模式都相容
   - 管道数据模式通常与顺序执行模式相容
   - 共享状态模式与并行控制流模式一起使用时需要特别注意并发安全

3. 资源模式的相容性:
   - 资源分配模式与几乎所有控制流模式都相容
   - 资源池模式特别适合与并行分支模式一起使用
   - 资源限制模式可以与任何可能导致过度并发的模式一起使用

4. 异常处理模式的相容性:
   - 错误传播模式可以与任何其他模式组合
   - 超时控制模式可以应用于任何可能耗时过长的模式
   - 重试模式通常与可能失败但可以重试的任务一起使用
   - 回退模式与几乎所有其他模式都相容
*/
```

下面是一个展示多种模式组合的复杂工作流示例：

```go
func main() {
    // 创建一个复合工作流，展示多种模式的相容性
    
    // 1. 创建共享上下文（共享状态模式）
    ctx := NewWorkflowContext()
    ctx.SetState("初始数据", "原始输入")
    
    // 2. 创建资源池（资源池模式）
    pool := NewResourcePool(3)
    pool.Initialize()
    
    // 3. 创建带重试策略的操作（重试模式）
    retryStrategy := NewSimpleRetryStrategy(3, 100*time.Millisecond, 1*time.Second)
    
    // 4. 创建带资源限制的并行工作流（并行分支模式 + 资源限制模式）
    parallelFlow := NewLimitedParallelWorkflow(2)
    
    // 5. 创建带超时的任务（超时控制模式）
    timeoutTask := NewTimeoutTask(
        NewSimpleContextAwareTask("访问外部服务", func(ctx *WorkflowContext) error {
            fmt.Println("尝试访问外部服务...")
            // 模拟长时间操作
            time.Sleep(1 * time.Second)
            ctx.SetState("外部数据", "已获取的数据")
            return nil
        }),
        2*time.Second,
    )
    
    // 6. 创建带回退的数据库操作（回退模式）
    dbOperation := NewFallbackTask(
        NewSimpleTask("主数据库操作", func() error {
            fmt.Println("尝试连接主数据库...")
            return fmt.Errorf("主数据库连接失败")
        }),
        NewSimpleTask("备用数据库操作", func() error {
            fmt.Println("连接备用数据库...")
            return nil
        }),
    )
    
    // 7. 将这些任务组合到工作流中
    workflow := NewSequentialWorkflow()
    
    // 第一步：初始化和准备
    workflow.AddTask(NewSimpleContextAwareTask("初始化", func(c *WorkflowContext) error {
        fmt.Println("初始化工作流...")
        data, _ := c.GetState("初始数据")
        fmt.Printf("使用初始数据: %v\n", data)
        return nil
    }))
    
    // 第二步：执行并行任务（带资源限制）
    parallelFlow.AddTask(NewPooledResourceTask("并行任务1", pool, func(item *PoolItem) error {
        fmt.Printf("执行并行任务1，使用资源%d\n", item.id)
        time.Sleep(500 * time.Millisecond)
        return nil
    }))
    
    parallelFlow.AddTask(NewPooledResourceTask("并行任务2", pool, func(item *PoolItem) error {
        fmt.Printf("执行并行任务2，使用资源%d\n", item.id)
        time.Sleep(700 * time.Millisecond)
        return nil
    }))
    
    parallelFlow.AddTask(NewPooledResourceTask("并行任务3", pool, func(item *PoolItem) error {
        fmt.Printf("执行并行任务3，使用资源%d\n", item.id)
        time.Sleep(600 * time.Millisecond)
        return nil
    }))
    
    workflow.AddTask(parallelFlow)
    
    // 第三步：带超时的外部服务访问
    workflow.AddTask(timeoutTask)
    
    // 第四步：条件分支处理（排他选择模式）
    choiceFlow := NewExclusiveChoiceWorkflow()
    choiceFlow.AddBranch(
        NewSimpleCondition(func() bool {
            // 检查共享上下文中的状态
            _, exists := ctx.GetState("外部数据")
            return exists
        }),
        NewSimpleContextAwareTask("处理外部数据", func(c *WorkflowContext) error {
            fmt.Println("处理外部数据...")
            data, _ := c.GetState("外部数据")
            fmt.Printf("外部数据: %v\n", data)
            return nil
        }),
    )
    choiceFlow.SetDefaultBranch(
        NewSimpleContextAwareTask("使用默认数据", func(c *WorkflowContext) error {
            fmt.Println("使用默认数据...")
            c.SetState("外部数据", "默认数据")
            return nil
        }),
    )
    
    workflow.AddTask(choiceFlow)
    
    // 第五步：带重试的数据库操作
    dbTask := NewRetryTask(dbOperation, retryStrategy)
    workflow.AddTask(dbTask)
    
    // 执行复合工作流
    fmt.Println("开始执行复合工作流...")
    err := workflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    } else {
        fmt.Println("工作流执行成功完成")
    }
}
```

### 等价性分析

等价性是指不同的工作流模式或模式组合在特定条件下能实现相同的功能。

```go
// 模式等价性分析
/*
1. 控制流模式等价性:
   - 单任务的顺序执行模式等价于该任务的直接执行
   - 包含单个并行分支的并行分支模式等价于顺序执行模式
   - 带有互斥条件的多选择模式等价于排他选择模式
   - 管理单一资源的资源池模式在某些场景下等价于资源分配模式

2. 数据流等价性:
   - 不传递数据的任务数据模式等价于基本的Task接口
   - 共享状态模式可以模拟任务数据模式，只需在上下文中存储和读取数据

3. 异常处理等价性:
   - 最大尝试次数为1的重试模式等价于没有重试的基本执行
   - 可以使用错误传播模式和条件判断来模拟回退模式
   - 资源限制为1的资源限制模式等价于顺序执行模式
*/
```

下面是一个展示模式等价性的示例：

```go
func main() {
    // 展示等价模式的例子
    
    fmt.Println("模式等价性示例:")
    
    // 示例1: 顺序执行与直接执行的等价性
    fmt.Println("\n1. 顺序执行模式与直接执行:")
    
    task := NewSimpleTask("简单任务", func() error {
        fmt.Println("执行简单任务")
        return nil
    })
    
    // 直接执行任务
    fmt.Println("直接执行:")
    task.Execute()
    
    // 使用顺序执行模式
    fmt.Println("通过顺序模式执行:")
    seqFlow := NewSequentialWorkflow()
    seqFlow.AddTask(task)
    seqFlow.Execute()
    
    // 示例2: 单并行与顺序执行的等价性
    fmt.Println("\n2. 单并行与顺序执行:")
    
    // 使用顺序执行
    fmt.Println("顺序执行:")
    seqFlow2 := NewSequentialWorkflow()
    seqFlow2.AddTask(NewSimpleTask("任务A", func() error {
        fmt.Println("顺序执行任务A")
        return nil
    }))
    seqFlow2.Execute()
    
    // 使用并行执行（但只有一个任务）
    fmt.Println("并行执行（单任务）:")
    parFlow := NewParallelWorkflow()
    parFlow.AddTask(NewSimpleTask("任务A", func() error {
        fmt.Println("并行执行任务A")
        return nil
    }))
    parFlow.Execute()
    
    // 示例3: 多选择与排他选择在某些条件下的等价性
    fmt.Println("\n3. 特定条件下多选择与排他选择:")
    
    value := 15
    
    // 使用排他选择
    fmt.Println("排他选择:")
    exclChoice := NewExclusiveChoiceWorkflow()
    exclChoice.AddBranch(
        NewSimpleCondition(func() bool { return value > 10 }),
        NewSimpleTask("条件满足", func() error {
            fmt.Println("排他选择: 值大于10")
            return nil
        }),
    )
    exclChoice.SetDefaultBranch(
        NewSimpleTask("条件不满足", func() error {
            fmt.Println("排他选择: 值不大于10")
            return nil
        }),
    )
    exclChoice.Execute()
    
    // 使用多选择（但条件互斥）
    fmt.Println("多选择（互斥条件）:")
    multiChoice := NewMultiChoiceWorkflow()
    multiChoice.AddBranch(
        NewSimpleCondition(func() bool { return value > 10 }),
        NewSimpleTask("条件1满足", func() error {
            fmt.Println("多选择: 值大于10")
            return nil
        }),
    )
    multiChoice.AddBranch(
        NewSimpleCondition(func() bool { return value <= 10 }),
        NewSimpleTask("条件2满足", func() error {
            fmt.Println("多选择: 值不大于10")
            return nil
        }),
    )
    multiChoice.Execute()
    
    // 示例4: 资源限制为1的并行等价于顺序执行
    fmt.Println("\n4. 资源限制为1的并行与顺序执行:")
    
    // 顺序执行
    fmt.Println("顺序执行:")
    seqFlow3 := NewSequentialWorkflow()
    seqFlow3.AddTask(NewSimpleTask("任务1", func() error {
        fmt.Println("顺序执行任务1")
        time.Sleep(100 * time.Millisecond)
        return nil
    }))
    seqFlow3.AddTask(NewSimpleTask("任务2", func() error {
        fmt.Println("顺序执行任务2")
        time.Sleep(100 * time.Millisecond)
        return nil
    }))
    seqFlow3.Execute()
    
    // 资源限制为1的并行执行
    fmt.Println("资源限制为1的并行执行:")
    limitedParFlow := NewLimitedParallelWorkflow(1)
    limitedParFlow.AddTask(NewSimpleTask("任务1", func() error {
        fmt.Println("限制并行执行任务1")
        time.Sleep(100 * time.Millisecond)
        return nil
    }))
    limitedParFlow.AddTask(NewSimpleTask("任务2", func() error {
        fmt.Println("限制并行执行任务2")
        time.Sleep(100 * time.Millisecond)
        return nil
    }))
    limitedParFlow.Execute()
}
```

### 嵌入性分析

嵌入性是指一个工作流模式能够包含或嵌套另一个工作流模式的能力。

```go
// 模式嵌入性分析
/*
1. 控制流嵌入性:
   - 顺序执行模式可以嵌入任何其他模式作为其中的一个任务
   - 并行分支模式可以嵌入任何其他模式作为并行分支
   - 排他选择和多选择模式可以在分支中嵌入任何其他模式
   - 同步模式和结构化同步合并模式需要特定的嵌入结构

2. 数据流嵌入性:
   - 任务数据模式可以嵌入到任何控制流模式中，作为数据处理方式
   - 管道数据模式通常作为独立的处理结构存在
   - 共享状态模式可以与任何其他模式结合使用

3. 资源模式嵌入性:
   - 资源分配和资源池模式可以嵌入到任何需要资源的工作流中
   - 资源限制模式通常应用于整个工作流或子工作流

4. 异常处理嵌入性:
   - 错误传播、重试和回退模式可以嵌入到任何其他模式中
   - 超时控制模式可以应用于任何可能耗时过长的模式或整个工作流
*/
```

下面是一个展示模式嵌入性的复杂示例：

```go
func main() {
    // 嵌入性演示：创建一个复杂的嵌套工作流
    
    fmt.Println("工作流模式嵌入性示例:")
    
    // 1. 最内层：带重试的资源操作
    retryStrategy := NewSimpleRetryStrategy(2, 100*time.Millisecond, 500*time.Millisecond)
    
    resourceTask := NewSimpleTask("资源操作", func() error {
        fmt.Println("执行资源操作...")
        // 模拟随机失败
        if rand.Intn(3) == 0 {
            return nil
        }
        return fmt.Errorf("资源操作临时失败")
    })
    
    // 包装为重试任务（嵌入重试模式）
    retriableTask := NewRetryTask(resourceTask, retryStrategy)
    
    // 2. 中间层：带超时的并行处理（嵌入超时控制和并行模式）
    parallelFlow := NewParallelWorkflow()
    
    // 添加重试任务作为并行分支之一
    parallelFlow.AddTask(retriableTask)
    
    // 添加另一个并行分支
    parallelFlow.AddTask(NewSimpleTask("并行操作", func() error {
        fmt.Println("执行并行操作...")
        time.Sleep(200 * time.Millisecond)
        return nil
    }))
    
    // 包装为超时任务（嵌入超时控制模式）
    timeoutParallel := NewTimeoutTask(parallelFlow, 1*time.Second)
    
    // 3. 外层：条件选择和顺序处理（嵌入条件选择和顺序模式）
    choiceWorkflow := NewExclusiveChoiceWorkflow()
    
    // 分支1：使用超时并行处理
    choiceWorkflow.AddBranch(
        NewSimpleCondition(func() bool { return rand.Intn(2) == 0 }),
        timeoutParallel,
    )
    
    // 分支2：使用顺序处理
    seqFlow := NewSequentialWorkflow()
    seqFlow.AddTask(NewSimpleTask("顺序任务1", func() error {
        fmt.Println("执行顺序任务1...")
        return nil
    }))
    seqFlow.AddTask(NewSimpleTask("顺序任务2", func() error {
        fmt.Println("执行顺序任务2...")
        return nil
    }))
    
    choiceWorkflow.AddBranch(
        NewSimpleCondition(func() bool { return true }),
        seqFlow,
    )
    
    // 4. 最外层：带共享状态的顺序工作流（嵌入共享状态和顺序模式）
    ctx := NewWorkflowContext()
    ctx.SetState("开始时间", time.Now())
    
    // 定义使用上下文的最终工作流
    finalWorkflow := NewSharedStateWorkflow()
    
    // 添加初始化任务
    finalWorkflow.AddTask(NewSimpleContextAwareTask("初始化", func(ctx *WorkflowContext) error {
        fmt.Println("初始化工作流...")
        startTime, _ := ctx.GetState("开始时间")
        fmt.Printf("开始时间: %v\n", startTime)
        return nil
    }))
    
    // 添加条件选择工作流的包装（使其可以访问上下文）
    finalWorkflow.AddTask(NewSimpleContextAwareTask("主处理", func(ctx *WorkflowContext) error {
        fmt.Println("执行主处理逻辑...")
        
        // 记录分支开始时间
        ctx.SetState("分支开始时间", time.Now())
        
        // 执行条件选择工作流
        err := choiceWorkflow.Execute()
        
        // 记录分支结束时间
        ctx.SetState("分支结束时间", time.Now())
        
        return err
    }))
    
    // 添加总结任务
    finalWorkflow.AddTask(NewSimpleContextAwareTask("总结", func(ctx *WorkflowContext) error {
        fmt.Println("执行工作流总结...")
        
        startTime, _ := ctx.GetState("开始时间")
        branchStartTime, _ := ctx.GetState("分支开始时间")
        branchEndTime, _ := ctx.GetState("分支结束时间")
        
        fmt.Printf("工作流开始时间: %v\n", startTime)
        fmt.Printf("分支执行时间: %v 到 %v\n", branchStartTime, branchEndTime)
        fmt.Printf("总执行时间: %v\n", time.Since(startTime.(time.Time)))
        
        return nil
    }))
    
    // 执行最终工作流
    err := finalWorkflow.Execute()
    if err != nil {
        fmt.Printf("工作流执行失败: %v\n", err)
    } else {
        fmt.Println("工作流成功完成")
    }
}
```

## 总结

本文使用Go语言实现了多种工作流模式，并分析了它们之间的形式关系。

1. **控制流模式**：我们实现了顺序执行、并行分支、同步、排他选择、简单合并、多选择、结构化同步合并和多合并等模式，这些模式控制了工作流中活动的执行顺序和条件。

2. **数据流模式**：通过任务数据、管道数据和共享状态模式，我们展示了数据如何在工作流中传递和共享。

3. **资源模式**：资源分配、资源池和资源限制模式提供了管理和限制资源使用的方法。

4. **异常处理模式**：错误传播、超时控制、重试和回退模式提供了健壮的错误处理机制。

5. **模式之间的关系**：
   - **相容性**：不同模式可以组合使用，创建复杂而强大的工作流
   - **等价性**：某些模式在特定条件下可以相互替代
   - **嵌入性**：模式可以嵌套，形成层次化的工作流结构

Go语言的并发特性（goroutines和channels）、强类型系统和错误处理机制使其成为实现工作流模式的理想选择。通过这些模式的组合，可以构建出满足各种复杂业务需求的工作流系统。

工作流模式不仅是软件设计的重要工具，也是形式化分析系统行为的基础。理解这些模式之间的关系，有助于设计更加灵活、可维护和可扩展的系统。
