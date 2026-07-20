# Go 工作流模式实现

```text
<think>
这个请求是要我用Go语言(golang)实现工作流模式，特别是使用Go 1.24版本的泛型和接口。我需要分析工作流的各种模式并实现它们。

首先，让我理解工作流模式的主要分类：

1. 控制流模式（Control-Flow Patterns）
2. 数据流模式（Data-Flow Patterns）
3. 资源模式（Resource Patterns）
4. 异常处理模式（Exception Handling Patterns）

这些是工作流系统中常见的模式类别。让我考虑每个类别下的具体模式：

**控制流模式**:
- 顺序（Sequence）
- 并行拆分/合并（Parallel Split/Synchronization）
- 条件选择（Exclusive Choice/Simple Merge）
- 多选择（Multi-Choice/Synchronizing Merge）
- 判别（Discriminator）
- 多实例（Multiple Instances）
- 延迟选择（Deferred Choice）
- 里程碑（Milestone）

**数据流模式**:
- 数据传递（Data Passing）
- 数据转换（Data Transformation）
- 数据路由（Data-based Routing）
- 数据合并（Data Aggregation）

**资源模式**:
- 资源分配（Resource Allocation）
- 资源池（Resource Pooling）
- 角色分配（Role-based Distribution）
- 自动分配（Automatic Assignment）

**异常处理模式**:
- 取消（Cancel）
- 补偿（Compensation）
- 超时（Timeout）
- 重试（Retry）
- 回滚（Rollback）

我将用Go 1.24的泛型和接口实现这些模式，创建一个模块化的工作流系统。需要注意的是，Go语言的设计哲学强调简单性和明确性，所以实现会考虑这些特点。

我将构建一个可扩展的工作流引擎，使用泛型接口定义核心组件，然后实现各种模式。所有代码将以Markdown格式输出，并组织成清晰的目录结构。

我不会包含外部链接，将确保所有内容都是自包含的文本格式。下面我将开始实现这个工作流系统。</think>
```

## 目录

- [Go 工作流模式实现](#go-工作流模式实现)
  - [目录](#目录)
  - [工作流模式分析](#工作流模式分析)
    - [控制流模式](#控制流模式)
    - [数据流模式](#数据流模式)
    - [资源模式](#资源模式)
    - [异常处理模式](#异常处理模式)
  - [基础架构实现](#基础架构实现)
  - [控制流模式实现](#控制流模式实现)
  - [数据流模式实现](#数据流模式实现)
  - [资源模式实现](#资源模式实现)
  - [异常处理模式实现](#异常处理模式实现)
  - [工作流使用示例](#工作流使用示例)
  - [更多工作流实现示例](#更多工作流实现示例)
    - [数据处理工作流示例](#数据处理工作流示例)
    - [审批流程示例](#审批流程示例)
  - [工作流模式间的关系与组合](#工作流模式间的关系与组合)

## 工作流模式分析

### 控制流模式

控制流模式关注工作流中任务的执行顺序和条件：

1. **顺序模式** - 按预定顺序执行任务
2. **并行分支/同步** - 并行执行多个任务分支，然后在某点同步
3. **排他选择/简单合并** - 基于条件选择一条执行路径
4. **多选择/同步合并** - 可选择多条执行路径，最终合并
5. **循环** - 重复执行任务直到满足条件
6. **多实例** - 同一任务的多个并行实例
7. **延迟选择** - 运行时决定执行路径
8. **里程碑** - 在达到特定状态前阻止执行

### 数据流模式

数据流模式关注数据在工作流中的移动和转换：

1. **数据传递** - 在活动间传递数据
2. **数据转换** - 转换数据格式或结构
3. **数据路由** - 基于数据内容路由流程
4. **数据合并** - 合并来自多个来源的数据

### 资源模式

资源模式关注工作流中资源的分配和管理：

1. **资源分配** - 为任务分配所需资源
2. **资源池** - 管理可用资源集合
3. **角色分配** - 基于角色分配任务
4. **工作负载均衡** - 平衡任务分配

### 异常处理模式

异常处理模式关注工作流执行中的错误和异常情况：

1. **取消** - 终止执行
2. **补偿** - 撤销已完成活动的效果
3. **超时** - 处理执行时间过长
4. **重试** - 重新尝试失败的活动
5. **回滚** - 恢复到先前状态

## 基础架构实现

首先，我们实现工作流引擎的基础架构：

```go:workflow/core.go
package workflow

import (
 "context"
 "errors"
 "fmt"
 "sync"
 "time"
)

// 任何可在工作流中执行的活动
type Activity[T any] interface {
 Execute(ctx context.Context, input T) (T, error)
 Name() string
}

// 工作流上下文，包含工作流执行的状态
type WorkflowContext[T any] struct {
 Data         T
 ActivityPath []string
 StartTime    time.Time
 Metadata     map[string]interface{}
 mutex        sync.RWMutex
}

// 创建新的工作流上下文
func NewWorkflowContext[T any](initialData T) *WorkflowContext[T] {
 return &WorkflowContext[T]{
  Data:         initialData,
  ActivityPath: make([]string, 0),
  StartTime:    time.Now(),
  Metadata:     make(map[string]interface{}),
 }
}

// 获取上下文数据
func (wc *WorkflowContext[T]) GetData() T {
 wc.mutex.RLock()
 defer wc.mutex.RUnlock()
 return wc.Data
}

// 设置上下文数据
func (wc *WorkflowContext[T]) SetData(data T) {
 wc.mutex.Lock()
 defer wc.mutex.Unlock()
 wc.Data = data
}

// 记录活动执行
func (wc *WorkflowContext[T]) RecordActivity(name string) {
 wc.mutex.Lock()
 defer wc.mutex.Unlock()
 wc.ActivityPath = append(wc.ActivityPath, name)
}

// 获取或设置元数据
func (wc *WorkflowContext[T]) GetMetadata(key string) (interface{}, bool) {
 wc.mutex.RLock()
 defer wc.mutex.RUnlock()
 val, ok := wc.Metadata[key]
 return val, ok
}

func (wc *WorkflowContext[T]) SetMetadata(key string, value interface{}) {
 wc.mutex.Lock()
 defer wc.mutex.Unlock()
 wc.Metadata[key] = value
}

// 基本工作流定义
type Workflow[T any] struct {
 Name       string
 RootNode   Activity[T]
 OnComplete func(*WorkflowContext[T])
 OnError    func(*WorkflowContext[T], error)
}

// 执行工作流
func (w *Workflow[T]) Execute(ctx context.Context, input T) (T, error) {
 workflowCtx := NewWorkflowContext(input)
 
 result, err := w.RootNode.Execute(ctx, input)
 if err != nil {
  if w.OnError != nil {
   w.OnError(workflowCtx, err)
  }
  return result, fmt.Errorf("工作流 '%s' 执行失败: %w", w.Name, err)
 }
 
 if w.OnComplete != nil {
  workflowCtx.SetData(result)
  w.OnComplete(workflowCtx)
 }
 
 return result, nil
}

// 错误定义
var (
 ErrActivityFailed = errors.New("活动执行失败")
 ErrWorkflowCancelled = errors.New("工作流被取消")
 ErrTimeout = errors.New("执行超时")
 ErrResourceUnavailable = errors.New("资源不可用")
)
```

## 控制流模式实现

现在实现控制流相关的模式：

```go:workflow/control_flow.go
package workflow

import (
 "context"
 "fmt"
 "sync"
)

// 顺序模式：按顺序执行多个活动
type SequenceActivity[T any] struct {
 Name_      string
 Activities []Activity[T]
}

func (s *SequenceActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 result := input
 
 for _, activity := range s.Activities {
  var err error
  result, err = activity.Execute(ctx, result)
  if err != nil {
   return result, fmt.Errorf("%s: %w", activity.Name(), err)
  }
 }
 
 return result, nil
}

func (s *SequenceActivity[T]) Name() string {
 return s.Name_
}

// 并行分支模式：并行执行多个活动
type ParallelActivity[T any, R any] struct {
 Name_         string
 Activities    []Activity[T]
 ResultMerger  func([]R, T) (T, error)
 ResultMapper  func(T) R
}

func (p *ParallelActivity[T, R]) Execute(ctx context.Context, input T) (T, error) {
 var wg sync.WaitGroup
 results := make([]R, len(p.Activities))
 errors := make([]error, len(p.Activities))
 
 for i, activity := range p.Activities {
  wg.Add(1)
  go func(index int, act Activity[T]) {
   defer wg.Done()
   result, err := act.Execute(ctx, input)
   if err != nil {
    errors[index] = err
    return
   }
   results[index] = p.ResultMapper(result)
  }(i, activity)
 }
 
 wg.Wait()
 
 // 检查错误
 for _, err := range errors {
  if err != nil {
   return input, err
  }
 }
 
 // 合并结果
 return p.ResultMerger(results, input)
}

func (p *ParallelActivity[T, R]) Name() string {
 return p.Name_
}

// 条件选择模式：基于条件选择一个活动执行
type ConditionActivity[T any] struct {
 Name_             string
 ConditionFunc     func(T) bool
 TruePathActivity  Activity[T]
 FalsePathActivity Activity[T]
}

func (c *ConditionActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 if c.ConditionFunc(input) {
  return c.TruePathActivity.Execute(ctx, input)
 }
 return c.FalsePathActivity.Execute(ctx, input)
}

func (c *ConditionActivity[T]) Name() string {
 return c.Name_
}

// 多选择模式：可能执行多条路径
type MultiChoiceActivity[T any] struct {
 Name_         string
 Choices       []struct {
  Condition func(T) bool
  Activity  Activity[T]
 }
 MergeResults func([]T) (T, error)
}

func (m *MultiChoiceActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 var wg sync.WaitGroup
 var mutex sync.Mutex
 results := make([]T, 0)
 
 for _, choice := range m.Choices {
  if choice.Condition(input) {
   wg.Add(1)
   go func(activity Activity[T]) {
    defer wg.Done()
    result, err := activity.Execute(ctx, input)
    if err == nil {
     mutex.Lock()
     results = append(results, result)
     mutex.Unlock()
    }
   }(choice.Activity)
  }
 }
 
 wg.Wait()
 
 // 如果没有活动执行
 if len(results) == 0 {
  return input, nil
 }
 
 // 合并结果
 return m.MergeResults(results)
}

func (m *MultiChoiceActivity[T]) Name() string {
 return m.Name_
}

// 循环模式：重复执行直到条件满足
type LoopActivity[T any] struct {
 Name_        string
 LoopActivity Activity[T]
 Condition    func(T) bool // 当返回true时继续循环
 MaxIterations int // 防止无限循环
}

func (l *LoopActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 result := input
 iterations := 0
 
 for l.Condition(result) {
  if iterations >= l.MaxIterations {
   return result, fmt.Errorf("达到最大迭代次数 %d", l.MaxIterations)
  }
  
  var err error
  result, err = l.LoopActivity.Execute(ctx, result)
  if err != nil {
   return result, err
  }
  
  iterations++
 }
 
 return result, nil
}

func (l *LoopActivity[T]) Name() string {
 return l.Name_
}

// 多实例模式：同一活动的多个并行实例
type MultiInstanceActivity[T any, I any, R any] struct {
 Name_           string
 ItemActivity    Activity[I]
 ItemsExtractor  func(T) []I
 ResultAggregator func([]R, T) (T, error)
 ResultMapper    func(I, I) R // 从输入项和结果项映射到输出项
}

func (m *MultiInstanceActivity[T, I, R]) Execute(ctx context.Context, input T) (T, error) {
 items := m.ItemsExtractor(input)
 results := make([]R, len(items))
 var wg sync.WaitGroup
 var mutex sync.Mutex
 errors := make([]error, 0)
 
 for i, item := range items {
  wg.Add(1)
  go func(index int, instanceInput I) {
   defer wg.Done()
   result, err := m.ItemActivity.Execute(ctx, instanceInput)
   if err != nil {
    mutex.Lock()
    errors = append(errors, err)
    mutex.Unlock()
    return
   }
   results[index] = m.ResultMapper(instanceInput, result)
  }(i, item)
 }
 
 wg.Wait()
 
 // 检查错误
 if len(errors) > 0 {
  return input, errors[0] // 返回第一个遇到的错误
 }
 
 // 聚合结果
 return m.ResultAggregator(results, input)
}

func (m *MultiInstanceActivity[T, I, R]) Name() string {
 return m.Name_
}
```

## 数据流模式实现

下面是数据流模式的实现：

```go:workflow/data_flow.go
package workflow

import (
 "context"
)

// 数据转换模式：转换输入数据格式
type TransformActivity[TInput any, TOutput any] struct {
 Name_        string
 Transformer  func(TInput) (TOutput, error)
}

func (t *TransformActivity[TInput, TOutput]) Execute(ctx context.Context, input TInput) (TOutput, error) {
 return t.Transformer(input)
}

func (t *TransformActivity[TInput, TOutput]) Name() string {
 return t.Name_
}

// 数据路由模式：基于数据内容选择执行路径
type DataRoutingActivity[T any] struct {
 Name_      string
 Router     func(T) string
 Activities map[string]Activity[T]
 DefaultActivity Activity[T]
}

func (d *DataRoutingActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 route := d.Router(input)
 activity, ok := d.Activities[route]
 
 if !ok {
  if d.DefaultActivity != nil {
   return d.DefaultActivity.Execute(ctx, input)
  }
  return input, nil // 如果没有匹配的路由和默认活动，则返回输入
 }
 
 return activity.Execute(ctx, input)
}

func (d *DataRoutingActivity[T]) Name() string {
 return d.Name_
}

// 数据合并模式：合并来自多个来源的数据
type DataAggregationActivity[TInput any, TOutput any] struct {
 Name_       string
 Inputs      []TInput
 Aggregator  func([]TInput) (TOutput, error)
}

func (d *DataAggregationActivity[TInput, TOutput]) Execute(ctx context.Context, _ TInput) (TOutput, error) {
 return d.Aggregator(d.Inputs)
}

func (d *DataAggregationActivity[TInput, TOutput]) Name() string {
 return d.Name_
}

// 数据过滤模式：过滤数据项
type DataFilterActivity[T any, I any] struct {
 Name_       string
 ItemsExtractor func(T) []I
 FilterFunc    func(I) bool
 ResultUpdater func(T, []I) (T, error)
}

func (d *DataFilterActivity[T, I]) Execute(ctx context.Context, input T) (T, error) {
 items := d.ItemsExtractor(input)
 filtered := make([]I, 0)
 
 for _, item := range items {
  if d.FilterFunc(item) {
   filtered = append(filtered, item)
  }
 }
 
 return d.ResultUpdater(input, filtered)
}

func (d *DataFilterActivity[T, I]) Name() string {
 return d.Name_
}
```

## 资源模式实现

现在实现资源相关的模式：

```go:workflow/resource.go
package workflow

import (
 "context"
 "errors"
 "sync"
 "time"
)

// 资源接口
type Resource interface {
 ID() string
 Type() string
 IsAvailable() bool
 Acquire() error
 Release() error
}

// 基本资源实现
type BaseResource struct {
 id        string
 resourceType string
 available bool
 mutex     sync.Mutex
}

func NewBaseResource(id string, resourceType string) *BaseResource {
 return &BaseResource{
  id:        id,
  resourceType: resourceType,
  available: true,
 }
}

func (r *BaseResource) ID() string {
 return r.id
}

func (r *BaseResource) Type() string {
 return r.resourceType
}

func (r *BaseResource) IsAvailable() bool {
 r.mutex.Lock()
 defer r.mutex.Unlock()
 return r.available
}

func (r *BaseResource) Acquire() error {
 r.mutex.Lock()
 defer r.mutex.Unlock()
 
 if !r.available {
  return ErrResourceUnavailable
 }
 
 r.available = false
 return nil
}

func (r *BaseResource) Release() error {
 r.mutex.Lock()
 defer r.mutex.Unlock()
 r.available = true
 return nil
}

// 资源池
type ResourcePool struct {
 resources map[string]Resource
 byType    map[string][]string
 mutex     sync.RWMutex
}

func NewResourcePool() *ResourcePool {
 return &ResourcePool{
  resources: make(map[string]Resource),
  byType:    make(map[string][]string),
 }
}

func (p *ResourcePool) AddResource(resource Resource) {
 p.mutex.Lock()
 defer p.mutex.Unlock()
 
 p.resources[resource.ID()] = resource
 
 // 按类型索引
 resourceType := resource.Type()
 if _, ok := p.byType[resourceType]; !ok {
  p.byType[resourceType] = make([]string, 0)
 }
 p.byType[resourceType] = append(p.byType[resourceType], resource.ID())
}

func (p *ResourcePool) GetResource(id string) (Resource, bool) {
 p.mutex.RLock()
 defer p.mutex.RUnlock()
 resource, ok := p.resources[id]
 return resource, ok
}

func (p *ResourcePool) AcquireResource(id string) error {
 p.mutex.RLock()
 resource, ok := p.resources[id]
 p.mutex.RUnlock()
 
 if !ok {
  return errors.New("资源不存在")
 }
 
 return resource.Acquire()
}

func (p *ResourcePool) ReleaseResource(id string) error {
 p.mutex.RLock()
 resource, ok := p.resources[id]
 p.mutex.RUnlock()
 
 if !ok {
  return errors.New("资源不存在")
 }
 
 return resource.Release()
}

func (p *ResourcePool) AcquireByType(resourceType string) (Resource, error) {
 p.mutex.RLock()
 ids, ok := p.byType[resourceType]
 p.mutex.RUnlock()
 
 if !ok || len(ids) == 0 {
  return nil, errors.New("没有可用的该类型资源")
 }
 
 // 寻找第一个可用资源
 for _, id := range ids {
  p.mutex.RLock()
  resource := p.resources[id]
  p.mutex.RUnlock()
  
  if resource.IsAvailable() {
   err := resource.Acquire()
   if err == nil {
    return resource, nil
   }
  }
 }
 
 return nil, ErrResourceUnavailable
}

// 资源分配模式：为活动分配资源
type ResourceActivity[T any] struct {
 Name_         string
 InnerActivity Activity[T]
 ResourcePool  *ResourcePool
 ResourceType  string
 OnAcquire     func(T, Resource) (T, error)
 OnRelease     func(T, Resource) (T, error)
}

func (r *ResourceActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 // 获取资源
 resource, err := r.ResourcePool.AcquireByType(r.ResourceType)
 if err != nil {
  return input, err
 }
 
 defer func() {
  _ = resource.Release()
 }()
 
 // 资源获取后的处理
 if r.OnAcquire != nil {
  input, err = r.OnAcquire(input, resource)
  if err != nil {
   return input, err
  }
 }
 
 // 执行内部活动
 result, err := r.InnerActivity.Execute(ctx, input)
 if err != nil {
  return result, err
 }
 
 // 释放资源前的处理
 if r.OnRelease != nil {
  result, err = r.OnRelease(result, resource)
 }
 
 return result, err
}

func (r *ResourceActivity[T]) Name() string {
 return r.Name_
}

// 角色分配模式：根据角色分配活动
type RoleBasedActivity[T any] struct {
 Name_          string
 RoleExtractor  func(T) string
 RoleActivities map[string]Activity[T]
 DefaultActivity Activity[T]
}

func (r *RoleBasedActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 role := r.RoleExtractor(input)
 activity, ok := r.RoleActivities[role]
 
 if !ok {
  if r.DefaultActivity != nil {
   return r.DefaultActivity.Execute(ctx, input)
  }
  return input, errors.New("未找到适合角色的活动")
 }
 
 return activity.Execute(ctx, input)
}

func (r *RoleBasedActivity[T]) Name() string {
 return r.Name_
}

// 工作负载均衡模式：在多个资源间均衡分配工作
type LoadBalancedActivity[T any] struct {
 Name_        string
 Workers      []Activity[T]
 nextWorker   int
 mutex        sync.Mutex
}

func (l *LoadBalancedActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 l.mutex.Lock()
 workerIndex := l.nextWorker
 l.nextWorker = (l.nextWorker + 1) % len(l.Workers)
 l.mutex.Unlock()
 
 return l.Workers[workerIndex].Execute(ctx, input)
}

func (l *LoadBalancedActivity[T]) Name() string {
 return l.Name_
}
```

## 异常处理模式实现

下面是异常处理相关的模式实现：

```go:workflow/exception.go
package workflow

import (
 "context"
 "errors"
 "time"
)

// 重试模式：在失败时重试活动
type RetryActivity[T any] struct {
 Name_         string
 InnerActivity Activity[T]
 MaxRetries    int
 RetryDelay    time.Duration
 ShouldRetry   func(error) bool
}

func (r *RetryActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 var result T
 var err error
 
 for attempt := 0; attempt <= r.MaxRetries; attempt++ {
  result, err = r.InnerActivity.Execute(ctx, input)
  if err == nil {
   return result, nil
  }
  
  if !r.ShouldRetry(err) {
   return result, err
  }
  
  if attempt < r.MaxRetries {
   select {
   case <-ctx.Done():
    return result, ctx.Err()
   case <-time.After(r.RetryDelay):
    // 继续下一次重试
   }
  }
 }
 
 return result, err
}

func (r *RetryActivity[T]) Name() string {
 return r.Name_
}

// 超时模式：确保活动在指定时间内完成
type TimeoutActivity[T any] struct {
 Name_         string
 InnerActivity Activity[T]
 Timeout       time.Duration
}

func (t *TimeoutActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 timeoutCtx, cancel := context.WithTimeout(ctx, t.Timeout)
 defer cancel()
 
 resultCh := make(chan struct {
  result T
  err    error
 })
 
 go func() {
  result, err := t.InnerActivity.Execute(timeoutCtx, input)
  resultCh <- struct {
   result T
   err    error
  }{result, err}
 }()
 
 select {
 case <-timeoutCtx.Done():
  if errors.Is(timeoutCtx.Err(), context.DeadlineExceeded) {
   var zeroValue T
   return zeroValue, ErrTimeout
  }
  var zeroValue T
  return zeroValue, timeoutCtx.Err()
 case r := <-resultCh:
  return r.result, r.err
 }
}

func (t *TimeoutActivity[T]) Name() string {
 return t.Name_
}

// 补偿模式：在失败时执行补偿操作
type CompensationActivity[T any] struct {
 Name_                string
 MainActivity         Activity[T]
 CompensationActivity Activity[T]
 ShouldCompensate     func(error) bool
}

func (c *CompensationActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 result, err := c.MainActivity.Execute(ctx, input)
 
 if err != nil && c.ShouldCompensate(err) {
  compensationResult, compensationErr := c.CompensationActivity.Execute(ctx, input)
  if compensationErr != nil {
   return result, errors.New("主活动和补偿活动都失败")
  }
  return compensationResult, err // 返回补偿结果和原始错误
 }
 
 return result, err
}

func (c *CompensationActivity[T]) Name() string {
 return c.Name_
}

// 取消模式：支持取消正在执行的活动
type CancellableActivity[T any] struct {
 Name_         string
 InnerActivity Activity[T]
 OnCancel      func(T) (T, error)
}

func (c *CancellableActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 result, err := c.InnerActivity.Execute(ctx, input)
 
 if errors.Is(ctx.Err(), context.Canceled) && c.OnCancel != nil {
  return c.OnCancel(input)
 }
 
 return result, err
}

func (c *CancellableActivity[T]) Name() string {
 return c.Name_
}

// 错误边界模式：捕获错误并提供替代路径
type ErrorBoundaryActivity[T any] struct {
 Name_           string
 TryActivity     Activity[T]
 CatchActivities map[error]Activity[T]
 FinallyActivity Activity[T]
}

func (e *ErrorBoundaryActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 result, err := e.TryActivity.Execute(ctx, input)
 
 // 如果有错误，寻找处理此错误的活动
 if err != nil {
  for knownErr, handler := range e.CatchActivities {
   if errors.Is(err, knownErr) {
    result, _ = handler.Execute(ctx, input)
    err = nil // 错误已处理
    break
   }
  }
 }
 
 // 执行finally活动（如果有）
 if e.FinallyActivity != nil {
  finalResult, finalErr := e.FinallyActivity.Execute(ctx, result)
  if finalErr != nil {
   return finalResult, finalErr
  }
  return finalResult, err
 }
 
 return result, err
}

func (e *ErrorBoundaryActivity[T]) Name() string {
 return e.Name_
}
```

## 工作流使用示例

现在提供一个示例，展示如何使用这些模式创建实际的工作流：

```go:examples/order_processing.go
package main

import (
 "context"
 "errors"
 "fmt"
 "log"
 "time"
 
 "workflow"
)

// 订单数据结构
type Order struct {
 ID            string
 CustomerID    string
 Items         []OrderItem
 TotalAmount   float64
 PaymentStatus string
 ShippingInfo  ShippingInfo
 CreatedAt     time.Time
 ProcessedBy   string
}

type OrderItem struct {
 ProductID  string
 Quantity   int
 UnitPrice  float64
 TotalPrice float64
}

type ShippingInfo struct {
 Address     string
 City        string
 PostalCode  string
 Country     string
 TrackingID  string
 ShippedAt   time.Time
 DeliveredAt time.Time
}

// 验证订单
func validateOrder(order Order) (Order, error) {
 if order.CustomerID == "" {
  return order, errors.New("客户ID不能为空")
 }
 
 if len(order.Items) == 0 {
  return order, errors.New("订单必须包含至少一个商品")
 }
 
 if order.ShippingInfo.Address == "" {
  return order, errors.New("送货地址不能为空")
 }
 
 return order, nil
}

// 计算订单总额
func calculateTotal(order Order) (Order, error) {
 total := 0.0
 
 for i, item := range order.Items {
  itemTotal := float64(item.Quantity) * item.UnitPrice
  order.Items[i].TotalPrice = itemTotal
  total += itemTotal
 }
 
 order.TotalAmount = total
 return order, nil
}

// 处理支付
func processPayment(order Order) (Order, error) {
 // 模拟支付处理
 log.Printf("处理订单 %s 的支付，金额: %.2f\n", order.ID, order.TotalAmount)
 
 // 80%的概率支付成功
 if order.ID[0] < 'p' { // 简单的模拟条件
  order.PaymentStatus = "已支付"
  return order, nil
 }
 
 order.PaymentStatus = "支付失败"
 return order, errors.New("支付处理失败")
}

// 准备发货
func prepareShipment(order Order) (Order, error) {
 log.Printf("准备订单 %s 的发货\n", order.ID)
 order.ShippingInfo.TrackingID = fmt.Sprintf("TRK-%s-%d", order.ID, time.Now().Unix())
 return order, nil
}

// 发送确认邮件
func sendConfirmationEmail(order Order) (Order, error) {
 log.Printf("发送订单 %s 的确认邮件到客户 %s\n", order.ID, order.CustomerID)
 return order, nil
}

// 更新库存
func updateInventory(order Order) (Order, error) {
 log.Printf("更新订单 %s 的库存\n", order.ID)
 return order, nil
}

// 取消订单
func cancelOrder(order Order) (Order, error) {
 log.Printf("取消订单 %s\n", order.ID)
 order.PaymentStatus = "已取消"
 return order, nil
}

func main() {
 // 创建资源池并添加资源
 resourcePool := workflow.NewResourcePool()
 
 // 添加处理人员资源
 for i := 1; i <= 3; i++ {
  resourcePool.AddResource(workflow.NewBaseResource(fmt.Sprintf("agent-%d", i), "agent"))
 }
 
 // 定义验证活动
 validateActivity := &workflow.TransformActivity[Order, Order]{
  Name_:       "验证订单",
  Transformer: validateOrder,
 }
 
 // 定义计算总额活动
 calculateActivity := &workflow.TransformActivity[Order, Order]{
  Name_:       "计算订单总额",
  Transformer: calculateTotal,
 }
 
 // 定义支付活动（带重试）
 paymentActivity := &workflow.RetryActivity[Order]{
  Name_:       "处理支付",
  InnerActivity: &workflow.TransformActivity[Order, Order]{
   Name_:       "支付处理",
   Transformer: processPayment,
  },
  MaxRetries:  3,
  RetryDelay:  time.Second * 2,
  ShouldRetry: func(err error) bool {
   // 决定是否应该重试特定错误
   return err.Error() == "支付处理失败"
  },
 }
 
 // 定义发货准备活动（带资源分配）
 shipmentActivity := &workflow.ResourceActivity[Order]{
  Name_:        "准备发货",
  ResourcePool: resourcePool,
  ResourceType: "agent",
  InnerActivity: &workflow.TransformActivity[Order, Order]{
   Name_:       "发货准备",
   Transformer: prepareShipment,
  },
  OnAcquire: func(order Order, resource workflow.Resource) (Order, error) {
   order.ProcessedBy = resource.ID()
   log.Printf("订单 %s 由 %s 处理\n", order.ID, resource.ID())
   return order, nil
  },
 }
 
 // 定义并行活动：同时发送确认邮件和更新库存
 parallelActivity := &workflow.ParallelActivity[Order, Order]{
  Name_: "后处理任务",
  Activities: []workflow.Activity[Order]{
   &workflow.TransformActivity[Order, Order]{
    Name_:       "发送确认邮件",
    Transformer: sendConfirmationEmail,
   },
   &workflow.TransformActivity[Order, Order]{
    Name_:       "更新库存",
    Transformer: updateInventory,
   },
  },
  ResultMapper: func(o Order) Order {
   return o
  },
  ResultMerger: func(results []Order, original Order) (Order, error) {
   // 在这个简单示例中，我们只返回原始订单
   // 实际应用中可能需要合并来自不同活动的结果
   return original, nil
  },
 }
 
 // 定义补偿活动，在支付失败时取消订单
 compensationActivity := &workflow.CompensationActivity[Order]{
  Name_:        "支付处理与补偿",
  MainActivity: paymentActivity,
  CompensationActivity: &workflow.TransformActivity[Order, Order]{
   Name_:       "取消订单",
   Transformer: cancelOrder,
  },
  ShouldCompensate: func(err error) bool {
   return err != nil
  },
 }
 
 // 构建完整的订单处理工作流
 orderProcessingWorkflow := &workflow.Workflow[Order]{
  Name: "订单处理工作流",
  RootNode: &workflow.SequenceActivity[Order]{
   Name_: "订单处理主序列",
   Activities: []workflow.Activity[Order]{
    validateActivity,
    calculateActivity,
    compensationActivity,
    &workflow.ConditionActivity[Order]{
     Name_: "支付状态检查",
     ConditionFunc: func(order Order) bool {
      return order.PaymentStatus == "已支付"
     },
     TruePathActivity: &workflow.SequenceActivity[Order]{
      Name_: "已支付路径",
      Activities: []workflow.Activity[Order]{
       shipmentActivity,
       parallelActivity,
      },
     },
     FalsePathActivity: &workflow.TransformActivity[Order, Order]{
      Name_: "未处理",
      Transformer: func(o Order) (Order, error) {
       return o, nil
      },
     },
    },
   },
  },
  OnComplete: func(ctx *workflow.WorkflowContext[Order]) {
   log.Printf("工作流完成！订单状态: %s\n", ctx.GetData().PaymentStatus)
  },
  OnError: func(ctx *workflow.WorkflowContext[Order], err error) {
   log.Printf("工作流错误: %v\n", err)
  },
 }
 
 // 创建测试订单
 testOrder := Order{
  ID:         "ORD-123456",
  CustomerID: "CUST-789",
  Items: []OrderItem{
   {ProductID: "PROD-A", Quantity: 2, UnitPrice: 39.99},
   {ProductID: "PROD-B", Quantity: 1, UnitPrice: 99.99},
  },
  ShippingInfo: ShippingInfo{
   Address:    "中关村科技园",
   City:       "北京",
   PostalCode: "100080",
   Country:    "中国",
  },
  CreatedAt: time.Now(),
 }
 
 // 执行工作流
 ctx := context.Background()
 result, err := orderProcessingWorkflow.Execute(ctx, testOrder)
 
 if err != nil {
  log.Printf("工作流执行失败: %v\n", err)
 } else {
  log.Printf("工作流执行成功。最终订单状态: %s, 追踪号: %s\n", 
   result.PaymentStatus, result.ShippingInfo.TrackingID)
 }
 
 // 示例：带超时的工作流执行
 timeoutOrder := testOrder
 timeoutOrder.ID = "ORD-TIMEOUT"
 
 timeoutWorkflow := &workflow.Workflow[Order]{
  Name: "带超时的订单处理",
  RootNode: &workflow.TimeoutActivity[Order]{
   Name_:   "2秒超时限制",
   Timeout: 2 * time.Second,
   InnerActivity: &workflow.SequenceActivity[Order]{
    Name_: "延时处理序列",
    Activities: []workflow.Activity[Order]{
     validateActivity,
     calculateActivity,
     &workflow.TransformActivity[Order, Order]{
      Name_: "模拟耗时操作",
      Transformer: func(o Order) (Order, error) {
       time.Sleep(3 * time.Second) // 故意超时
       return o, nil
      },
     },
     compensationActivity,
    },
   },
  },
 }
 
 _, timeoutErr := timeoutWorkflow.Execute(ctx, timeoutOrder)
 if timeoutErr != nil {
  log.Printf("超时工作流结果: %v\n", timeoutErr)
 }
}
```

## 更多工作流实现示例

### 数据处理工作流示例

```go:examples/data_processing.go
package main

import (
 "context"
 "errors"
 "fmt"
 "log"
 "strings"
 
 "workflow"
)

// 数据记录类型
type DataRecord struct {
 ID       string
 RawData  string
 Parsed   map[string]interface{}
 Filtered bool
 Error    string
}

// 解析数据
func parseData(record DataRecord) (DataRecord, error) {
 // 简单的解析示例，实际应用中可能更复杂
 if record.RawData == "" {
  return record, errors.New("空数据")
 }
 
 parsed := make(map[string]interface{})
 parts := strings.Split(record.RawData, ",")
 
 for _, part := range parts {
  kv := strings.Split(part, "=")
  if len(kv) == 2 {
   parsed[kv[0]] = kv[1]
  }
 }
 
 record.Parsed = parsed
 return record, nil
}

// 过滤数据
func filterData(record DataRecord) (DataRecord, error) {
 // 根据某些条件过滤数据
 if len(record.Parsed) < 2 {
  record.Filtered = true
  return record, nil
 }
 
 // 检查是否有必要字段
 _, hasName := record.Parsed["name"]
 _, hasValue := record.Parsed["value"]
 
 if !hasName || !hasValue {
  record.Filtered = true
 }
 
 return record, nil
}

// 处理单个记录的函数
func processRecord(ctx context.Context, record DataRecord) (DataRecord, error) {
 // 创建数据处理工作流
 dataProcessingFlow := workflow.SequenceActivity[DataRecord]{
  Name_: "数据处理序列",
  Activities: []workflow.Activity[DataRecord]{
   &workflow.TransformActivity[DataRecord, DataRecord]{
    Name_:       "数据解析",
    Transformer: parseData,
   },
   &workflow.TransformActivity[DataRecord, DataRecord]{
    Name_:       "数据过滤",
    Transformer: filterData,
   },
   &workflow.ErrorBoundaryActivity[DataRecord]{
    Name_: "错误处理",
    TryActivity: &workflow.ConditionActivity[DataRecord]{
     Name_: "条件验证",
     ConditionFunc: func(record DataRecord) bool {
      return !record.Filtered
     },
     TruePathActivity: &workflow.TransformActivity[DataRecord, DataRecord]{
      Name_: "处理有效数据",
      Transformer: func(r DataRecord) (DataRecord, error) {
       log.Printf("处理记录 %s: %v\n", r.ID, r.Parsed)
       return r, nil
      },
     },
     FalsePathActivity: &workflow.TransformActivity[DataRecord, DataRecord]{
      Name_: "跳过过滤数据",
      Transformer: func(r DataRecord) (DataRecord, error) {
       log.Printf("跳过记录 %s: 已被过滤\n", r.ID)
       return r, nil
      },
     },
    },
    CatchActivities: map[error]workflow.Activity[DataRecord]{
     errors.New("空数据"): &workflow.TransformActivity[DataRecord, DataRecord]{
      Name_: "处理空数据错误",
      Transformer: func(r DataRecord) (DataRecord, error) {
       r.Error = "空数据错误"
       log.Printf("记录 %s 错误: 空数据\n", r.ID)
       return r, nil
      },
     },
    },
    FinallyActivity: &workflow.TransformActivity[DataRecord, DataRecord]{
     Name_: "最终记录",
     Transformer: func(r DataRecord) (DataRecord, error) {
      log.Printf("完成记录 %s 处理\n", r.ID)
      return r, nil
     },
    },
   },
  },
 }
 
 return dataProcessingFlow.Execute(ctx, record)
}

func main() {
 // 创建一些测试数据记录
 testRecords := []DataRecord{
  {ID: "REC-1", RawData: "name=apple,color=red,value=5"},
  {ID: "REC-2", RawData: "type=fruit,color=yellow"},
  {ID: "REC-3", RawData: ""},
  {ID: "REC-4", RawData: "name=orange,value=3,origin=china"},
 }
 
 ctx := context.Background()
 
 // 使用多实例模式处理所有记录
 multiInstanceActivity := workflow.MultiInstanceActivity[[]DataRecord, DataRecord, DataRecord]{
  Name_: "批量处理记录",
  ItemActivity: &workflow.TransformActivity[DataRecord, DataRecord]{
   Name_: "记录处理器",
   Transformer: func(record DataRecord) (DataRecord, error) {
    return processRecord(ctx, record)
   },
  },
  ItemsExtractor: func(records []DataRecord) []DataRecord {
   return records
  },
  ResultMapper: func(input, result DataRecord) DataRecord {
   return result
  },
  ResultAggregator: func(results []DataRecord, original []DataRecord) ([]DataRecord, error) {
   return results, nil
  },
 }
 
 processedRecords, err := multiInstanceActivity.Execute(ctx, testRecords)
 if err != nil {
  log.Printf("处理错误: %v\n", err)
  return
 }
 
 // 显示结果统计
 filtered := 0
 errors := 0
 for _, record := range processedRecords {
  if record.Filtered {
   filtered++
  }
  if record.Error != "" {
   errors++
  }
 }
 
 fmt.Printf("处理结果: 总共 %d 条记录, %d 条已过滤, %d 条错误\n", 
  len(processedRecords), filtered, errors)
}
```

### 审批流程示例

```go:examples/approval_workflow.go
package main

import (
 "context"
 "errors"
 "fmt"
 "log"
 "time"
 
 "workflow"
)

// 请求数据类型
type ApprovalRequest struct {
 ID             string
 RequesterID    string
 RequestType    string
 Description    string
 Amount         float64
 Status         string
 CurrentLevel   int
 ApprovalChain  []ApprovalStep
 Comments       []Comment
 CreatedAt      time.Time
 LastModifiedAt time.Time
}

type ApprovalStep struct {
 Level      int
 ApproverID string
 Status     string
 ApprovedAt time.Time
}

type Comment struct {
 UserID    string
 Text      string
 Timestamp time.Time
}

// 验证请求
func validateRequest(request ApprovalRequest) (ApprovalRequest, error) {
 if request.RequesterID == "" {
  return request, errors.New("请求者ID不能为空")
 }
 
 if request.RequestType == "" {
  return request, errors.New("请求类型不能为空")
 }
 
 if request.Amount <= 0 {
  return request, errors.New("金额必须大于零")
 }
 
 return request, nil
}

// 初始化审批链
func initializeApprovalChain(request ApprovalRequest) (ApprovalRequest, error) {
 // 根据金额确定审批链
 request.ApprovalChain = []ApprovalStep{}
 request.CurrentLevel = 1
 request.Status = "待审批"
 
 // 例如：不同金额需要不同级别的审批
 if request.Amount <= 1000 {
  // 只需要一级审批
  request.ApprovalChain = append(request.ApprovalChain, ApprovalStep{
   Level:  1,
   Status: "待审批",
  })
 } else if request.Amount <= 10000 {
  // 需要两级审批
  request.ApprovalChain = append(request.ApprovalChain, 
   ApprovalStep{Level: 1, Status: "待审批"},
   ApprovalStep{Level: 2, Status: "等待中"})
 } else {
  // 需要三级审批
  request.ApprovalChain = append(request.ApprovalChain, 
   ApprovalStep{Level: 1, Status: "待审批"},
   ApprovalStep{Level: 2, Status: "等待中"},
   ApprovalStep{Level: 3, Status: "等待中"})
 }
 
 return request, nil
}

// 提交审批结果
func submitApproval(approved bool, approverID string) func(ApprovalRequest) (ApprovalRequest, error) {
 return func(request ApprovalRequest) (ApprovalRequest, error) {
  currentLevelIndex := request.CurrentLevel - 1
  if currentLevelIndex < 0 || currentLevelIndex >= len(request.ApprovalChain) {
   return request, errors.New("无效的审批级别")
  }
  
  // 更新当前级别的审批状态
  request.ApprovalChain[currentLevelIndex].ApproverID = approverID
  request.ApprovalChain[currentLevelIndex].ApprovedAt = time.Now()
  
  if approved {
   request.ApprovalChain[currentLevelIndex].Status = "已批准"
   
   // 检查是否有下一级审批
   if request.CurrentLevel < len(request.ApprovalChain) {
    request.CurrentLevel++
    request.ApprovalChain[request.CurrentLevel-1].Status = "待审批"
    request.Status = fmt.Sprintf("等待%d级审批", request.CurrentLevel)
   } else {
    // 所有级别都已批准
    request.Status = "已批准"
   }
  } else {
   // 拒绝审批，整个请求被拒绝
   request.ApprovalChain[currentLevelIndex].Status = "已拒绝"
   request.Status = "已拒绝"
  }
  
  request.LastModifiedAt = time.Now()
  return request, nil
 }
}

// 添加评论
func addComment(userID, text string) func(ApprovalRequest) (ApprovalRequest, error) {
 return func(request ApprovalRequest) (ApprovalRequest, error) {
  comment := Comment{
   UserID:    userID,
   Text:      text,
   Timestamp: time.Now(),
  }
  
  request.Comments = append(request.Comments, comment)
  request.LastModifiedAt = time.Now()
  return request, nil
 }
}

// 通知请求者
func notifyRequester(request ApprovalRequest) (ApprovalRequest, error) {
 log.Printf("通知请求者 %s: 您的请求 %s 状态已更新为 %s\n", 
  request.RequesterID, request.ID, request.Status)
 return request, nil
}

func main() {
 // 创建审批流程工作流
 approvalWorkflow := workflow.Workflow[ApprovalRequest]{
  Name: "审批流程",
  RootNode: &workflow.SequenceActivity[ApprovalRequest]{
   Name_: "审批主流程",
   Activities: []workflow.Activity[ApprovalRequest]{
    &workflow.TransformActivity[ApprovalRequest, ApprovalRequest]{
     Name_:       "验证请求",
     Transformer: validateRequest,
    },
    &workflow.TransformActivity[ApprovalRequest, ApprovalRequest]{
     Name_:       "初始化审批链",
     Transformer: initializeApprovalChain,
    },
    &workflow.DataRoutingActivity[ApprovalRequest]{
     Name_: "审批级别路由",
     Router: func(request ApprovalRequest) string {
      return fmt.Sprintf("level%d", request.CurrentLevel)
     },
     Activities: map[string]workflow.Activity[ApprovalRequest]{
      "level1": &workflow.TransformActivity[ApprovalRequest, ApprovalRequest]{
       Name_:       "一级审批",
       Transformer: submitApproval(true, "APPROVER-L1"),
      },
      "level2": &workflow.TransformActivity[ApprovalRequest, ApprovalRequest]{
       Name_:       "二级审批",
       Transformer: submitApproval(true, "APPROVER-L2"),
      },
      "level3": &workflow.TransformActivity[ApprovalRequest, ApprovalRequest]{
       Name_:       "三级审批",
       Transformer: submitApproval(false, "APPROVER-L3"), // 假设三级审批被拒绝
      },
     },
     DefaultActivity: &workflow.TransformActivity[ApprovalRequest, ApprovalRequest]{
      Name_: "未知级别",
      Transformer: func(r ApprovalRequest) (ApprovalRequest, error) {
       return r, errors.New("未知审批级别")
      },
     },
    },
    &workflow.ConditionActivity[ApprovalRequest]{
     Name_: "检查审批状态",
     ConditionFunc: func(request ApprovalRequest) bool {
      return request.CurrentLevel < len(request.ApprovalChain) && 
          request.Status != "已拒绝"
     },
     TruePathActivity: &workflow.TransformActivity[ApprovalRequest, ApprovalRequest]{
      Name_: "继续下一级审批",
      Transformer: func(r ApprovalRequest) (ApprovalRequest, error) {
       log.Printf("请求 %s 进入下一级审批 %d\n", r.ID, r.CurrentLevel)
       return r, nil
      },
     },
     FalsePathActivity: &workflow.SequenceActivity[ApprovalRequest]{
      Name_: "审批完成处理",
      Activities: []workflow.Activity[ApprovalRequest]{
       &workflow.TransformActivity[ApprovalRequest, ApprovalRequest]{
        Name_:       "添加最终评论",
        Transformer: addComment("SYSTEM", "审批流程完成"),
       },
       &workflow.TransformActivity[ApprovalRequest, ApprovalRequest]{
        Name_:       "通知请求者",
        Transformer: notifyRequester,
       },
      },
     },
    },
   },
  },
  OnComplete: func(ctx *workflow.WorkflowContext[ApprovalRequest]) {
   request := ctx.GetData()
   log.Printf("审批流程完成: 请求 %s 的最终状态为 %s\n", request.ID, request.Status)
  },
 }
 
 // 创建测试请求
 testRequest := ApprovalRequest{
  ID:          "REQ-12345",
  RequesterID: "EMP-789",
  RequestType: "报销",
  Description: "商务旅行费用",
  Amount:      5000.00,
  CreatedAt:   time.Now(),
 }
 
 // 执行工作流
 ctx := context.Background()
 result, err := approvalWorkflow.Execute(ctx, testRequest)
 
 if err != nil {
  log.Printf("审批流程执行失败: %v\n", err)
 } else {
  log.Printf("审批流程结果: 状态=%s, 当前级别=%d\n", 
   result.Status, result.CurrentLevel)
  
  // 打印审批链
  for i, step := range result.ApprovalChain {
   log.Printf("  审批步骤 %d: 级别=%d, 审批人=%s, 状态=%s\n", 
    i+1, step.Level, step.ApproverID, step.Status)
  }
 }
}
```

## 工作流模式间的关系与组合

工作流模式之间存在多种关系:

1. **组合关系**: 大多数工作流实际上是多种模式的组合。例如，一个实际工作流可能包含顺序流、条件分支、并行执行和异常处理等多种模式。

2. **嵌套关系**: 模式可以嵌套使用，如在条件分支中包含并行活动，或在重试模式中包含资源分配。

3. **互补关系**: 不同类别的模式通常互补，共同构成完整的工作流。如控制流模式决定执行顺序，数据流模式处理数据传输，资源模式管理资源。

4. **转换关系**: 某些模式可以通过特定配置转换为其他模式。例如，多选择模式可以通过特定配置变为排他选择。

通过Go语言的泛型和接口抽象，我们实现了一个灵活且类型安全的工作流引擎，支持所有主要工作流模式及其组合。此实现充分利用了Go 1.24的语言特性，提供了一个可扩展的框架，可以应用于各种业务场景。
