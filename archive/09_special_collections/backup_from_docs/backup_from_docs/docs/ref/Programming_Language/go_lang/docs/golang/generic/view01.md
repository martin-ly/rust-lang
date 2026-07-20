# Go 语言高级模式：并发、并行与工作流系统设计

本文档整合并扩展了 Go 语言中高级设计模式的实现，重点关注并发、并行处理以及工作流系统的构建。
利用 Go 1.24+ 的泛型和接口特性，旨在提供类型安全、可复用且符合 Go 语言习惯（Idiomatic）的模式实现和设计思路。

## 目录

- [Go 语言高级模式：并发、并行与工作流系统设计](#go-语言高级模式并发并行与工作流系统设计)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [Go 语言特性与模式设计](#go-语言特性与模式设计)
    - [泛型的应用价值](#泛型的应用价值)
  - [2. 并发与并行设计模式](#2-并发与并行设计模式)
    - [2.1 基础并发模式](#21-基础并发模式)
      - [2.1.1 Worker Pool 模式](#211-worker-pool-模式)
        - [Worker Pool：实现与代码示例](#worker-pool实现与代码示例)
      - [2.1.2 Pipeline 模式](#212-pipeline-模式)
        - [Pipeline：实现与代码示例](#pipeline实现与代码示例)
      - [2.1.3 Fan-Out/Fan-In 模式](#213-fan-outfan-in-模式)
        - [Fan-Out/Fan-In：实现与代码示例](#fan-outfan-in实现与代码示例)
      - [2.1.4 Future/Promise 模式](#214-futurepromise-模式)
        - [Future/Promise：实现与代码示例](#futurepromise实现与代码示例)
    - [2.2 同步模式](#22-同步模式)
      - [2.2.1 Barrier 模式](#221-barrier-模式)
        - [Barrier：实现与代码示例](#barrier实现与代码示例)
        - [泛型 Barrier (数据交换)](#泛型-barrier-数据交换)
      - [2.2.2 Mutex 模式 (扩展)](#222-mutex-模式-扩展)
        - [Mutex：实现与代码示例](#mutex实现与代码示例)
        - [泛型 Mutex (保护资源)](#泛型-mutex-保护资源)
      - [2.2.3 Read-Write Lock 模式 (扩展)](#223-read-write-lock-模式-扩展)
        - [RWLock：实现与代码示例](#rwlock实现与代码示例)
        - [泛型 RWLock (保护资源)](#泛型-rwlock-保护资源)
      - [2.2.4 Semaphore 模式](#224-semaphore-模式)
        - [Semaphore：实现与代码示例](#semaphore实现与代码示例)
        - [泛型 Semaphore (资源池)](#泛型-semaphore-资源池)
      - [2.2.5 `sync/atomic` 包的应用 (扩展讨论)](#225-syncatomic-包的应用-扩展讨论)
    - [2.3 并发控制模式](#23-并发控制模式)
      - [2.3.1 Context 模式](#231-context-模式)
        - [Context：实现与代码示例](#context实现与代码示例)
      - [2.3.2 Rate Limiting 模式](#232-rate-limiting-模式)
        - [RateLimiter：实现与代码示例 (令牌桶)](#ratelimiter实现与代码示例-令牌桶)
        - [泛型 Rate Limiter](#泛型-rate-limiter)
      - [2.3.3 Circuit Breaker 模式](#233-circuit-breaker-模式)
        - [CircuitBreaker：实现与代码示例](#circuitbreaker实现与代码示例)
        - [泛型 Circuit Breaker](#泛型-circuit-breaker)
      - [2.3.4 Bulkhead 模式](#234-bulkhead-模式)
        - [Bulkhead：实现与代码示例](#bulkhead实现与代码示例)
        - [泛型 Bulkhead](#泛型-bulkhead)
    - [2.4 消息通信模式](#24-消息通信模式)
      - [2.4.1 Publish-Subscribe 模式](#241-publish-subscribe-模式)
        - [PubSub：实现与代码示例](#pubsub实现与代码示例)
        - [异步 Publisher 与 Topic Listener](#异步-publisher-与-topic-listener)
      - [2.4.2 Actor 模式](#242-actor-模式)
        - [Actor：实现与代码示例](#actor实现与代码示例)
        - [扩展讨论：监督、层级与持久化](#扩展讨论监督层级与持久化)
      - [2.4.3 CSP (Communicating Sequential Processes) 模式](#243-csp-communicating-sequential-processes-模式)
        - [CSP：实现与代码示例 (Pipe, Mux, Demux, Filter, Map)](#csp实现与代码示例-pipe-mux-demux-filter-map)
        - [进程网络 (ProcessNetwork)](#进程网络-processnetwork)
    - [2.5 并行数据处理模式](#25-并行数据处理模式)
      - [2.5.1 Map-Reduce 模式](#251-map-reduce-模式)
        - [MapReduce：实现与代码示例](#mapreduce实现与代码示例)
        - [并发 Map-Reduce 与管道](#并发-map-reduce-与管道)
      - [2.5.2 Fork-Join 模式](#252-fork-join-模式)
        - [ForkJoin：实现与代码示例](#forkjoin实现与代码示例)
        - [递归任务 (RecursiveTask)](#递归任务-recursivetask)
        - [并行 For 与并行 Reduce](#并行-for-与并行-reduce)
    - [2.6 并发模式选择与权衡 (扩展讨论)](#26-并发模式选择与权衡-扩展讨论)
    - [2.7 分布式并发模式简介 (扩展讨论)](#27-分布式并发模式简介-扩展讨论)
  - [3. 工作流模式与系统实现](#3-工作流模式与系统实现)
    - [3.1 工作流核心概念](#31-工作流核心概念)
      - [活动 (Activity)](#活动-activity)
      - [工作流上下文 (WorkflowContext)](#工作流上下文-workflowcontext)
      - [工作流定义 (Workflow)](#工作流定义-workflow)
      - [基础架构代码](#基础架构代码)
    - [3.2 控制流模式 (Control-Flow Patterns)](#32-控制流模式-control-flow-patterns)
      - [3.2.1 顺序 (Sequence)](#321-顺序-sequence)
        - [Sequence：实现与代码示例](#sequence实现与代码示例)
      - [3.2.2 并行分支/同步 (Parallel Split/Synchronization)](#322-并行分支同步-parallel-splitsynchronization)
        - [Parallel：实现与代码示例](#parallel实现与代码示例)
      - [3.2.3 排他选择/简单合并 (Exclusive Choice/Simple Merge)](#323-排他选择简单合并-exclusive-choicesimple-merge)
        - [Condition：实现与代码示例](#condition实现与代码示例)
      - [3.2.4 多选择/同步合并 (Multi-Choice/Synchronizing Merge)](#324-多选择同步合并-multi-choicesynchronizing-merge)
        - [MultiChoice：实现与代码示例](#multichoice实现与代码示例)
      - [3.2.5 循环 (Loop)](#325-循环-loop)
        - [Loop：实现与代码示例](#loop实现与代码示例)
      - [3.2.6 多实例 (Multiple Instances)](#326-多实例-multiple-instances)
        - [MultiInstance：实现与代码示例](#multiinstance实现与代码示例)
      - [3.2.7 延迟选择 (Deferred Choice) (概念扩展)](#327-延迟选择-deferred-choice-概念扩展)
      - [3.2.8 里程碑 (Milestone) (概念扩展)](#328-里程碑-milestone-概念扩展)
    - [3.3 数据流模式 (Data-Flow Patterns)](#33-数据流模式-data-flow-patterns)
      - [3.3.1 数据传递 (Data Passing) (隐式实现)](#331-数据传递-data-passing-隐式实现)
      - [3.3.2 数据转换 (Data Transformation)](#332-数据转换-data-transformation)
        - [Transform：实现与代码示例](#transform实现与代码示例)
      - [3.3.3 数据路由 (Data-based Routing)](#333-数据路由-data-based-routing)
        - [DataRouting：实现与代码示例](#datarouting实现与代码示例)
      - [3.3.4 数据合并 (Data Aggregation)](#334-数据合并-data-aggregation)
        - [DataAggregation：实现与代码示例](#dataaggregation实现与代码示例)
      - [3.3.5 数据过滤 (Data Filter)](#335-数据过滤-data-filter)
        - [DataFilter：实现与代码示例](#datafilter实现与代码示例)
    - [3.4 资源模式 (Resource Patterns)](#34-资源模式-resource-patterns)
      - [3.4.1 资源定义与资源池 (Resource \& Pool)](#341-资源定义与资源池-resource--pool)
        - [ResourcePool：实现与代码示例](#resourcepool实现与代码示例)
      - [3.4.2 资源分配 (Resource Allocation)](#342-资源分配-resource-allocation)
        - [ResourceActivity：实现与代码示例](#resourceactivity实现与代码示例)
      - [3.4.3 角色分配 (Role-based Distribution)](#343-角色分配-role-based-distribution)
        - [RoleBased：实现与代码示例](#rolebased实现与代码示例)
      - [3.4.4 工作负载均衡 (Workload Balancing)](#344-工作负载均衡-workload-balancing)
        - [LoadBalanced：实现与代码示例](#loadbalanced实现与代码示例)
      - [3.4.5 扩展讨论：资源优先级、预留](#345-扩展讨论资源优先级预留)
    - [3.5 异常处理模式 (Exception Handling Patterns)](#35-异常处理模式-exception-handling-patterns)
      - [3.5.1 重试 (Retry)](#351-重试-retry)
        - [Retry：实现与代码示例](#retry实现与代码示例)
      - [3.5.2 超时 (Timeout)](#352-超时-timeout)
        - [Timeout：实现与代码示例](#timeout实现与代码示例)
      - [3.5.3 补偿 (Compensation)](#353-补偿-compensation)
        - [Compensation：实现与代码示例](#compensation实现与代码示例)
      - [3.5.4 取消 (Cancel)](#354-取消-cancel)
        - [Cancellable：实现与代码示例](#cancellable实现与代码示例)
      - [3.5.5 错误边界 (Error Boundary)](#355-错误边界-error-boundary)
        - [ErrorBoundary：实现与代码示例](#errorboundary实现与代码示例)
      - [3.5.6 回滚 (Rollback) (概念扩展)](#356-回滚-rollback-概念扩展)
    - [3.6 工作流示例](#36-工作流示例)
      - [3.6.1 订单处理工作流](#361-订单处理工作流)
      - [3.6.2 数据处理工作流](#362-数据处理工作流)
      - [3.6.3 审批流程工作流](#363-审批流程工作流)
    - [3.7 工作流模式间的关系与组合](#37-工作流模式间的关系与组合)
    - [3.8 工作流引擎扩展 (讨论)](#38-工作流引擎扩展-讨论)
      - [持久化与状态管理](#持久化与状态管理)
      - [事件驱动与触发器](#事件驱动与触发器)
      - [可视化与监控](#可视化与监控)
      - [Saga 模式与分布式事务](#saga-模式与分布式事务)
  - [4. 并发模式在工作流中的应用 (交叉关联)](#4-并发模式在工作流中的应用-交叉关联)
  - [5. 总结](#5-总结)
  - [6. 思维导图 (Text 格式)](#6-思维导图-text-格式)

---

## 1. 引言

### Go 语言特性与模式设计

Go 语言以其原生并发支持（goroutine 和 channel）、简洁的语法、高效的性能和强大的标准库，成为构建高性能、高并发系统的热门选择。其设计哲学强调显式、组合优于继承，这深刻影响了 Go 中设计模式的实现方式。我们倾向于使用接口来定义行为，通过组合结构体来构建复杂功能，并通过 channel 和 goroutine 来处理并发。

### 泛型的应用价值

自 Go 1.18 引入泛型以来，Go 语言在类型安全和代码复用方面获得了显著提升。在实现设计模式时，泛型允许我们：

- **编写更通用的模式实现**: 无需为不同数据类型重复编写相似的代码。
- **提高类型安全性**: 在编译时捕捉更多类型错误，减少运行时错误。
- **增强代码可读性**: 减少类型断言和 `interface{}` 的使用，使代码意图更清晰。

本文档中的所有模式实现都将利用 Go 1.24+ 的泛型特性。

---

## 2. 并发与并行设计模式

并发是指同时处理多个任务的能力，而并行是指同时执行多个任务。Go 语言的 goroutine 和 channel 为实现这些模式提供了强大的基础。

### 2.1 基础并发模式

这些模式提供了构建并发应用的基本构建块。

#### 2.1.1 Worker Pool 模式

管理一组工作协程（Worker）来处理任务队列中的任务，有效控制并发数量，避免资源耗尽。

##### Worker Pool：实现与代码示例

```go
package workerpool

import (
 "context"
 "sync"
 "sync/atomic" // 用于 IsDone 检查
)

// Task 表示可以由工作者处理的任务
type Task[T any, R any] interface {
 Execute(ctx context.Context) R // 传递上下文给任务
}

// WorkerPool 管理一组工作者协程
type WorkerPool[T any, R any] struct {
 workerCount int
 taskQueue   chan Task[T, R]
 resultQueue chan R
 wg          sync.WaitGroup
 ctx         context.Context    // 主上下文，用于启动时传递
 cancel      context.CancelFunc // 用于停止工作池
 stopped     atomic.Bool        // 标记是否已停止
}

// NewWorkerPool 创建一个新的工作池
func NewWorkerPool[T any, R any](parentCtx context.Context, workerCount int, queueSize int) *WorkerPool[T, R] {
 if workerCount <= 0 {
  workerCount = 1 // 至少一个 worker
 }
 if queueSize <= 0 {
     queueSize = workerCount // 默认队列大小
 }
 // 创建可取消的上下文，继承自父上下文
 ctx, cancel := context.WithCancel(parentCtx)

 pool := &WorkerPool[T, R]{
  workerCount: workerCount,
  taskQueue:   make(chan Task[T, R], queueSize),
  resultQueue: make(chan R, queueSize),
  ctx:         ctx,
  cancel:      cancel,
 }

 pool.start()
 return pool
}

// 启动工作池
func (wp *WorkerPool[T, R]) start() {
 for i := 0; i < wp.workerCount; i++ {
  wp.wg.Add(1)
  go func(workerID int) {
   defer wp.wg.Done()
   // fmt.Printf("Worker %d starting\n", workerID) // 调试信息
   wp.worker(workerID)
   // fmt.Printf("Worker %d stopping\n", workerID) // 调试信息
  }(i)
 }
}

// 工作者函数
func (wp *WorkerPool[T, R]) worker(id int) {
 for {
  select {
  case <-wp.ctx.Done(): // 检查工作池是否被停止
   return
  case task, ok := <-wp.taskQueue:
   if !ok { // taskQueue 被关闭
    return
   }
   // 执行任务，传递工作池的上下文
   result := task.Execute(wp.ctx)

   // 将结果发送到结果队列，同时检查工作池是否停止
   select {
   case wp.resultQueue <- result:
   case <-wp.ctx.Done():
    // 如果在发送结果时工作池停止了，则放弃发送
    return
   }
  }
 }
}

// Submit 提交任务到工作池
// 返回 false 如果工作池已停止且任务未被提交
func (wp *WorkerPool[T, R]) Submit(task Task[T, R]) bool {
 if wp.stopped.Load() {
     return false // 如果已停止，不接受新任务
 }
 select {
 case wp.taskQueue <- task:
  return true
 case <-wp.ctx.Done(): // 在尝试提交时工作池停止
  return false
 }
}

// Results 返回结果通道，用于消费处理结果
func (wp *WorkerPool[T, R]) Results() <-chan R {
 return wp.resultQueue
}

// Stop 停止工作池并等待所有工作者完成
func (wp *WorkerPool[T, R]) Stop() {
 // 使用 CAS 确保 Stop 只执行一次停止逻辑
 if wp.stopped.CompareAndSwap(false, true) {
  // fmt.Println("Stopping worker pool...") // 调试信息
  wp.cancel() // 发送停止信号给所有 worker
  close(wp.taskQueue) // 关闭任务队列，表示不再有新任务
 }
}

// Wait 等待所有工作者完成其当前任务并退出
func (wp *WorkerPool[T, R]) Wait() {
    wp.wg.Wait() // 等待所有 worker goroutine 结束
    // 此时所有 worker 已退出，可以安全关闭结果队列
    // 确保 resultQueue 只关闭一次
    // (通常由创建者在消费完所有结果后关闭，或在 Stop 后调用 Wait 再关闭)
    // 为了简化，假设在 Wait 后关闭是安全的
    // 需要额外的逻辑来防止重复关闭
    // close(wp.resultQueue) // 关闭结果队列的最佳时机取决于使用者如何消费结果
}

// Shutdown 停止接受新任务并等待所有任务完成
func (wp *WorkerPool[T, R]) Shutdown() {
    wp.Stop() // 停止接受新任务，关闭 taskQueue
    wp.Wait() // 等待 worker 完成
    // 在这里关闭结果队列是安全的
    // 需要防止重复关闭（例如，添加一个 once 标志）
    // onceCloseResult := sync.Once{}
    // onceCloseResult.Do(func() { close(wp.resultQueue) })
}


// 使用示例
type SimpleTaskImpl[T any] struct {
 Data T
 Fn   func(ctx context.Context, data T) T // 任务函数接受上下文
}

func (t SimpleTaskImpl[T]) Execute(ctx context.Context) T {
 // 任务可以在执行期间检查上下文是否取消
 select {
 case <-ctx.Done():
  // fmt.Printf("Task cancelled for data: %v\n", t.Data) // 调试信息
  var zero T
  return zero // 返回零值或特定错误指示
 default:
  return t.Fn(ctx, t.Data)
 }
}
```

#### 2.1.2 Pipeline 模式

创建一系列处理阶段（Stage），每个阶段处理数据并将结果传递给下一个阶段，形成数据流处理管道。

##### Pipeline：实现与代码示例

```go
package pipeline

import "context"

// Processor 定义了处理函数接口
type Processor[T any, R any] interface {
 Process(ctx context.Context, input T) (R, error) // 返回错误以便处理阶段失败
}

// ProcessorFunc 允许使用函数作为处理器
type ProcessorFunc[T any, R any] func(ctx context.Context, input T) (R, error)

func (pf ProcessorFunc[T, R]) Process(ctx context.Context, input T) (R, error) {
 return pf(ctx, input)
}

// PipelineStage 表示一个处理管道阶段
type PipelineStage[In any, Out any] struct {
 processor Processor[In, Out]
 name      string // 阶段名称，用于日志/错误
}

// NewPipelineStage 创建一个新的管道阶段
func NewPipelineStage[In any, Out any](name string, processor Processor[In, Out]) *PipelineStage[In, Out] {
 return &PipelineStage[In, Out]{processor: processor, name: name}
}

// Process 处理输入并返回结果
func (p *PipelineStage[In, Out]) Process(ctx context.Context, input In) (Out, error) {
 // 可以在这里添加日志或 tracing
 result, err := p.processor.Process(ctx, input)
 if err != nil {
     return result, fmt.Errorf("pipeline stage '%s' failed: %w", p.name, err)
 }
 return result, nil
}


// Stream 将管道阶段应用于输入通道并返回输出通道
// inChan: 输入数据通道
// outChan: 输出数据通道
// errChan: 错误通道
func Stream[In any, Out any](
 ctx context.Context,
 stage *PipelineStage[In, Out],
 inChan <-chan In,
 outChan chan<- Out,
 errChan chan<- error,
 wg *sync.WaitGroup, // 使用 WaitGroup 管理 goroutine 生命周期
) {
 defer wg.Done() // 通知 WaitGroup 此 goroutine 已完成

 for {
  select {
  case <-ctx.Done(): // 检查全局上下文取消
   // fmt.Printf("Stream cancelled in stage %s\n", stage.name) // 调试
   return
  case item, ok := <-inChan:
   if !ok { // 输入通道已关闭
    // fmt.Printf("Input channel closed for stage %s\n", stage.name) // 调试
    return
   }

   // 处理项目
   result, err := stage.Process(ctx, item)
   if err != nil {
    // 发送错误到错误通道，非阻塞
    select {
    case errChan <- err:
    default: // 如果错误通道阻塞，丢弃错误或采取其他策略
        // log.Printf("Error channel full, dropping error in stage %s: %v", stage.name, err)
    }
    // 发生错误后是否继续处理下一个项目取决于策略，这里选择继续
    continue
   }

   // 将结果发送到输出通道，同时检查上下文取消
   select {
   case outChan <- result:
   case <-ctx.Done():
    // fmt.Printf("Stream cancelled while sending output in stage %s\n", stage.name) // 调试
    return
   }
  }
 }
}


// BuildAndRunPipeline 构建并运行一个多阶段管道
// inputChan: 初始输入通道
// stages: 按顺序排列的 PipelineStage 实例列表
// 返回最终的输出通道和错误通道
func BuildAndRunPipeline(
    ctx context.Context,
    inputChan interface{}, // 初始输入通道 (类型为 interface{})
    stages ...interface{}, // PipelineStage 实例列表 (类型为 interface{})
) (<-chan interface{}, <-chan error) {

    if len(stages) == 0 {
        panic("pipeline must have at least one stage")
    }

    errChan := make(chan error, len(stages)) // 错误通道，带缓冲
    var wg sync.WaitGroup
    currentInputChan := inputChan // 当前阶段的输入通道

    // 动态创建和连接通道
    for i, stageIntf := range stages {
        stage, ok := stageIntf.(pipelineStageInternal) // 需要内部接口或反射
        if !ok {
            panic(fmt.Sprintf("invalid type for stage %d: expected internal pipeline stage", i))
        }

        currentOutputChan := make(chan interface{}, cap(currentInputChan.(chan interface{}))) // 创建输出通道
        wg.Add(1)

        // 启动当前阶段的 Stream goroutine
        go func(s pipelineStageInternal, in <-chan interface{}, out chan<- interface{}) {
            // Stream 函数需要适配 interface{} 或使用反射
            // 这里简化，假设有适配的 StreamInternal 函数
            StreamInternal(ctx, s, in, out, errChan, &wg)
            // 当前阶段完成后关闭其输出通道
            close(out)
        }(stage, currentInputChan.(chan interface{}), currentOutputChan)

        // 更新下一阶段的输入通道
        currentInputChan = currentOutputChan
    }

    // 启动一个 goroutine 等待所有阶段完成，然后关闭错误通道
    go func() {
        wg.Wait()
        close(errChan)
        // fmt.Println("Pipeline finished.") // 调试
    }()

    return currentInputChan.(chan interface{}), errChan // 返回最后一个阶段的输出和错误通道
}

// 内部接口或标记，用于类型断言 (或者使用反射)
type pipelineStageInternal interface {
    // 定义内部需要的方法
    getName() string
    processInternal(ctx context.Context, input interface{}) (interface{}, error)
}

// StreamInternal 的简化适配版本 (仅为示意)
func StreamInternal(ctx context.Context, stage pipelineStageInternal, inChan <-chan interface{}, outChan chan<- interface{}, errChan chan<- error, wg *sync.WaitGroup) {
     defer wg.Done()
     for {
         select {
         case <-ctx.Done(): return
         case item, ok := <-inChan:
             if !ok { return }
             result, err := stage.processInternal(ctx, item) // 调用内部处理方法
             if err != nil {
                 select { case errChan <- err: default: }
                 continue
             }
             select {
             case outChan <- result:
             case <-ctx.Done(): return
             }
         }
     }
}

// 示例：假设 Stage 结构体实现了 pipelineStageInternal 接口
func (p *PipelineStage[In, Out]) getName() string { return p.name }
func (p *PipelineStage[In, Out]) processInternal(ctx context.Context, input interface{}) (interface{}, error) {
    inTyped, ok := input.(In)
    if !ok {
        // 类型不匹配，返回错误
        var zero Out
        return zero, fmt.Errorf("pipeline stage '%s' received wrong input type: expected %T, got %T", p.name, *new(In), input)
    }
    return p.Process(ctx, inTyped)
}

// 注意：上面 BuildAndRunPipeline 的实现依赖于类型断言或反射，
// 并且为了简化示例使用了 interface{}。
// 在实际应用中，构建类型安全的、泛型的多阶段管道连接可能需要更复杂的技巧，
// 例如使用代码生成或更高级的泛型技术（如果语言支持）。
// 或者，接受一定程度的运行时类型检查。
```

#### 2.1.3 Fan-Out/Fan-In 模式

将工作分发（Fan-Out）给多个并发的处理器，然后将它们的结果合并（Fan-In）回一个流中。

##### Fan-Out/Fan-In：实现与代码示例

```go
package fanoutfanin

import (
 "context"
 "sync"
)

// Processor 定义可以并行处理数据的接口
type Processor[T any, R any] interface {
 Process(ctx context.Context, input T) (R, error) // 允许处理出错
}

// ProcessorFunc 允许使用函数作为处理器
type ProcessorFunc[T any, R any] func(ctx context.Context, input T) (R, error)

func (pf ProcessorFunc[T, R]) Process(ctx context.Context, input T) (R, error) {
 return pf(ctx, input)
}

// Result 包装结果或错误
type Result[R any] struct {
 Value R
 Err   error
}

// FanOut 将输入分发给多个并发处理器，返回结果通道数组
func FanOut[T any, R any](
 ctx context.Context,
 input <-chan T,
 processor Processor[T, R],
 workers int,
) []<-chan Result[R] { // 返回 Result 类型通道
 if workers <= 0 {
  workers = 1
 }
 outputs := make([]<-chan Result[R], workers)

 for i := 0; i < workers; i++ {
  outputs[i] = worker(ctx, input, processor)
 }

 return outputs
}

// worker 启动一个工作协程处理输入通道的数据，将结果或错误写入输出通道
func worker[T any, R any](
 ctx context.Context,
 input <-chan T,
 processor Processor[T, R],
) <-chan Result[R] {
 output := make(chan Result[R])

 go func() {
  defer close(output)
  for {
   select {
   case <-ctx.Done(): // 检查上下文取消
    return
   case item, ok := <-input:
    if !ok { // 输入通道关闭
     return
    }
    // 处理项目
    resultValue, err := processor.Process(ctx, item)
    res := Result[R]{Value: resultValue, Err: err}

    // 将结果（或错误）发送到输出通道，同时检查取消
    select {
    case output <- res:
    case <-ctx.Done():
     return
    }
   }
  }
 }()

 return output
}

// FanIn 合并多个结果通道为一个输出通道
// 只转发非错误的结果
func FanIn[R any](ctx context.Context, inputs []<-chan Result[R]) <-chan R {
 output := make(chan R)
 var wg sync.WaitGroup

 // 为每个输入通道启动一个goroutine来转发数据
 for _, ch := range inputs {
  wg.Add(1)
  go func(c <-chan Result[R]) {
   defer wg.Done()
   for {
    select {
    case <-ctx.Done(): // 检查上下文取消
     return
    case res, ok := <-c:
     if !ok { // 输入通道关闭
      return
     }
     // 如果处理成功，则转发结果值
     if res.Err == nil {
      select {
      case output <- res.Value:
      case <-ctx.Done():
       return
      }
     } else {
         // 处理错误，例如记录日志
         // log.Printf("Fan-in worker encountered error: %v", res.Err)
     }
    }
   }
  }(ch)
 }

 // 启动一个goroutine，在所有输入goroutine完成后关闭输出通道
 go func() {
  wg.Wait()
  close(output)
 }()

 return output
}

// FanInWithError 合并多个结果通道为一个输出通道，同时将错误发送到错误通道
func FanInWithError[R any](ctx context.Context, inputs []<-chan Result[R]) (<-chan R, <-chan error) {
    output := make(chan R)
    errChan := make(chan error, len(inputs)) // 缓冲错误通道
    var wg sync.WaitGroup

    for _, ch := range inputs {
        wg.Add(1)
        go func(c <-chan Result[R]) {
            defer wg.Done()
            for {
                select {
                case <-ctx.Done():
                    return
                case res, ok := <-c:
                    if !ok {
                        return
                    }
                    if res.Err == nil {
                        select {
                        case output <- res.Value:
                        case <-ctx.Done():
                            return
                        }
                    } else {
                        select {
                        case errChan <- res.Err:
                        case <-ctx.Done():
                            return
                        // 如果 errChan 满了，可以考虑丢弃或阻塞
                        default: // 非阻塞发送错误
                           // log.Printf("Error channel full, dropping error in FanInWithError: %v", res.Err)
                        }
                    }
                }
            }
        }(ch)
    }

    go func() {
        wg.Wait()
        close(output)
        close(errChan)
    }()

    return output, errChan
}


// Process 执行完整的Fan-Out/Fan-In流程，忽略错误
func Process[T any, R any](
 ctx context.Context,
 input <-chan T,
 processor Processor[T, R],
 workers int,
) <-chan R {
 outputs := FanOut(ctx, input, processor, workers)
 return FanIn(ctx, outputs)
}

// ProcessWithError 执行完整的Fan-Out/Fan-In流程，并收集错误
func ProcessWithError[T any, R any](
 ctx context.Context,
 input <-chan T,
 processor Processor[T, R],
 workers int,
) (<-chan R, <-chan error) {
 outputs := FanOut(ctx, input, processor, workers)
 return FanInWithError(ctx, outputs)
}
```

#### 2.1.4 Future/Promise 模式

允许启动一个异步计算（Promise），并在稍后的某个时间点获取其结果（Future），而无需阻塞主线程。

##### Future/Promise：实现与代码示例

```go
package future

import (
 "context"
 "sync"
 "sync/atomic" // 用于 done 标志
 "errors"
 // "fmt" // 用于调试 panic
)

// Future 代表异步计算的最终结果
type Future[T any] interface {
 // Get 返回结果，如果未完成则阻塞直到完成或上下文取消
 Get(ctx context.Context) (T, error)
 // IsDone 检查计算是否完成
 IsDone() bool
 // ResultChan 返回一个通道，当计算完成时会发送结果（或错误）。
 // 注意：此通道在结果发送后会关闭。多次读取会得到零值。
 ResultChan() <-chan Result[T]
}

// Promise 用于设置Future的结果或错误
type Promise[T any] interface {
 // SetResult 设置成功结果。如果 Future 已完成，则无操作。
 SetResult(result T) bool
 // SetError 设置错误结果。如果 Future 已完成，则无操作。
 SetError(err error) bool
 // Future 获取关联的Future
 Future() Future[T]
}

// Result 封装了Future的结果或错误
type Result[T any] struct {
 Value T
 Err   error
}

// futureImpl 是Future和Promise的实现
type futureImpl[T any] struct {
 result      Result[T]
 done        atomic.Bool // 使用原子操作保证线程安全
 mu          sync.Mutex // 保护 result 字段的写入 (虽然 once 保证只写一次，但读取仍需保护?)
 resultCh    chan Result[T] // 结果通道，容量为1
 once        sync.Once // 保证结果只设置一次
}

// NewPromise 创建一个新的Promise和关联的Future
func NewPromise[T any]() (Promise[T], Future[T]) {
 f := &futureImpl[T]{
  resultCh: make(chan Result[T], 1), // 容量为1，非阻塞发送
 }
 return f, f
}

// Future 获取关联的Future
func (f *futureImpl[T]) Future() Future[T] {
 return f
}

// set 内部方法，确保结果只设置一次并返回是否成功设置
func (f *futureImpl[T]) set(res Result[T]) bool {
    resultSet := false
    f.once.Do(func() {
        f.mu.Lock() // 保护 result 写入
        f.result = res
        f.mu.Unlock()
        f.done.Store(true)
        f.resultCh <- res // 将结果发送到通道
        close(f.resultCh) // 关闭通道，表示完成
        resultSet = true
    })
    return resultSet
}


// SetResult 设置成功结果
func (f *futureImpl[T]) SetResult(result T) bool {
 return f.set(Result[T]{Value: result})
}

// SetError 设置错误结果
func (f *futureImpl[T]) SetError(err error) {
 return f.set(Result[T]{Err: err})
}

// Get 返回结果，如果未完成则阻塞直到完成或上下文取消
func (f *futureImpl[T]) Get(ctx context.Context) (T, error) {
 select {
 case res, ok := <-f.resultCh: // 尝试从结果通道读取
  if ok {
      // 通道未关闭且收到结果
      // 加锁读取共享的 result 字段是更安全的做法，即使 once 保证只写一次
      // f.mu.Lock()
      // defer f.mu.Unlock()
      // return f.result.Value, f.result.Err
      // 或者直接使用从 channel 读到的 res
      return res.Value, res.Err
  } else {
      // 通道已关闭，说明结果已设置，直接读取共享变量
      f.mu.Lock()
      defer f.mu.Unlock()
      return f.result.Value, f.result.Err
  }
 case <-ctx.Done(): // 检查上下文是否取消
  var zero T
  return zero, ctx.Err()
 }
}

// IsDone 检查计算是否完成
func (f *futureImpl[T]) IsDone() bool {
 return f.done.Load()
}

// ResultChan 返回结果通道
func (f *futureImpl[T]) ResultChan() <-chan Result[T] {
 return f.resultCh
}


// RunAsync 异步执行任务并返回Future
// fn: 要异步执行的函数，接受一个 context
func RunAsync[T any](fn func(ctx context.Context) (T, error)) Future[T] {
 promise, future := NewPromise[T]()
 // 创建一个独立的、可取消的上下文用于这个异步任务
 // 这样即使父上下文取消，任务本身也可以决定如何响应
 // 如果不需要独立取消，可以直接使用 context.Background() 或传递父上下文
 taskCtx, cancelTask := context.WithCancel(context.Background())

 go func() {
  defer cancelTask() // 确保任务 goroutine 退出时取消其上下文
  defer func() {
   if r := recover(); r != nil {
    // 如果 fn 发生 panic，将其捕获并设置为错误
    // fmt.Printf("Async task panicked: %v\n", r) // 调试信息
    // 包含堆栈信息可能更有用
    // debug.PrintStack()
    err := fmt.Errorf("async task panicked: %v", r)
    promise.SetError(err)
   }
  }()

  // 执行任务，传入任务特定的上下文
  result, err := fn(taskCtx)

  // 检查任务上下文是否在函数执行期间被取消
  // 这是一种可能的处理方式，取决于任务 fn 是否检查 ctx.Done()
  select {
  case <-taskCtx.Done():
      // 如果任务已被外部（或内部逻辑）取消，即使 fn 返回了结果，也可能需要报告取消错误
      // 这里的逻辑取决于具体需求：是优先 fn 的结果/错误，还是优先上下文的取消？
      // 假设如果上下文取消，则报告取消错误
      promise.SetError(taskCtx.Err())
  default:
      // 上下文未取消，设置 fn 的结果或错误
      if err != nil {
          promise.SetError(err)
      } else {
          promise.SetResult(result)
      }
  }

 }()

 return future
}

// AwaitAll 等待多个 Future 完成，并返回所有结果和第一个遇到的错误
func AwaitAll[T any](ctx context.Context, futures ...Future[T]) ([]T, error) {
    results := make([]T, len(futures))
    var firstErr error
    var wg sync.WaitGroup
    mu := sync.Mutex{} // 保护 firstErr 的写入

    wg.Add(len(futures))
    for i, f := range futures {
        go func(index int, fut Future[T]) {
            defer wg.Done()
            val, err := fut.Get(ctx) // 等待每个 Future 完成
            if err != nil {
                mu.Lock()
                if firstErr == nil { // 只记录第一个错误
                    firstErr = err
                }
                mu.Unlock()
                // 可以考虑在出错时取消上下文，让其他等待也尽快失败
                // cancelCtx() // 需要传递 cancel 函数
            }
            // 注意：即使出错，也可能需要存储部分结果 val (取决于需求)
            results[index] = val
        }(i, f)
    }

    wg.Wait() // 等待所有 goroutine 完成

    // 检查等待过程中上下文是否被取消
    if ctx.Err() != nil && firstErr == nil {
       return results, ctx.Err()
    }


    return results, firstErr
}
```

---

### 2.2 同步模式

同步模式用于协调多个 goroutine 对共享资源的访问。

#### 2.2.1 Barrier 模式

允许多个 goroutine 在一个同步点汇合，所有 goroutine 都到达后才能继续执行。

##### Barrier：实现与代码示例

```go
package barrier

import (
 "context"
 "sync"
 "errors"
)

// Barrier 允许goroutine在某个点同步
type Barrier interface {
 // Wait 阻塞直到所有参与者到达屏障点。
 // 返回值表示是否是最后一个到达的 goroutine (true) 或其他 (false)。
 Wait() (bool, error)
 // WaitWithContext 带有上下文的等待。
 // 如果上下文取消，返回错误。
 WaitWithContext(ctx context.Context) (bool, error)
}

// barrierImpl 实现了Barrier接口
type barrierImpl struct {
 parties     int // 需要等待的参与者数量
 count       int // 当前已到达的参与者数量
 generation  int // 用于区分不同的等待周期
 mu          sync.Mutex
 cond        *sync.Cond
}

// NewBarrier 创建一个新的barrier
func NewBarrier(parties int) Barrier {
 if parties <= 0 {
  panic("barrier parties must be positive")
 }
 b := &barrierImpl{
  parties: parties,
 }
 b.cond = sync.NewCond(&b.mu)
 return b
}

// Wait 阻塞直到所有参与者到达
func (b *barrierImpl) Wait() (bool, error) {
 b.mu.Lock()
 defer b.mu.Unlock()

 generation := b.generation

 b.count++
 if b.count < 1 || b.count > b.parties {
     // 防御性编程：检查计数器状态
     return false, errors.New("barrier internal state error: invalid count")
 }

 isLast := false
 if b.count == b.parties {
  // 最后一个到达的goroutine
  isLast = true
  b.count = 0 // 重置计数器
  b.generation++ // 进入下一代
  b.cond.Broadcast() // 唤醒所有等待的goroutine
 } else {
  // 等待直到所有goroutine到达（即 generation 改变）
  for generation == b.generation {
   b.cond.Wait()
   // 被唤醒后，重新检查条件
  }
 }

 return isLast, nil
}

// WaitWithContext 带有上下文的等待
func (b *barrierImpl) WaitWithContext(ctx context.Context) (bool, error) {
    done := make(chan struct{ isLast bool; err error }, 1)
    waiterDone := make(chan struct{}) // 用于通知等待 goroutine 退出

    go func() {
        defer close(waiterDone) // 确保 goroutine 退出时通知
        isLast, err := b.Wait()
        // 检查上下文是否在 Wait 返回后已取消
        select {
        case <-ctx.Done():
            done <- struct{ isLast bool; err error }{false, ctx.Err()}
        default:
            done <- struct{ isLast bool; err error }{isLast, err}
        }
    }()

    select {
    case res := <-done:
        return res.isLast, res.err
    case <-ctx.Done():
        // 上下文取消，需要尝试唤醒可能阻塞在 Wait() 中的 goroutine
        // 这是一个复杂的问题。一种可能是定期唤醒或使用其他同步机制。
        // 这里简单地返回错误，但可能留下悬挂的 goroutine。
        // 尝试通知 waiter goroutine 退出 (如果它还没退出的话)
        // 注意：这并不能保证 Wait() 内部的 cond.Wait() 被中断
        // <- waiterDone // 等待 waiter goroutine 确认退出（可能会阻塞）
        return false, ctx.Err()
    }
}
```

##### 泛型 Barrier (数据交换)

允许在同步点交换数据。 **注意：** 此实现为概念演示，结果传递的同步逻辑可能不完整或存在竞争条件。健壮的实现通常更复杂。

```go
package barrier

import (
 "context"
 "sync"
 "errors"
)

// GenericBarrier 泛型版本，支持在同步点交换数据
type GenericBarrier[T any] interface {
 // Exchange 在同步点交换数据。
 // 每个 goroutine 提供一个数据项，并接收所有参与者提供的数据项列表。
 Exchange(ctx context.Context, data T) ([]T, error)
}

// genericBarrierImpl 实现了GenericBarrier接口
type genericBarrierImpl[T any] struct {
 parties     int
 count       int
 generation  int
 dataStore   map[int][]T // 使用 map 按 generation 存储结果
 mu          sync.Mutex
 cond        *sync.Cond
}

// NewGenericBarrier 创建一个新的泛型barrier
func NewGenericBarrier[T any](parties int) GenericBarrier[T] {
 if parties <= 0 {
  panic("barrier parties must be positive")
 }
 b := &genericBarrierImpl[T]{
  parties:   parties,
  dataStore: make(map[int][]T),
 }
 b.cond = sync.NewCond(&b.mu)
 return b
}

// Exchange 在同步点交换数据 (带上下文)
func (b *genericBarrierImpl[T]) Exchange(ctx context.Context, data T) ([]T, error) {
    done := make(chan struct{ result []T; err error }, 1)
    waiterDone := make(chan struct{})

    go func() {
        defer close(waiterDone)
        b.mu.Lock()
        defer b.mu.Unlock()

        currentGen := b.generation

        // 将数据添加到当前 generation 的存储中
        if _, ok := b.dataStore[currentGen]; !ok {
            b.dataStore[currentGen] = make([]T, 0, b.parties)
        }
        b.dataStore[currentGen] = append(b.dataStore[currentGen], data)
        b.count++

        var resultData []T
        var exchangeErr error

        if b.count == b.parties {
            // 最后一个到达
            resultData = make([]T, len(b.dataStore[currentGen]))
            copy(resultData, b.dataStore[currentGen])
            // delete(b.dataStore, currentGen) // 清理旧数据 (可选)

            b.count = 0      // 重置计数
            b.generation++   // 进入下一代
            b.cond.Broadcast() // 唤醒其他等待者
        } else {
            // 不是最后一个，等待
            startWait := time.Now() // 用于检测可能的死锁或长时间等待
            for currentGen == b.generation {
                // 使用带超时的 Wait 或定期检查 context
                // 这里简化为直接 Wait，但在 WaitWithContext 中需要处理取消
                 waitChan := make(chan struct{})
                 go func() {
                     b.cond.Wait()
                     close(waitChan)
                 }()

                 select {
                 case <-waitChan: // 被唤醒
                     // 检查 generation 是否改变
                 case <-ctx.Done(): // 上下文取消
                     exchangeErr = ctx.Err()
                     // 需要某种方式中断 cond.Wait()，这很困难
                     // 尝试通过 Broadcast 唤醒自己？可能导致意外行为
                     // b.cond.Broadcast() // 不推荐
                     goto sendResult // 跳出循环并发送错误
                 // 可选：添加超时检测
                 // case <-time.After(someTimeout):
                 //     exchangeErr = errors.New("barrier wait timed out")
                 //     goto sendResult
                 }

                 // 如果等待时间过长，也可以认为是错误
                 if time.Since(startWait) > time.Minute*5 { // 示例超时
                     exchangeErr = errors.New("barrier wait potentially deadlocked")
                     goto sendResult
                 }
            }
            // 被唤醒，获取结果
            // 假设最后一个 goroutine 在 broadcast 前已将结果放入 dataStore
            resultData = make([]T, len(b.dataStore[currentGen]))
            copy(resultData, b.dataStore[currentGen])
            // 注意：这里获取的是上一代的结果
        }

    sendResult:
        // 检查是否需要发送错误
        if exchangeErr != nil {
            done <- struct{ result []T; err error }{nil, exchangeErr}
        } else {
            done <- struct{ result []T; err error }{resultData, nil}
        }

    }() // end of goroutine

    select {
    case res := <-done:
        return res.result, res.err
    case <-ctx.Done():
        // 外部上下文取消
        // <-waiterDone // 等待 goroutine 结束
        return nil, ctx.Err()
    }
}
```

#### 2.2.2 Mutex 模式 (扩展)

提供对标准 `sync.Mutex` 的扩展，如 `TryLock` 和带超时的锁获取。

##### Mutex：实现与代码示例

```go
package mutex

import (
 "context"
 "sync"
 "time"
)

// Mutex 扩展了标准库的互斥锁功能
type Mutex interface {
 // Lock 获取锁 (阻塞)
 Lock()
 // Unlock 释放锁
 Unlock()
 // TryLock 尝试获取锁，如果锁已被持有则立即返回 false
 TryLock() bool
 // LockWithTimeout 尝试在指定超时时间内获取锁
 LockWithTimeout(timeout time.Duration) bool
 // LockWithContext 尝试在上下文取消前获取锁
 LockWithContext(ctx context.Context) bool
}

// mutexImpl 实现Mutex接口，使用 channel 辅助实现 TryLock/Timeout/Context
type mutexImpl struct {
 mu       sync.Mutex // 底层互斥锁
 lockCh   chan struct{} // 用于模拟锁状态，容量为1
}

// NewMutex 创建一个新的互斥锁
func NewMutex() Mutex {
 m := &mutexImpl{
  lockCh: make(chan struct{}, 1), // 容量为1的通道
 }
 m.lockCh <- struct{}{} // 初始化时放入一个 token，表示锁可用
 return m
}

// Lock 获取锁
func (m *mutexImpl) Lock() {
 // 阻塞地从 channel 获取 token
 <-m.lockCh
 // 获取真正的 mutex
 m.mu.Lock()
}

// Unlock 释放锁
func (m *mutexImpl) Unlock() {
 // 先释放 mutex
 m.mu.Unlock()
 // 再将 token 放回 channel，表示锁可用
 // 使用 select 防止阻塞（理论上不应阻塞）
 select {
 case m.lockCh <- struct{}{}:
 default:
     // 如果 channel 已满，说明 Unlock 被调用次数多于 Lock
     panic("mutex unlocked when not locked")
 }
}

// TryLock 尝试获取锁，返回是否成功
func (m *mutexImpl) TryLock() bool {
 // 非阻塞地尝试从 channel 获取 token
 select {
 case <-m.lockCh:
  // 获取 token 成功，现在获取真正的 mutex
  m.mu.Lock()
  return true
 default:
  // Channel 为空，表示锁已被持有
  return false
 }
}

// LockWithTimeout 尝试在超时前获取锁
func (m *mutexImpl) LockWithTimeout(timeout time.Duration) bool {
 ctx, cancel := context.WithTimeout(context.Background(), timeout)
 defer cancel()
 return m.LockWithContext(ctx)
}

// LockWithContext 尝试在上下文取消前获取锁
func (m *mutexImpl) LockWithContext(ctx context.Context) bool {
 // 尝试从 channel 获取 token，带上上下文取消
 select {
 case <-m.lockCh:
  // 获取 token 成功，现在获取真正的 mutex
  m.mu.Lock()
  return true
 case <-ctx.Done():
  // 上下文取消或超时
  return false
 }
}
```

##### 泛型 Mutex (保护资源)

封装资源和互斥锁，提供安全的访问方法。

```go
package mutex

import "sync"

// GenericMutex 泛型版本的互斥锁，提供受保护资源的安全访问
type GenericMutex[T any] struct {
 mu       sync.Mutex
 resource T
}

// NewGenericMutex 创建一个新的泛型互斥锁
func NewGenericMutex[T any](resource T) *GenericMutex[T] {
 return &GenericMutex[T]{
  resource: resource,
 }
}

// WithLock 在持有锁的情况下执行函数，访问资源
// fn 接收资源指针，允许修改
func (g *GenericMutex[T]) WithLock(fn func(resource *T)) {
 g.mu.Lock()
 defer g.mu.Unlock()
 fn(&g.resource)
}

// WithLockResult 在持有锁的情况下执行函数并返回结果
// fn 接收资源值（拷贝），通常用于只读操作
func (g *GenericMutex[T]) WithLockResult(fn func(resource T) any) any {
 g.mu.Lock()
 defer g.mu.Unlock()
 return fn(g.resource)
}

// Get 获取受保护资源的当前值（带锁）
// 返回值的拷贝，避免外部意外修改（除非 T 是指针或引用类型）
func (g *GenericMutex[T]) Get() T {
 g.mu.Lock()
 defer g.mu.Unlock()
 return g.resource
}

// Set 设置受保护资源的新值（带锁）
func (g *GenericMutex[T]) Set(value T) {
 g.mu.Lock()
 defer g.mu.Unlock()
 g.resource = value
}

// Swap 替换受保护资源的值并返回旧值（带锁）
func (g *GenericMutex[T]) Swap(newValue T) T {
    g.mu.Lock()
    defer g.mu.Unlock()
    oldValue := g.resource
    g.resource = newValue
    return oldValue
}
```

#### 2.2.3 Read-Write Lock 模式 (扩展)

允许多个读操作并发执行，但写操作是互斥的。提供对 `sync.RWMutex` 的扩展。**注意：** `TryRLock`, `RLockWithTimeout`, `RLockWithContext` 的模拟实现较为困难且可能不健壮，推荐优先使用标准库 `sync.RWMutex` 的原生方法（Go 1.18+ `TryLock`, `TryRLock`）。

##### RWLock：实现与代码示例

```go
package rwlock

import (
 "context"
 "sync"
 "time"
)

// RWLock 读写锁接口，扩展 sync.RWMutex
type RWLock interface {
 RLock()
 RUnlock()
 Lock()
 Unlock()
 TryRLock() bool // 注意：标准库 1.18+ 已提供
 TryLock() bool  // 注意：标准库 1.18+ 已提供
 // RLockWithTimeout 带超时的读锁获取 (难以精确模拟)
 RLockWithTimeout(timeout time.Duration) bool
 LockWithTimeout(timeout time.Duration) bool
 // RLockWithContext 带上下文的读锁获取 (难以精确模拟)
 RLockWithContext(ctx context.Context) bool
 LockWithContext(ctx context.Context) bool
}

// rwLockImpl 读写锁实现 (使用标准库 RWMutex)
type rwLockImpl struct {
 mu sync.RWMutex
}

// NewRWLock 创建新的读写锁 (推荐使用标准库)
func NewRWLock() RWLock {
 return &rwLockImpl{}
}

func (rw *rwLockImpl) RLock() { rw.mu.RLock() }
func (rw *rwLockImpl) RUnlock() { rw.mu.RUnlock() }
func (rw *rwLockImpl) Lock() { rw.mu.Lock() }
func (rw *rwLockImpl) Unlock() { rw.mu.Unlock() }

// 使用 Go 1.18+ 的原生 TryRLock
func (rw *rwLockImpl) TryRLock() bool { return rw.mu.TryRLock() }
// 使用 Go 1.18+ 的原生 TryLock
func (rw *rwLockImpl) TryLock() bool { return rw.mu.TryLock() }

// RLockWithTimeout/Context 难以精确且高效地模拟 RWMutex 的行为。
// 标准库未提供。如果需要这种功能，可能需要更复杂的自定义锁或权衡。
// 以下为简化/占位实现：
func (rw *rwLockImpl) RLockWithTimeout(timeout time.Duration) bool {
 // 简化：不支持，或者尝试性地 Lock 再 Unlock 探测写锁？不可靠。
 return false // 或者 panic("not supported")
}

func (rw *rwLockImpl) LockWithTimeout(timeout time.Duration) bool {
 // 可以尝试用 goroutine + Lock + select + timer 实现，但较复杂
 // 简化：不支持
 ctx, cancel := context.WithTimeout(context.Background(), timeout)
 defer cancel()
 return rw.LockWithContext(ctx) // 复用 LockWithContext
}

func (rw *rwLockImpl) RLockWithContext(ctx context.Context) bool {
 // 简化：不支持
 return false
}

func (rw *rwLockImpl) LockWithContext(ctx context.Context) bool {
 // 使用 goroutine 尝试获取锁，并通过 select 监听上下文取消
 lockAcquired := make(chan struct{})
 go func() {
  rw.mu.Lock()
  close(lockAcquired) // 通知锁已获取
 }()

 select {
 case <-lockAcquired: // 成功获取锁
  return true
 case <-ctx.Done(): // 上下文取消
  // 锁最终会被 goroutine 获取，需要一种方式让它释放
  // 如果 goroutine 在 Lock() 阻塞，我们无法直接中断它
  // 这会导致锁被持有直到 goroutine 获取后才可能释放（如果它检查了状态）
  // 或者需要更复杂的机制来处理这种情况。
  // 简单返回 false，但可能导致锁竞争或 goroutine 泄漏。
  // 一个可能的处理是，一旦获取到锁，立即检查 ctx.Done()，如果 done 则 Unlock
  // go func() {
  //     <-lockAcquired // 等待锁获取
  //     select {
  //     case <-ctx.Done():
  //         rw.mu.Unlock() // 如果在获取后上下文已取消，则释放
  //     default:
  //         // 锁正常持有
  //     }
  // }()
  return false
 }
}
```

##### 泛型 RWLock (保护资源)

封装资源和读写锁，提供安全的读写访问方法。

```go
package rwlock

import "sync"

// GenericRWLock 泛型读写锁，保护泛型资源
type GenericRWLock[T any] struct {
 mu       sync.RWMutex
 resource T
}

// NewGenericRWLock 创建泛型读写锁
func NewGenericRWLock[T any](resource T) *GenericRWLock[T] {
 return &GenericRWLock[T]{
  resource: resource,
 }
}

// WithRLock 使用读锁执行只读操作
func (g *GenericRWLock[T]) WithRLock(fn func(resource T)) {
 g.mu.RLock()
 defer g.mu.RUnlock()
 fn(g.resource) // 传递值拷贝
}

// WithLock 使用写锁执行读写操作
func (g *GenericRWLock[T]) WithLock(fn func(resource *T)) {
 g.mu.Lock()
 defer g.mu.Unlock()
 fn(&g.resource) // 传递指针允许修改
}

// WithRLockResult 使用读锁执行只读操作并返回结果
func (g *GenericRWLock[T]) WithRLockResult(fn func(resource T) any) any {
 g.mu.RLock()
 defer g.mu.RUnlock()
 return fn(g.resource)
}

// WithLockResult 使用写锁执行读写操作并返回结果
func (g *GenericRWLock[T]) WithLockResult(fn func(resource *T) any) any {
 g.mu.Lock()
 defer g.mu.Unlock()
 return fn(&g.resource)
}

// GetRead 获取资源的只读拷贝（带读锁）
func (g *GenericRWLock[T]) GetRead() T {
 g.mu.RLock()
 defer g.mu.RUnlock()
 return g.resource // 返回拷贝
}

// SetWrite 设置资源的新值（带写锁）
func (g *GenericRWLock[T]) SetWrite(value T) {
 g.mu.Lock()
 defer g.mu.Unlock()
 g.resource = value
}

// SwapWrite 替换资源值并返回旧值（带写锁）
func (g *GenericRWLock[T]) SwapWrite(newValue T) T {
    g.mu.Lock()
    defer g.mu.Unlock()
    oldValue := g.resource
    g.resource = newValue
    return oldValue
}
```

#### 2.2.4 Semaphore 模式

控制同时访问某个特定资源的 goroutine 数量。推荐使用 `golang.org/x/sync/semaphore`。

##### Semaphore：实现与代码示例

```go
package semaphore

import (
 "context"
 "errors"
 "golang.org/x/sync/semaphore" // 推荐使用标准扩展库
)

// Semaphore 控制对有限资源的访问 (接口定义)
type Semaphore interface {
 Acquire(ctx context.Context, n int) error
 Release(n int)
 TryAcquire(n int) bool
 AvailablePermits() int // 可能无法精确实现
 MaxPermits() int
}

// ErrInvalidPermits 定义错误
var ErrInvalidPermits = errors.New("invalid number of permits requested")

// --- 使用 golang.org/x/sync/semaphore 的实现 ---
type stdSemaphoreWrapper struct {
 weight *semaphore.Weighted
 max    int64
}

// NewSemaphore 创建基于标准库的信号量 (推荐)
func NewSemaphore(maxPermits int) Semaphore {
 if maxPermits <= 0 {
  panic("semaphore max permits must be positive")
 }
 return &stdSemaphoreWrapper{
  weight: semaphore.NewWeighted(int64(maxPermits)),
  max:    int64(maxPermits),
 }
}

func (s *stdSemaphoreWrapper) Acquire(ctx context.Context, n int) error {
 if n <= 0 || int64(n) > s.max {
  return ErrInvalidPermits
 }
 return s.weight.Acquire(ctx, int64(n))
}

func (s *stdSemaphoreWrapper) Release(n int) {
 if n <= 0 {
  return
 }
 // 标准库 semaphore 会处理释放过多许可的情况 (内部计数不会超过 max)
 s.weight.Release(int64(n))
}

func (s *stdSemaphoreWrapper) TryAcquire(n int) bool {
 if n <= 0 || int64(n) > s.max {
  return false
 }
 return s.weight.TryAcquire(int64(n))
}

// AvailablePermits 标准库 semaphore 不直接提供此功能。
func (s *stdSemaphoreWrapper) AvailablePermits() int {
 // 无法精确获取，返回 -1 或 panic
 return -1 // 表示不可用
}

func (s *stdSemaphoreWrapper) MaxPermits() int {
 return int(s.max)
}
```

##### 泛型 Semaphore (资源池)

使用信号量来管理一个固定大小的资源池。

```go
package semaphore

import (
 "context"
 "sync"
 "errors"
)

// ResourcePool 使用信号量管理的泛型资源池
type ResourcePool[T any] struct {
 sem       Semaphore   // 控制访问的信号量 (推荐 NewSemaphore 实现)
 resources chan T      // 存储可用资源的通道
 max       int         // 资源池最大容量
 mu        sync.Mutex  // 保护内部状态，例如关闭标志
 closed    bool        // 标记池是否已关闭
}

// NewResourcePool 创建一个新的资源池
func NewResourcePool[T any](initialResources []T) (*ResourcePool[T], error) {
 if len(initialResources) == 0 {
  return nil, errors.New("must provide initial resources")
 }
 max := len(initialResources)
 pool := &ResourcePool[T]{
  sem:       NewSemaphore(max), // 使用上面推荐的实现
  resources: make(chan T, max),
  max:       max,
 }

 // 将初始资源放入通道
 for _, res := range initialResources {
  pool.resources <- res
 }

 return pool, nil
}

// Acquire 获取一个资源 (阻塞)
func (p *ResourcePool[T]) Acquire(ctx context.Context) (T, error) {
 p.mu.Lock()
 if p.closed {
  p.mu.Unlock()
  var zero T
  return zero, errors.New("resource pool is closed")
 }
 p.mu.Unlock()


 // 1. 获取信号量许可
 err := p.sem.Acquire(ctx, 1)
 if err != nil {
  var zero T
  return zero, err // 获取许可失败 (超时或取消)
 }

 // 2. 从通道获取资源
 // 因为已获取许可，理论上通道必有资源，但需再次检查关闭状态
 select {
 case resource, ok := <-p.resources:
     if !ok { // 通道已关闭
         // 这种情况理论上不应发生，除非 Close 实现有问题
         p.sem.Release(1) // 归还许可
         var zero T
         return zero, errors.New("resource pool channel unexpectedly closed")
     }
     return resource, nil
 case <-ctx.Done(): // 再次检查上下文
  p.sem.Release(1) // 获取了许可但上下文取消了，归还许可
  var zero T
  return zero, ctx.Err()
 }
}

// Release 归还资源到池中
func (p *ResourcePool[T]) Release(resource T) error {
 p.mu.Lock()
 if p.closed {
  p.mu.Unlock()
  // 池已关闭，资源如何处理？可以选择销毁或忽略
  // log.Printf("Pool closed, resource not released: %v", resource)
  return errors.New("resource pool is closed")
 }
 p.mu.Unlock()

 // 1. 将资源放回通道
 select {
 case p.resources <- resource:
  // 2. 释放信号量许可
  p.sem.Release(1)
  return nil
 default:
  // 通道已满，理论上不应发生
  return errors.New("failed to release resource: pool channel is unexpectedly full")
 }
}

// TryAcquire 尝试获取一个资源，非阻塞
func (p *ResourcePool[T]) TryAcquire() (T, bool) {
 p.mu.Lock()
 if p.closed {
  p.mu.Unlock()
  var zero T
  return zero, false
 }
 p.mu.Unlock()

 // 1. 尝试获取信号量许可
 if !p.sem.TryAcquire(1) {
  var zero T
  return zero, false // 没有可用许可
 }

 // 2. 尝试从通道获取资源
 select {
 case resource, ok := <-p.resources:
  if !ok { // 通道已关闭
      p.sem.Release(1)
      var zero T
      return zero, false
  }
  return resource, true
 default:
  // 获取了许可但通道为空？状态不一致
  p.sem.Release(1) // 归还许可
  var zero T
  return zero, false
 }
}

// Close 关闭资源池，不再接受归还，并可选地清理资源
func (p *ResourcePool[T]) Close(cleanup func(T)) error {
    p.mu.Lock()
    if p.closed {
        p.mu.Unlock()
        return errors.New("resource pool already closed")
    }
    p.closed = true
    close(p.resources) // 关闭资源通道，阻止新的 Release 放入
    p.mu.Unlock()

    // 等待所有信号量许可被获取并释放？或者直接清理？
    // 清理剩余资源
    if cleanup != nil {
        for resource := range p.resources { // 读取通道中剩余的资源
            cleanup(resource)
        }
    }
    // 此时信号量可能还有许可，但已无意义，因为通道已关闭

    return nil
}


// Available 返回当前可用资源数量 (可能不精确)
func (p *ResourcePool[T]) Available() int {
 p.mu.Lock()
 defer p.mu.Unlock()
 if p.closed {
     return 0
 }
 // 优先使用信号量信息
 availableSem := p.sem.AvailablePermits()
 if availableSem != -1 {
     return availableSem
 }
 // 回退检查通道长度
 return len(p.resources)
}

// MaxSize 返回资源池最大容量
func (p *ResourcePool[T]) MaxSize() int {
 return p.max
}
```

#### 2.2.5 `sync/atomic` 包的应用 (扩展讨论)

标准库的 `sync/atomic` 包提供了一系列原子操作函数（如 `AddInt64`, `CompareAndSwapInt64`, `LoadPointer`, `StorePointer` 等），用于在不使用互斥锁的情况下对基本数据类型（整数、指针）进行线程安全的操作。

**优点**:

- **性能**: 在高并发、低争用的场景下，原子操作通常比互斥锁性能更好，因为它们通常直接映射到底层 CPU 指令，避免了锁的开销和上下文切换。
- **无死锁**: 原子操作不会导致死锁。

**缺点**:

- **复杂性**: 使用原子操作构建复杂的同步逻辑（例如，需要协调多个变量的更新）比使用锁更困难，更容易出错。
- **有限类型**: 主要适用于基本类型和指针。保护复杂数据结构通常仍需要锁。

**常见应用场景**:

- **原子计数器**: 如统计请求数、错误数。
- **状态标记**: 使用原子操作安全地更新状态标志（如 `atomic.Bool` in Go 1.19+ 或 `atomic.Value`）。
- **实现无锁数据结构**: 构建如无锁队列、栈等（通常非常复杂，需要深入理解内存模型）。
- **一次性初始化**: 结合 `sync.Once` 或原子操作（如 CAS）实现单例或延迟初始化。

在选择使用原子操作还是锁时，需要权衡性能需求和代码的复杂性与可维护性。对于简单的计数或状态更新，原子操作是很好的选择。对于保护复杂数据结构或涉及多个变量的临界区，互斥锁通常更简单、更安全。

---

### 2.3 并发控制模式

这些模式用于管理和限制并发行为，以提高系统的稳定性和弹性。

#### 2.3.1 Context 模式

`context` 包是 Go 中控制 goroutine 生命周期、传递取消信号、超时和请求范围值的标准方式。

##### Context：实现与代码示例

```go
package contextpattern

import (
 "context"
 "sync"
 "time"
 "errors" // 用于错误处理
)

// Task 表示可以被取消的任务
type Task[T any] interface {
 // Execute 执行任务并返回结果，接受上下文
 Execute(ctx context.Context) (T, error)
}

// TaskFunc 允许使用函数作为任务
type TaskFunc[T any] func(ctx context.Context) (T, error)

func (tf TaskFunc[T]) Execute(ctx context.Context) (T, error) {
 return tf(ctx)
}

// ExecuteWithTimeout 在指定超时内执行任务
func ExecuteWithTimeout[T any](parentCtx context.Context, task Task[T], timeout time.Duration) (T, error) {
 // 创建带超时的子上下文
 ctx, cancel := context.WithTimeout(parentCtx, timeout)
 defer cancel() // 确保释放资源
 return task.Execute(ctx)
}

// ExecuteWithDeadline 在指定截止时间前执行任务
func ExecuteWithDeadline[T any](parentCtx context.Context, task Task[T], deadline time.Time) (T, error) {
 // 创建带截止时间的子上下文
 ctx, cancel := context.WithDeadline(parentCtx, deadline)
 defer cancel()
 return task.Execute(ctx)
}

// ParallelExecute 并行执行多个任务，任一任务出错或上下文取消则取消所有任务
func ParallelExecute[T any](parentCtx context.Context, tasks []Task[T]) ([]T, error) {
 // 创建可取消的子上下文，用于控制所有并行任务
 ctx, cancel := context.WithCancel(parentCtx)
 defer cancel() // 确保在函数退出时取消所有子任务

 results := make([]T, len(tasks))
 errChan := make(chan error, 1) // 只需捕获第一个错误
 var wg sync.WaitGroup

 for i, task := range tasks {
  wg.Add(1)
  go func(i int, t Task[T]) {
   defer wg.Done()

   // 在 goroutine 启动后立即检查上下文，避免不必要的执行
   select {
   case <-ctx.Done():
       return // 如果启动时已取消，直接返回
   default:
   }

   result, err := t.Execute(ctx) // 执行任务，传入子上下文
   if err != nil {
       // 尝试发送错误到通道，如果已有错误则忽略
       select {
       case errChan <- err:
           cancel() // 收到第一个错误后，立即取消其他任务
       case <-ctx.Done(): // 如果在发送错误时上下文已取消
       }
       return
   }

   // 存储结果（需要考虑并发安全，但这里假设索引写入是安全的）
   results[i] = result

   // 任务成功完成，检查上下文是否已被其他任务取消
   select {
   case <-ctx.Done():
       // 任务完成但上下文已取消，结果可能无效或不完整
       return
   default:
   }

  }(i, task)
 }

 // 等待所有任务完成或被取消
 wg.Wait()
 close(errChan) // 关闭错误通道

 // 检查是否有错误或父上下文是否取消
 select {
 case err := <-errChan: // 优先返回任务执行错误
    return results, err // 返回可能不完整的结果和错误
 case <-parentCtx.Done(): // 检查原始父上下文是否取消
    return results, parentCtx.Err() // 返回可能不完整的结果和父上下文错误
 default:
    // 所有任务成功完成且父上下文未取消
    return results, nil
 }
}


##### 泛型 Context Value

提供类型安全的方式在上下文中传递值。

```go
package contextpattern

import "context"

// contextKey 是用于 context.WithValue 的私有键类型，防止冲突
type contextKey string

// ValueSetter 定义了在上下文中设置特定类型值的接口
type ValueSetter[T any] interface {
    Set(ctx context.Context, val T) context.Context
}

// ValueGetter 定义了从上下文中获取特定类型值的接口
type ValueGetter[T any] interface {
    Get(ctx context.Context) (T, bool)
    MustGet(ctx context.Context) T
}

// ContextValue 结合了 Setter 和 Getter
type ContextValue[T any] interface {
    ValueSetter[T]
    ValueGetter[T]
}

// contextValueImpl 实现了 ContextValue
type contextValueImpl[T any] struct {
    key contextKey
}

// NewContextValue 创建一个新的 ContextValue 工具，使用描述性名称作为键
func NewContextValue[T any](keyName string) ContextValue[T] {
    return &contextValueImpl[T]{
        key: contextKey(keyName), // 使用字符串创建私有键
    }
}

// Set 在上下文中设置值
func (cv *contextValueImpl[T]) Set(ctx context.Context, val T) context.Context {
    return context.WithValue(ctx, cv.key, val)
}

// Get 从上下文中获取值
func (cv *contextValueImpl[T]) Get(ctx context.Context) (T, bool) {
    val, ok := ctx.Value(cv.key).(T) // 类型断言
    return val, ok
}

// MustGet 从上下文中获取值，如果不存在或类型不匹配则触发 panic
func (cv *contextValueImpl[T]) MustGet(ctx context.Context) T {
    val, ok := cv.Get(ctx)
    if !ok {
        panic("value not found in context or type mismatch for key: " + string(cv.key))
    }
    return val
}

/*
// 使用示例:
var UserIDContext = NewContextValue[string]("user_id")
var RequestIDContext = NewContextValue[int]("request_id")

func handleRequest(ctx context.Context, userID string, reqID int) {
    ctx = UserIDContext.Set(ctx, userID)
    ctx = RequestIDContext.Set(ctx, reqID)
    processRequest(ctx)
}

func processRequest(ctx context.Context) {
    userID := UserIDContext.MustGet(ctx)
    reqID, ok := RequestIDContext.Get(ctx)
    if ok {
        fmt.Printf("Processing request %d for user %s\n", reqID, userID)
    }
}
*/
```

#### 2.3.2 Rate Limiting 模式

控制操作的速率，防止系统过载。令牌桶算法是常用实现。

##### RateLimiter：实现与代码示例 (令牌桶)

```go
package ratelimiter

import (
 "context"
 "sync"
 "time"
 "errors" // 用于错误
)

// RateLimiter 限制操作的速率
type RateLimiter interface {
 // Allow 检查是否允许立即执行操作。如果允许，则消耗一个令牌。
 Allow() bool
 // Wait 等待直到操作被允许执行，或上下文取消。
 Wait(ctx context.Context) error
 // Reserve 尝试预留一个操作许可。返回需要等待的时间。
 // 如果立即可用，等待时间为 0。
 Reserve(ctx context.Context) (time.Duration, error)
 // SetRate 动态调整速率 (每秒令牌数)
 SetRate(rate float64)
 // SetBurst 动态调整桶容量 (最大并发/突发量)
 SetBurst(burst int)
}

// TokenBucketLimiter 使用令牌桶算法实现速率限制
type TokenBucketLimiter struct {
 rate       float64     // 每秒产生的令牌数
 capacity   float64     // 桶容量 (burst size)
 tokens     float64     // 当前令牌数
 lastUpdate time.Time   // 上次更新时间
 mu         sync.Mutex  // 互斥锁保护内部状态
}

// NewTokenBucketLimiter 创建一个新的令牌桶限制器
// rate: 每秒允许的操作数
// burst: 桶的容量，即允许的最大突发操作数
func NewTokenBucketLimiter(rate float64, burst int) *TokenBucketLimiter {
 if rate <= 0 || burst <= 0 {
  panic("rate and burst must be positive")
 }
 return &TokenBucketLimiter{
  rate:       rate,
  capacity:   float64(burst),
  tokens:     float64(burst), // 初始时桶是满的
  lastUpdate: time.Now(),
 }
}

// update 更新令牌数量 (非线程安全，需要在锁内调用)
func (tb *TokenBucketLimiter) update(now time.Time) {
 elapsed := now.Sub(tb.lastUpdate).Seconds()
 if elapsed > 0 {
    newTokens := elapsed * tb.rate
    tb.tokens = tb.tokens + newTokens
    if tb.tokens > tb.capacity {
        tb.tokens = tb.capacity // 不超过容量
    }
    tb.lastUpdate = now
 }
}


// Allow 检查是否允许立即执行操作
func (tb *TokenBucketLimiter) Allow() bool {
 tb.mu.Lock()
 defer tb.mu.Unlock()

 now := time.Now()
 tb.update(now) // 更新令牌

 if tb.tokens >= 1 {
  tb.tokens-- // 消耗一个令牌
  return true
 }

 return false // 令牌不足
}

// Wait 等待直到操作被允许执行，或上下文取消
func (tb *TokenBucketLimiter) Wait(ctx context.Context) error {
 tb.mu.Lock()
 now := time.Now()
 tb.update(now)

 // 检查是否立即可用
 if tb.tokens >= 1 {
  tb.tokens--
  tb.mu.Unlock()
  return nil
 }

 // 计算需要多少令牌以及需要等待多久
 tokensNeeded := 1.0 - tb.tokens
 waitDuration := time.Duration(tokensNeeded / tb.rate * float64(time.Second))
 tb.mu.Unlock() // 释放锁，准备等待

 // 创建定时器
 timer := time.NewTimer(waitDuration)
 defer timer.Stop() // 确保定时器资源被释放

 select {
 case <-timer.C: // 等待时间到
  // 再次尝试获取 (理论上此时应该可用，但可能有并发竞争或计时误差)
  // 为避免复杂重试逻辑，这里假设等待后即可获取
  // 实际生产代码可能需要循环检查 Allow()
  // 或者使用 Reserve 获取精确等待时间
  if tb.Allow() { // 再次调用 Allow 来消耗令牌
      return nil
  }
  // 如果 Allow 失败（极小概率），返回错误
  return errors.New("rate limiter wait completed but token acquisition failed unexpectedly")
 case <-ctx.Done(): // 上下文取消
  return ctx.Err()
 }
}

// Reserve 尝试预留一个操作许可
func (tb *TokenBucketLimiter) Reserve(ctx context.Context) (time.Duration, error) {
    tb.mu.Lock()
    now := time.Now()
    tb.update(now)

    if tb.tokens >= 1 {
        tb.tokens--
        tb.mu.Unlock()
        return 0, nil // 立即可用
    }

    // 计算需要等待的时间
    tokensNeeded := 1.0 - tb.tokens
    waitDuration := time.Duration(tokensNeeded / tb.rate * float64(time.Second))
    tb.mu.Unlock() // 释放锁

    // 检查等待时间是否超过上下文的 deadline (如果存在)
    if deadline, ok := ctx.Deadline(); ok {
        if now.Add(waitDuration).After(deadline) {
            return 0, context.DeadlineExceeded // 等待时间超过 deadline
        }
    }

    return waitDuration, nil
}


// SetRate 动态调整速率
func (tb *TokenBucketLimiter) SetRate(rate float64) {
 if rate <= 0 {
  return // 或者 panic/返回错误
 }
 tb.mu.Lock()
 defer tb.mu.Unlock()

 now := time.Now()
 tb.update(now) // 更新当前令牌数
 tb.rate = rate
}

// SetBurst 动态调整桶容量
func (tb *TokenBucketLimiter) SetBurst(burst int) {
 if burst <= 0 {
     return
 }
 tb.mu.Lock()
 defer tb.mu.Unlock()

 now := time.Now()
 tb.update(now) // 更新当前令牌数
 tb.capacity = float64(burst)
 // 如果当前令牌数超过新容量，调整为新容量
 if tb.tokens > tb.capacity {
     tb.tokens = tb.capacity
 }
}

// --- 推荐使用 golang.org/x/time/rate ---
// 标准扩展库提供了更完善和高效的实现。
// import "golang.org/x/time/rate"
// func ExampleUsage() {
//     limiter := rate.NewLimiter(rate.Limit(10), 5) // 每秒10个事件，允许5个突发
//     ctx := context.Background()
//     if err := limiter.Wait(ctx); err != nil {
//         // 处理错误
//     }
//     // 执行操作
//
//     if limiter.Allow() {
//         // 执行操作
//     }
// }
```

##### 泛型 Rate Limiter

包装速率限制器，用于限制泛型函数的执行速率。

```go
package ratelimiter

import (
 "context"
 // "golang.org/x/time/rate" // 假设使用标准库 limiter
)

// GenericRateLimiter 泛型速率限制器
type GenericRateLimiter[T any] struct {
 // 使用接口，可以适配不同的限流器实现
 limiter RateLimiter
 // 或者直接使用标准库 limiter:
 // limiter *rate.Limiter
}

// NewGenericRateLimiter 创建泛型速率限制器
func NewGenericRateLimiter[T any](limiter RateLimiter) *GenericRateLimiter[T] {
 return &GenericRateLimiter[T]{limiter: limiter}
}

/*
// 使用标准库的构造函数示例
func NewGenericStdRateLimiter[T any](r rate.Limit, b int) *GenericRateLimiter[T] {
    return &GenericRateLimiter[T]{
        limiter: rate.NewLimiter(r, b), // 需要适配接口或直接使用 rate.Limiter
    }
}
*/

// Execute 在速率限制下执行函数
// fn: 要执行的目标函数
// 返回函数结果和可能由限流器或上下文产生的错误
func (g *GenericRateLimiter[T]) Execute(ctx context.Context, fn func() (T, error)) (T, error) {
 // 等待许可
 err := g.limiter.Wait(ctx) // 或者使用 limiter.Wait(ctx) 如果直接用标准库
 if err != nil {
  var zero T
  return zero, err // 返回等待错误 (如 context canceled)
 }

 // 执行目标函数
 return fn()
}

// TryExecute 尝试立即执行函数，如果速率允许
// 如果不允许，则返回错误 ErrRateLimitExceeded (需要定义)
func (g *GenericRateLimiter[T]) TryExecute(fn func() (T, error)) (T, error) {
    if g.limiter.Allow() { // 或者 limiter.Allow()
        return fn()
    }
    var zero T
    return zero, ErrRateLimitExceeded // 需要定义此错误
}

// ErrRateLimitExceeded 定义速率限制错误
var ErrRateLimitExceeded = errors.New("rate limit exceeded")

```

#### 2.3.3 Circuit Breaker 模式

防止应用程序重复尝试执行可能失败的操作，允许下游服务恢复。

##### CircuitBreaker：实现与代码示例

```go
package circuitbreaker

import (
 "errors"
 "sync"
 "time"
 "sync/atomic" // 用于状态计数
)

// CircuitState 表示断路器的状态
type CircuitState int32 // 使用 int32 以便原子操作

const (
 // StateClosed 闭合状态，允许请求通过
 StateClosed CircuitState = iota
 // StateOpen 打开状态，阻断所有请求
 StateOpen
 // StateHalfOpen 半开状态，允许有限请求用于测试下游服务是否恢复
 StateHalfOpen
)

// String 方法用于打印状态
func (s CircuitState) String() string {
    switch s {
    case StateClosed: return "Closed"
    case StateOpen: return "Open"
    case StateHalfOpen: return "HalfOpen"
    default: return "Unknown"
    }
}

// CircuitBreaker 断路器接口
type CircuitBreaker interface {
 // Execute 执行操作。如果断路器打开，则返回 ErrCircuitOpen。
 Execute(ctx context.Context, operation func() (interface{}, error)) (interface{}, error)
 // GetState 获取当前状态
 GetState() CircuitState
 // Reset 手动重置断路器到闭合状态
 Reset()
 // AddListener 添加状态变化监听器 (可选扩展)
 // AddListener(listener func(oldState, newState CircuitState))
}

// Options 断路器配置选项
type Options struct {
 // FailureThreshold 连续失败多少次后打开断路器
 FailureThreshold uint32
 // ResetTimeout 断路器打开后，经过多长时间尝试进入半开状态
 ResetTimeout time.Duration
 // HalfOpenSuccessThreshold 在半开状态下，需要多少次连续成功才能完全闭合
 HalfOpenSuccessThreshold uint32
 // IsSuccessful 判断操作是否成功 (可选，默认 err == nil)
 IsSuccessful func(result interface{}, err error) bool
 // IsFailure 判断错误是否应计入失败次数 (可选，默认 err != nil)
 IsFailure func(err error) bool
 // OnStateChange 状态变化时的回调 (可选)
 OnStateChange func(oldState, newState CircuitState)
}

// DefaultOptions 默认配置
var DefaultOptions = Options{
 FailureThreshold:          5,
 ResetTimeout:            10 * time.Second,
 HalfOpenSuccessThreshold: 1,
}

// circuitBreakerImpl 断路器实现
type circuitBreakerImpl struct {
 options         Options
 state           atomic.Int32 // 当前状态 (使用原子类型)
 consecutiveFailures atomic.Uint32 // 连续失败次数
 consecutiveSuccesses atomic.Uint32 // 半开状态下的连续成功次数
 lastStateChange atomic.Int64 // 上次状态改变时间 (Unix Nano)
 mu              sync.Mutex   // 用于保护状态转换逻辑的临界区
}

// NewCircuitBreaker 创建新的断路器
func NewCircuitBreaker(opts Options) CircuitBreaker {
 // 设置默认值
 if opts.FailureThreshold == 0 { opts.FailureThreshold = DefaultOptions.FailureThreshold }
 if opts.ResetTimeout == 0 { opts.ResetTimeout = DefaultOptions.ResetTimeout }
 if opts.HalfOpenSuccessThreshold == 0 { opts.HalfOpenSuccessThreshold = DefaultOptions.HalfOpenSuccessThreshold }
 if opts.IsFailure == nil { opts.IsFailure = func(err error) bool { return err != nil }}
 if opts.IsSuccessful == nil { opts.IsSuccessful = func(res interface{}, err error) bool { return err == nil }}


 cb := &circuitBreakerImpl{
  options: opts,
 }
 cb.state.Store(int32(StateClosed))
 cb.lastStateChange.Store(time.Now().UnixNano())
 return cb
}

// GetState 获取当前状态
func (cb *circuitBreakerImpl) GetState() CircuitState {
 return CircuitState(cb.state.Load())
}

// Reset 手动重置断路器到闭合状态
func (cb *circuitBreakerImpl) Reset() {
 cb.mu.Lock() // 保护状态重置
 oldState := CircuitState(cb.state.Swap(int32(StateClosed)))
 cb.consecutiveFailures.Store(0)
 cb.consecutiveSuccesses.Store(0)
 cb.lastStateChange.Store(time.Now().UnixNano())
 cb.mu.Unlock() // 解锁前调用回调

 if oldState != StateClosed && cb.options.OnStateChange != nil {
     go cb.options.OnStateChange(oldState, StateClosed) // 异步调用回调
 }
}

// allowRequest 检查是否允许请求通过 (核心逻辑)
func (cb *circuitBreakerImpl) allowRequest() bool {
 currentState := CircuitState(cb.state.Load())

 switch currentState {
 case StateClosed:
  return true
 case StateOpen:
  // 检查是否应该过渡到 HalfOpen
  lastChange := time.Unix(0, cb.lastStateChange.Load())
  if time.Since(lastChange) > cb.options.ResetTimeout {
      // 尝试将状态从 Open 转换为 HalfOpen
      if cb.state.CompareAndSwap(int32(StateOpen), int32(StateHalfOpen)) {
          // 转换成功，重置半开计数器
          cb.consecutiveSuccesses.Store(0)
          if cb.options.OnStateChange != nil {
              go cb.options.OnStateChange(StateOpen, StateHalfOpen)
          }
          return true // 允许第一个半开请求
      }
      // 如果 CAS 失败，说明其他 goroutine 已改变状态，重新加载状态并判断
      // 简单起见，这里假设转换成功或保持 Open
      return cb.state.Load() == int32(StateHalfOpen)
  }
  return false // 仍在 Open 状态的超时时间内
 case StateHalfOpen:
  // 半开状态总是允许请求（由 Execute 控制次数）
  return true
 default:
  // 未知状态，保守起见，不允许
  return false
 }
}

// Execute 执行操作
func (cb *circuitBreakerImpl) Execute(ctx context.Context, operation func() (interface{}, error)) (interface{}, error) {
 if !cb.allowRequest() {
  return nil, ErrCircuitOpen // 断路器打开或仍在 Open 超时内
 }

 // 在半开状态下，我们需要限制并发执行（通常只允许一个）
 // 这可以通过额外的锁或信号量实现，这里简化处理
 // 假设 allowRequest() 返回 true 就执行

 // 执行操作
 // 需要处理 operation 可能的 panic
 var result interface{}
 var err error
 panicErr := func() (panicRec interface{}) {
     defer func() {
         panicRec = recover()
     }()
     result, err = operation()
     return
 }()

 if panicErr != nil {
     // 操作 panic，视为失败
     cb.recordFailure()
     return nil, fmt.Errorf("circuit breaker operation panicked: %v", panicErr)
 }

 // 根据结果记录成功或失败
 cb.recordResult(result, err)

 return result, err
}

// recordResult 根据操作结果更新断路器状态
func (cb *circuitBreakerImpl) recordResult(result interface{}, err error) {
    isFailure := cb.options.IsFailure(err) // 检查是否是计数的失败
    isSuccess := cb.options.IsSuccessful(result, err) // 检查是否是成功

    currentState := CircuitState(cb.state.Load())

    if isFailure {
        cb.recordFailure()
    } else if isSuccess {
        cb.recordSuccess(currentState)
    }
    // 如果既不是明确的成功也不是失败，状态可能不更新
}

// recordFailure 处理失败情况
func (cb *circuitBreakerImpl) recordFailure() {
    currentState := CircuitState(cb.state.Load())

    switch currentState {
    case StateClosed:
        newFailures := cb.consecutiveFailures.Add(1)
        if newFailures >= cb.options.FailureThreshold {
            // 失败次数达到阈值，尝试转换为 Open
            if cb.state.CompareAndSwap(int32(StateClosed), int32(StateOpen)) {
                cb.lastStateChange.Store(time.Now().UnixNano())
                if cb.options.OnStateChange != nil {
                    go cb.options.OnStateChange(StateClosed, StateOpen)
                }
            }
        }
    case StateHalfOpen:
        // 半开状态下任何失败都立即转回 Open
        if cb.state.CompareAndSwap(int32(StateHalfOpen), int32(StateOpen)) {
            cb.lastStateChange.Store(time.Now().UnixNano())
            if cb.options.OnStateChange != nil {
                 go cb.options.OnStateChange(StateHalfOpen, StateOpen)
            }
        }
    // case StateOpen: // Open 状态不处理失败记录
    }
}

// recordSuccess 处理成功情况
func (cb *circuitBreakerImpl) recordSuccess(currentState CircuitState) {
    switch currentState {
    case StateClosed:
        // 在关闭状态，成功会重置失败计数器 (如果计数器大于0)
        if cb.consecutiveFailures.Load() > 0 {
            cb.consecutiveFailures.Store(0)
        }
    case StateHalfOpen:
        newSuccesses := cb.consecutiveSuccesses.Add(1)
        if newSuccesses >= cb.options.HalfOpenSuccessThreshold {
            // 半开状态下成功次数达到阈值，尝试转换为 Closed
            if cb.state.CompareAndSwap(int32(StateHalfOpen), int32(StateClosed)) {
                cb.consecutiveFailures.Store(0) // 重置失败计数
                cb.lastStateChange.Store(time.Now().UnixNano())
                if cb.options.OnStateChange != nil {
                    go cb.options.OnStateChange(StateHalfOpen, StateClosed)
                }
            }
        }
    // case StateOpen: // Open 状态不处理成功记录
    }
}


// ErrCircuitOpen 断路器打开错误
var ErrCircuitOpen = errors.New("circuit breaker is open")
```

##### 泛型 Circuit Breaker

包装断路器，用于保护泛型函数的调用。

```go
package circuitbreaker

import "context"

// GenericCircuitBreaker 泛型断路器
type GenericCircuitBreaker[T any] struct {
 breaker CircuitBreaker
}

// NewGenericCircuitBreaker 创建泛型断路器
func NewGenericCircuitBreaker[T any](options Options) *GenericCircuitBreaker[T] {
 return &GenericCircuitBreaker[T]{
  breaker: NewCircuitBreaker(options),
 }
}

// Execute 执行受断路器保护的操作
func (gcb *GenericCircuitBreaker[T]) Execute(ctx context.Context, operation func() (T, error)) (T, error) {
 resultIntf, err := gcb.breaker.Execute(ctx, func() (interface{}, error) {
  return operation() // 调用原始的泛型函数
 })

 if err != nil {
  var zero T
  // 如果错误是 ErrCircuitOpen，直接返回
  if errors.Is(err, ErrCircuitOpen) {
      return zero, err
  }
  // 如果是 panic 错误或其他执行错误
  return zero, err
 }

 // 类型断言结果
 result, ok := resultIntf.(T)
 if !ok {
     // 类型断言失败，这通常表示 operation 的返回值类型与预期不符
     var zero T
     // 可能需要返回一个特定的类型错误
     return zero, fmt.Errorf("circuit breaker operation returned unexpected type: %T", resultIntf)
 }

 return result, nil
}

// GetState 获取底层断路器的状态
func (gcb *GenericCircuitBreaker[T]) GetState() CircuitState {
    return gcb.breaker.GetState()
}

// Reset 重置底层断路器
func (gcb *GenericCircuitBreaker[T]) Reset() {
    gcb.breaker.Reset()
}
```

#### 2.3.4 Bulkhead 模式

将系统资源（如连接池、线程池）隔离成不同的部分，限制每个部分的并发量，防止一个部分的故障或过载影响整个系统。

##### Bulkhead：实现与代码示例

```go
package bulkhead

import (
 "context"
 "errors"
 "sync"
 "sync/atomic" // 用于并发计数
)

// Bulkhead 将系统隔离成不同部分，限制每个部分的并发执行数
type Bulkhead interface {
 // Execute 执行操作。如果达到并发限制且队列已满（或无队列），则阻塞或返回错误。
 Execute(ctx context.Context, operation func() (interface{}, error)) (interface{}, error)
 // TryExecute 尝试执行操作。如果达到并发限制，则立即返回错误。
 TryExecute(operation func() (interface{}, error)) (interface{}, error)
 // GetAvailableConcurrency 获取当前可用的并发槽数量
 GetAvailableConcurrency() int64
 // GetMaxConcurrency 获取最大并发数
 GetMaxConcurrency() int64
}

// bulkheadImpl Bulkhead 实现 (使用信号量)
type bulkheadImpl struct {
 sem            *semaphore.Weighted // 使用标准库信号量控制并发
 maxConcurrency int64             // 最大并发数
}

// NewBulkhead 创建新的 Bulkhead (基于信号量)
func NewBulkhead(maxConcurrency int64) Bulkhead {
 if maxConcurrency <= 0 {
  panic("maxConcurrency must be positive")
 }
 return &bulkheadImpl{
  sem:            semaphore.NewWeighted(maxConcurrency),
  maxConcurrency: maxConcurrency,
 }
}

// Execute 执行操作，阻塞等待许可
func (b *bulkheadImpl) Execute(ctx context.Context, operation func() (interface{}, error)) (interface{}, error) {
 // 获取许可，如果 ctx 取消则返回错误
 err := b.sem.Acquire(ctx, 1)
 if err != nil {
  return nil, err // 通常是 context.Canceled 或 context.DeadlineExceeded
 }
 // 确保释放许可
 defer b.sem.Release(1)

 // 执行操作
 // 处理 operation 可能的 panic
 var result interface{}
 var opErr error
 panicErr := func() (panicRec interface{}) {
     defer func() {
         panicRec = recover()
     }()
     result, opErr = operation()
     return
 }()

 if panicErr != nil {
     return nil, fmt.Errorf("bulkhead operation panicked: %v", panicErr)
 }

 return result, opErr
}

// TryExecute 尝试执行操作，非阻塞
func (b *bulkheadImpl) TryExecute(operation func() (interface{}, error)) (interface{}, error) {
 // 尝试获取许可
 if !b.sem.TryAcquire(1) {
  return nil, ErrBulkheadFull // 达到并发限制
 }
 // 确保释放许可
 defer b.sem.Release(1)

 // 执行操作 (同样需要处理 panic)
 var result interface{}
 var opErr error
 panicErr := func() (panicRec interface{}) {
     defer func() {
         panicRec = recover()
     }()
     result, opErr = operation()
     return
 }()

 if panicErr != nil {
     return nil, fmt.Errorf("bulkhead operation panicked: %v", panicErr)
 }
 return result, opErr
}


// GetAvailableConcurrency 获取当前可用的并发槽数量 (近似值)
// 注意：标准库 semaphore 不直接提供可用数量，需要自行维护或不提供
func (b *bulkheadImpl) GetAvailableConcurrency() int64 {
 // 无法精确获取，返回 -1 或估算
 return -1 // 表示不可用
 // 或者可以维护一个 atomic counter，但这会增加复杂性
}

// GetMaxConcurrency 获取最大并发数
func (b *bulkheadImpl) GetMaxConcurrency() int64 {
 return b.maxConcurrency
}

// ErrBulkheadFull Bulkhead 已满错误 (用于 TryExecute)
var ErrBulkheadFull = errors.New("bulkhead capacity is full")

// BulkheadWithQueue 带等待队列的 Bulkhead 实现 (更复杂)
type bulkheadWithQueueImpl struct {
    sem            *semaphore.Weighted // 控制并发执行
    maxConcurrency int64
    waitQueue      chan func() (interface{}, error) // 等待队列
    queueSize      int
    mu             sync.Mutex // 保护内部状态
    activeWorkers  int32 // 跟踪活跃 worker 数量
    stopCh         chan struct{} // 用于停止 worker
    wg             sync.WaitGroup // 等待 worker 停止
}

// NewBulkheadWithQueue 创建带队列的 Bulkhead
func NewBulkheadWithQueue(maxConcurrency, queueSize int) *bulkheadWithQueueImpl {
    if maxConcurrency <= 0 || queueSize < 0 {
        panic("maxConcurrency must be positive, queueSize must be non-negative")
    }
    b := &bulkheadWithQueueImpl{
        sem:            semaphore.NewWeighted(int64(maxConcurrency)),
        maxConcurrency: int64(maxConcurrency),
        waitQueue:      make(chan func() (interface{}, error), queueSize),
        queueSize:      queueSize,
        stopCh:         make(chan struct{}),
    }
    // 启动 worker 来处理等待队列中的任务
    // b.startWorkers() // 需要实现 startWorkers 逻辑
    return b
}

// Execute (带队列的版本)
func (b *bulkheadWithQueueImpl) Execute(ctx context.Context, operation func() (interface{}, error)) (interface{}, error) {
    // 尝试非阻塞地将任务放入队列
    select {
    case b.waitQueue <- operation:
        // 任务已放入队列，由 worker 处理
        // 需要一种方式获取结果 (例如，operation 返回 Future 或使用结果通道)
        // 这里简化，假设不需要直接返回结果
        return nil, nil // 表示任务已排队
    default:
        // 队列已满
        return nil, ErrBulkheadQueueFull // 需要定义此错误
    }
}
// TryExecute (带队列的版本)
func (b *bulkheadWithQueueImpl) TryExecute(operation func() (interface{}, error)) (interface{}, error) {
    // 尝试获取信号量许可
    if b.sem.TryAcquire(1) {
        defer b.sem.Release(1)
        // 直接执行
        // ... (panic handling) ...
        return operation()
    }
    return nil, ErrBulkheadFull
}
// 其他方法 (GetAvailableConcurrency, GetMaxConcurrency, startWorkers, Stop) 需要相应实现

var ErrBulkheadQueueFull = errors.New("bulkhead queue is full")

```

##### 泛型 Bulkhead

包装 Bulkhead，用于限制泛型函数的并发执行。

```go
package bulkhead

import "context"

// GenericBulkhead 泛型Bulkhead
type GenericBulkhead[T any] struct {
 bulkhead Bulkhead
}

// NewGenericBulkhead 创建泛型Bulkhead
func NewGenericBulkhead[T any](maxConcurrency int64) *GenericBulkhead[T] {
 // 可以选择创建哪种类型的 Bulkhead 实现
 return &GenericBulkhead[T]{
  bulkhead: NewBulkhead(maxConcurrency), // 使用基于信号量的版本
 }
}

// NewGenericBulkheadWithQueue 创建带队列的泛型 Bulkhead
// func NewGenericBulkheadWithQueue[T any](maxConcurrency, queueSize int) *GenericBulkhead[T] {
//     return &GenericBulkhead[T]{
//         bulkhead: NewBulkheadWithQueue(maxConcurrency, queueSize),
//     }
// }

// Execute 执行受 Bulkhead 保护的操作
func (gb *GenericBulkhead[T]) Execute(ctx context.Context, operation func() (T, error)) (T, error) {
 resultIntf, err := gb.bulkhead.Execute(ctx, func() (interface{}, error) {
  return operation()
 })

 if err != nil {
  var zero T
  return zero, err // 包括 ErrBulkheadFull, ErrBulkheadQueueFull, ctx.Err() 等
 }

 // 类型断言
 result, ok := resultIntf.(T)
 if !ok && resultIntf != nil { // 如果 Execute 返回 nil, nil (例如排队成功)，则 ok 会是 false
     // 处理类型断言失败
     var zero T
     return zero, fmt.Errorf("bulkhead operation returned unexpected type: %T", resultIntf)
 }
 return result, nil
}

// TryExecute 尝试执行受 Bulkhead 保护的操作
func (gb *GenericBulkhead[T]) TryExecute(operation func() (T, error)) (T, error) {
 resultIntf, err := gb.bulkhead.TryExecute(func() (interface{}, error) {
  return operation()
 })

 if err != nil {
  var zero T
  // 主要是 ErrBulkheadFull
  return zero, err
 }

 // 类型断言
 result, ok := resultIntf.(T)
 if !ok {
     var zero T
     return zero, fmt.Errorf("bulkhead operation returned unexpected type: %T", resultIntf)
 }
 return result, nil
}

// GetAvailableConcurrency 获取可用并发数
func (gb *GenericBulkhead[T]) GetAvailableConcurrency() int64 {
    return gb.bulkhead.GetAvailableConcurrency()
}

// GetMaxConcurrency 获取最大并发数
func (gb *GenericBulkhead[T]) GetMaxConcurrency() int64 {
    return gb.bulkhead.GetMaxConcurrency()
}
```

---

### 2.4 消息通信模式

这些模式关注于 goroutine 或进程之间如何交换信息。

#### 2.4.1 Publish-Subscribe 模式

允许消息发布者将消息发送给零个或多个订阅者，而无需知道订阅者的具体身份。

##### PubSub：实现与代码示例

```go
package pubsub

import (
 // "context" // 在异步版本中可能需要
 "sync"
 "fmt" // 用于生成 ID
)

// Event 表示可以发布的事件
type Event[T any] struct {
 Topic   string
 Payload T
}

// Subscriber 表示订阅者接口
type Subscriber[T any] interface {
 // OnEvent 当事件发生时被调用
 OnEvent(event Event[T])
 // ID 返回订阅者的唯一标识符 (可选，用于精确取消订阅)
 // ID() string
}

// SubscriberFunc 允许使用函数作为订阅者
type SubscriberFunc[T any] func(event Event[T])

func (sf SubscriberFunc[T]) OnEvent(event Event[T]) {
 sf(event)
}

// Subscription 代表一个具体的订阅关系，用于取消
type Subscription interface {
    Unsubscribe()
    Topic() string
    // ID() string // 可选的唯一 ID
}

// Publisher 发布者接口
type Publisher[T any] interface {
 // Publish 发布事件到指定主题
 Publish(topic string, payload T)
 // Subscribe 订阅主题，返回一个 Subscription 用于取消
 Subscribe(topic string, subscriber Subscriber[T]) (Subscription, error)
 // SubscribeFunc 订阅主题的便捷方法，使用函数作为处理器
 SubscribeFunc(topic string, handler func(Event[T])) (Subscription, error)
 // Unsubscribe(subID string) // 旧的取消方式，可以用 Subscription.Unsubscribe() 替代
}

// pubSubImpl 发布-订阅实现
type pubSubImpl[T any] struct {
 // 使用 map[topic]map[subscriberID]subscriber 更安全
 subscribers map[string]map[uintptr]Subscriber[T] // 主题 -> 订阅者指针地址 -> 订阅者
 mu          sync.RWMutex
 idCounter   uintptr // 使用 uintptr 作为简单的唯一 ID
}

// subscriptionImpl 实现 Subscription 接口
type subscriptionImpl[T any] struct {
    publisher *pubSubImpl[T]
    topic     string
    subID     uintptr // 使用订阅者的指针地址作为 ID
}

func (s *subscriptionImpl[T]) Unsubscribe() {
    s.publisher.unsubscribeByID(s.topic, s.subID)
}
func (s *subscriptionImpl[T]) Topic() string { return s.topic }
// func (s *subscriptionImpl[T]) ID() string { return fmt.Sprintf("%s-%d", s.topic, s.subID) }


// NewPublisher 创建新的发布者
func NewPublisher[T any]() Publisher[T] {
 return &pubSubImpl[T]{
  subscribers: make(map[string]map[uintptr]Subscriber[T]),
 }
}

// Publish 发布事件到指定主题
func (ps *pubSubImpl[T]) Publish(topic string, payload T) {
 ps.mu.RLock() // 使用读锁允许多个发布者并发

 event := Event[T]{
  Topic:   topic,
  Payload: payload,
 }

 // 获取当前主题的所有订阅者
 subsForTopic, topicExists := ps.subscribers[topic]
 // 获取通配符 "*" 的所有订阅者
 subsWildcard, wildcardExists := ps.subscribers["*"]

 ps.mu.RUnlock() // 尽快释放读锁

 // 异步通知订阅者
 notify := func(subs map[uintptr]Subscriber[T]) {
     if subs == nil { return }
     // 创建副本以避免在迭代时持有锁或受并发修改影响
     subsCopy := make([]Subscriber[T], 0, len(subs))
     ps.mu.RLock()
     for _, sub := range subs {
         subsCopy = append(subsCopy, sub)
     }
     ps.mu.RUnlock()

     for _, sub := range subsCopy {
         go func(s Subscriber[T]) {
             // 可以在这里添加 panic 恢复
             defer func() {
                 if r := recover(); r != nil {
                     // log.Printf("Subscriber panicked: %v", r)
                 }
             }()
             s.OnEvent(event)
         }(sub)
     }
 }

 if topicExists {
     notify(subsForTopic)
 }
 if wildcardExists {
     notify(subsWildcard)
 }
}

// subscribeInternal 内部订阅逻辑
func (ps *pubSubImpl[T]) subscribeInternal(topic string, subscriber Subscriber[T]) (Subscription, error) {
    ps.mu.Lock()
    defer ps.mu.Unlock()

    if subscriber == nil {
        return nil, errors.New("subscriber cannot be nil")
    }

    // 使用订阅者指针的地址作为 ID
    subID := uintptr(unsafe.Pointer(&subscriber)) // 注意：这依赖于 subscriber 不被移动，对函数可能不安全

    if _, ok := ps.subscribers[topic]; !ok {
        ps.subscribers[topic] = make(map[uintptr]Subscriber[T])
    }

    // 检查是否已订阅
    if _, exists := ps.subscribers[topic][subID]; exists {
         // 可以选择返回错误或返回现有订阅
         // return nil, fmt.Errorf("subscriber already subscribed to topic %s", topic)
    }

    ps.subscribers[topic][subID] = subscriber

    return &subscriptionImpl[T]{
        publisher: ps,
        topic:     topic,
        subID:     subID,
    }, nil
}

// Subscribe 订阅主题
func (ps *pubSubImpl[T]) Subscribe(topic string, subscriber Subscriber[T]) (Subscription, error) {
    // 注意：直接传递接口可能导致 subID 不稳定，最好传递指针
    // 如果 subscriber 是值类型，每次调用 subID 都可能不同
    // 建议：接口应该由指针实现，或者用户负责传递指针
    return ps.subscribeInternal(topic, subscriber)
}

// SubscribeFunc 订阅主题的便捷方法
func (ps *pubSubImpl[T]) SubscribeFunc(topic string, handler func(Event[T])) (Subscription, error) {
    if handler == nil {
        return nil, errors.New("handler cannot be nil")
    }
    // 将函数包装成 SubscriberFunc
    subscriber := SubscriberFunc[T](handler)
    // 注意：这里 subscriber 是一个函数值，其地址可能不稳定
    // 使用函数订阅时取消订阅可能需要不同的机制（例如返回一个唯一的 ID）
    // 或者要求用户管理 Subscription 对象
    // 为了简化，这里仍然使用指针地址，但这可能不适用于函数值
    return ps.subscribeInternal(topic, subscriber)
}


// unsubscribeByID 内部取消订阅逻辑
func (ps *pubSubImpl[T]) unsubscribeByID(topic string, subID uintptr) {
    ps.mu.Lock()
    defer ps.mu.Unlock()

    if subs, ok := ps.subscribers[topic]; ok {
        delete(subs, subID)
        if len(subs) == 0 {
            delete(ps.subscribers, topic) // 清理空的主题
        }
    }
}

// 注意：上面使用 unsafe.Pointer 获取地址作为 ID 对于函数值或接口值可能不可靠。
// 更健壮的实现通常会生成唯一的字符串或整数 ID，并在订阅时返回，
// 然后在取消订阅时使用该 ID。Subscription 接口就是为此设计的。
```

##### 异步 Publisher 与 Topic Listener

提供缓冲和后台处理，以及简化的监听接口。

```go
package pubsub

import (
 "context"
 "sync"
 // ... (依赖上面的 Publisher, Subscriber 等定义)
)

// AsyncPublisher 异步发布者，提供缓冲和后台发布
type AsyncPublisher[T any] struct {
 publisher Publisher[T] // 底层同步 Publisher
 eventChan chan Event[T]   // 事件缓冲通道
 ctx       context.Context // 控制后台 goroutine 生命周期
 cancel    context.CancelFunc
 wg        sync.WaitGroup
 onceStop  sync.Once // 确保停止逻辑只执行一次
}

// NewAsyncPublisher 创建新的异步发布者
// bufferSize: 事件通道的缓冲区大小
func NewAsyncPublisher[T any](parentCtx context.Context, bufferSize int) *AsyncPublisher[T] {
 if bufferSize <= 0 {
  bufferSize = 100 // 默认缓冲大小
 }
 ctx, cancel := context.WithCancel(parentCtx)
 ap := &AsyncPublisher[T]{
  publisher: NewPublisher[T](), // 创建内部同步 Publisher
  eventChan: make(chan Event[T], bufferSize),
  ctx:       ctx,
  cancel:    cancel,
 }

 ap.start()
 return ap
}

// start 启动后台处理 goroutine
func (ap *AsyncPublisher[T]) start() {
 ap.wg.Add(1)
 go func() {
  defer ap.wg.Done()
  // fmt.Println("AsyncPublisher worker started.") // 调试
  for {
   select {
   case event, ok := <-ap.eventChan:
    if !ok { // 通道关闭
        // fmt.Println("AsyncPublisher event channel closed.") // 调试
        return
    }
    // 调用底层同步 Publisher 发布
    ap.publisher.Publish(event.Topic, event.Payload)
   case <-ap.ctx.Done(): // 上下文取消
    // fmt.Println("AsyncPublisher worker stopping due to context cancellation.") // 调试
    // 可选：处理 eventChan 中剩余的事件？
    // for event := range ap.eventChan { ap.publisher.Publish(event.Topic, event.Payload) }
    return
   }
  }
 }()
}

// Publish 异步发布事件到缓冲通道
// 如果通道已满，可以选择阻塞或丢弃 (这里选择阻塞)
func (ap *AsyncPublisher[T]) Publish(topic string, payload T) error {
 select {
 case <-ap.ctx.Done(): // 检查是否已停止
     return ap.ctx.Err()
 default:
 }

 event := Event[T]{Topic: topic, Payload: payload}
 select {
 case ap.eventChan <- event:
  return nil
 case <-ap.ctx.Done(): // 在尝试发送时停止
  return ap.ctx.Err()
 // 可选：添加 default case 处理通道满的情况 (例如丢弃或返回错误)
 // default: return errors.New("event channel full, message dropped")
 }
}

// Subscribe 代理订阅请求到底层 Publisher
func (ap *AsyncPublisher[T]) Subscribe(topic string, subscriber Subscriber[T]) (Subscription, error) {
 return ap.publisher.Subscribe(topic, subscriber)
}

// SubscribeFunc 代理订阅请求到底层 Publisher
func (ap *AsyncPublisher[T]) SubscribeFunc(topic string, handler func(Event[T])) (Subscription, error) {
 return ap.publisher.SubscribeFunc(topic, handler)
}

// Stop 停止异步发布者，等待后台 goroutine 完成
func (ap *AsyncPublisher[T]) Stop() {
 ap.onceStop.Do(func() {
     // fmt.Println("Stopping AsyncPublisher...") // 调试
     ap.cancel() // 取消上下文，通知 worker 停止
     // 不立即关闭 eventChan，允许 worker 处理完剩余事件
     // 或者可以在 worker 退出前关闭
     // close(ap.eventChan) // 关闭通道，可选
 })
 ap.wg.Wait() // 等待 worker goroutine 退出
 // fmt.Println("AsyncPublisher stopped.") // 调试
}


// TopicListener 主题监听器，简化订阅管理
type TopicListener[T any] struct {
 publisher Publisher[T] // 可以是同步或异步 Publisher
 subs      map[string]Subscription // 主题 -> 当前订阅关系
 mu        sync.Mutex
}

// NewTopicListener 创建新的主题监听器
func NewTopicListener[T any](publisher Publisher[T]) *TopicListener[T] {
 if publisher == nil {
  panic("publisher cannot be nil")
 }
 return &TopicListener[T]{
  publisher: publisher,
  subs:      make(map[string]Subscription),
 }
}

// Listen 开始监听指定主题。如果已在监听，会先取消旧的订阅。
func (tl *TopicListener[T]) Listen(topic string, handler func(T)) error {
 if handler == nil {
     return errors.New("handler cannot be nil")
 }
 tl.mu.Lock()
 defer tl.mu.Unlock()

 // 如果已监听，取消旧订阅
 if oldSub, ok := tl.subs[topic]; ok {
  oldSub.Unsubscribe()
  delete(tl.subs, topic)
 }

 // 创建新订阅
 newSub, err := tl.publisher.SubscribeFunc(topic, func(event Event[T]) {
  handler(event.Payload) // 只传递 payload 给 handler
 })
 if err != nil {
  return fmt.Errorf("failed to subscribe to topic %s: %w", topic, err)
 }

 // 存储新订阅
 tl.subs[topic] = newSub
 return nil
}

// StopListening 停止监听指定主题
func (tl *TopicListener[T]) StopListening(topic string) {
 tl.mu.Lock()
 defer tl.mu.Unlock()

 if sub, ok := tl.subs[topic]; ok {
  sub.Unsubscribe()
  delete(tl.subs, topic)
 }
}


// StopAll 停止监听所有主题
func (tl *TopicListener[T]) StopAll() {
 tl.mu.Lock()
 defer tl.mu.Unlock()

 for topic, sub := range tl.subs {
  sub.Unsubscribe()
  delete(tl.subs, topic) // 从 map 中移除
 }
 // 清空 map (可选，因为上面已经删除了所有键)
 // tl.subs = make(map[string]Subscription)
}
```

#### 2.4.2 Actor 模式

使用独立的、带有状态和行为的执行单元（Actor），通过异步消息传递进行通信。

##### Actor：实现与代码示例

```go
package actor

import (
 "context"
 "errors"
 "sync"
 "fmt" // 用于 ID 生成
 "sync/atomic" // 用于状态
 "time" // 用于 Ask 超时
 "unsafe" // 用于 Actor 地址作为 ID (有风险)
)

// Message 表示actor可以处理的消息
type Message[T any] struct {
 Sender  *ActorRef[T] // 发送者引用 (可选)
 Content T          // 消息内容
 Response chan<- any // 用于 Ask 模式的响应通道 (可选)
}

// Actor 定义了 actor 的行为接口
type Actor[T any] interface {
 // Receive 处理接收到的消息
 Receive(ctx context.Context, msg Message[T]) error
 // PreStart 在actor启动前调用，可用于初始化
 PreStart(ctx context.Context) error
 // PostStop 在actor停止后调用，可用于清理资源
 PostStop(ctx context.Context) error
}

// ActorRef actor的引用，用于向 actor 发送消息
type ActorRef[T any] struct {
 id        string
 mailbox   chan Message[T]
 system    *ActorSystem[T] // 指向所属的 ActorSystem
 stopOnce  sync.Once      // 确保停止逻辑只执行一次
 stopped   atomic.Bool    // 标记是否已停止
}

// Tell 发送异步消息（"fire and forget"）
// 如果邮箱已满，根据 ActorSystem 配置可能阻塞或返回错误
func (ref *ActorRef[T]) Tell(msg T, sender *ActorRef[T]) error {
    if ref.stopped.Load() {
        return ErrActorStopped
    }
    message := Message[T]{Content: msg, Sender: sender}
    select {
    case ref.mailbox <- message:
        return nil
    case <-ref.system.ctx.Done(): // ActorSystem 已停止
        return ErrActorSystemShutdown
    default:
        // 邮箱满的处理策略取决于系统设计
        // 可以阻塞、返回错误或丢弃
        // 这里返回错误
        return ErrMailboxFull
    }
}

// Ask 发送消息并等待响应 (同步调用)
// timeout: 等待响应的超时时间
func (ref *ActorRef[T]) Ask(ctx context.Context, msg T, timeout time.Duration) (any, error) {
    if ref.stopped.Load() {
        return nil, ErrActorStopped
    }
    // 创建一个用于接收响应的通道
    responseChan := make(chan any, 1)
    message := Message[T]{
        Content:  msg,
        // Sender 可以是 nil 或调用者的 ActorRef (如果适用)
        Response: responseChan,
    }

    // 使用带超时的子上下文
    askCtx, cancel := context.WithTimeout(ctx, timeout)
    defer cancel()

    // 发送消息到邮箱
    select {
    case ref.mailbox <- message:
        // 消息已发送，等待响应或超时/取消
        select {
        case response := <-responseChan:
            return response, nil
        case <-askCtx.Done():
            return nil, fmt.Errorf("actor ask timed out or cancelled: %w", askCtx.Err())
        }
    case <-askCtx.Done(): // 发送消息时就超时或取消
        return nil, fmt.Errorf("failed to send ask message: %w", askCtx.Err())
    case <-ref.system.ctx.Done(): // ActorSystem 已停止
         return nil, ErrActorSystemShutdown
    default: // 邮箱满
        return nil, ErrMailboxFull
    }
}


// ID 获取actor ID
func (ref *ActorRef[T]) ID() string {
 return ref.id
}

// Stop 停止此 actor
func (ref *ActorRef[T]) Stop() {
    // 使用 sync.Once 确保停止逻辑只被调用一次
    ref.stopOnce.Do(func() {
        if ref.stopped.CompareAndSwap(false, true) {
            ref.system.stopActorByID(ref.id) // 通知 ActorSystem 停止
        }
    })
}

// IsStopped 检查 actor 是否已停止
func (ref *ActorRef[T]) IsStopped() bool {
    return ref.stopped.Load()
}


// ActorSystem 管理actor的生命周期
type ActorSystem[T any] struct {
 name        string // Actor 系统名称 (可选)
 actors      sync.Map // 存储 actorContext (线程安全 map: string -> *actorContext[T])
 ctx         context.Context    // ActorSystem 的根上下文
 cancel      context.CancelFunc // 用于停止整个系统
 wg          sync.WaitGroup     // 等待所有 actor 停止
 idCounter   atomic.Uint64    // 用于生成唯一 Actor ID
}

// actorContext 封装actor的运行环境
type actorContext[T any] struct {
 actor      Actor[T]         // Actor 实例
 ref        *ActorRef[T]     // Actor 引用
 ctx        context.Context    // Actor 自身的上下文
 cancelFunc context.CancelFunc // 用于停止此 Actor 的函数
 wg         *sync.WaitGroup    // 指向 ActorSystem 的 WaitGroup
}

// NewActorSystem 创建新的actor系统
func NewActorSystem[T any](name string) *ActorSystem[T] {
 ctx, cancel := context.WithCancel(context.Background())
 return &ActorSystem[T]{
  name:   name,
  ctx:    ctx,
  cancel: cancel,
 }
}

// Spawn 创建一个新的actor
// namePrefix: Actor 名称前缀 (可选)
// actor: 要运行的 Actor 实例
// mailboxSize: Actor 邮箱的缓冲大小
func (s *ActorSystem[T]) Spawn(namePrefix string, actor Actor[T], mailboxSize int) (*ActorRef[T], error) {
    if actor == nil {
        return nil, errors.New("actor instance cannot be nil")
    }
    if mailboxSize <= 0 {
        mailboxSize = 100 // 默认大小
    }

    // 生成唯一ID
    idNum := s.idCounter.Add(1)
    id := fmt.Sprintf("%s-%d", namePrefix, idNum)
    if namePrefix == "" {
        id = fmt.Sprintf("actor-%d", idNum)
    }

    // 创建actor引用
    ref := &ActorRef[T]{
        id:      id,
        mailbox: make(chan Message[T], mailboxSize),
        system:  s,
    }

    // 创建actor上下文
    actorCtx, cancel := context.WithCancel(s.ctx) // 继承系统上下文
    ctx := &actorContext[T]{
        actor:      actor,
        ref:        ref,
        ctx:        actorCtx,
        cancelFunc: cancel,
        wg:         &s.wg, // 共享系统的 WaitGroup
    }

    // 存储到系统 (使用 sync.Map)
    s.actors.Store(id, ctx)

    // 增加系统 WaitGroup 计数
    s.wg.Add(1)

    // 调用 PreStart，如果失败则清理并返回错误
    err := actor.PreStart(actorCtx)
    if err != nil {
        cancel() // 取消 actor 上下文
        s.actors.Delete(id) // 从 map 中移除
        s.wg.Done() // 减少 WaitGroup 计数
        return nil, fmt.Errorf("actor %s PreStart failed: %w", id, err)
    }

    // 启动actor处理循环
    go s.runActor(ctx)

    return ref, nil
}

// runActor 运行actor的消息处理循环
func (s *ActorSystem[T]) runActor(actCtx *actorContext[T]) {
    defer func() {
        // Actor 停止后的清理工作
        _ = actCtx.actor.PostStop(actCtx.ctx) // 调用 PostStop
        actCtx.wg.Done() // 通知 WaitGroup 此 actor 已停止
        // 可选：从 ActorSystem 中移除自身引用？通常由 Stop 方法处理
        // s.actors.Delete(actCtx.ref.id)
        close(actCtx.ref.mailbox) // 关闭邮箱
        // fmt.Printf("Actor %s stopped.\n", actCtx.ref.id) // 调试信息
    }()

    // fmt.Printf("Actor %s started.\n", actCtx.ref.id) // 调试信息

    for {
        select {
        case msg, ok := <-actCtx.ref.mailbox:
            if !ok { // 邮箱已关闭 (通常在 Stop 时发生)
                return
            }
            // 处理消息
            func() {
                // 处理消息时的 panic 恢复
                defer func() {
                    if r := recover(); r != nil {
                        // log.Printf("Actor %s panicked while processing message: %v", actCtx.ref.id, r)
                        // 可以根据监督策略决定如何处理 (重启、停止等)
                        // 简单起见，这里仅记录
                    }
                }()
                err := actCtx.actor.Receive(actCtx.ctx, msg)
                if err != nil {
                    // log.Printf("Actor %s Receive error: %v", actCtx.ref.id, err)
                    // 处理错误，例如发送错误响应或停止 actor
                    if msg.Response != nil {
                        select {
                        case msg.Response <- err: // 发送错误作为响应
                        default: // 如果响应通道阻塞或关闭
                        }
                    }
                }
            }()

        case <-actCtx.ctx.Done(): // Actor 被停止 (通过 ref.Stop() 或系统关闭)
            return
        }
    }
}

// stopActorByID 内部方法，用于停止指定 ID 的 actor
func (s *ActorSystem[T]) stopActorByID(id string) {
    if actCtxIntf, ok := s.actors.LoadAndDelete(id); ok { // 原子加载并删除
        actCtx := actCtxIntf.(*actorContext[T])
        actCtx.cancelFunc() // 取消 actor 的上下文，触发 runActor 退出
        // runActor 中的 defer wg.Done() 会处理 WaitGroup
    }
}


// Shutdown 停止整个 ActorSystem，等待所有 actor 退出
func (s *ActorSystem[T]) Shutdown(timeout time.Duration) error {
    s.cancel() // 取消根上下文，向所有 actor 发送停止信号

    // 等待所有 actor goroutine 完成，带超时
    waitChan := make(chan struct{})
    go func() {
        s.wg.Wait() // 等待所有 actor 的 wg.Done()
        close(waitChan)
    }()

    select {
    case <-waitChan:
        return nil // 正常关闭
    case <-time.After(timeout):
        return fmt.Errorf("actor system shutdown timed out after %v", timeout)
    }
}

// GetActor 获取指定 ID 的 ActorRef (如果存在)
func (s *ActorSystem[T]) GetActor(id string) (*ActorRef[T], bool) {
    if actCtxIntf, ok := s.actors.Load(id); ok {
        actCtx := actCtxIntf.(*actorContext[T])
        // 检查 actor 是否已停止
        if actCtx.ref.IsStopped() {
            return nil, false
        }
        return actCtx.ref, true
    }
    return nil, false
}


// 错误定义
var (
    ErrMailboxFull         = errors.New("actor mailbox is full")
    ErrActorStopped        = errors.New("actor is stopped")
    ErrActorSystemShutdown = errors.New("actor system is shut down")
)

// --- 基础 Actor 实现 (可选) ---
type BaseActor[T any] struct{}
func (a *BaseActor[T]) PreStart(ctx context.Context) error { return nil }
func (a *BaseActor[T]) PostStop(ctx context.Context) error { return nil }
func (a *BaseActor[T]) Receive(ctx context.Context, msg Message[T]) error {
    // 默认忽略所有消息或返回未处理错误
    return fmt.Errorf("unhandled message: %v", msg.Content)
}

```

##### 扩展讨论：监督、层级与持久化

- **监督 (Supervision)**: Actor 系统通常包含监督策略。当一个 Actor 失败（例如 panic 或返回错误）时，其父 Actor（监督者）可以决定如何处理：重启 Actor、停止 Actor、停止自己或将错误升级给自己的监督者。这需要实现 Actor 层级结构。
- **层级 (Hierarchy)**: Actor 可以创建子 Actor，形成树状结构。这有助于组织系统、隔离失败和分配任务。`ActorSystem` 可以看作是根监督者。
- **位置透明性 (Location Transparency)**: 理想的 Actor 系统中，发送消息给 Actor 时无需关心它是在本地还是远程机器上。这通常需要网络层和 Actor 地址解析机制。
- **持久化 (Persistence)**: 对于有状态 Actor，需要将其状态持久化存储，以便在 Actor 重启或系统恢复后能恢复状态。常见的模式是事件溯源（Event Sourcing）。

这些高级特性通常需要更复杂的 Actor System 实现，例如使用现有的 Go Actor 框架（如 Proto.Actor）或自行构建。

#### 2.4.3 CSP (Communicating Sequential Processes) 模式

Go 语言并发模型的核心。强调通过通道（Channel）在独立的顺序执行单元（goroutine）之间传递消息，而不是通过共享内存来通信。

##### CSP：实现与代码示例 (Pipe, Mux, Demux, Filter, Map)

```go
package csp

import (
 "context"
 "sync"
)

// Process 代表一个独立的顺序进程，通过通道接收输入并发送输出
type Process[In, Out any] interface {
 // Run 启动进程。需要处理输入通道关闭和上下文取消。
 Run(ctx context.Context, in <-chan In, out chan<- Out)
}

// ProcessFunc 允许使用函数作为进程
type ProcessFunc[In, Out any] func(ctx context.Context, in <-chan In, out chan<- Out)

func (pf ProcessFunc[In, Out]) Run(ctx context.Context, in <-chan In, out chan<- Out) {
 pf(ctx, in, out)
}

// Pipe 连接两个进程 P1(In -> Mid) 和 P2(Mid -> Out)
// 返回一个 WaitGroup，用于等待两个进程完成
func Pipe[In, Mid, Out any](ctx context.Context,
 first Process[In, Mid],
 second Process[Mid, Out],
 inChan <-chan In,
 outChan chan<- Out,
 bufferSize int) *sync.WaitGroup {

 middleChan := make(chan Mid, bufferSize) // 创建中间通道
 var wg sync.WaitGroup
 wg.Add(2)

 // 启动第一个进程
 go func() {
  defer wg.Done()
  defer close(middleChan) // P1 完成后关闭中间通道，通知 P2 输入结束
  first.Run(ctx, inChan, middleChan)
 }()

 // 启动第二个进程
 go func() {
  defer wg.Done()
  second.Run(ctx, middleChan, outChan)
 }()

 return &wg // 返回 WaitGroup 以便调用者等待
}

// Multiplexer (Mux) 将多个输入通道合并为一个输出通道
func Multiplexer[T any](ctx context.Context, inputs ...<-chan T) <-chan T {
 out := make(chan T)
 var wg sync.WaitGroup

 output := func(item T) {
     // 将数据发送到输出通道，处理上下文取消
     select {
     case out <- item:
     case <-ctx.Done():
     }
 }

 wg.Add(len(inputs))
 for _, ch := range inputs {
  go func(c <-chan T) {
   defer wg.Done()
   for {
    select {
    case item, ok := <-c:
     if !ok { // 输入通道关闭
      return
     }
     output(item)
    case <-ctx.Done(): // 上下文取消
     return
    }
   }
  }(ch)
 }

 // 等待所有输入 goroutine 完成后关闭输出通道
 go func() {
  wg.Wait()
  close(out)
 }()

 return out
}

// Demultiplexer (Demux) 将一个输入通道的数据分发到多个输出通道
// distributionFunc: 决定将输入项发送到哪个输出通道 (返回索引)
// numOutputs: 输出通道的数量
func Demultiplexer[T any](ctx context.Context, input <-chan T, distributionFunc func(T) int, numOutputs int) []<-chan T {
    if numOutputs <= 0 {
        return nil
    }
    outputs := make([]chan T, numOutputs) // 创建内部可写通道
    readOutputs := make([]<-chan T, numOutputs) // 创建只读通道返回给调用者
    for i := 0; i < numOutputs; i++ {
        outputs[i] = make(chan T) // 可以添加缓冲
        readOutputs[i] = outputs[i]
    }

    go func() {
        // 关闭所有输出通道当输入结束或上下文取消
        defer func() {
            for _, ch := range outputs {
                close(ch)
            }
        }()

        for {
            select {
            case item, ok := <-input:
                if !ok { // 输入通道关闭
                    return
                }
                // 计算目标输出通道索引
                targetIndex := distributionFunc(item)
                if targetIndex >= 0 && targetIndex < numOutputs {
                    // 发送数据到目标通道，处理上下文取消
                    select {
                    case outputs[targetIndex] <- item:
                    case <-ctx.Done():
                        return
                    }
                } else {
                    // 处理无效索引，例如记录日志或发送到默认通道
                    // log.Printf("Demux: invalid target index %d for item %v", targetIndex, item)
                }
            case <-ctx.Done(): // 上下文取消
                return
            }
        }
    }()

    return readOutputs
}


// Filter 创建一个进程，只转发满足条件的元素
func Filter[T any](ctx context.Context, predicate func(T) bool) Process[T, T] {
 return ProcessFunc[T, T](func(ctx context.Context, in <-chan T, out chan<- T) {
  for {
   select {
   case item, ok := <-in:
    if !ok { return } // 输入关闭
    if predicate(item) {
     select {
     case out <- item: // 发送满足条件的元素
     case <-ctx.Done(): return // 上下文取消
     }
    }
   case <-ctx.Done(): return // 上下文取消
   }
  }
 })
}

// Map 创建一个进程，对每个元素应用转换函数
func Map[T, R any](ctx context.Context, fn func(T) R) Process[T, R] {
 return ProcessFunc[T, R](func(ctx context.Context, in <-chan T, out chan<- R) {
  for {
   select {
   case item, ok := <-in:
    if !ok { return }
    result := fn(item) // 应用转换函数
    select {
    case out <- result:
    case <-ctx.Done(): return
    }
   case <-ctx.Done(): return
   }
  }
 })
}
```

##### 进程网络 (ProcessNetwork)

构建一个动态的、由通道连接的 goroutine 网络。

```go
package csp

import (
 "context"
 "sync"
 "errors"
 "fmt"
)

// ProcessNetwork 一个动态的 CSP 进程网络
type ProcessNetwork[T any] struct {
 processes map[string]Process[T, T] // 进程名称 -> 进程实例
 inputs    map[string]chan T        // 进程名称 -> 输入通道
 outputs   map[string]chan T        // 进程名称 -> 输出通道
 mu        sync.RWMutex             // 保护网络结构
 ctx       context.Context          // 网络根上下文
 cancel    context.CancelFunc       // 用于停止整个网络
 wg        sync.WaitGroup           // 等待所有进程和连接 goroutine 停止
}

// NewProcessNetwork 创建一个新的 CSP 进程网络
func NewProcessNetwork[T any]() *ProcessNetwork[T] {
 ctx, cancel := context.WithCancel(context.Background())
 return &ProcessNetwork[T]{
  processes: make(map[string]Process[T, T]),
  inputs:    make(map[string]chan T),
  outputs:   make(map[string]chan T),
  ctx:       ctx,
  cancel:    cancel,
 }
}

// AddProcess 添加进程到网络
// name: 进程的唯一名称
// process: 实现 Process[T, T] 接口的实例
// bufferSize: 输入输出通道的缓冲区大小
func (pn *ProcessNetwork[T]) AddProcess(name string, process Process[T, T], bufferSize int) error {
 if process == nil {
     return errors.New("process cannot be nil")
 }
 pn.mu.Lock()
 defer pn.mu.Unlock()

 if _, exists := pn.processes[name]; exists {
  return fmt.Errorf("process with name '%s' already exists", name)
 }

 if bufferSize < 0 { bufferSize = 0 } // 默认为无缓冲

 inChan := make(chan T, bufferSize)
 outChan := make(chan T, bufferSize)

 pn.processes[name] = process
 pn.inputs[name] = inChan
 pn.outputs[name] = outChan

 // 启动进程 goroutine
 pn.wg.Add(1)
 go func() {
  defer pn.wg.Done()
  defer close(outChan) // 进程结束后关闭其输出通道
  // 可以在这里添加 panic 恢复
  process.Run(pn.ctx, inChan, outChan)
 }()

 return nil
}

// Connect 连接两个进程的输出和输入
// fromProcess: 源进程名称
// toProcess: 目标进程名称
func (pn *ProcessNetwork[T]) Connect(fromProcess, toProcess string) error {
 pn.mu.RLock() // 只需要读锁来获取通道
 fromChan, fromExists := pn.outputs[fromProcess]
 toChan, toExists := pn.inputs[toProcess]
 pn.mu.RUnlock()

 if !fromExists {
  return fmt.Errorf("source process '%s' not found", fromProcess)
 }
 if !toExists {
  return fmt.Errorf("target process '%s' not found", toProcess)
 }

 // 启动转发 goroutine
 pn.wg.Add(1)
 go func() {
  defer pn.wg.Done()
  for {
   select {
   case <-pn.ctx.Done(): // 网络停止
    return
   case item, ok := <-fromChan:
    if !ok { // 源通道关闭
     // 是否需要关闭目标通道？取决于设计，通常不在这里关闭
     return
    }
    // 将数据转发到目标通道
    select {
    case toChan <- item:
    case <-pn.ctx.Done(): // 网络在转发时停止
     return
     // 注意：如果目标通道阻塞，这里会一直阻塞
     // 可以考虑添加超时或检查目标进程状态
    }
   }
  }
 }()

 return nil
}

// Send 向指定进程的输入通道发送数据
func (pn *ProcessNetwork[T]) Send(processName string, data T) error {
 pn.mu.RLock()
 inChan, exists := pn.inputs[processName]
 pn.mu.RUnlock()

 if !exists {
  return fmt.Errorf("process '%s' not found", processName)
 }

 select {
 case inChan <- data:
  return nil
 case <-pn.ctx.Done(): // 网络已停止
  return pn.ctx.Err()
  // 可选：添加超时
  // case <-time.After(timeout): return errors.New("send timeout")
 }
}

// Receive 从指定进程的输出通道接收数据 (阻塞)
func (pn *ProcessNetwork[T]) Receive(processName string) (T, error) {
 pn.mu.RLock()
 outChan, exists := pn.outputs[processName]
 pn.mu.RUnlock()

 if !exists {
  var zero T
  return zero, fmt.Errorf("process '%s' not found", processName)
 }

 select {
 case data, ok := <-outChan:
  if !ok { // 通道已关闭
   var zero T
   return zero, fmt.Errorf("output channel for process '%s' is closed", processName)
  }
  return data, nil
 case <-pn.ctx.Done(): // 网络已停止
  var zero T
  return zero, pn.ctx.Err()
 }
}

// TryReceive 非阻塞地尝试从指定进程的输出通道接收数据
func (pn *ProcessNetwork[T]) TryReceive(processName string) (T, bool, error) {
    pn.mu.RLock()
    outChan, exists := pn.outputs[processName]
    pn.mu.RUnlock()

    if !exists {
        var zero T
        return zero, false, fmt.Errorf("process '%s' not found", processName)
    }

    select {
    case data, ok := <-outChan:
        if !ok { // 通道已关闭
            var zero T
            return zero, false, fmt.Errorf("output channel for process '%s' is closed", processName)
        }
        return data, true, nil // 成功接收
    case <-pn.ctx.Done(): // 网络已停止
        var zero T
        return zero, false, pn.ctx.Err()
    default: // 通道中无数据
        var zero T
        return zero, false, nil // 未收到数据，但不是错误
    }
}


// Stop 停止进程网络，等待所有 goroutine 完成
func (pn *ProcessNetwork[T]) Stop() {
 pn.cancel() // 取消根上下文
 pn.wg.Wait() // 等待所有 goroutine 停止
}
```

---

### 2.5 并行数据处理模式

这些模式专注于利用多核处理器并行处理大量数据。

#### 2.5.1 Map-Reduce 模式

一种用于大规模数据处理的编程模型，分为 Map（映射/转换）、Shuffle（排序/分组，通常隐式或由框架处理）和 Reduce（归约/聚合）三个阶段。

##### MapReduce：实现与代码示例

```go
package mapreduce

import (
 "context"
 "sync"
 "runtime" // 用于获取 CPU 核心数
)

// MapFunc 映射函数类型：将输入 T 转换为中间结果 M
type MapFunc[T, M any] func(ctx context.Context, item T) (M, error)

// ReduceFunc 归约函数类型：将中间结果 M 合并到累积结果 R
type ReduceFunc[M, R any] func(ctx context.Context, accumulator R, item M) (R, error)

// MapReduce 执行基本的 Map-Reduce 操作
// data: 输入数据切片
// mapFn: 映射函数
// reduceFn: 归约函数
// initialValue: 归约的初始值
// parallelism: 并行执行 Map 阶段的 goroutine 数量 (0 表示使用 GOMAXPROCS)
// 返回最终的归约结果和第一个遇到的错误
func MapReduce[T, M, R any](
 ctx context.Context,
 data []T,
 mapFn MapFunc[T, M],
 reduceFn ReduceFunc[M, R],
 initialValue R,
 parallelism int,
) (R, error) {

 if len(data) == 0 {
     return initialValue, nil
 }

 if parallelism <= 0 {
  parallelism = runtime.GOMAXPROCS(0)
 }
 if parallelism > len(data) { // 避免创建比数据项还多的 goroutine
     parallelism = len(data)
 }


 // --- Map 阶段 ---
 mapResults := make(chan M) // 存储 Map 结果
 errChan := make(chan error, 1) // 存储第一个 Map 错误
 mapCtx, mapCancel := context.WithCancel(ctx) // 用于取消 Map 阶段
 defer mapCancel()

 var mapWg sync.WaitGroup
 mapWg.Add(parallelism)

 itemsPerWorker := (len(data) + parallelism - 1) / parallelism

 for i := 0; i < parallelism; i++ {
  start := i * itemsPerWorker
  end := start + itemsPerWorker
  if end > len(data) {
   end = len(data)
  }
  if start >= end { // 如果分配不到任务则跳过
      mapWg.Done()
      continue
  }

  go func(workerData []T) {
   defer mapWg.Done()
   for _, item := range workerData {
    select {
    case <-mapCtx.Done(): // 检查是否被取消
     return
    default:
        mappedItem, err := mapFn(mapCtx, item)
        if err != nil {
            // 报告第一个错误并取消其他 mapper
            select {
            case errChan <- err:
                mapCancel()
            case <-mapCtx.Done(): // 如果已取消则忽略
            }
            return // 出错后此 worker 停止
        }
        // 发送 Map 结果
        select {
        case mapResults <- mappedItem:
        case <-mapCtx.Done():
            return
        }
    }
   }
  }(data[start:end])
 }

 // 启动一个 goroutine 等待所有 mapper 完成后关闭 mapResults 通道
 go func() {
  mapWg.Wait()
  close(mapResults)
  close(errChan) // 关闭错误通道
 }()


 // --- Reduce 阶段 ---
 finalResult := initialValue
 var reduceErr error

 // 检查 Map 阶段是否出错
 if mapErr := <-errChan; mapErr != nil {
     // 如果 Map 阶段出错，清空 mapResults 通道并返回错误
     go func() {
         for range mapResults {} // 消耗掉可能仍在发送的结果
     }()
     return initialValue, fmt.Errorf("map phase failed: %w", mapErr)
 }


 // 顺序执行 Reduce
 reduceLoop:
 for {
     select {
     case <-ctx.Done(): // 检查外部上下文是否取消
         reduceErr = ctx.Err()
         break reduceLoop
     case item, ok := <-mapResults:
         if !ok { // Map 结果通道关闭
             break reduceLoop
         }
         // 执行 Reduce 函数
         var err error
         finalResult, err = reduceFn(ctx, finalResult, item)
         if err != nil {
             reduceErr = fmt.Errorf("reduce phase failed: %w", err)
             mapCancel() // 取消可能还在运行的 mapper (虽然理论上已结束)
             // 清空 mapResults
             go func() {
                 for range mapResults {}
             }()
             break reduceLoop
         }
     }
 }

 return finalResult, reduceErr
}
```

##### 并发 Map-Reduce 与管道

可以进一步将 Map 和 Reduce 阶段也并行化，并构建可重用的处理管道。

```go
package mapreduce

import (
 "context"
 "sync"
 "runtime"
 // ... (依赖 MapFunc, ReduceFunc 等)
)

// ConcurrentMapReduce 执行并发 Map 和并发 Reduce
// combinerFn: (可选) 在 Map 阶段后、Reduce 阶段前，在每个 Mapper 本地进行预聚合，减少传输数据量
// reduceParallelism: 并行执行 Reduce 的 goroutine 数量
func ConcurrentMapReduce[T, M, R any](
 ctx context.Context,
 data []T,
 mapFn MapFunc[T, M],
 reduceFn ReduceFunc[M, R], // 主 Reduce 函数
 combinerFn ReduceFunc[M, R], // 可选的 Combiner 函数 (签名与 Reduce 相同)
 initialValue R,
 mapParallelism int,
 reduceParallelism int,
) (R, error) {
    if len(data) == 0 {
        return initialValue, nil
    }

    if mapParallelism <= 0 { mapParallelism = runtime.GOMAXPROCS(0) }
    if reduceParallelism <= 0 { reduceParallelism = runtime.GOMAXPROCS(0) }
    if mapParallelism > len(data) { mapParallelism = len(data) }


    mapCtx, mapCancel := context.WithCancel(ctx)
    defer mapCancel()
    errChan := make(chan error, 1) // 捕获第一个错误

    // --- Map (和可选的 Combine) 阶段 ---
    intermediateResults := make([]chan R, mapParallelism) // 每个 mapper 输出一个 R 类型通道 (如果使用 combiner)
                                                         // 或者输出 M 类型通道 (如果不使用 combiner)
    var mapWg sync.WaitGroup
    mapWg.Add(mapParallelism)
    itemsPerWorker := (len(data) + mapParallelism - 1) / mapParallelism

    for i := 0; i < mapParallelism; i++ {
        start := i * itemsPerWorker
        end := start + itemsPerWorker
        if end > len(data) { end = len(data) }
        if start >= end {
            mapWg.Done()
            intermediateResults[i] = make(chan R) // 创建空通道
            close(intermediateResults[i])         // 立即关闭
            continue
        }

        // 每个 mapper 输出一个通道
        outputChan := make(chan R) // 假设使用了 Combiner
        intermediateResults[i] = outputChan

        go func(workerData []T, out chan<- R) {
            defer mapWg.Done()
            defer close(out) // Mapper 完成后关闭其输出通道

            localResult := initialValue // Combiner 的本地初始值
            hasCombined := false

            for _, item := range workerData {
                select {
                case <-mapCtx.Done(): return
                default:
                    mappedItem, err := mapFn(mapCtx, item)
                    if err != nil {
                        select { case errChan <- err: mapCancel(); default: }
                        return
                    }

                    if combinerFn != nil {
                        // 使用 Combiner 进行本地聚合
                        localResult, err = combinerFn(mapCtx, localResult, mappedItem)
                        if err != nil {
                            select { case errChan <- err: mapCancel(); default: }
                            return
                        }
                        hasCombined = true
                    } else {
                        // 不使用 Combiner，需要将 M 发送到 Reduce 阶段
                        // (需要修改通道类型和后续逻辑)
                        // 这里假设必须用 Combiner 或 Map 直接输出 R
                        // 为了简化，我们假设 Map 直接输出 R 或者 Combiner 存在
                        panic("ConcurrentMapReduce requires either a combiner or MapFunc outputting R directly in this simplified example")
                    }
                }
            }
            // 发送本地聚合结果 (如果使用了 combiner 且有结果)
            if combinerFn != nil && hasCombined {
                 select {
                 case out <- localResult:
                 case <-mapCtx.Done(): return
                 }
            } else if !hasCombined && combinerFn != nil {
                 // 如果 combiner 存在但没有数据处理，发送初始值？取决于定义
                 // select { case out <- initialValue: case <-mapCtx.Done(): }
            }
        }(data[start:end], outputChan)
    }

    // 等待 Map 阶段完成，并检查错误
    go func() {
        mapWg.Wait()
        // Map 阶段结束，关闭错误通道（如果之前没有错误发生）
        // select { case <-errChan: default: close(errChan) }
        // 不能在这里关闭 errChan，因为 Reduce 可能出错

        // Mux 合并所有 mapper 的输出通道
        // (需要实现 Mux 函数)
        // allIntermediateResults := Mux(mapCtx, intermediateResults...)
        // close(allIntermediateResults) // Mux 内部会关闭
    }()


    // --- Reduce 阶段 (并行) ---
    // 合并来自所有 mapper 的中间结果
    mergedIntermediateChan := Mux(mapCtx, intermediateResults...) // 使用 CSP Mux

    // 检查 Map 阶段错误
    select {
    case mapErr := <-errChan:
        if mapErr != nil {
            go func() { for range mergedIntermediateChan {} }() // Drain channel
            return initialValue, fmt.Errorf("map phase failed: %w", mapErr)
        }
    default: // Map 阶段无错误
    }

    // 并行 Reduce
    var reduceWg sync.WaitGroup
    reduceOutputs := make([]R, reduceParallelism)
    reduceErrChan := make(chan error, 1) // 捕获第一个 Reduce 错误
    reduceCtx, reduceCancel := context.WithCancel(mapCtx) // Reduce 上下文
    defer reduceCancel()

    reduceWg.Add(reduceParallelism)
    itemsPerReducer := 100 // 每个 reducer 处理多少项 (可调)

    for i := 0; i < reduceParallelism; i++ {
        go func(reducerID int) {
            defer reduceWg.Done()
            localReduceResult := initialValue
            itemCount := 0

            for {
                select {
                case <-reduceCtx.Done(): return
                case item, ok := <-mergedIntermediateChan: // 从合并通道读取
                    if !ok { // 通道关闭
                        reduceOutputs[reducerID] = localReduceResult // 存储最终结果
                        return
                    }
                    // 执行 Reduce
                    var err error
                    localReduceResult, err = reduceFn(reduceCtx, localReduceResult, item) // 注意：这里 item 是 R 类型
                    if err != nil {
                        select { case reduceErrChan <- err: reduceCancel(); default: }
                        return
                    }
                    itemCount++
                    // 可选：达到一定数量后输出中间结果？ (更复杂)
                }
            }
        }(i)
    }

    // 等待所有 Reducer 完成
    reduceWg.Wait()
    close(reduceErrChan) // 关闭 Reduce 错误通道

    // 检查 Reduce 错误
    if reduceErr := <-reduceErrChan; reduceErr != nil {
        return initialValue, fmt.Errorf("reduce phase failed: %w", reduceErr)
    }

    // --- Final Combine 阶段 ---
    // 合并所有并行 Reducer 的结果
    finalResult := initialValue
    finalCombineFn := reduceFn // 使用主 Reduce 函数来合并 Reducer 的结果
    for _, res := range reduceOutputs {
         select {
         case <-ctx.Done(): // 检查原始上下文
             return finalResult, ctx.Err()
         default:
             var err error
             finalResult, err = finalCombineFn(ctx, finalResult, res)
             if err != nil {
                 return finalResult, fmt.Errorf("final combine phase failed: %w", err)
             }
         }
    }

    return finalResult, nil
}


// MapReducePipeline 构建可重用的 Map-Reduce 管道 (概念)
type MapReducePipeline[T, M, R any] struct {
 mapFn             MapFunc[T, M]
 reduceFn          ReduceFunc[M, R]
 combinerFn        ReduceFunc[M, R] // 可选
 initialValue      R
 mapParallelism    int
 reduceParallelism int
}

// NewMapReducePipeline 创建管道
func NewMapReducePipeline[T, M, R any](
 mapFn MapFunc[T, M], reduceFn ReduceFunc[M, R], combinerFn ReduceFunc[M, R],
 initialValue R, mapP, reduceP int) *MapReducePipeline[T, M, R] {
    return &MapReducePipeline[T, M, R]{
        mapFn: mapFn, reduceFn: reduceFn, combinerFn: combinerFn,
        initialValue: initialValue, mapParallelism: mapP, reduceParallelism: reduceP,
    }
}

// Process 使用管道处理数据
func (p *MapReducePipeline[T, M, R]) Process(ctx context.Context, data []T) (R, error) {
    return ConcurrentMapReduce(ctx, data, p.mapFn, p.reduceFn, p.combinerFn,
        p.initialValue, p.mapParallelism, p.reduceParallelism)
}
```

#### 2.5.2 Fork-Join 模式

将一个大任务递归地分解（Fork）为更小的、可以独立并行处理的子任务，然后将子任务的结果合并（Join）起来得到最终结果。常用于分治算法。

##### ForkJoin：实现与代码示例

```go
package forkjoin

import (
 "context"
 "sync"
 "runtime"
 "errors"
)

// Task 表示可分解为子任务的任务接口
type Task[T any] interface {
 // Execute 直接计算任务结果（当任务足够小，不再分解时调用）
 Execute(ctx context.Context) (T, error)
 // ShouldFork 判断当前任务是否应该被分解成子任务
 ShouldFork(ctx context.Context) bool
 // Fork 将任务分解为子任务列表
 Fork(ctx context.Context) ([]Task[T], error)
 // Join 合并子任务的结果得到当前任务的结果
 Join(ctx context.Context, results []T) (T, error)
}

// ForkJoinPool 管理并行执行的任务
type ForkJoinPool struct {
 parallelism int             // 并发级别
 sem         *semaphore.Weighted // 控制并发 goroutine 数量
}

// NewForkJoinPool 创建新的 Fork-Join 池
func NewForkJoinPool(parallelism int) *ForkJoinPool {
 if parallelism <= 0 {
  parallelism = runtime.GOMAXPROCS(0)
 }
 return &ForkJoinPool{
  parallelism: parallelism,
  sem:         semaphore.NewWeighted(int64(parallelism)),
 }
}

// Invoke 开始执行一个顶层任务
func (p *ForkJoinPool) Invoke[T any](ctx context.Context, task Task[T]) (T, error) {
 return p.compute(ctx, task)
}

// compute 递归执行任务的核心逻辑
func (p *ForkJoinPool) compute[T any](ctx context.Context, task Task[T]) (T, error) {
    // 检查上下文是否已取消
    select {
    case <-ctx.Done():
        var zero T
        return zero, ctx.Err()
    default:
    }

    if !task.ShouldFork(ctx) {
        // 任务足够小，直接计算
        return task.Execute(ctx)
    }

    // --- Fork 阶段 ---
    subTasks, err := task.Fork(ctx)
    if err != nil {
        var zero T
        return zero, fmt.Errorf("fork failed: %w", err)
    }
    if len(subTasks) == 0 {
        // Fork 产生零个子任务，行为类似于直接计算
        return task.Execute(ctx)
    }

    // --- 并行执行子任务 ---
    results := make([]T, len(subTasks))
    errs := make([]error, len(subTasks)) // 存储每个子任务的错误
    var wg sync.WaitGroup
    childCtx, cancelChildren := context.WithCancel(ctx) // 用于取消所有子任务
    defer cancelChildren() // 确保子上下文被取消

    wg.Add(len(subTasks))
    for i, subTask := range subTasks {
        go func(index int, st Task[T]) {
            defer wg.Done()
            // 尝试获取信号量以并行执行，如果获取失败则在当前 goroutine 同步执行
            if p.sem.TryAcquire(1) {
                defer p.sem.Release(1)
                results[index], errs[index] = p.compute(childCtx, st) // 递归调用 compute
            } else {
                // 无法获取许可，同步执行（防止过多 goroutine）
                results[index], errs[index] = p.compute(childCtx, st)
            }
            // 如果当前子任务出错，取消其他子任务
            if errs[index] != nil {
                cancelChildren()
            }
        }(i, subTask)
    }

    wg.Wait() // 等待所有子任务完成

    // --- Join 阶段 ---
    // 检查是否有错误发生
    var firstErr error
    for _, e := range errs {
        if e != nil {
            firstErr = e
            break // 只返回第一个错误
        }
    }

    // 如果子任务出错或上下文取消，则返回错误
    if firstErr != nil {
        // 优先返回子任务执行错误
        var zero T
        return zero, firstErr
    }
    select {
        case <-ctx.Done(): // 检查原始上下文是否取消
            var zero T
            return zero, ctx.Err()
        default:
    }


    // 所有子任务成功，合并结果
    return task.Join(ctx, results)
}
```

##### 递归任务 (RecursiveTask)

一个辅助结构体，简化实现常见的递归分解任务。

```go
package forkjoin

import "context"

// RecursiveAction 定义没有返回值的递归任务 (简化版)
type RecursiveAction[T any] struct {
    Data      T
    Threshold int
    Size      func(T) int       // 计算数据大小
    Split     func(T) []T       // 分割数据
    Compute   func(context.Context, T) error // 直接计算小块数据
}

func (ra *RecursiveAction[T]) Execute(ctx context.Context) (struct{}, error) {
    return struct{}{}, ra.Compute(ctx, ra.Data)
}

func (ra *RecursiveAction[T]) ShouldFork(ctx context.Context) bool {
    return ra.Size(ra.Data) > ra.Threshold
}

func (ra *RecursiveAction[T]) Fork(ctx context.Context) ([]Task[struct{}], error) {
    parts := ra.Split(ra.Data)
    tasks := make([]Task[struct{}], len(parts))
    for i, part := range parts {
        tasks[i] = &RecursiveAction[T]{ // 创建新的子任务实例
            Data:      part,
            Threshold: ra.Threshold,
            Size:      ra.Size,
            Split:     ra.Split,
            Compute:   ra.Compute,
        }
    }
    return tasks, nil
}

func (ra *RecursiveAction[T]) Join(ctx context.Context, results []struct{}) (struct{}, error) {
    // 对于 Action，Join 通常是无操作或只检查错误（已在 compute 中处理）
    return struct{}{}, nil
}

// RecursiveTask 定义有返回值的递归任务
type RecursiveTask[T any, R any] struct {
    Data      T
    Threshold int
    Size      func(T) int       // 计算数据大小
    Split     func(T) []T       // 分割数据
    Compute   func(context.Context, T) (R, error) // 直接计算小块数据
    Combine   func([]R) (R, error) // 合并子结果
}

func (rt *RecursiveTask[T, R]) Execute(ctx context.Context) (R, error) {
    return rt.Compute(ctx, rt.Data)
}

func (rt *RecursiveTask[T, R]) ShouldFork(ctx context.Context) bool {
    return rt.Size(rt.Data) > rt.Threshold
}

func (rt *RecursiveTask[T, R]) Fork(ctx context.Context) ([]Task[R], error) {
    parts := rt.Split(rt.Data)
    tasks := make([]Task[R], len(parts))
    for i, part := range parts {
        tasks[i] = &RecursiveTask[T, R]{ // 创建新的子任务实例
            Data:      part,
            Threshold: rt.Threshold,
            Size:      rt.Size,
            Split:     rt.Split,
            Compute:   rt.Compute,
            Combine:   rt.Combine,
        }
    }
    return tasks, nil
}

func (rt *RecursiveTask[T, R]) Join(ctx context.Context, results []R) (R, error) {
    return rt.Combine(results)
}
```

##### 并行 For 与并行 Reduce

使用 Fork-Join 池来实现常见的并行循环和归约操作。

```go
package forkjoin

import "context"

// ParallelFor 使用 Fork-Join 池并行执行一个函数，应用于数据切片的每个（或每批）元素
// pool: ForkJoinPool 实例
// items: 要处理的数据切片
// batchSize: 每个子任务处理的数据量（阈值）
// fn: 应用于每个批次数据的函数
func ParallelFor[T any](
 ctx context.Context,
 pool *ForkJoinPool,
 items []T,
 batchSize int,
 fn func(ctx context.Context, batch []T) error,
) error {
 if len(items) == 0 { return nil }
 if batchSize <= 0 { batchSize = 1 }

 // 创建一个 RecursiveAction 任务
 task := &RecursiveAction[[]T]{
  Data:      items,
  Threshold: batchSize,
  Size: func(data []T) int {
   return len(data)
  },
  Split: func(data []T) [][]T {
   // 基本的二分法分割
   if len(data) <= batchSize { // 防止无限分割
       return [][]T{data}
   }
   mid := len(data) / 2
   if mid == 0 && len(data) > 0 { // 处理小切片
        return [][]T{data}
   } else if mid > 0 {
        return [][]T{data[:mid], data[mid:]}
   }
   return nil // 空切片
  },
  Compute: func(ctx context.Context, batch []T) error {
      // 对小块数据执行 fn
      if len(batch) > 0 {
        return fn(ctx, batch)
      }
      return nil
  },
 }

 // 使用 ForkJoinPool 执行
 _, err := pool.Invoke(ctx, task)
 return err
}

// ParallelReduce 使用 Fork-Join 池并行地对数据切片进行映射和归约
// pool: ForkJoinPool 实例
// items: 要处理的数据切片
// batchSize: 每个子任务处理的数据量（阈值）
// mapFn: 应用于每个批次数据并产生中间结果的函数
// reduceFn: 合并两个中间结果的函数
// identity: 归约操作的幺元（零值）
func ParallelReduce[T any, R any](
 ctx context.Context,
 pool *ForkJoinPool,
 items []T,
 batchSize int,
 mapFn func(ctx context.Context, batch []T) (R, error),
 reduceFn func(left R, right R) (R, error), // 合并函数
 identity R, // 归约的初始/零值
) (R, error) {
 if len(items) == 0 {
  return identity, nil
 }
 if batchSize <= 0 { batchSize = 1 }

 // 创建一个 RecursiveTask 任务
 task := &RecursiveTask[[]T, R]{
  Data:      items,
  Threshold: batchSize,
  Size: func(data []T) int {
   return len(data)
  },
  Split: func(data []T) [][]T {
      if len(data) <= batchSize { return [][]T{data} }
      mid := len(data) / 2
      if mid == 0 && len(data) > 0 { return [][]T{data} }
      if mid > 0 { return [][]T{data[:mid], data[mid:]} }
      return nil
  },
  Compute: func(ctx context.Context, batch []T) (R, error) {
      // 对小块数据执行 mapFn
      if len(batch) > 0 {
        return mapFn(ctx, batch)
      }
      return identity, nil // 空批次返回 identity
  },
  Combine: func(results []R) (R, error) {
      // 合并子任务的结果
      finalResult := identity
      var combineErr error
      for _, res := range results {
          finalResult, combineErr = reduceFn(finalResult, res)
          if combineErr != nil {
              // 如何处理合并错误？可以返回错误或记录
              // return identity, fmt.Errorf("reduce combine error: %w", combineErr)
              // 这里选择继续合并，但可能结果不正确
          }
      }
      return finalResult, combineErr // 返回最终合并结果和可能的最后一个错误
  },
 }

 // 使用 ForkJoinPool 执行
 return pool.Invoke(ctx, task)
}
```

---

### 2.6 并发模式选择与权衡 (扩展讨论)

选择合适的并发模式取决于具体场景：

- **任务分发与处理**:
  - `Worker Pool`: 控制固定数量 worker 处理独立任务，管理资源。
  - `Fan-Out/Fan-In`: 将一批数据分发给多个 worker 并行处理，然后合并结果。
- **数据流处理**:
  - `Pipeline`: 顺序处理数据流，每个阶段处理特定逻辑。
  - `CSP`: 使用 channel 构建灵活的数据流和 goroutine 协作。
- **异步操作**:
  - `Future/Promise`: 获取异步操作的结果，避免阻塞。
  - `goroutine + channel`: Go 原生的异步通信方式。
- **同步与资源共享**:
  - `Mutex/RWLock`: 保护共享内存访问。
  - `Semaphore`: 控制对有限资源的访问数量。
  - `Barrier`: 同步多个 goroutine 在某一点汇合。
  - `atomic`: 高性能原子操作，适用于简单计数或状态。
- **并发控制与弹性**:
  - `Context`: 控制 goroutine 生命周期，传递取消信号和超时。
  - `Rate Limiter`: 限制操作速率。
  - `Circuit Breaker`: 防止对故障服务的重复调用。
  - `Bulkhead`: 隔离资源，防止故障蔓延。
- **消息通信**:
  - `Pub/Sub`: 解耦发布者和订阅者。
  - `Actor`: 封装状态和行为，通过消息通信，适合有状态并发。
- **并行计算**:
  - `Map-Reduce`: 大规模数据聚合。
  - `Fork-Join`: 分治算法的并行化。

**权衡**:

- **复杂度**: CSP 和 Actor 模式可能比简单的 Mutex 或 Worker Pool 更复杂。
- **性能**: 原子操作通常最快，但适用性有限。锁在高争用下有开销。Channel 通信有一定开销。
- **灵活性**: CSP 提供了高度灵活的 goroutine 协作方式。Actor 模式易于构建分布式系统。
- **状态管理**: Actor 模式天然适合有状态并发。共享内存+锁需要仔细设计状态管理。

---

### 2.7 分布式并发模式简介 (扩展讨论)

当并发扩展到多台机器时，需要考虑分布式环境的挑战：

- **分布式锁**: 使用 ZooKeeper, etcd, Redis 等实现跨机器的互斥访问。
- **分布式队列**: Kafka, RabbitMQ, NATS 等用于跨服务任务分发。
- **分布式事务**:
  - **Saga 模式**: 通过一系列本地事务和补偿操作实现最终一致性。
  - **两阶段提交 (2PC) / 三阶段提交 (3PC)**: 强一致性协议，但复杂且可能阻塞。
- **分布式一致性**: Raft, Paxos 等共识算法用于维护副本间状态一致。
- **服务发现**: Consul, etcd 等用于查找和连接分布式服务。
- **远程过程调用 (RPC)**: gRPC, Thrift 等用于服务间通信。

Go 语言及其生态系统（如 gRPC, NATS client, etcd client）为实现这些分布式模式提供了良好的支持。

---

## 3. 工作流模式与系统实现

工作流系统用于编排一系列按特定规则执行的任务或活动。Go 语言的并发特性和接口使其成为构建灵活、高效工作流引擎的良好选择。

### 3.1 工作流核心概念

定义工作流引擎的基础组件。

#### 活动 (Activity)

工作流中的基本执行单元。

```go
// 任何可在工作流中执行的活动
type Activity[T any] interface {
 Execute(ctx context.Context, input T) (T, error) // 输入输出类型相同，简化示例
 Name() string
}

// 可以定义输入输出不同的活动接口
type ActivityInOut[InputT any, OutputT any] interface {
    Execute(ctx context.Context, input InputT) (OutputT, error)
    Name() string
}

// 基础活动结构，方便嵌入
type BaseActivity struct {
    ActivityName string
}
func (b *BaseActivity) Name() string { return b.ActivityName }
```

#### 工作流上下文 (WorkflowContext)

包含工作流执行过程中的状态、数据和元数据。

```go
// 工作流上下文，包含工作流执行的状态
type WorkflowContext[T any] struct {
 Data         T                 // 工作流实例的数据
 ActivityPath []string          // 记录执行过的活动路径
 StartTime    time.Time         // 工作流开始时间
 Metadata     map[string]any    // 存储额外信息
 mutex        sync.RWMutex      // 保护上下文内部状态
}

// 创建新的工作流上下文
func NewWorkflowContext[T any](initialData T) *WorkflowContext[T] {
 return &WorkflowContext[T]{
  Data:         initialData,
  ActivityPath: make([]string, 0),
  StartTime:    time.Now(),
  Metadata:     make(map[string]any),
 }
}

// GetData 获取上下文数据 (线程安全)
func (wc *WorkflowContext[T]) GetData() T {
 wc.mutex.RLock()
 defer wc.mutex.RUnlock()
 return wc.Data
}

// SetData 设置上下文数据 (线程安全)
func (wc *WorkflowContext[T]) SetData(data T) {
 wc.mutex.Lock()
 defer wc.mutex.Unlock()
 wc.Data = data
}

// RecordActivity 记录活动执行路径 (线程安全)
func (wc *WorkflowContext[T]) RecordActivity(name string) {
 wc.mutex.Lock()
 defer wc.mutex.Unlock()
 wc.ActivityPath = append(wc.ActivityPath, name)
}

// GetMetadata 获取元数据 (线程安全)
func (wc *WorkflowContext[T]) GetMetadata(key string) (any, bool) {
 wc.mutex.RLock()
 defer wc.mutex.RUnlock()
 val, ok := wc.Metadata[key]
 return val, ok
}

// SetMetadata 设置元数据 (线程安全)
func (wc *WorkflowContext[T]) SetMetadata(key string, value any) {
 wc.mutex.Lock()
 defer wc.mutex.Unlock()
 wc.Metadata[key] = value
}
```

#### 工作流定义 (Workflow)

定义了工作流的结构（通常是根活动）和生命周期回调。

```go
// 基本工作流定义
type Workflow[T any] struct {
 Name       string                 // 工作流名称
 RootNode   Activity[T]            // 工作流的入口活动
 OnComplete func(*WorkflowContext[T]) // 完成时的回调
 OnError    func(*WorkflowContext[T], error) // 出错时的回调
}

// 用于在 context 中传递 WorkflowContext 的键
type workflowCtxKeyType struct{}
var workflowCtxKey = workflowCtxKeyType{}

// Execute 执行工作流
func (w *Workflow[T]) Execute(ctx context.Context, input T) (T, error) {
 workflowCtx := NewWorkflowContext(input)

 // 将 WorkflowContext 放入 Go 的 context 中，以便活动访问
 ctx = context.WithValue(ctx, workflowCtxKey, workflowCtx)
 // 也可放入其他工作流级别的元数据
 // ctx = context.WithValue(ctx, "workflowName", w.Name)

 workflowCtx.RecordActivity("WorkflowStart:" + w.Name)

 result, err := w.RootNode.Execute(ctx, input) // 执行根活动

 workflowCtx.RecordActivity("WorkflowEnd:" + w.Name)

 if err != nil {
  workflowCtx.SetMetadata("error", err.Error())
  if w.OnError != nil {
      // 运行在单独 goroutine 防止阻塞 Execute 返回？看需求
      // go w.OnError(workflowCtx, err)
      w.OnError(workflowCtx, err)
  }
  // 尝试从错误中提取来源活动
  activityErr := &ActivityError{}
  sourceActivity := "未知"
  if errors.As(err, &activityErr) {
      sourceActivity = activityErr.ActivityName
  }
  return result, fmt.Errorf("工作流 '%s' 在活动 '%s' 失败: %w", w.Name, sourceActivity, err)
 }

 workflowCtx.SetData(result) // 更新最终数据
 if w.OnComplete != nil {
     // go w.OnComplete(workflowCtx) // 异步回调？
     w.OnComplete(workflowCtx)
 }

 return result, nil
}

// Helper to get WorkflowContext from Go context
func GetWorkflowContext[T any](ctx context.Context) (*WorkflowContext[T], bool) {
    wc, ok := ctx.Value(workflowCtxKey).(*WorkflowContext[T])
    return wc, ok
}


// --- ActivityError 和 WrapActivityError ---
// 定义一个包装错误的类型，用于携带活动名称
type ActivityError struct {
    ActivityName string
    Err error
}
func (e *ActivityError) Error() string { return fmt.Sprintf("%s: %v", e.ActivityName, e.Err) }
func (e *ActivityError) Unwrap() error { return e.Err }

// 包装错误的辅助函数
func WrapActivityError[T any](activity Activity[T], err error) error {
    if err == nil { return nil }
    // 避免重复包装
    if _, ok := err.(*ActivityError); ok { return err }
    return &ActivityError{ActivityName: activity.Name(), Err: err}
}

// --- 错误定义 ---
var (
 ErrActivityFailed      = errors.New("活动执行失败")
 ErrWorkflowCancelled   = errors.New("工作流被取消")
 ErrTimeout             = errors.New("执行超时")
 ErrResourceUnavailable = errors.New("资源不可用")
 ErrConditionNotMet     = errors.New("条件不满足")
 ErrCompensationFailed  = errors.New("补偿操作失败")
 ErrInvalidState        = errors.New("无效的工作流状态")
 ErrInvalidPermits      = errors.New("invalid number of permits requested")
)
```

#### 基础架构代码

```go
package workflow

import (
 "context"
 "errors"
 "fmt"
 "sync"
 "time"
 // "strings" // 用于 extractErrorSource
)

// (包含上面 Activity, WorkflowContext, Workflow, ActivityError, WrapActivityError, 错误定义 的代码)

```

---

### 3.2 控制流模式 (Control-Flow Patterns)

定义工作流中活动的执行顺序和逻辑。

#### 3.2.1 顺序 (Sequence)

按预定义顺序依次执行一系列活动。

##### Sequence：实现与代码示例

```go
package workflow

import (
 "context"
 // "fmt"
)

// 顺序模式：按顺序执行多个活动
type SequenceActivity[T any] struct {
 Name_      string
 Activities []Activity[T]
}

// NewSequence 创建顺序活动
func NewSequence[T any](name string, activities ...Activity[T]) *SequenceActivity[T] {
 return &SequenceActivity[T]{Name_: name, Activities: activities}
}

func (s *SequenceActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 result := input
 var err error

 // 尝试从 context 获取 WorkflowContext 以记录路径
 wc, wcOK := GetWorkflowContext[T](ctx)

 for _, activity := range s.Activities {
  // 检查上下文取消
  select {
  case <-ctx.Done():
   return result, WrapActivityError(s, ctx.Err())
  default:
  }

  // 记录活动开始 (如果 WorkflowContext 可用)
  if wcOK {
      wc.RecordActivity(activity.Name() + ":Start")
  }

  // 执行活动
  result, err = activity.Execute(ctx, result)

   // 记录活动结束 (如果 WorkflowContext 可用)
  if wcOK {
       if err != nil {
           wc.RecordActivity(activity.Name() + ":Error")
       } else {
           wc.RecordActivity(activity.Name() + ":End")
       }
   }


  if err != nil {
   // 包装错误
   return result, WrapActivityError(activity, err)
  }
 }

 return result, nil
}

func (s *SequenceActivity[T]) Name() string {
 if s.Name_ == "" { return "Sequence" }
 return s.Name_
}
```

#### 3.2.2 并行分支/同步 (Parallel Split/Synchronization)

并行执行多个活动分支，并在所有分支完成后同步。

##### Parallel：实现与代码示例

```go
package workflow

import (
 "context"
 "sync"
 "errors"
 "fmt"
)

// 并行分支模式：并行执行多个活动
// R 是每个并行活动产生的结果类型（与 T 可能不同）
// Merger 函数用于将所有并行结果 R 合并回 T 类型
type ParallelActivity[T any, R any] struct {
 Name_         string
 Activities    []Activity[T] // 假设所有并行活动输入都是 T
 ResultMapper  func(T) (R, error) // 将每个分支的 T 结果转换为 R
 ResultMerger  func([]R, T) (T, error) // 合并 R 列表和原始 T 到最终 T
}

// NewParallel 创建并行活动
func NewParallel[T any, R any](name string, merger func([]R, T) (T, error), mapper func(T) (R, error), activities ...Activity[T]) *ParallelActivity[T, R] {
    if mapper == nil { // 提供默认映射器（如果 R 和 T 相同）
        // This requires R and T to be the same type, which generics can't enforce here directly.
        // A runtime check or separate constructor might be needed if R != T requires a mapper.
        // Assuming R and T can be the same for a default:
        mapper = func(val T) (R, error) {
            var r R
            if c, ok := any(val).(R); ok {
                r = c
                return r, nil
            }
            // This default is unsafe if T and R are different.
            // Consider panicking or requiring mapper if R != T.
            return r, fmt.Errorf("default mapper requires R and T to be the same type, or T assignable to R")
        }
    }
    if merger == nil {
        // Provide a default merger that returns the original input T (ignoring R results)
         merger = func(results []R, original T) (T, error) { return original, nil }
    }

    return &ParallelActivity[T, R]{
        Name_:        name,
        Activities:   activities,
        ResultMapper: mapper,
        ResultMerger: merger,
    }
}


func (p *ParallelActivity[T, R]) Execute(ctx context.Context, input T) (T, error) {
 numActivities := len(p.Activities)
 if numActivities == 0 {
  return input, nil
 }

 var wg sync.WaitGroup
 results := make([]R, numActivities)
 errs := make([]error, numActivities)
 childCtx, cancel := context.WithCancel(ctx) // 子上下文用于取消所有分支
 defer cancel()

 wc, wcOK := GetWorkflowContext[T](ctx) // 获取 WorkflowContext

 for i, activity := range p.Activities {
  wg.Add(1)
  go func(index int, act Activity[T]) {
   defer wg.Done()

   // 记录活动开始 (需要线程安全地访问 wc)
   if wcOK {
       // wc.mutex.Lock() // 假设有锁
       // wc.RecordActivity(act.Name() + ":Start_Parallel")
       // wc.mutex.Unlock()
   }

   activityResult, err := act.Execute(childCtx, input) // 使用子上下文

   // 记录活动结束
   if wcOK {
       // wc.mutex.Lock()
       // if err != nil { wc.RecordActivity(act.Name() + ":Error_Parallel") } else { wc.RecordActivity(act.Name() + ":End_Parallel") }
       // wc.mutex.Unlock()
   }


   if err != nil {
       // 使用原子或锁保护 errs 的写入？ 或者使用 channel
       errs[index] = WrapActivityError(act, err)
       cancel() // 立即取消其他分支
       return
   }
   // 在取消前检查上下文是否已由其他 goroutine 取消
   select {
       case <-childCtx.Done():
           errs[index] = childCtx.Err()
           return
       default:
   }

   // 映射结果
   mappedResult, mapErr := p.ResultMapper(activityResult)
   if mapErr != nil {
    errs[index] = WrapActivityError(act, fmt.Errorf("result mapping failed: %w", mapErr))
    cancel()
    return
   }
   results[index] = mappedResult

  }(i, activity)
 }

 wg.Wait()

 // 收集第一个错误
 var firstError error
 for i, err := range errs {
     if err != nil {
         // 过滤掉由 cancel() 引起的 context canceled 错误（除非它是唯一的错误）
         if errors.Is(err, context.Canceled) || errors.Is(err, context.DeadlineExceeded) {
             // 如果还没有其他错误，记录取消错误
             if firstError == nil {
                 firstError = err
             }
         } else {
             // 记录第一个非取消错误
             if firstError == nil || errors.Is(firstError, context.Canceled) || errors.Is(firstError, context.DeadlineExceeded){
                firstError = err
             }
             // 如果希望聚合所有非取消错误，可以在这里收集
         }
     }
 }


 if firstError != nil {
     // 返回原始输入和遇到的第一个（非取消优先）错误
     return input, WrapActivityError(p, firstError)
 }

 // 合并结果
 finalResult, mergeErr := p.ResultMerger(results, input)
 if mergeErr != nil {
  return input, WrapActivityError(p, fmt.Errorf("result merging failed: %w", mergeErr))
 }

 return finalResult, nil
}

func (p *ParallelActivity[T, R]) Name() string {
 if p.Name_ == "" { return "Parallel" }
 return p.Name_
}
```

#### 3.2.3 排他选择/简单合并 (Exclusive Choice/Simple Merge)

基于条件判断，选择唯一一个分支执行。

##### Condition：实现与代码示例

```go
package workflow

import (
 "context"
 "fmt"
 // "errors"
)

// 条件选择模式：基于条件选择一个活动执行
type ConditionActivity[T any] struct {
 Name_             string
 ConditionFunc     func(ctx context.Context, data T) (bool, error) // 条件函数，接收上下文
 TruePathActivity  Activity[T]           // 条件为 true 时执行
 FalsePathActivity Activity[T]           // 条件为 false 时执行 (可选)
}

// NewCondition 创建条件活动
func NewCondition[T any](name string, condition func(ctx context.Context, data T) (bool, error), truePath Activity[T], falsePath Activity[T]) *ConditionActivity[T] {
 return &ConditionActivity[T]{
  Name_:            name,
  ConditionFunc:    condition,
  TruePathActivity: truePath,
  FalsePathActivity: falsePath,
 }
}

func (c *ConditionActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 wc, wcOK := GetWorkflowContext[T](ctx) // 获取 WorkflowContext

 // 执行条件判断
 conditionMet, err := c.ConditionFunc(ctx, input)
 if err != nil {
  return input, WrapActivityError(c, fmt.Errorf("condition check failed: %w", err))
 }

 var selectedActivity Activity[T]
 branchName := ""

 if conditionMet {
  if c.TruePathActivity == nil {
   if wcOK { wc.RecordActivity(c.Name() + ":Branch[true]_NoOp") }
   return input, nil // 条件满足但无 True 分支
  }
  selectedActivity = c.TruePathActivity
  branchName = "true"
 } else {
  if c.FalsePathActivity == nil {
   if wcOK { wc.RecordActivity(c.Name() + ":Branch[false]_NoOp") }
   return input, nil // 条件不满足但无 False 分支
  }
  selectedActivity = c.FalsePathActivity
  branchName = "false"
 }

 // 记录选择了哪个分支
 if wcOK {
     wc.RecordActivity(fmt.Sprintf("%s:Branch[%s]", c.Name(), branchName))
     wc.RecordActivity(selectedActivity.Name() + ":Start_Condition")
 }

 // 执行选定的活动
 result, err := selectedActivity.Execute(ctx, input)

 if wcOK {
     if err != nil { wc.RecordActivity(selectedActivity.Name() + ":Error_Condition") } else { wc.RecordActivity(selectedActivity.Name() + ":End_Condition") }
 }


 if err != nil {
  // 包装错误
  return result, WrapActivityError(selectedActivity, err)
 }

 return result, nil
}

func (c *ConditionActivity[T]) Name() string {
 if c.Name_ == "" { return "Condition" }
 return c.Name_
}
```

#### 3.2.4 多选择/同步合并 (Multi-Choice/Synchronizing Merge)

基于多个条件判断，可能并行执行多个满足条件的分支，最后等待所有执行的分支完成并合并结果。

##### MultiChoice：实现与代码示例

```go
package workflow

import (
 "context"
 "sync"
 "fmt"
 // "errors"
)

// Choice 定义了多选择中的一个分支及其条件
type Choice[T any] struct {
    Condition func(ctx context.Context, data T) (bool, error)
    Activity  Activity[T]
}

// MultiChoiceActivity 模式：可能执行多条路径，然后合并结果
type MultiChoiceActivity[T any] struct {
 Name_         string
 Choices       []Choice[T]             // 条件和对应的活动
 MergeResults func([]T) (T, error)    // 合并所有成功执行分支的结果
 FailFast      bool                    // 是否在一个分支失败时取消其他分支 (可选)
}

// NewMultiChoice 创建多选择活动
func NewMultiChoice[T any](name string, merger func([]T) (T, error), choices ...Choice[T]) *MultiChoiceActivity[T] {
    if merger == nil {
        // 默认合并：返回第一个结果或初始值 (可能需要更智能的默认)
        merger = func(results []T) (T, error) {
            if len(results) > 0 {
                return results[0], nil
            }
            var zero T
            return zero, nil
        }
    }
    return &MultiChoiceActivity[T]{
        Name_:        name,
        Choices:      choices,
        MergeResults: merger,
        FailFast:     true, // 默认快速失败
    }
}


func (m *MultiChoiceActivity[T]) Execute(ctx context.Context, input T) (T, error) {
    var wg sync.WaitGroup
    var mutex sync.Mutex // 保护 results 和 errs 的并发写入
    results := make([]T, 0)
    errs := make([]error, 0) // 收集错误
    selectedCount := 0

    childCtx, cancel := context.WithCancel(ctx) // 用于 FailFast
    defer cancel()

    wc, wcOK := GetWorkflowContext[T](ctx)

    for i, choice := range m.Choices {
        conditionMet, err := choice.Condition(childCtx, input) // 使用子上下文检查条件
        if err != nil {
             err = WrapActivityError(m, fmt.Errorf("choice %d condition check failed: %w", i, err))
             mutex.Lock()
             errs = append(errs, err)
             mutex.Unlock()
             if m.FailFast { cancel() } // 条件检查失败也可能触发 FailFast
             continue // 跳过此分支
        }

        if conditionMet {
            selectedCount++
            wg.Add(1)
            go func(idx int, act Activity[T]) {
                defer wg.Done()

                // 记录分支开始
                branchName := fmt.Sprintf("Choice[%d]_%s", idx, act.Name())
                if wcOK { /* wc.RecordActivity(branchName + ":Start_MultiChoice") */ } // 需要锁

                // 执行活动
                result, execErr := act.Execute(childCtx, input) // 使用子上下文

                // 记录分支结束
                if wcOK { /* ... Record End or Error ... */ } // 需要锁

                mutex.Lock() // 加锁保护共享变量
                if execErr != nil {
                    errs = append(errs, WrapActivityError(act, execErr))
                    if m.FailFast {
                        cancel() // 快速失败，取消其他分支
                    }
                } else {
                    // 只有成功的结果才添加到 results 列表
                     select {
                     case <-childCtx.Done(): // 如果在成功后被取消了，就不添加结果？
                     default: results = append(results, result)
                     }
                }
                mutex.Unlock() // 解锁

            }(i, choice.Activity)
        }
    }

    wg.Wait() // 等待所有选定并启动的分支完成或被取消

    // --- 处理结果和错误 ---
    // 检查是否有错误发生
    var firstError error
    for _, e := range errs {
         if e != nil {
             if errors.Is(e, context.Canceled) || errors.Is(e, context.DeadlineExceeded) {
                 if firstError == nil { firstError = e }
             } else {
                 if firstError == nil || errors.Is(firstError, context.Canceled) || errors.Is(firstError, context.DeadlineExceeded) {
                     firstError = e
                 }
             }
         }
    }


    if firstError != nil {
        // 如果有错误，返回错误和原始输入（或部分结果？取决于设计）
        // 即使有错误，MergeResults 是否仍应被调用以处理部分成功的结果？
        // 假设不调用 MergeResults，直接返回错误
        return input, WrapActivityError(m, firstError)
    }

    // 如果没有错误且没有分支被执行
    if selectedCount == 0 || len(results) == 0 {
        if wcOK { wc.RecordActivity(m.Name() + ":NoChoiceTaken") }
        return input, nil // 没有分支执行或成功，返回原始输入
    }

    // 合并成功的结果
    finalResult, mergeErr := m.MergeResults(results)
    if mergeErr != nil {
        return input, WrapActivityError(m, fmt.Errorf("result merging failed: %w", mergeErr))
    }

    return finalResult, nil
}


func (m *MultiChoiceActivity[T]) Name() string {
 if m.Name_ == "" { return "MultiChoice" }
 return m.Name_
}
```

#### 3.2.5 循环 (Loop)

重复执行某个活动或子流程，直到满足退出条件。

##### Loop：实现与代码示例

```go
package workflow

import (
 "context"
 "fmt"
 // "errors"
)

// 循环模式：重复执行直到条件满足
type LoopActivity[T any] struct {
 Name_        string
 LoopActivity Activity[T]                // 要循环执行的活动
 // Condition 返回 true 时继续循环，返回 false 时退出
 Condition    func(ctx context.Context, data T, iteration int) (bool, error)
 MaxIterations int                     // 可选：最大迭代次数，防止无限循环 (0 表示不限制)
}

// NewLoop 创建循环活动
func NewLoop[T any](name string, condition func(ctx context.Context, data T, iteration int) (bool, error), loopActivity Activity[T]) *LoopActivity[T] {
    return &LoopActivity[T]{
        Name_:        name,
        Condition:    condition,
        LoopActivity: loopActivity,
        MaxIterations: 0, // 默认不限制
    }
}

// WithMaxIterations 设置最大迭代次数
func (l *LoopActivity[T]) WithMaxIterations(max int) *LoopActivity[T] {
    if max >= 0 {
        l.MaxIterations = max
    }
    return l
}

func (l *LoopActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 result := input
 iteration := 0
 wc, wcOK := GetWorkflowContext[T](ctx)

 for {
  // 0. 检查上下文取消
  select {
  case <-ctx.Done():
   return result, WrapActivityError(l, ctx.Err())
  default:
  }

  // 1. 检查最大迭代次数
  if l.MaxIterations > 0 && iteration >= l.MaxIterations {
      err := fmt.Errorf("loop '%s' exceeded max iterations (%d)", l.Name(), l.MaxIterations)
      return result, WrapActivityError(l, err)
  }

  // 2. 检查循环条件
  continueLoop, err := l.Condition(ctx, result, iteration)
  if err != nil {
      err = fmt.Errorf("loop '%s' condition check failed at iteration %d: %w", l.Name(), iteration, err)
      return result, WrapActivityError(l, err)
  }

  if !continueLoop {
      if wcOK { wc.RecordActivity(fmt.Sprintf("%s:ConditionFalse_Iter%d", l.Name(), iteration)) }
      break // 条件不满足，退出循环
  }

  // 3. 执行循环体活动
  iteration++ // 增加迭代计数器
  if wcOK { wc.RecordActivity(fmt.Sprintf("%s:Iter%d_Start", l.Name(), iteration)) }

  loopResult, loopErr := l.LoopActivity.Execute(ctx, result)

  if wcOK {
      if loopErr != nil { wc.RecordActivity(fmt.Sprintf("%s:Iter%d_Error", l.Name(), iteration)) } else { wc.RecordActivity(fmt.Sprintf("%s:Iter%d_End", l.Name(), iteration)) }
  }


  if loopErr != nil {
      // 循环体执行错误，包装错误并退出
      err = fmt.Errorf("loop '%s' body failed at iteration %d: %w", l.Name(), iteration, loopErr)
      return loopResult, WrapActivityError(l.LoopActivity, err)
  }

  result = loopResult // 更新结果，用于下一次条件检查和循环体执行

 } // end for

 return result, nil // 循环正常结束
}


func (l *LoopActivity[T]) Name() string {
 if l.Name_ == "" { return "Loop" }
 return l.Name_
}
```

#### 3.2.6 多实例 (Multiple Instances)

为数据集中的每个项并行或顺序地执行同一个活动或子流程。

##### MultiInstance：实现与代码示例

```go
package workflow

import (
 "context"
 "sync"
 "fmt"
 // "errors"
)

// MultiInstanceActivity 模式：为集合中的每个项目执行同一活动
// T: 整体工作流数据类型
// I: 集合中单个项目的类型
// R: 每个实例执行后产生的结果类型
type MultiInstanceActivity[T any, I any, R any] struct {
 Name_           string
 ItemActivity    Activity[I]                // 对单个项目执行的活动
 ItemsExtractor  func(T) ([]I, error)       // 从工作流数据 T 中提取项目列表 I
 ResultAggregator func([]R, T) (T, error)    // 将所有实例的结果 R 聚合回工作流数据 T
 // ResultMapper func(I, I) R // 旧的定义，假设 Activity[I] 返回 I
 // ResultMapper func(I, R) R // 更通用的定义，需要知道 ItemActivity 的输出类型？
 // 假设 ItemActivity 的 Execute 返回的类型就是 R
 // 或者让 ItemActivity 是 ActivityInOut[I, R]
 // 为了简化，假设 ItemActivity 返回 I，然后聚合器处理 []I
 // --- 调整：让 ItemActivity 是 ActivityInOut[I, R] ---
 ItemActivityTyped ActivityInOut[I, R] // 使用输入输出不同的活动接口
 ResultAggregatorTyped func(map[int]R, T) (T, error) // 按索引聚合结果 R 列表和原始 T 到最终 T
 Parallel          bool                  // 是否并行执行实例 (默认 false)
 FailFast          bool                  // 并行执行时，是否快速失败
}

// NewMultiInstance 创建多实例活动 (顺序执行)
func NewMultiInstance[T any, I any, R any](name string,
    extractor func(T) ([]I, error),
    itemActivity ActivityInOut[I, R], // 明确使用 InOut 接口
    aggregator func(map[int]R, T) (T, error)) *MultiInstanceActivity[T, I, R] {
    return &MultiInstanceActivity[T, I, R]{
        Name_:            name,
        ItemsExtractor:   extractor,
        ItemActivityTyped: itemActivity, // 存储 InOut 类型
        ResultAggregatorTyped: aggregator,
        Parallel:         false, // 默认顺序
        FailFast:         true,
    }
}

// SetParallel 设置是否并行执行
func (m *MultiInstanceActivity[T, I, R]) SetParallel(parallel bool, failFast bool) *MultiInstanceActivity[T, I, R] {
    m.Parallel = parallel
    m.FailFast = failFast
    return m
}


func (m *MultiInstanceActivity[T, I, R]) Execute(ctx context.Context, input T) (T, error) {
    // 1. 提取项目列表
    items, err := m.ItemsExtractor(input)
    if err != nil {
        return input, WrapActivityError(m, fmt.Errorf("failed to extract items: %w", err))
    }

    numItems := len(items)
    if numItems == 0 {
        return input, nil // 没有项目，直接返回
    }

    wc, wcOK := GetWorkflowContext[T](ctx)

    // --- 执行实例 ---
    results := make(map[int]R) // 使用 map 存储结果，索引对应原始 items 索引
    errs := make([]error, numItems) // 存储每个实例的错误
    var wg sync.WaitGroup
    var mutex sync.Mutex // 保护 results 和 errs (仅在并行时严格需要)

    execCtx, cancel := context.WithCancel(ctx) // 用于 FailFast
    defer cancel()

    if m.Parallel {
        // --- 并行执行 ---
        wg.Add(numItems)
        for i, item := range items {
            go func(index int, instanceInput I) {
                defer wg.Done()
                instanceName := fmt.Sprintf("%s:Instance[%d]", m.ItemActivityTyped.Name(), index)
                if wcOK { /* Record Start */ }

                // 执行单个实例活动
                result, execErr := m.ItemActivityTyped.Execute(execCtx, instanceInput)

                if wcOK { /* Record End/Error */ }

                mutex.Lock()
                if execErr != nil {
                    errs[index] = WrapActivityError(m.ItemActivityTyped, fmt.Errorf("instance %d failed: %w", index, execErr))
                    if m.FailFast { cancel() } // 快速失败
                } else {
                     select {
                     case <-execCtx.Done(): // 检查是否被取消
                         errs[index] = execCtx.Err()
                     default:
                         results[index] = result // 存储成功结果
                     }
                }
                mutex.Unlock()

            }(i, item)
        }
        wg.Wait() // 等待所有并行实例完成或取消
    } else {
        // --- 顺序执行 ---
        for i, item := range items {
             // 检查上下文取消
             select {
             case <-execCtx.Done():
                 errs[i] = execCtx.Err()
                 break // 停止顺序执行
             default:
             }

             instanceName := fmt.Sprintf("%s:Instance[%d]", m.ItemActivityTyped.Name(), i)
             if wcOK { wc.RecordActivity(instanceName + ":Start_Seq") }

             result, execErr := m.ItemActivityTyped.Execute(execCtx, item)

             if wcOK {
                 if execErr != nil { wc.RecordActivity(instanceName + ":Error_Seq") } else { wc.RecordActivity(instanceName + ":End_Seq") }
             }


             if execErr != nil {
                 errs[i] = WrapActivityError(m.ItemActivityTyped, fmt.Errorf("instance %d failed: %w", i, execErr))
                 // 顺序执行时，是否也需要 FailFast? 如果需要，这里就 break
                 if m.FailFast { // 即使顺序执行也可以选择 FailFast
                     cancel() // 设置取消状态
                     break
                 }
             } else {
                 results[i] = result
             }
        }
    }

    // --- 处理错误 ---
    var firstError error
    for _, e := range errs {
        if e != nil {
             if errors.Is(e, context.Canceled) || errors.Is(e, context.DeadlineExceeded) {
                 if firstError == nil { firstError = e }
             } else {
                 if firstError == nil || errors.Is(firstError, context.Canceled) || errors.Is(firstError, context.DeadlineExceeded){
                     firstError = e
                 }
             }
        }
    }

    if firstError != nil {
        // 返回错误和原始输入
        return input, WrapActivityError(m, firstError)
    }


    // --- 聚合结果 ---
    if m.ResultAggregatorTyped == nil {
        // 如果没有聚合器，直接返回原始输入
        return input, nil
    }

    finalResult, aggErr := m.ResultAggregatorTyped(results, input)
    if aggErr != nil {
        return input, WrapActivityError(m, fmt.Errorf("result aggregation failed: %w", aggErr))
    }

    return finalResult, nil
}


func (m *MultiInstanceActivity[T, I, R]) Name() string {
 if m.Name_ == "" { return "MultiInstance" }
 return m.Name_
}
```

#### 3.2.7 延迟选择 (Deferred Choice) (概念扩展)

与排他选择类似，但选择哪个分支执行的决定不是基于工作流数据本身，而是基于外部事件或与环境的交互。例如，等待用户输入、接收特定消息或满足时间条件。

- **实现思路**:
  - 通常需要一个“等待”活动，该活动会挂起工作流的执行。
  - 引擎需要有能力监听外部事件（如消息队列、定时器、API 调用）。
  - 当特定事件发生时，引擎唤醒对应的工作流实例，并根据事件内容或类型决定执行哪个后续分支。
  - 这通常涉及到工作流引擎的持久化和事件订阅机制。
  - `context` 可以用于传递超时或取消信号给等待活动。

#### 3.2.8 里程碑 (Milestone) (概念扩展)

工作流执行到一个点（里程碑），必须等待某个条件满足（例如，某个状态达成、特定数据可用）才能继续。如果条件在到达里程碑时尚未满足，工作流会在此暂停。

- **实现思路**:
  - 里程碑活动会检查特定条件。
  - 如果条件满足，则直接通过。
  - 如果条件不满足，活动会将工作流置于等待状态，并可能注册一个监听器或触发器，以便在条件满足时重新激活工作流。
  - 这同样需要引擎的持久化和事件处理能力。
  - 与延迟选择的区别在于，延迟选择是等待 *触发分支选择* 的事件，而里程碑是等待 *允许继续执行* 的条件满足。

---

### 3.3 数据流模式 (Data-Flow Patterns)

关注数据如何在工作流活动之间传递、转换和使用。

#### 3.3.1 数据传递 (Data Passing) (隐式实现)

数据在活动之间传递是工作流的基础。在当前实现中：

- `Activity[T]` 接口规定了输入输出类型相同 (`T`)，数据 `result` 在 `SequenceActivity` 等控制流活动中被依次传递。
- `WorkflowContext[T]` 持有整个工作流实例的数据 `Data`，活动可以通过读取和写入 `WorkflowContext`（如果允许）来共享更广泛范围的数据（当前实现未直接提供此机制给活动，活动只接收 T 并返回 T）。
- 可以通过 `context.Context` 传递请求范围的值，但不适合传递大的业务数据。

更复杂的引擎可能提供更明确的数据映射机制，允许活动声明其输入/输出数据项，并由引擎负责在活动间传递和转换数据。

#### 3.3.2 数据转换 (Data Transformation)

活动专门用于修改或转换工作流数据。

##### Transform：实现与代码示例

```go
package workflow

import (
 "context"
 "fmt"
)

// 数据转换模式：应用一个函数来转换数据
// 使用 ActivityInOut 接口更通用
type TransformActivity[TInput any, TOutput any] struct {
 Name_        string
 Transformer  func(ctx context.Context, input TInput) (TOutput, error)
}

// NewTransform 创建转换活动
func NewTransform[TInput any, TOutput any](name string, transformer func(ctx context.Context, input TInput) (TOutput, error)) *TransformActivity[TInput, TOutput] {
 return &TransformActivity[TInput, TOutput]{Name_: name, Transformer: transformer}
}

// Execute 实现 ActivityInOut 接口
func (t *TransformActivity[TInput, TOutput]) Execute(ctx context.Context, input TInput) (TOutput, error) {
 result, err := t.Transformer(ctx, input)
 if err != nil {
  // WrapActivityError 需要适配 ActivityInOut 或提供通用包装器
  // return result, WrapActivityError(t, err) // 假设有通用包装器
  return result, fmt.Errorf("%s: %w", t.Name(), err) // 简单包装
 }
 return result, nil
}

func (t *TransformActivity[TInput, TOutput]) Name() string {
 if t.Name_ == "" { return "Transform" }
 return t.Name_
}

// 如果需要适配 Activity[T] 接口（输入输出同类型）
type TransformActivitySameType[T any] struct {
    Name_        string
    Transformer  func(ctx context.Context, input T) (T, error)
}
func NewTransformSameType[T any](name string, transformer func(ctx context.Context, input T) (T, error)) *TransformActivitySameType[T] {
    return &TransformActivitySameType[T]{Name_: name, Transformer: transformer}
}
func (t *TransformActivitySameType[T]) Execute(ctx context.Context, input T) (T, error) {
     result, err := t.Transformer(ctx, input)
     if err != nil { return result, WrapActivityError(t, err) } // 使用之前的 Wrap 函数
     return result, nil
}
func (t *TransformActivitySameType[T]) Name() string {
    if t.Name_ == "" { return "Transform" }
    return t.Name_
}

```

#### 3.3.3 数据路由 (Data-based Routing)

根据工作流数据的 *内容* 来决定接下来执行哪个活动分支（类似于 `ConditionActivity`，但路由逻辑可能更复杂）。

##### DataRouting：实现与代码示例

```go
package workflow

import (
 "context"
 "fmt"
 // "errors"
)

// 数据路由模式：基于数据内容选择执行路径
type DataRoutingActivity[T any] struct {
 Name_      string
 // Router 函数返回一个字符串键，用于选择下一个活动
 Router     func(ctx context.Context, data T) (string, error)
 Activities map[string]Activity[T] // 路由键 -> 活动 映射
 DefaultActivity Activity[T]           // 可选：当没有路由匹配时执行的默认活动
}

// NewDataRouter 创建数据路由活动
func NewDataRouter[T any](name string, router func(ctx context.Context, data T) (string, error), activities map[string]Activity[T]) *DataRoutingActivity[T] {
 return &DataRoutingActivity[T]{
  Name_:      name,
  Router:     router,
  Activities: activities,
 }
}

// WithDefault 设置默认活动
func (d *DataRoutingActivity[T]) WithDefault(defaultActivity Activity[T]) *DataRoutingActivity[T] {
    d.DefaultActivity = defaultActivity
    return d
}

func (d *DataRoutingActivity[T]) Execute(ctx context.Context, input T) (T, error) {
 wc, wcOK := GetWorkflowContext[T](ctx)

 // 确定路由键
 routeKey, err := d.Router(ctx, input)
 if err != nil {
  return input, WrapActivityError(d, fmt.Errorf("router function failed: %w", err))
 }

 if wcOK { wc.RecordActivity(fmt.Sprintf("%s:RouteKey[%s]", d.Name(), routeKey)) }

 // 查找对应的活动
 activity, ok := d.Activities[routeKey]

 if !ok {
  // 没有匹配的路由
  if d.DefaultActivity != nil {
      // 执行默认活动
      activity = d.DefaultActivity
      if wcOK { wc.RecordActivity(fmt.Sprintf("%s:Route->Default[%s]", d.Name(), activity.Name())) }
  } else {
      // 没有匹配且没有默认活动，可以选择报错或直接返回
      if wcOK { wc.RecordActivity(d.Name() + ":RouteNotFound") }
      // return input, WrapActivityError(d, fmt.Errorf("no route found for key '%s' and no default activity defined", routeKey))
      return input, nil // 或者选择不报错，直接结束
  }
 } else {
     if wcOK { wc.RecordActivity(fmt.Sprintf("%s:Route->Activity[%s]", d.Name(), activity.Name())) }
 }

 // 执行选定的活动
 result, err := activity.Execute(ctx, input)
 if err != nil {
     return result, WrapActivityError(activity, err) // 错误已包含活动名称
 }

 return result, nil
}

func (d *DataRoutingActivity[T]) Name() string {
 if d.Name_ == "" { return "DataRouter" }
 return d.Name_
}
```

#### 3.3.4 数据合并 (Data Aggregation)

将来自不同来源（例如并行分支的输出）的数据合并成单一的数据结构。

##### DataAggregation：实现与代码示例

这个模式通常不是一个独立的活动，而是作为其他模式（如 `ParallelActivity` 或 `MultiChoiceActivity`）的 `ResultMerger` 函数来实现。`ParallelActivity` 中的 `ResultMerger` 就是数据聚合的一个例子。

```go
// (参考 ParallelActivity 中的 ResultMerger 定义)
// func ResultMerger[R any, T any](results []R, original T) (T, error)

// 示例聚合器：将并行处理的整数结果求和并添加到原始数据的某个字段
/*
type WorkflowData struct {
    Values []int
    Sum    int
}

// 并行活动处理 Values 中的每个 int，返回处理后的 int (R=int)
// 聚合器将所有返回的 int 求和，并更新 WorkflowData.Sum
func aggregateSum(results []int, original WorkflowData) (WorkflowData, error) {
    currentSum := 0
    for _, r := range results {
        currentSum += r
    }
    original.Sum = currentSum // 更新原始数据
    return original, nil
}

parallelAdder := NewParallel("SumValues", aggregateSum,
    func(val int) (int, error) { return val, nil }, // 假设 R = T = int
    // ... list of activities processing each int ...
)
*/
```

#### 3.3.5 数据过滤 (Data Filter)

根据条件从数据集合（通常是工作流数据的一部分）中移除或选择元素。

##### DataFilter：实现与代码示例

```go
package workflow

import (
 "context"
 "fmt"
)

// 数据过滤模式：过滤数据项
// T: 整体工作流数据类型
// I: 集合中单个项目的类型
type DataFilterActivity[T any, I any] struct {
 Name_         string
 ItemsExtractor func(T) ([]I, error)       // 从 T 中提取项目列表
 FilterFunc    func(ctx context.Context, item I) (bool, error) // 判断是否保留该项目 (true=保留)
 ResultUpdater func(T, []I) (T, error)    // 使用过滤后的列表更新 T
}

// NewDataFilter 创建数据过滤活动
func NewDataFilter[T any, I any](name string,
    extractor func(T) ([]I, error),
    filter func(ctx context.Context, item I) (bool, error),
    updater func(T, []I) (T, error)) *DataFilterActivity[T, I] {
    return &DataFilterActivity[T, I]{
        Name_:         name,
        ItemsExtractor: extractor,
        FilterFunc:    filter,
        ResultUpdater: updater,
    }
}

func (d *DataFilterActivity[T, I]) Execute(ctx context.Context, input T) (T, error) {
    // 1. 提取项目
    items, err := d.ItemsExtractor(input)
    if err != nil {
        return input, WrapActivityError(d, fmt.Errorf("failed to extract items: %w", err))
    }

    filtered := make([]I, 0, len(items)) // 预分配容量

    // 2. 应用过滤器
    for i, item := range items {
        // 检查上下文
        select {
        case <-ctx.Done(): return input, WrapActivityError(d, ctx.Err())
        default:
        }

        keep, filterErr := d.FilterFunc(ctx, item)
        if filterErr != nil {
            err = fmt.Errorf("filter function failed for item %d: %w", i, filterErr)
            return input, WrapActivityError(d, err)
        }
        if keep {
            filtered = append(filtered, item)
        }
    }

    // 3. 更新结果
    result, updateErr := d.ResultUpdater(input, filtered)
    if updateErr != nil {
        return input, WrapActivityError(d, fmt.Errorf("result update failed: %w", updateErr))
    }

    return result, nil
}


func (d *DataFilterActivity[T, I]) Name() string {
 if d.Name_ == "" { return "DataFilter" }
 return d.Name_
}
```

---

### 3.4 资源模式 (Resource Patterns)

关注工作流执行过程中如何分配、管理和使用外部资源（如人力、计算资源、API 配额等）。

#### 3.4.1 资源定义与资源池 (Resource & Pool)

定义资源的基本接口和管理资源池的结构。

##### ResourcePool：实现与代码示例

```go
package workflow

import (
 // "context" // 可能在 Acquire 中需要
 "errors"
 "sync"
 // "time"
)

// Resource 接口定义了工作流中可管理的基本资源单元
type Resource interface {
 ID() string          // 唯一标识符
 Type() string        // 资源类型 (用于分类和查找)
 IsAvailable() bool   // 检查资源当前是否可用
 Acquire() error      // 尝试获取资源独占权，如果不可用则返回错误
 Release() error      // 释放资源
}

// BaseResource 提供 Resource 接口的基本实现 (可嵌入)
type BaseResource struct {
 id           string
 resourceType string
 available    atomic.Bool // 使用原子变量标记可用性
 mutex        sync.Mutex  // 用于保护 Acquire/Release 的原子性 (虽然可用性是原子的)
}

// NewBaseResource 创建基本资源
func NewBaseResource(id string, resourceType string) *BaseResource {
 r := &BaseResource{id: id, resourceType: resourceType}
 r.available.Store(true) // 初始可用
 return r
}

func (r *BaseResource) ID() string   { return r.id }
func (r *BaseResource) Type() string { return r.resourceType }
func (r *BaseResource) IsAvailable() bool { return r.available.Load() }

func (r *BaseResource) Acquire() error {
 // 使用 CAS 尝试将 available 从 true 变为 false
 if r.available.CompareAndSwap(true, false) {
  // 在成功获取后加锁（如果需要执行其他与获取相关的原子操作）
  // r.mutex.Lock()
  // defer r.mutex.Unlock()
  return nil // 获取成功
 }
 return ErrResourceUnavailable // 资源已被占用
}

func (r *BaseResource) Release() error {
 // 使用 CAS 尝试将 available 从 false 变为 true
 if r.available.CompareAndSwap(false, true) {
   // 在成功释放后加锁（如果需要执行其他与释放相关的原子操作）
   // r.mutex.Lock()
   // defer r.mutex.Unlock()
   return nil // 释放成功
 }
 // 尝试释放一个已经是 available 的资源？可以忽略或返回错误
 return errors.New("resource already available or state error during release")
}


// ResourcePool 管理一组资源
type ResourcePool struct {
 resources map[string]Resource // 按 ID 存储资源
 byType    map[string][]string // 按类型存储资源 ID 列表
 mutex     sync.RWMutex      // 保护 Pool 内部结构
}

// NewResourcePool 创建新的资源池
func NewResourcePool() *ResourcePool {
 return &ResourcePool{
  resources: make(map[string]Resource),
  byType:    make(map[string][]string),
 }
}

// AddResource 向池中添加资源
func (p *ResourcePool) AddResource(resource Resource) error {
 if resource == nil || resource.ID() == "" {
  return errors.New("invalid resource or resource ID")
 }
 p.mutex.Lock()
 defer p.mutex.Unlock()

 // 检查 ID 是否重复
 if _, exists := p.resources[resource.ID()]; exists {
     return fmt.Errorf("resource with ID '%s' already exists", resource.ID())
 }

 p.resources[resource.ID()] = resource

 // 按类型索引
 resourceType := resource.Type()
 if _, ok := p.byType[resourceType]; !ok {
  p.byType[resourceType] = make([]string, 0, 1)
 }
 p.byType[resourceType] = append(p.byType[resourceType], resource.ID())
 return nil
}

// GetResource 根据 ID 获取资源 (不获取所有权)
func (p *ResourcePool) GetResource(id string) (Resource, bool) {
 p.mutex.RLock()
 defer p.mutex.RUnlock()
 resource, ok := p.resources[id]
 return resource, ok
}

// AcquireResourceByID 尝试获取指定 ID 的资源
func (p *ResourcePool) AcquireResourceByID(id string) (Resource, error) {
 p.mutex.RLock()
 resource, ok := p.resources[id]
 p.mutex.RUnlock()

 if !ok {
  return nil, fmt.Errorf("resource with ID '%s' not found", id)
 }

 // 尝试获取资源
 err := resource.Acquire()
 if err != nil {
     return nil, err // 可能是 ErrResourceUnavailable
 }

 return resource, nil // 获取成功
}

// ReleaseResourceByID 释放指定 ID 的资源
func (p *ResourcePool) ReleaseResourceByID(id string) error {
 p.mutex.RLock()
 resource, ok := p.resources[id]
 p.mutex.RUnlock()

 if !ok {
  return fmt.Errorf("resource with ID '%s' not found", id)
 }

 return resource.Release()
}

// AcquireResourceByType 尝试按类型获取一个可用资源 (简单轮询)
// 返回获取到的资源，如果无可用则返回 ErrResourceUnavailable
func (p *ResourcePool) AcquireResourceByType(resourceType string) (Resource, error) {
 p.mutex.RLock()
 ids, ok := p.byType[resourceType]
 if !ok || len(ids) == 0 {
  p.mutex.RUnlock()
  return nil, fmt.Errorf("no resources of type '%s' found", resourceType)
 }
 // 创建 ID 列表副本，避免长时间持有读锁
 idsCopy := make([]string, len(ids))
 copy(idsCopy, ids)
 p.mutex.RUnlock()

 // 遍历该类型的所有资源 ID，尝试获取第一个可用的
 for _, id := range idsCopy {
     // 再次获取资源引用（可能在两次 RLock 之间被移除，虽然概率小）
     p.mutex.RLock()
     resource, exists := p.resources[id]
     p.mutex.RUnlock()
     if !exists { continue } // 资源已被移除

     // 尝试获取
     err := resource.Acquire()
     if err == nil {
         return resource, nil // 获取成功
     }
     // 如果错误不是 ErrResourceUnavailable，可能是其他问题
     if !errors.Is(err, ErrResourceUnavailable) {
         // log warning or return specific error?
     }
 }

 return nil, ErrResourceUnavailable // 没有找到可用的该类型资源
}

// ListResourcesByType 列出指定类型的所有资源 ID
func (p *ResourcePool) ListResourcesByType(resourceType string) []string {
    p.mutex.RLock()
    defer p.mutex.RUnlock()
    ids, ok := p.byType[resourceType]
    if !ok {
        return []string{}
    }
    // 返回副本
    idsCopy := make([]string, len(ids))
    copy(idsCopy, ids)
    return idsCopy
}
```

#### 3.4.2 资源分配 (Resource Allocation)

在工作流活动执行前获取所需资源，执行后释放。

##### ResourceActivity：实现与代码示例

```go
package workflow

import (
 "context"
 "fmt"
)

// ResourceActivity 模式：为活动自动分配和释放资源
type ResourceActivity[T any] struct {
 Name_         string
 InnerActivity Activity[T]     // 需要资源才能执行的内部活动
 ResourcePool  *ResourcePool   // 资源池引用
 ResourceType  string          // 需要的资源类型
 ResourceID    string          // 可选：指定需要的具体资源 ID
 // OnAcquire 可选：获取资源后，执行内部活动前调用，可修改输入 T
 OnAcquire     func(ctx context.Context, data T, resource Resource) (T, error)
 // OnRelease 可选：释放资源前，执行内部活动后调用，可修改结果 T
 OnRelease     func(ctx context.Context, data T, resource Resource) (T, error)
}

// NewResourceActivity 创建资源分配活动 (按类型)
func NewResourceActivityByType[T any](name string, pool *ResourcePool, resourceType string, inner Activity[T]) *ResourceActivity[T] {
    return &ResourceActivity[T]{
        Name_: name, ResourcePool: pool, ResourceType: resourceType, InnerActivity: inner,
    }
}
// NewResourceActivityByID 创建资源分配活动 (按 ID)
func NewResourceActivityByID[T any](name string, pool *ResourcePool, resourceID string, inner Activity[T]) *ResourceActivity[T] {
    return &ResourceActivity[T]{
        Name_: name, ResourcePool: pool, ResourceID: resourceID, InnerActivity: inner,
    }
}
// WithCallbacks 添加回调函数
func (r *ResourceActivity[T]) WithCallbacks(onAcquire func(context.Context, T, Resource) (T, error), onRelease func(context.Context, T, Resource) (T, error)) *ResourceActivity[T] {
    r.OnAcquire = onAcquire
    r.OnRelease = onRelease
    return r
}

func (r *ResourceActivity[T]) Execute(ctx context.Context, input T) (T, error) {
    if r.ResourcePool == nil || r.InnerActivity == nil {
        return input, WrapActivityError(r, errors.New("ResourcePool or InnerActivity is nil"))
    }
    if r.ResourceType == "" && r.ResourceID == "" {
         return input, WrapActivityError(r, errors.New("either ResourceType or ResourceID must be specified"))
    }

    wc, wcOK := GetWorkflowContext[T](ctx)

    // 1. 获取资源
    var resource Resource
    var acquireErr error
    acquireStart := time.Now()

    if r.ResourceID != "" {
        if wcOK { wc.RecordActivity(fmt.Sprintf("%s:AcquiringByID[%s]", r.Name(), r.ResourceID)) }
        resource, acquireErr = r.ResourcePool.AcquireResourceByID(r.ResourceID)
    } else {
         if wcOK { wc.RecordActivity(fmt.Sprintf("%s:AcquiringByType[%s]", r.Name(), r.ResourceType)) }
         resource, acquireErr = r.ResourcePool.AcquireByType(r.ResourceType)
    }
    acquireDuration := time.Since(acquireStart)

    if acquireErr != nil {
        if wcOK { wc.RecordActivity(fmt.Sprintf("%s:AcquireFailed (%v)", r.Name(), acquireDuration)) }
        return input, WrapActivityError(r, fmt.Errorf("failed to acquire resource: %w", acquireErr))
    }

    // 确保资源最终被释放
    defer func() {
        releaseErr := r.ResourcePool.ReleaseResourceByID(resource.ID())
        if releaseErr != nil {
             // log.Printf("Warning: failed to release resource %s in activity %s: %v", resource.ID(), r.Name(), releaseErr)
             if wcOK { wc.RecordActivity(fmt.Sprintf("%s:ReleaseFailed[%s]", r.Name(), resource.ID())) }
        } else {
             if wcOK { wc.RecordActivity(fmt.Sprintf("%s:Released[%s]", r.Name(), resource.ID())) }
        }
    }()

    if wcOK { wc.RecordActivity(fmt.Sprintf("%s:Acquired[%s] (%v)", r.Name(), resource.ID(), acquireDuration)) }


    // 2. OnAcquire 回调 (如果存在)
    modifiedInput := input
    if r.OnAcquire != nil {
        var onAcquireErr error
        modifiedInput, onAcquireErr = r.OnAcquire(ctx, input, resource)
        if onAcquireErr != nil {
            return input, WrapActivityError(r, fmt.Errorf("OnAcquire callback failed: %w", onAcquireErr))
        }
    }

    // 3. 执行内部活动
    result, execErr := r.InnerActivity.Execute(ctx, modifiedInput)
    if execErr != nil {
        // 内部活动失败，错误已包含活动名称，无需再次包装 r.Name()
        return result, execErr
    }

    // 4. OnRelease 回调 (如果存在)
    finalResult := result
    if r.OnRelease != nil {
        var onReleaseErr error
        finalResult, onReleaseErr = r.OnRelease(ctx, result, resource)
        if onReleaseErr != nil {
            // OnRelease 失败，此时内部活动已成功，返回 OnRelease 错误和活动结果
             return result, WrapActivityError(r, fmt.Errorf("OnRelease callback failed: %w", onReleaseErr))
        }
    }

    return finalResult, nil
}


func (r *ResourceActivity[T]) Name() string {
 if r.Name_ == "" { return "ResourceActivity" }
 return r.Name_
}
```

#### 3.4.3 角色分配 (Role-based Distribution)

根据与工作项关联的角色（例如审批者级别、处理组）将任务分配给合适的资源或执行不同的活动。

##### RoleBased：实现与代码示例

```go
package workflow

import (
 "context"
 "fmt"
 "errors"
)

// 角色分配模式：根据从数据中提取的角色，选择不同的活动执行
type RoleBasedActivity[T any] struct {
 Name_          string
 // RoleExtractor 从工作流数据 T 中提取角色标识符 (string)
 RoleExtractor  func(ctx context.Context, data T) (string, error)
 // RoleActivities 将角色标识符映射到要执行的 Activity
 RoleActivities map[string]Activity[T]
 DefaultActivity Activity[T] // 可选：当角色无匹配活动时执行
}

// NewRoleBasedActivity 创建角色分配活动
func NewRoleBasedActivity[T any](name string, extractor func(ctx context.Context, data T) (string, error), activities map[string]Activity[T]) *RoleBasedActivity[T] {
    return &RoleBasedActivity[T]{
        Name_:          name,
        RoleExtractor:  extractor,
        RoleActivities: activities,
    }
}

// WithDefault 设置默认活动
func (r *RoleBasedActivity[T]) WithDefault(defaultActivity Activity[T]) *RoleBasedActivity[T] {
    r.DefaultActivity = defaultActivity
    return r
}

func (r *RoleBasedActivity[T]) Execute(ctx context.Context, input T) (T, error) {
    wc, wcOK := GetWorkflowContext[T](ctx)

    // 1. 提取角色
    role, err := r.RoleExtractor(ctx, input)
    if err != nil {
        return input, WrapActivityError(r, fmt.Errorf("failed to extract role: %w", err))
    }

    if wcOK { wc.RecordActivity(fmt.Sprintf("%s:ExtractedRole[%s]", r.Name(), role)) }

    // 2. 查找角色对应的活动
    activity, ok := r.RoleActivities[role]
    if !ok {
        // 角色没有匹配的活动
        if r.DefaultActivity != nil {
            activity = r.DefaultActivity
             if wcOK { wc.RecordActivity(fmt.Sprintf("%s:Role->Default[%s]", r.Name(), activity.Name())) }
        } else {
            // 没有匹配且无默认活动
            if wcOK { wc.RecordActivity(r.Name() + ":RoleNotFound") }
            return input, WrapActivityError(r, fmt.Errorf("no activity found for role '%s' and no default activity defined", role))
        }
    } else {
         if wcOK { wc.RecordActivity(fmt.Sprintf("%s:Role->Activity[%s]", r.Name(), activity.Name())) }
    }

    // 3. 执行选定的活动
    result, err := activity.Execute(ctx, input)
    if err != nil {
        return result, WrapActivityError(activity, err) // 错误已包含活动名
    }

    return result, nil
}


func (r *RoleBasedActivity[T]) Name() string {
 if r.Name_ == "" { return "RoleBasedActivity" }
 return r.Name_
}
```

#### 3.4.4 工作负载均衡 (Workload Balancing)

将传入的工作项分发给一组等效的资源（Worker），以平衡负载。

##### LoadBalanced：实现与代码示例

这个模式通常与 `Worker Pool` 或一组 `Resource` 结合使用。`Worker Pool` 本身就隐式地实现了负载均衡（goroutine 调度器会处理）。如果有一组特定的、可识别的 `Resource`（例如，多个 API 处理节点），可以实现一个简单的轮询或随机选择策略来分配任务。

```go
package workflow

import (
 "context"
 "sync"
 "sync/atomic" // 用于轮询计数器
 "math/rand"  // 用于随机选择
 // "errors"
)

// LoadBalancedActivity 模式：将工作分发给一组工作活动 (Workers)
// 假设所有 Worker 执行相同的逻辑但可能代表不同资源实例
type LoadBalancedActivity[T any] struct {
 Name_        string
 Workers      []Activity[T] // 一组等效的工作活动
 // 负载均衡策略 (可以扩展为接口)
 strategy     loadBalanceStrategy
 nextIndex    atomic.Uint64 // 用于轮询策略
}

// 负载均衡策略类型
type loadBalanceStrategy int
const (
    RoundRobin loadBalanceStrategy = iota // 轮询
    Random                             // 随机
    // LeastBusy                        // 最少工作量 (需要监控 worker 状态，较复杂)
)

// NewLoadBalancedActivity 创建负载均衡活动
func NewLoadBalancedActivity[T any](name string, strategy loadBalanceStrategy, workers ...Activity[T]) (*LoadBalancedActivity[T], error) {
    if len(workers) == 0 {
        return nil, errors.New("must provide at least one worker activity")
    }
    // 检查 worker 是否为 nil?
    return &LoadBalancedActivity[T]{
        Name_:    name,
        Workers:  workers,
        strategy: strategy,
    }, nil
}

func (l *LoadBalancedActivity[T]) Execute(ctx context.Context, input T) (T, error) {
    numWorkers := len(l.Workers)
    if numWorkers == 0 {
        return input, WrapActivityError(l, errors.New("no workers configured"))
    }

    var selectedWorker Activity[T]
    workerIndex := -1

    // 选择 Worker
    switch l.strategy {
    case Random:
        workerIndex = rand.Intn(numWorkers) // 注意：需要初始化随机种子 time.Now().UnixNano()
        selectedWorker = l.Workers[workerIndex]
    case RoundRobin:
        fallthrough // 默认使用轮询
    default:
        // 原子地增加计数器并取模，实现轮询
        idx := l.nextIndex.Add(1)
        workerIndex = int((idx - 1) % uint64(numWorkers)) // -1 是因为 Add 返回新值
        selectedWorker = l.Workers[workerIndex]
    }

    wc, wcOK := GetWorkflowContext[T](ctx)
    if wcOK { wc.RecordActivity(fmt.Sprintf("%s:DispatchToWorker[%d]_%s", l.Name(), workerIndex, selectedWorker.Name())) }

    // 执行选定的 Worker 活动
    result, err := selectedWorker.Execute(ctx, input)
    if err != nil {
        return result, WrapActivityError(selectedWorker, err) // 错误已包含 worker 名
    }

    return result, nil
}

func (l *LoadBalancedActivity[T]) Name() string {
 if l.Name_ == "" { return "LoadBalancedActivity" }
 return l.Name_
}
```

#### 3.4.5 扩展讨论：资源优先级、预留

- **优先级**: 可以为资源或等待获取资源的工作项设置优先级。资源池在分配时可以优先考虑高优先级请求。实现方式：
  - 使用优先级队列存储等待请求。
  - 为资源打上优先级标签，优先分配给匹配的请求。
- **预留**: 允许提前为某个工作流实例或特定任务预留资源，确保其在需要时可用。实现方式：
  - 资源池提供 `Reserve(resourceType, reservationID)` 方法。
  - 被预留的资源在 `AcquireByType` 时会被跳过，除非调用者提供了正确的 `reservationID`。
  - 需要处理预留超时或取消。

这些高级功能会显著增加资源池和资源分配活动的复杂性。

---

### 3.5 异常处理模式 (Exception Handling Patterns)

定义工作流如何处理执行过程中发生的错误和异常。

#### 3.5.1 重试 (Retry)

当活动执行失败时，自动重新尝试执行该活动若干次。

##### Retry：实现与代码示例

```go
package workflow

import (
 "context"
 "time"
 "errors"
 "fmt"
)

// RetryActivity 模式：在失败时重试内部活动
type RetryActivity[T any] struct {
 Name_         string
 InnerActivity Activity[T]     // 要重试的活动
 MaxRetries    int             // 最大重试次数 (不包括首次尝试)
 RetryDelay    time.Duration   // 每次重试前的延迟
 BackoffFactor float64         // 可选：指数退避因子 (e.g., 2.0)
 MaxRetryDelay time.Duration   // 可选：最大重试延迟
 ShouldRetry   func(err error) bool // 可选：判断哪个错误应该触发重试 (默认所有错误都重试)
}

// NewRetryActivity 创建重试活动
func NewRetryActivity[T any](name string, inner Activity[T], maxRetries int, retryDelay time.Duration) *RetryActivity[T] {
    return &RetryActivity[T]{
        Name_:         name,
        InnerActivity: inner,
        MaxRetries:    maxRetries,
        RetryDelay:    retryDelay,
        BackoffFactor: 1.0, // 默认无指数退避
        ShouldRetry:   func(err error) bool { return err != nil }, // 默认重试所有错误
    }
}

// WithBackoff 设置指数退避
func (r *RetryActivity[T]) WithBackoff(factor float64, maxDelay time.Duration) *RetryActivity[T] {
    if factor >= 1.0 {
        r.BackoffFactor = factor
    }
    r.MaxRetryDelay = maxDelay
    return r
}

// WithShouldRetry 设置自定义的错误判断逻辑
func (r *RetryActivity[T]) WithShouldRetry(shouldRetry func(err error) bool) *RetryActivity[T] {
    if shouldRetry != nil {
        r.ShouldRetry = shouldRetry
    }
    return r
}

func (r *RetryActivity[T]) Execute(ctx context.Context, input T) (T, error) {
    var result T
    var lastErr error
    currentDelay := r.RetryDelay

    wc, wcOK := GetWorkflowContext[T](ctx)

    for attempt := 0; attempt <= r.MaxRetries; attempt++ {
        // 检查上下文取消
        select {
        case <-ctx.Done():
            if lastErr != nil { // 如果之前有错误，返回最后一个错误和取消错误
                 return result, WrapActivityError(r, fmt.Errorf("retry cancelled: %w (last error: %v)", ctx.Err(), lastErr))
            }
            return result, WrapActivityError(r, ctx.Err())
        default:
        }

        if wcOK && attempt > 0 { wc.RecordActivity(fmt.Sprintf("%s:Attempt[%d]", r.Name(), attempt)) }

        // 执行内部活动
        result, lastErr = r.InnerActivity.Execute(ctx, input)

        if lastErr == nil {
            // 成功执行，返回结果
            if wcOK && attempt > 0 { wc.RecordActivity(fmt.Sprintf("%s:SuccessOnAttempt[%d]", r.Name(), attempt)) }
            return result, nil
        }

        // 执行失败，判断是否应该重试
        if !r.ShouldRetry(lastErr) {
            // 错误不应该重试，直接返回错误
            if wcOK { wc.RecordActivity(fmt.Sprintf("%s:NonRetryableError_Attempt[%d]", r.Name(), attempt)) }
            return result, WrapActivityError(r.InnerActivity, lastErr) // 包装原始活动错误
        }

        // 判断是否还有重试机会
        if attempt >= r.MaxRetries {
            // 已达到最大重试次数
            if wcOK { wc.RecordActivity(fmt.Sprintf("%s:MaxRetriesReached[%d]", r.Name(), attempt)) }
            break // 跳出循环，返回最后一个错误
        }

        // --- 准备下一次重试 ---
        // 计算延迟
        delay := currentDelay
        if r.BackoffFactor > 1.0 {
            currentDelay = time.Duration(float64(currentDelay) * r.BackoffFactor)
            if r.MaxRetryDelay > 0 && currentDelay > r.MaxRetryDelay {
                currentDelay = r.MaxRetryDelay
            }
            delay = currentDelay // 更新下次使用的延迟
        }

        if wcOK { wc.RecordActivity(fmt.Sprintf("%s:RetryDelaying[%v]_Attempt[%d]", r.Name(), delay, attempt)) }

        // 等待延迟或上下文取消
        select {
        case <-time.After(delay):
            // 继续下一次尝试
        case <-ctx.Done():
            // 在延迟期间被取消
            return result, WrapActivityError(r, fmt.Errorf("retry cancelled during delay: %w (last error: %v)", ctx.Err(), lastErr))
        }
    } // end for

    // 循环结束（达到最大重试次数），返回最后一个遇到的错误
    finalErr := fmt.Errorf("activity '%s' failed after %d retries: %w", r.InnerActivity.Name(), r.MaxRetries, lastErr)
    return result, WrapActivityError(r, finalErr) // 包装重试活动的错误
}


func (r *RetryActivity[T]) Name() string {
 if r.Name_ == "" { return "Retry" }
 return r.Name_
}
```

#### 3.5.2 超时 (Timeout)

为活动的执行设置时间限制，如果超时则中断活动并（通常）产生错误。

##### Timeout：实现与代码示例

```go
package workflow

import (
 "context"
 "time"
 "errors"
 // "fmt"
)

// TimeoutActivity 模式：限制内部活动的执行时间
type TimeoutActivity[T any] struct {
 Name_         string
 InnerActivity Activity[T]
 Timeout       time.Duration // 超时时间
}

// NewTimeoutActivity 创建超时活动
func NewTimeoutActivity[T any](name string, timeout time.Duration, inner Activity[T]) *TimeoutActivity[T] {
    return &TimeoutActivity[T]{Name_: name, Timeout: timeout, InnerActivity: inner}
}

func (t *TimeoutActivity[T]) Execute(ctx context.Context, input T) (T, error) {
    if t.Timeout <= 0 { // 如果超时无效，则直接执行内部活动
        return t.InnerActivity.Execute(ctx, input)
    }

    // 创建带超时的子上下文
    timeoutCtx, cancel := context.WithTimeout(ctx, t.Timeout)
    defer cancel() // 确保释放定时器资源

    wc, wcOK := GetWorkflowContext[T](ctx)
    if wcOK { wc.RecordActivity(fmt.Sprintf("%s:StartingWithTimeout[%v]", t.Name(), t.Timeout)) }

    // 使用通道来接收内部活动的结果或错误
    resultCh := make(chan struct {
        result T
        err    error
    }, 1) // 缓冲为 1，确保 goroutine 不会因发送阻塞而泄漏

    go func() {
        // 在新的 goroutine 中执行内部活动，使用带超时的上下文
        // 需要处理内部活动可能的 panic
        var res T
        var execErr error
        panicErr := func() (p interface{}) {
             defer func() { p = recover() }()
             res, execErr = t.InnerActivity.Execute(timeoutCtx, input)
             return
        }()
        if panicErr != nil {
             execErr = fmt.Errorf("inner activity panicked: %v", panicErr)
        }

        // 将结果或错误发送到通道
        resultCh <- struct { result T; err error }{res, execErr}
    }()

    // 等待结果或超时/取消
    select {
    case <-timeoutCtx.Done(): // 超时或父上下文取消
        err := timeoutCtx.Err() // 获取错误原因
        if errors.Is(err, context.DeadlineExceeded) {
            // 是因为我们设置的超时而取消
             if wcOK { wc.RecordActivity(fmt.Sprintf("%s:TimeoutExceeded", t.Name())) }
             finalErr := fmt.Errorf("activity '%s' timed out after %v: %w", t.InnerActivity.Name(), t.Timeout, ErrTimeout)
             // 返回零值和超时错误
             var zero T
             return zero, WrapActivityError(t, finalErr)
        } else {
            // 是因为父上下文被取消
            if wcOK { wc.RecordActivity(fmt.Sprintf("%s:Cancelled", t.Name())) }
            // 返回零值和取消错误
            var zero T
            return zero, WrapActivityError(t, err)
        }

    case res := <-resultCh: // 内部活动正常完成 (或出错)
        if res.err != nil {
             if wcOK { wc.RecordActivity(fmt.Sprintf("%s:InnerError", t.Name())) }
             // 返回内部活动的错误（已由内部活动包装）
             return res.result, res.err
        }
         if wcOK { wc.RecordActivity(fmt.Sprintf("%s:CompletedWithinTimeout", t.Name())) }
         // 返回内部活动的结果
         return res.result, nil
    }
}


func (t *TimeoutActivity[T]) Name() string {
 if t.Name_ == "" { return "Timeout" }
 return t.Name_
}
```

#### 3.5.3 补偿 (Compensation)

如果某个活动（主活动）成功执行后，工作流后续步骤失败，则执行一个补偿活动来撤销主活动造成的影响（或执行反向操作）。

##### Compensation：实现与代码示例

补偿通常在更高层次的工作流逻辑中处理，而不是一个简单的包装活动。例如，使用 `ErrorBoundaryActivity` 或在 `SequenceActivity` 的错误处理逻辑中触发。

一个简单的补偿 *包装器* 模式可以这样实现（但这通常不是补偿模式的最佳实践，Saga 模式更常用）：

```go
package workflow

import (
 "context"
 "errors"
 "fmt"
)

// CompensationWrapperActivity 尝试封装一个需要补偿的活动
// 注意：这种简单的包装器在复杂流程中可能不足够。
type CompensationWrapperActivity[T any] struct {
 Name_                string
 MainActivity         Activity[T]     // 主要执行的活动
 CompensationActivity Activity[T]     // 如果后续流程失败，需要执行的补偿活动
 NeedsCompensation *atomic.Bool    // 外部设置的标志，指示是否需要执行补偿
}

// NewCompensationWrapper 创建补偿包装器
func NewCompensationWrapper[T any](name string, main, compensation Activity[T], needsCompensation *atomic.Bool) *CompensationWrapperActivity[T] {
    return &CompensationWrapperActivity[T]{
        Name_: name, MainActivity: main, CompensationActivity: compensation, NeedsCompensation: needsCompensation,
    }
}


func (c *CompensationWrapperActivity[T]) Execute(ctx context.Context, input T) (T, error) {
    wc, wcOK := GetWorkflowContext[T](ctx)
    if wcOK { wc.RecordActivity(c.Name() + ":ExecutingMain") }

    // 执行主活动
    result, err := c.MainActivity.Execute(ctx, input)
    if err != nil {
         if wcOK { wc.RecordActivity(c.Name() + ":MainFailed") }
         // 主活动失败，不需要补偿，直接返回错误
         return result, err // 错误已由 MainActivity 包装
    }

    // 主活动成功，检查是否需要补偿（由外部逻辑驱动）
    if c.NeedsCompensation != nil && c.NeedsCompensation.Load() {
        if wcOK { wc.RecordActivity(c.Name() + ":CompensationNeeded") }
        // 执行补偿活动
        // 补偿活动应该使用原始输入还是主活动的结果？取决于具体逻辑
        // 这里假设补偿使用原始输入 input
        compResult, compErr := c.CompensationActivity.Execute(ctx, input) // 或者使用 result?
        if compErr != nil {
             if wcOK { wc.RecordActivity(c.Name() + ":CompensationFailed") }
             // 补偿失败，这是一个严重问题，返回补偿错误和原始成功结果？
             // 或者返回一个聚合错误？
             compErr = WrapActivityError(c.CompensationActivity, compErr)
             finalErr := fmt.Errorf("compensation failed for '%s' after main activity succeeded: %w", c.MainActivity.Name(), compErr)
             return result, WrapActivityError(c, finalErr)
        }
        // 补偿成功
        if wcOK { wc.RecordActivity(c.Name() + ":CompensationSucceeded") }
        // 补偿成功后返回什么？通常应该指示流程失败，但补偿完成
        // 可能返回一个特定错误，或者返回补偿的结果 compResult？
        // 返回一个表示“已补偿”的特定错误可能更好
        return compResult, fmt.Errorf("workflow compensated after initial success of %s", c.MainActivity.Name()) // 返回补偿结果和补偿信号错误
    }

    // 主活动成功且不需要补偿
    if wcOK { wc.RecordActivity(c.Name() + ":MainSucceeded_NoCompensation") }
    return result, nil
}


func (c *CompensationWrapperActivity[T]) Name() string {
 if c.Name_ == "" { return "CompensationWrapper" }
 return c.Name_
}

// --- 更常见的补偿处理方式：在错误处理中触发 ---
/*
func executeSequenceWithCompensation() {
    mainActivity := ...
    nextActivity := ...
    compensationActivity := ...

    result, err := mainActivity.Execute(ctx, input)
    if err != nil {
        // 主活动失败，无需补偿
        return err
    }

    finalResult, err := nextActivity.Execute(ctx, result)
    if err != nil {
        // 后续活动失败，触发补偿
        _, compErr := compensationActivity.Execute(ctx, input) // or result?
        if compErr != nil {
            // 补偿失败，记录严重错误
        }
        // 返回原始错误
        return err
    }
    // 全部成功
    return nil
}
*/

// Saga 模式是处理分布式事务和补偿的更系统化的方法。
```

#### 3.5.4 取消 (Cancel)

允许外部信号（通常通过 `context.Context`）中断正在执行的工作流或活动。

##### Cancellable：实现与代码示例

取消主要通过在每个活动的 `Execute` 方法开始时和可能的长时间操作期间检查 `ctx.Done()` 来实现。

```go
package workflow

import (
 "context"
 "errors"
 // "fmt"
)

// CancellableActivity 包装器 (示例，实际取消由内部活动检查 ctx 实现)
// 这个包装器本身作用不大，除非你想在取消时执行特定逻辑 OnCancel
type CancellableActivity[T any] struct {
 Name_         string
 InnerActivity Activity[T]
 // OnCancel 可选：当上下文被取消时调用，可以执行清理操作
 OnCancel      func(ctx context.Context, data T) (T, error)
}

// NewCancellableActivity 创建可取消活动包装器
func NewCancellableActivity[T any](name string, inner Activity[T], onCancel func(context.Context, T) (T, error)) *CancellableActivity[T] {
    return &CancellableActivity[T]{
        Name_: name, InnerActivity: inner, OnCancel: onCancel,
    }
}

func (c *CancellableActivity[T]) Execute(ctx context.Context, input T) (T, error) {
    // 1. 立即检查上下文
    select {
    case <-ctx.Done():
        if c.OnCancel != nil {
            return c.OnCancel(ctx, input) // 执行取消回调
        }
        return input, WrapActivityError(c, ctx.Err()) // 返回原始输入和取消错误
    default:
    }

    // 2. 执行内部活动 (内部活动应该自己检查 ctx.Done())
    result, err := c.InnerActivity.Execute(ctx, input)

    // 3. 执行后再次检查上下文 (可能在内部活动执行期间被取消)
    select {
    case <-ctx.Done():
        // 执行已完成，但上下文被取消了
        if c.OnCancel != nil {
             // 是否应该传入 result 而不是 input？ 取决于 OnCancel 语义
             cancelResult, cancelErr := c.OnCancel(ctx, result) // 使用活动结果调用 OnCancel
             if cancelErr != nil {
                 // OnCancel 出错，返回哪个错误？原始取消错误还是 OnCancel 错误？
                 return cancelResult, WrapActivityError(c, fmt.Errorf("OnCancel failed after context done: %w (original ctx err: %v)", cancelErr, ctx.Err()))
             }
             // 返回 OnCancel 结果和原始取消错误
             return cancelResult, WrapActivityError(c, ctx.Err())
        }
        // 没有 OnCancel，返回活动结果和取消错误
        return result, WrapActivityError(c, ctx.Err())
    default:
        // 未取消，正常返回内部活动的结果或错误
        if err != nil {
            return result, err // 错误已由内部活动包装
        }
        return result, nil
    }
}


func (c *CancellableActivity[T]) Name() string {
 if c.Name_ == "" { return "Cancellable" }
 return c.Name_
}

// --- 在活动内部检查取消的示例 ---
/*
type LongRunningActivity[T any] struct { BaseActivity }

func (a *LongRunningActivity[T]) Execute(ctx context.Context, input T) (T, error) {
    for i := 0; i < 10; i++ {
        select {
        case <-ctx.Done():
            // log.Printf("Activity %s cancelled at step %d", a.Name(), i)
            return input, WrapActivityError(a, ctx.Err())
        case <-time.After(1 * time.Second): // 模拟工作
            // log.Printf("Activity %s working step %d", a.Name(), i)
        }
    }
    return input, nil // 正常完成
}
*/
```

#### 3.5.5 错误边界 (Error Boundary)

类似于 try-catch 块，捕获特定活动或子流程中发生的错误，并根据错误类型执行不同的处理逻辑（Catch 活动），无论成功或失败都可能执行 Finally 活动。

##### ErrorBoundary：实现与代码示例

```go
package workflow

import (
 "context"
 "errors"
 "fmt"
)

// ErrorBoundaryActivity 模式：捕获错误并提供替代路径
type ErrorBoundaryActivity[T any] struct {
 Name_           string
 TryActivity     Activity[T]             // 尝试执行的主活动
 // CatchHandlers 错误类型 -> 处理活动的映射 (使用 error 作为 key 可能不理想)
 // 更好的方式是用一个函数列表，每个函数检查错误类型并返回对应的 Handler
 CatchHandlers   []CatchHandler[T]
 FinallyActivity Activity[T]             // 可选：无论成功失败都执行的活动
}

// CatchHandler 定义了如何处理特定错误
type CatchHandler[T any] struct {
    // IsError 判断错误是否匹配此 Handler (例如，errors.Is 或类型断言)
    IsError func(err error) bool
    Handler Activity[T] // 处理匹配错误时执行的活动
}


// NewErrorBoundary 创建错误边界活动
func NewErrorBoundary[T any](name string, try Activity[T]) *ErrorBoundaryActivity[T] {
    return &ErrorBoundaryActivity[T]{
        Name_: name, TryActivity: try, CatchHandlers: make([]CatchHandler[T], 0),
    }
}

// AddCatch 添加一个错误处理分支
func (e *ErrorBoundaryActivity[T]) AddCatch(isError func(err error) bool, handler Activity[T]) *ErrorBoundaryActivity[T] {
    if isError != nil && handler != nil {
        e.CatchHandlers = append(e.CatchHandlers, CatchHandler[T]{IsError: isError, Handler: handler})
    }
    return e
}

// WithFinally 添加 Finally 活动
func (e *ErrorBoundaryActivity[T]) WithFinally(finally Activity[T]) *ErrorBoundaryActivity[T] {
    e.FinallyActivity = finally
    return e
}


func (e *ErrorBoundaryActivity[T]) Execute(ctx context.Context, input T) (T, error) {
    var tryResult T
    var tryErr error
    var finalResult T
    var finalErr error

    wc, wcOK := GetWorkflowContext[T](ctx)
    if wcOK { wc.RecordActivity(e.Name() + ":TryStart") }

    // --- Try Phase ---
    tryPanicErr := func() (p interface{}) {
        defer func() { p = recover() }()
        tryResult, tryErr = e.TryActivity.Execute(ctx, input)
        return
    }()

    if tryPanicErr != nil {
        tryErr = fmt.Errorf("try activity '%s' panicked: %v", e.TryActivity.Name(), tryPanicErr)
        // 将 panic 视为错误，进入 Catch 阶段
         if wcOK { wc.RecordActivity(e.Name() + ":TryPanic") }
    } else if tryErr != nil {
         if wcOK { wc.RecordActivity(e.Name() + ":TryError") }
         // 记录尝试错误，进入 Catch 阶段
    } else {
         if wcOK { wc.RecordActivity(e.Name() + ":TrySuccess") }
         // 尝试成功，跳过 Catch 阶段
    }


    // --- Catch Phase ---
    catchExecuted := false
    if tryErr != nil {
        var handlerActivity Activity[T]
        for _, catcher := range e.CatchHandlers {
            if catcher.IsError(tryErr) { // 找到匹配的错误处理器
                handlerActivity = catcher.Handler
                if wcOK { wc.RecordActivity(fmt.Sprintf("%s:Catch[%s]", e.Name(), handlerActivity.Name())) }
                break
            }
        }

        if handlerActivity != nil {
            // 执行匹配的 Catch Handler
            catchResult, catchErr := handlerActivity.Execute(ctx, input) // Catch Handler 通常接收原始输入
            if catchErr != nil {
                 // Catch Handler 也失败了，错误升级
                 if wcOK { wc.RecordActivity(fmt.Sprintf("%s:Catch[%s]Failed", e.Name(), handlerActivity.Name())) }
                 tryErr = fmt.Errorf("catch handler '%s' failed while handling '%v': %w", handlerActivity.Name(), tryErr, catchErr)
            } else {
                 // Catch Handler 成功，原始错误被处理
                 if wcOK { wc.RecordActivity(fmt.Sprintf("%s:Catch[%s]Succeeded", e.Name(), handlerActivity.Name())) }
                 tryErr = nil // 标记错误已被处理
                 tryResult = catchResult // Catch Handler 的结果成为边界活动的结果
                 catchExecuted = true
            }
        } else {
             // 没有找到匹配的 Catch Handler，原始错误 tryErr 保持不变
             if wcOK { wc.RecordActivity(e.Name() + ":CatchNotFound") }
        }
    }


    // --- Finally Phase ---
    // 无论 Try/Catch 结果如何，都执行 Finally (如果定义了)
    if e.FinallyActivity != nil {
         if wcOK { wc.RecordActivity(e.Name() + ":FinallyStart") }
         // Finally 活动的输入是什么？通常是 Try 或 Catch 的结果
         inputForFinally := tryResult
         if tryErr != nil && !catchExecuted {
             // 如果 Try 失败且没有 Catch 处理，Finally 可能需要原始输入？
             // 或者传入包含错误信息的上下文？这里简化为传入 tryResult
         }

         finalResult, finalErr = e.FinallyActivity.Execute(ctx, inputForFinally)
         if wcOK {
             if finalErr != nil { wc.RecordActivity(e.Name() + ":FinallyError") } else { wc.RecordActivity(e.Name() + ":FinallySuccess") }
         }

    } else {
        // 没有 Finally 活动，直接使用 Try/Catch 的结果
        finalResult = tryResult
    }


    // --- 返回最终结果和错误 ---
    if finalErr != nil {
        // Finally 失败是最高优先级错误
        return finalResult, WrapActivityError(e.FinallyActivity, finalErr)
    }
    if tryErr != nil {
        // 如果 Try 失败且未被 Catch 处理，或者 Catch 处理失败，返回该错误
        // 注意：tryErr 可能已被 Catch 包装过
        return tryResult, WrapActivityError(e, tryErr) // 包装边界活动的错误
    }
    // Finally 成功（或不存在），Try 成功或 Catch 成功
    return finalResult, nil
}


func (e *ErrorBoundaryActivity[T]) Name() string {
 if e.Name_ == "" { return "ErrorBoundary" }
 return e.Name_
}
```

#### 3.5.6 回滚 (Rollback) (概念扩展)

在工作流失败时，将系统状态恢复到工作流开始前或某个稳定检查点的状态。

- **实现思路**:
  - **检查点 (Checkpointing)**: 在工作流的关键节点保存状态快照。
  - **状态恢复**: 如果发生不可恢复的错误，引擎可以加载最近的检查点状态来重置工作流数据。
  - **与补偿的区别**: 补偿是执行 *反向操作* 来逻辑上撤销已完成活动的影响；回滚是直接 *恢复到之前的状态*。回滚通常更简单，但不适用于所有场景（例如，已经发送了邮件无法“回滚”）。
  - **实现复杂度**: 需要可靠的状态存储和恢复机制，可能涉及数据库事务或专门的状态管理系统。简单的工作流可能不需要完全的回滚机制，而依赖补偿。

---

### 3.6 工作流示例

展示如何组合使用上述模式来构建实际的工作流。

#### 3.6.1 订单处理工作流

(代码与 `go_generic_workflow.md` 中 `examples/order_processing.go` 的 `main` 函数内容类似，展示了 Sequence, Transform, Retry, Resource, Parallel, Condition, Compensation 模式的组合)

```go
package main // (假设在 examples 目录下)

import (
 "context"
 "errors"
 "fmt"
 "log"
 "os"
 "strings"
 "sync/atomic"
 "time"

 "workflow" // 导入定义的 workflow 包
)

// --- 数据结构定义 (Order, OrderItem, ShippingInfo) ---
type Order struct {
 ID            string
 CustomerID    string
 Items         []OrderItem
 TotalAmount   float64
 PaymentStatus string // "Pending", "Paid", "Failed", "Cancelled", "Refunded"
 ShippingInfo  ShippingInfo
 CreatedAt     time.Time
 ProcessedBy   string      // 由哪个资源处理
 NeedsCompensation atomic.Bool // 用于补偿示例 (在 ErrorBoundary 中不再需要)
 LastError     string      // 记录最后错误信息
}
type OrderItem struct {
 ProductID  string
 Quantity   int
 UnitPrice  float64
 TotalPrice float64 // 由 calculateTotal 计算
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

// --- 活动函数实现 ---
func validateOrder(ctx context.Context, order Order) (Order, error) {
 log.Printf("[Activity: ValidateOrder] Validating order %s", order.ID)
 if order.CustomerID == "" { return order, errors.New("customer ID cannot be empty") }
 if len(order.Items) == 0 { return order, errors.New("order must have items") }
 if order.ShippingInfo.Address == "" { return order, errors.New("shipping address cannot be empty") }
 time.Sleep(50 * time.Milliseconds) // Simulate work
 return order, nil
}

func calculateTotal(ctx context.Context, order Order) (Order, error) {
 log.Printf("[Activity: CalculateTotal] Calculating total for order %s", order.ID)
 total := 0.0
 for i, item := range order.Items {
  itemTotal := float64(item.Quantity) * item.UnitPrice
  // 注意：直接修改传入切片的元素可能不是最佳实践，取决于 T 是否为指针。
  // 如果 Order 是值类型，这里的修改不会影响原始数据。
  // 更好的做法是创建新的 Items 切片。为简化示例，这里直接修改。
  // order.Items[i].TotalPrice = itemTotal // 需要 T 是指针或返回新 Order
  total += itemTotal
 }
 order.TotalAmount = total // 修改的是 order 的副本（如果 Order 是值类型）
 time.Sleep(30 * time.Milliseconds)
 log.Printf("[Activity: CalculateTotal] Calculated total: %.2f", order.TotalAmount)
 return order, nil // 返回修改后的副本
}

// 模拟支付，ID 以 'f' 开头的支付失败
var paymentCounter int // 用于模拟间歇性失败
func processPayment(ctx context.Context, order Order) (Order, error) {
 log.Printf("[Activity: ProcessPayment] Processing payment for order %s, amount: %.2f", order.ID, order.TotalAmount)
 time.Sleep(150 * time.Milliseconds) // Simulate API call
 paymentCounter++
    // 模拟 50% 失败率
 // if strings.HasPrefix(order.ID, "f") || paymentCounter%2 != 0 {
    // 为了测试 ErrorBoundary，让其必然失败
    if true { // 强制失败来测试补偿
  log.Printf("[Activity: ProcessPayment] Payment failed for order %s", order.ID)
  order.PaymentStatus = "Failed"
        order.LastError = "Payment processing failed (simulated)"
  return order, errors.New(order.LastError)
 }
 log.Printf("[Activity: ProcessPayment] Payment successful for order %s", order.ID)
 order.PaymentStatus = "Paid"
 return order, nil
}

func prepareShipment(ctx context.Context, order Order) (Order, error) {
 log.Printf("[Activity: PrepareShipment] Preparing shipment for order %s by %s", order.ID, order.ProcessedBy)
 if order.ProcessedBy == "" { return order, errors.New("order not assigned to any agent") }
 order.ShippingInfo.TrackingID = fmt.Sprintf("TRK-%s-%d", order.ID, time.Now().UnixNano())
 order.ShippingInfo.ShippedAt = time.Now()
 time.Sleep(100 * time.Milliseconds)
 log.Printf("[Activity: PrepareShipment] Shipment ready, Tracking ID: %s", order.ShippingInfo.TrackingID)
 return order, nil
}

func sendConfirmationEmail(ctx context.Context, order Order) (Order, error) {
 log.Printf("[Activity: SendConfirmationEmail] Sending confirmation for order %s to %s", order.ID, order.CustomerID)
 time.Sleep(80 * time.Milliseconds) // Simulate email sending
 return order, nil
}

func updateInventory(ctx context.Context, order Order) (Order, error) {
 log.Printf("[Activity: UpdateInventory] Updating inventory for order %s", order.ID)
 // Deduct items from inventory...
 time.Sleep(70 * time.Milliseconds)
 return order, nil
}

// 补偿活动 1: 取消订单 (逻辑上的)
func cancelOrder(ctx context.Context, order Order) (Order, error) {
 log.Printf("[Activity: CancelOrder] Compensating: Cancelling order %s", order.ID)
 order.PaymentStatus = "Cancelled"
    order.LastError = "Order cancelled due to payment failure"
 time.Sleep(40 * time.Milliseconds)
 return order, nil
}

// 补偿活动 2: 退款 (如果需要)
func refundPayment(ctx context.Context, order Order) (Order, error) {
 // 仅当之前状态是 "Failed" 或 "Paid" 时才需要退款？
 // 这里简化，假设 CancelOrder 后总是尝试退款
 log.Printf("[Activity: RefundPayment] Compensating: Refunding payment for order %s", order.ID)
 // ... 调用退款 API ...
 order.PaymentStatus = "Refunded" // 或保持 Cancelled?
    order.LastError = "Order cancelled and payment refunded"
 time.Sleep(90 * time.Milliseconds)
 return order, nil
}

func main() {
 // 配置日志输出到文件和控制台
    logFile, _ := os.Create("workflow_order.log")
    defer logFile.Close()
    log.SetOutput(io.MultiWriter(os.Stdout, logFile))
    log.SetFlags(log.Ldate | log.Ltime | log.Lmicroseconds)


 log.Println("--- Starting Order Processing Workflow Example ---")
 // 创建资源池
 resourcePool := workflow.NewResourcePool()
 resourcePool.AddResource(workflow.NewBaseResource("agent-1", "agent"))
 resourcePool.AddResource(workflow.NewBaseResource("agent-2", "agent"))

 // --- 定义活动实例 ---
 validateAct := workflow.NewTransformSameType("ValidateOrder", validateOrder)
 calculateAct := workflow.NewTransformSameType("CalculateTotal", calculateTotal)
 paymentAct := workflow.NewTransformSameType("ProcessPayment", processPayment)
 shipmentActInner := workflow.NewTransformSameType("PrepareShipmentInner", prepareShipment)
 emailAct := workflow.NewTransformSameType("SendConfirmation", sendConfirmationEmail)
 inventoryAct := workflow.NewTransformSameType("UpdateInventory", updateInventory)
 cancelAct := workflow.NewTransformSameType("CancelOrder", cancelOrder) // 补偿活动
 refundAct := workflow.NewTransformSameType("RefundPayment", refundPayment) // 补偿活动

 // --- 组合活动 ---

    // 1. 重试支付活动
 retryPayment := workflow.NewRetryActivity("RetryPayment", paymentAct, 1, 50*time.Millisecond). // 重试 1 次，延迟 50ms
  WithShouldRetry(func(err error) bool {
            // 只重试模拟的失败错误
   return err != nil && strings.Contains(err.Error(), "Payment processing failed")
  })

    // 2. 定义支付失败时的补偿流程 (顺序执行取消和退款)
    compensatePayment := workflow.NewSequence("CompensateFailedPayment", cancelAct, refundAct)

    // 3. 使用错误边界包装支付(及重试)逻辑，并在失败时执行补偿流程
 handlePayment := workflow.NewErrorBoundary("HandlePayment", retryPayment).
  AddCatch(func(err error) bool { return err != nil }, compensatePayment) // 捕获任何错误并执行补偿

    // 4. 准备发货活动 (需要分配 'agent' 资源)
 resourceShipment := workflow.NewResourceActivityByType("AssignAgentAndShip", resourcePool, "agent", shipmentActInner).
  WithCallbacks(
   func(ctx context.Context, order Order, resource workflow.Resource) (Order, error) {
    // OnAcquire: 记录分配到的 Agent
    order.ProcessedBy = resource.ID()
    log.Printf("[Resource Callback] Order %s assigned to %s", order.ID, resource.ID())
    return order, nil
   }, nil, // OnRelease: 不需要特殊处理
  )

    // 5. 支付成功后的并行任务 (发邮件和更新库存)
 postPaymentTasks := workflow.NewParallel("PostPaymentParallel",
  func(results []Order, original Order) (Order, error) {
            // 简单的合并：只返回原始订单状态（并行任务主要执行副作用）
            // 更复杂的合并可以检查 results 中的错误或状态
            return original, nil
        },
  func(order Order) (Order, error) { return order, nil }, // 简单映射器 (R=T=Order)
  emailAct,
  inventoryAct,
 )

    // 6. 定义支付成功后的完整流程
    successPath := workflow.NewSequence("SuccessfulPaymentPath",
        resourceShipment, // 分配资源并准备发货
        postPaymentTasks, // 并行执行邮件和库存更新
    )

    // 7. 使用条件活动根据支付状态选择路径
    checkPaymentAndProceed := workflow.NewCondition("CheckPaymentStatus",
        func(ctx context.Context, order Order) (bool, error) {
            return order.PaymentStatus == "Paid", nil // 检查支付是否成功
        },
        successPath, // True: 执行成功路径
        workflow.NewTransformSameType("PaymentFailedPath", // False: 支付失败或已补偿，记录最终状态
             func(ctx context.Context, order Order) (Order, error) {
                 log.Printf("Order %s ended with status: %s. Last Error: %s", order.ID, order.PaymentStatus, order.LastError)
                 return order, nil // 工作流本身不失败，但订单状态反映了问题
             }),
    )


 // --- 构建完整的工作流 ---
 orderProcessingWorkflow := &workflow.Workflow[Order]{
  Name: "OrderProcessing",
  RootNode: workflow.NewSequence("MainOrderFlow",
   validateAct,      // 验证
   calculateAct,     // 计算总额
   handlePayment,    // 处理支付（含重试和错误边界/补偿）
   checkPaymentAndProceed, // 根据支付结果选择后续路径
  ),
  OnComplete: func(wCtx *workflow.WorkflowContext[Order]) {
   finalOrder := wCtx.GetData()
   log.Printf("--- Workflow '%s' COMPLETED for Order %s ---", "OrderProcessing", finalOrder.ID)
   log.Printf("Final Status: %s, Tracking ID: %s, Processed By: %s, Total Amount: %.2f",
    finalOrder.PaymentStatus, finalOrder.ShippingInfo.TrackingID, finalOrder.ProcessedBy, finalOrder.TotalAmount)
            log.Printf("Activity Path: %v", wCtx.ActivityPath)
  },
  OnError: func(wCtx *workflow.WorkflowContext[Order], err error) {
            finalOrder := wCtx.GetData()
   log.Printf("--- Workflow '%s' FAILED for Order %s ---", "OrderProcessing", finalOrder.ID)
            log.Printf("Error: %v", err)
   log.Printf("Final Status: %s, Last Error: %s", finalOrder.PaymentStatus, finalOrder.LastError)
            log.Printf("Activity Path: %v", wCtx.ActivityPath)
  },
 }

 // --- 执行工作流 ---
 testOrder := Order{
  ID:         "ORD-fail-comp", // ID 触发支付失败以测试补偿
  CustomerID: "CUST-789",
  Items: []OrderItem{
   {ProductID: "PROD-A", Quantity: 2, UnitPrice: 39.99},
   {ProductID: "PROD-B", Quantity: 1, UnitPrice: 99.99},
  },
  ShippingInfo: ShippingInfo{ Address: "123 Main St", City: "Anytown", PostalCode: "10001", Country: "US" },
  CreatedAt:   time.Now(),
        PaymentStatus: "Pending",
 }

 ctx := context.Background()
 _, execErr := orderProcessingWorkflow.Execute(ctx, testOrder)

    log.Println("--- Workflow Execution Finished ---")
    if execErr != nil {
        log.Printf("Execute returned error: %v", execErr)
    } else {
         log.Println("Execute returned successfully.")
    }
    log.Println("----------------------------------------")


    // 可以添加更多测试用例，例如支付成功的场景
    // testOrderSuccess := Order{ ID: "ORD-success", ... }
    // orderProcessingWorkflow.Execute(ctx, testOrderSuccess)
}
```

#### 3.6.2 数据处理工作流

(代码与 `go_generic_workflow.md` 中 `examples/data_processing.go` 的 `main` 函数内容类似，展示了 Sequence, Transform, ErrorBoundary, Condition, MultiInstance 模式的组合)

```go
package main // (假设在 examples 目录下)

import (
 "context"
 "errors"
 "fmt"
 "log"
 "os"
    "io"
 "strings"

 "workflow" // 导入定义的 workflow 包
)

// --- 数据结构定义 ---
type DataRecord struct {
 ID       string
 RawData  string
 Parsed   map[string]any // 使用 any 代替 interface{}
 Filtered bool
 Valid    bool
 Error    string
}

// --- 活动函数实现 ---
func parseData(ctx context.Context, record DataRecord) (DataRecord, error) {
 log.Printf("[Activity: ParseData] Parsing record %s", record.ID)
 if record.RawData == "" {
  record.Error = "Empty raw data"
  // 返回错误还是仅标记错误？这里返回错误以测试 ErrorBoundary
  return record, errors.New(record.Error)
 }
 record.Parsed = make(map[string]any)
 parts := strings.Split(record.RawData, ",")
 for _, part := range parts {
  kv := strings.SplitN(part, "=", 2) // Use SplitN for values containing '='
  if len(kv) == 2 {
   record.Parsed[strings.TrimSpace(kv[0])] = strings.TrimSpace(kv[1])
  }
 }
    if len(record.Parsed) == 0 {
        record.Error = "Parsing failed, no key-value pairs found"
        return record, errors.New(record.Error)
    }
 return record, nil
}

func filterData(ctx context.Context, record DataRecord) (DataRecord, error) {
 log.Printf("[Activity: FilterData] Filtering record %s", record.ID)
    if record.Error != "" { // 如果上一步解析出错，跳过过滤
        record.Filtered = true
        return record, nil
    }
 // 示例过滤条件：Parsed 数据必须包含 "status" 字段且值为 "active"
 status, ok := record.Parsed["status"].(string)
 if !ok || status != "active" {
  log.Printf("[Activity: FilterData] Record %s filtered out (status != active or missing)", record.ID)
  record.Filtered = true
 } else {
        record.Filtered = false
    }
 return record, nil
}

func validateData(ctx context.Context, record DataRecord) (DataRecord, error) {
    log.Printf("[Activity: ValidateData] Validating record %s", record.ID)
    if record.Error != "" || record.Filtered { // 跳过已出错或已过滤的
        record.Valid = false
        return record, nil
    }
    // 示例验证：必须包含 "name" 和 "value" 字段
     _, hasName := record.Parsed["name"]
     valStr, hasValue := record.Parsed["value"].(string)
     if !hasName || !hasValue || valStr == "" {
         record.Valid = false
         record.Error = "Validation failed: missing name or value"
         log.Printf("[Activity: ValidateData] Record %s invalid: %s", record.ID, record.Error)
         // 返回错误还是仅设置标志？返回错误
         return record, errors.New(record.Error)
     }
     record.Valid = true
     log.Printf("[Activity: ValidateData] Record %s is valid.", record.ID)
     return record, nil
}


func processValidRecord(ctx context.Context, record DataRecord) (DataRecord, error) {
 log.Printf(">>> [Activity: ProcessValid] Processing VALID record %s: %v", record.ID, record.Parsed)
 // ... 实际处理逻辑 ...
 time.Sleep(20 * time.Milliseconds)
 return record, nil
}

func handleRecordError(ctx context.Context, record DataRecord) (DataRecord, error) {
 log.Printf("!!! [Activity: HandleError] Handling ERROR for record %s: %s", record.ID, record.Error)
 // ... 错误处理逻辑，例如记录到死信队列 ...
 return record, nil // 错误处理本身不应再失败
}

func skipRecord(ctx context.Context, record DataRecord) (DataRecord, error) {
    log.Printf("--- [Activity: SkipRecord] Skipping record %s (Filtered: %v, Valid: %v, Error: %s)",
        record.ID, record.Filtered, record.Valid, record.Error)
    return record, nil
}

func finalizeRecord(ctx context.Context, record DataRecord) (DataRecord, error) {
    log.Printf("=== [Activity: Finalize] Finalizing record %s ===", record.ID)
    // ... 最终清理或记录 ...
    return record, nil
}


func main() {
    logFile, _ := os.Create("workflow_data.log")
    defer logFile.Close()
    log.SetOutput(io.MultiWriter(os.Stdout, logFile))
    log.SetFlags(log.Ldate | log.Ltime | log.Lmicroseconds)

 log.Println("--- Starting Data Processing Workflow Example ---")

    // --- 定义单个记录的处理流程 ---
    recordProcessingFlow := workflow.NewSequence("SingleRecordFlow",
        workflow.NewTransformSameType("Parse", parseData),
        workflow.NewTransformSameType("Filter", filterData),
        workflow.NewTransformSameType("Validate", validateData),
        // 如果 Validate 成功，则 Process；否则 Skip
        workflow.NewCondition("CheckValidity",
            func(ctx context.Context, r DataRecord) (bool, error) { return r.Valid && r.Error == "", nil },
            workflow.NewTransformSameType("ProcessIfValid", processValidRecord), // True Path
            workflow.NewTransformSameType("SkipIfNotValid", skipRecord),       // False Path
        ),
    )

    // --- 使用错误边界包装整个流程，处理特定错误并添加 Finally ---
    recordPipelineWithBoundary := workflow.NewErrorBoundary("RecordBoundary", recordProcessingFlow).
        AddCatch( // 捕获解析或验证阶段的错误
            func(err error) bool { return err != nil }, // 捕获任何错误
            workflow.NewTransformSameType("HandleAnyError", handleRecordError), // 执行错误处理活动
        ).
        WithFinally( // 无论成功失败都执行 finalize
             workflow.NewTransformSameType("Finalize", finalizeRecord),
        )


 // --- 创建测试数据 ---
 testRecords := []DataRecord{
  {ID: "REC-1", RawData: "name=apple,color=red,value=5,status=active"},  // Valid
  {ID: "REC-2", RawData: "type=fruit,color=yellow,status=inactive"}, // Filtered out
  {ID: "REC-3", RawData: ""},                                        // Parse error
  {ID: "REC-4", RawData: "name=orange,status=active"},               // Validation error (missing value)
        {ID: "REC-5", RawData: "item=book,value=20,status=active,name=Go Patterns"}, // Valid
        {ID: "REC-6", RawData: "status=active,value=100,name=Another"},      // Valid
 }

 // --- 使用多实例活动并行处理所有记录 ---
    // I = DataRecord (单个项目类型)
    // R = DataRecord (每个实例处理后的结果类型)
    // T = []DataRecord (整个工作流的数据类型，即记录列表)
 multiInstanceActivity := workflow.NewMultiInstance("BatchProcessRecords",
        // ItemsExtractor: 从输入 T ([]DataRecord) 提取项目 I (DataRecord)
        func(allRecords []DataRecord) ([]DataRecord, error) { return allRecords, nil },
        // ItemActivityTyped: 对每个 I (DataRecord) 执行的活动 (返回 R=DataRecord)
        // 注意：这里需要一个 ActivityInOut[DataRecord, DataRecord]
        // 我们将 recordPipelineWithBoundary 包装一下
        &workflow.ActivityFuncWrapper[DataRecord, DataRecord]{ // 需要定义这个包装器
             ActivityName: "RecordProcessor",
             ExecFunc: recordPipelineWithBoundary.Execute,
        },
        // ResultAggregatorTyped: 将结果 map[int]R (map[int]DataRecord) 聚合回 T ([]DataRecord)
  func(results map[int]DataRecord, original []DataRecord) ([]DataRecord, error) {
   finalRecords := make([]DataRecord, len(original))
            // 聚合结果，保留原始顺序，用处理后的结果覆盖
            for i := range original {
                if res, ok := results[i]; ok {
                    finalRecords[i] = res // 使用处理后的结果
                } else {
                    // 如果并行执行中某个实例出错且未产生结果，保留原始记录？
                    // 或者根据错误处理逻辑决定？这里保留原始记录
                    finalRecords[i] = original[i]
                    // 可以检查原始记录的 Error 字段，看是否被之前的步骤设置过
                    // log.Printf("Warning: No result found for original record index %d", i)
                }
            }
   return finalRecords, nil
  },
 ).SetParallel(true, false) // 并行执行，不快速失败

    // --- 定义并执行整个工作流 ---
    batchWorkflow := workflow.Workflow[[]DataRecord]{
        Name: "BatchDataProcessing",
        RootNode: multiInstanceActivity, // 根节点是多实例活动
        OnComplete: func(wCtx *workflow.WorkflowContext[[]DataRecord]) {
            processedRecords := wCtx.GetData()
            log.Println("--- Batch Workflow COMPLETED ---")
            validCount, filteredCount, errorCount := 0, 0, 0
            for _, r := range processedRecords {
                if r.Valid && r.Error == "" && !r.Filtered { validCount++ }
                if r.Filtered { filteredCount++ }
                if r.Error != "" { errorCount++ }
            }
            log.Printf("Processing Summary: Total=%d, ValidProcessed=%d, Filtered=%d, Errors=%d",
                len(processedRecords), validCount, filteredCount, errorCount)
        },
        OnError: func(wCtx *workflow.WorkflowContext[[]DataRecord], err error) {
             log.Printf("--- Batch Workflow FAILED ---")
             log.Printf("Error: %v", err)
             // 可以打印部分处理结果 (wCtx.GetData())
        },
    }

 ctx := context.Background()
 _, execErr := batchWorkflow.Execute(ctx, testRecords)

    log.Println("--- Batch Workflow Execution Finished ---")
    if execErr != nil {
        log.Printf("Execute returned error: %v", execErr)
    } else {
        log.Println("Execute returned successfully.")
    }
    log.Println("-----------------------------------------")
}

// ActivityFuncWrapper - Helper to wrap an Execute function into ActivityInOut
type ActivityFuncWrapper[In any, Out any] struct {
    ActivityName string
    ExecFunc func(ctx context.Context, input In) (Out, error)
}
func (w *ActivityFuncWrapper[In, Out]) Execute(ctx context.Context, input In) (Out, error) {
    return w.ExecFunc(ctx, input)
}
func (w *ActivityFuncWrapper[In, Out]) Name() string {
    return w.ActivityName
}

```

#### 3.6.3 审批流程工作流

(代码与 `go_generic_workflow.md` 中 `examples/approval_workflow.go` 的 `main` 函数内容类似，展示了 Sequence, Transform, DataRouting, Condition 模式的组合)

```go
package main // (假设在 examples 目录下)

import (
 "context"
 "errors"
 "fmt"
 "log"
 "os"
    "io"
 "time"

 "workflow" // 导入定义的 workflow 包
)

// --- 数据结构定义 ---
type ApprovalRequest struct {
 ID             string
 RequesterID    string
 RequestType    string
 Description    string
 Amount         float64
 Status         string // "Pending L1", "Pending L2", "Pending L3", "Approved", "Rejected"
 CurrentLevel   int    // 当前需要审批的级别 (1, 2, 3...)
 ApprovalChain  []ApprovalStep
 Comments       []Comment
 CreatedAt      time.Time
 LastModifiedAt time.Time
    LastError      string // 记录错误
}
type ApprovalStep struct {
 Level      int
 ApproverID string // 实际批准人 ID
 Status     string // "Pending", "Approved", "Rejected"
 ApprovedAt time.Time
 Comment    string // 审批人评论
}
type Comment struct {
 UserID    string
 Text      string
 Timestamp time.Time
}

// --- 活动函数实现 ---
func validateRequest(ctx context.Context, request ApprovalRequest) (ApprovalRequest, error) {
 log.Printf("[Activity: ValidateRequest] Validating request %s", request.ID)
 if request.RequesterID == "" { return request, errors.New("requester ID is empty") }
 if request.RequestType == "" { return request, errors.New("request type is empty") }
 if request.Amount <= 0 { return request, errors.New("amount must be positive") }
 request.Status = "Validated"
 return request, nil
}

func initializeApprovalChain(ctx context.Context, request ApprovalRequest) (ApprovalRequest, error) {
 log.Printf("[Activity: InitChain] Initializing chain for request %s, amount %.2f", request.ID, request.Amount)
 request.ApprovalChain = []ApprovalStep{} // 清空旧链（如果可能重入）
 request.CurrentLevel = 1

 if request.Amount <= 1000 {
  request.ApprovalChain = append(request.ApprovalChain, ApprovalStep{Level: 1, Status: "Pending"})
        request.Status = "Pending L1 Approval"
 } else if request.Amount <= 10000 {
  request.ApprovalChain = append(request.ApprovalChain,
   ApprovalStep{Level: 1, Status: "Pending"},
   ApprovalStep{Level: 2, Status: "Waiting"}) // 标记后续级别为等待
        request.Status = "Pending L1 Approval"
 } else {
  request.ApprovalChain = append(request.ApprovalChain,
   ApprovalStep{Level: 1, Status: "Pending"},
   ApprovalStep{Level: 2, Status: "Waiting"},
   ApprovalStep{Level: 3, Status: "Waiting"})
        request.Status = "Pending L1 Approval"
 }
 request.LastModifiedAt = time.Now()
 log.Printf("[Activity: InitChain] Chain initialized: %d levels", len(request.ApprovalChain))
 return request, nil
}

// submitApproval 返回一个活动函数，模拟特定级别的审批动作
func submitApproval(level int, approved bool, approverID, comment string) func(context.Context, ApprovalRequest) (ApprovalRequest, error) {
 return func(ctx context.Context, request ApprovalRequest) (ApprovalRequest, error) {
  log.Printf("[Activity: SubmitApproval L%d] Simulating approval for request %s by %s (Approved: %v)",
   level, request.ID, approverID, approved)

  if level != request.CurrentLevel {
   err := fmt.Errorf("mismatched approval level: expected %d, got activity for L%d", request.CurrentLevel, level)
            request.LastError = err.Error()
            return request, err
  }
  if request.Status == "Approved" || request.Status == "Rejected" {
             err := fmt.Errorf("request %s already finalized with status %s", request.ID, request.Status)
             request.LastError = err.Error()
             return request, err
        }

  currentLevelIndex := request.CurrentLevel - 1
  if currentLevelIndex < 0 || currentLevelIndex >= len(request.ApprovalChain) {
   err := errors.New("invalid current approval level index")
            request.LastError = err.Error()
            return request, err
  }

  // 更新当前级别的审批状态
  request.ApprovalChain[currentLevelIndex].ApproverID = approverID
  request.ApprovalChain[currentLevelIndex].ApprovedAt = time.Now()
        request.ApprovalChain[currentLevelIndex].Comment = comment

  if approved {
   request.ApprovalChain[currentLevelIndex].Status = "Approved"
   // 检查是否有下一级审批
   if request.CurrentLevel < len(request.ApprovalChain) {
    request.CurrentLevel++
    request.ApprovalChain[request.CurrentLevel-1].Status = "Pending" // 更新下一级状态
    request.Status = fmt.Sprintf("Pending L%d Approval", request.CurrentLevel)
                log.Printf("[Activity: SubmitApproval L%d] Approved, proceeding to L%d", level, request.CurrentLevel)
   } else {
    // 所有级别都已批准
    request.Status = "Approved"
                log.Printf("[Activity: SubmitApproval L%d] Final approval!", level)
   }
  } else {
   // 拒绝审批，整个请求被拒绝
   request.ApprovalChain[currentLevelIndex].Status = "Rejected"
   request.Status = "Rejected"
             log.Printf("[Activity: SubmitApproval L%d] Rejected by %s", level, approverID)
  }

  request.LastModifiedAt = time.Now()
  return request, nil // 审批动作本身不返回错误，除非内部逻辑出错
 }
}

func addComment(userID, text string) func(context.Context, ApprovalRequest) (ApprovalRequest, error) {
 return func(ctx context.Context, request ApprovalRequest) (ApprovalRequest, error) {
  log.Printf("[Activity: AddComment] User %s adding comment to request %s", userID, request.ID)
  comment := Comment{ UserID: userID, Text: text, Timestamp: time.Now() }
  request.Comments = append(request.Comments, comment)
  request.LastModifiedAt = time.Now()
  return request, nil
 }
}

func notifyRequester(ctx context.Context, request ApprovalRequest) (ApprovalRequest, error) {
 log.Printf(">>> [Notification] Notifying requester %s: Request %s status updated to %s",
  request.RequesterID, request.ID, request.Status)
 // ... 实际的通知逻辑 (e.g., send email, message queue) ...
 time.Sleep(50 * time.Milliseconds)
 return request, nil
}

func main() {
    logFile, _ := os.Create("workflow_approval.log")
    defer logFile.Close()
    log.SetOutput(io.MultiWriter(os.Stdout, logFile))
    log.SetFlags(log.Ldate | log.Ltime | log.Lmicroseconds)

 log.Println("--- Starting Approval Workflow Example ---")

 // --- 定义审批活动 ---
 // 假设 L1, L2 批准，L3 拒绝
 approveL1 := workflow.NewTransformSameType("ApproveL1", submitApproval(1, true, "APPROVER-L1", "LGTM"))
 approveL2 := workflow.NewTransformSameType("ApproveL2", submitApproval(2, true, "APPROVER-L2", "Looks ok"))
 rejectL3 := workflow.NewTransformSameType("RejectL3", submitApproval(3, false, "APPROVER-L3", "Amount too high"))

    // 定义未知级别处理活动
    unknownLevelHandler := workflow.NewTransformSameType("HandleUnknownLevel",
         func(ctx context.Context, r ApprovalRequest) (ApprovalRequest, error) {
             err := fmt.Errorf("workflow error: unknown or unexpected approval level %d for status %s", r.CurrentLevel, r.Status)
             r.LastError = err.Error()
             r.Status = "Error"
             log.Printf("[Activity: HandleUnknownLevel] %v", err)
             return r, err // 返回错误，使工作流失败
         })

 // --- 构建审批路由和循环逻辑 ---
 // 使用 LoopActivity 来处理多级审批，直到状态变为 Approved 或 Rejected
 approvalLoop := workflow.NewLoop("ApprovalLoop",
        // Loop Condition: 继续循环当状态是 Pending Lx
        func(ctx context.Context, req ApprovalRequest, iteration int) (bool, error) {
            keepLooping := strings.HasPrefix(req.Status, "Pending")
            log.Printf("[Loop Condition] Iteration %d, Status: %s, Keep Looping: %v", iteration, req.Status, keepLooping)
            return keepLooping, nil
        },
        // Loop Body: 使用 DataRouting 根据 CurrentLevel 选择正确的审批活动
        workflow.NewDataRouter("RouteApprovalLevel",
            func(ctx context.Context, req ApprovalRequest) (string, error) {
                // 路由键基于当前需要审批的级别
                return fmt.Sprintf("level%d", req.CurrentLevel), nil
            },
            // 路由映射
            map[string]workflow.Activity[ApprovalRequest]{
                "level1": approveL1,
                "level2": approveL2,
                "level3": rejectL3,
                // 可以添加更多级别
            },
        ).WithDefault(unknownLevelHandler), // 处理未知级别
    ).WithMaxIterations(10) // 设置最大迭代次数防止意外死循环

    // --- 构建最终处理流程 (审批结束后) ---
    finalProcessing := workflow.NewSequence("FinalProcessing",
        workflow.NewTransformSameType("AddFinalComment", addComment("SYSTEM", "Approval process finished.")),
        workflow.NewTransformSameType("NotifyRequester", notifyRequester),
    )

 // --- 构建完整的工作流 ---
 approvalWorkflow := &workflow.Workflow[ApprovalRequest]{
  Name: "ExpenseApproval",
  RootNode: workflow.NewSequence("MainApprovalFlow",
   workflow.NewTransformSameType("Validate", validateRequest),
   workflow.NewTransformSameType("InitializeChain", initializeApprovalChain),
            approvalLoop, // 执行审批循环
            finalProcessing, // 循环结束后执行最终处理
  ),
  OnComplete: func(wCtx *workflow.WorkflowContext[ApprovalRequest]) {
   req := wCtx.GetData()
   log.Printf("--- Workflow '%s' COMPLETED for Request %s ---", "ExpenseApproval", req.ID)
   log.Printf("Final Status: %s", req.Status)
            // 打印审批链详情
            for _, step := range req.ApprovalChain {
                 log.Printf("  L%d: Status=%s, Approver=%s, Comment='%s'", step.Level, step.Status, step.ApproverID, step.Comment)
            }
  },
  OnError: func(wCtx *workflow.WorkflowContext[ApprovalRequest], err error) {
   req := wCtx.GetData()
            log.Printf("--- Workflow '%s' FAILED for Request %s ---", "ExpenseApproval", req.ID)
   log.Printf("Error: %v", err)
            log.Printf("Final Status: %s, Last Error: %s", req.Status, req.LastError)
  },
 }

 // --- 执行工作流 ---
 testRequest := ApprovalRequest{
  ID:          "REQ-large-expense",
  RequesterID: "EMP-101",
  RequestType: "软件采购",
  Description: "IDE License",
  Amount:      15000.00, // > 10000, 需要 3 级审批
  CreatedAt:   time.Now(),
        Status:      "New",
 }

 ctx := context.Background()
 _, execErr := approvalWorkflow.Execute(ctx, testRequest)

    log.Println("--- Approval Workflow Execution Finished ---")
    if execErr != nil {
        log.Printf("Execute returned error: %v", execErr)
    } else {
        log.Println("Execute returned successfully.")
    }
    log.Println("-----------------------------------------")

    // 可以创建不同 Amount 的请求来测试不同审批路径
}
```

---

### 3.7 工作流模式间的关系与组合

工作流模式并非孤立存在，它们经常被组合和嵌套使用，以构建复杂的业务流程：

1. **组合 (Composition)**: 大多数实际工作流都是多种模式的组合。例如，一个订单处理流程可能顺序执行验证和计算，然后根据支付结果进行条件分支，成功的分支可能并行执行发货和通知，失败的分支可能执行补偿。
2. **嵌套 (Nesting)**: 模式可以嵌套。一个 `SequenceActivity` 可以包含 `ParallelActivity` 或 `ConditionActivity`。一个 `LoopActivity` 的循环体可以是另一个复杂的 `SequenceActivity`。一个 `ErrorBoundaryActivity` 可以保护包含多种其他模式的子流程。
3. **互补 (Complementarity)**: 不同类别的模式相互补充。
    - **控制流**定义“何时”和“以何种顺序”执行。
    - **数据流**定义数据“如何”在活动间流动和转换。
    - **资源**模式管理活动执行所需的“参与者”或“工具”。
    - **异常处理**定义“如果出错”该怎么办。
4. **转换 (Transformation)**: 某些模式可以通过特定配置简化为其他模式。例如，`MultiChoiceActivity` 如果所有条件互斥，就等同于 `ConditionActivity` 或 `DataRoutingActivity`。`ParallelActivity` 如果只有一个分支，就等同于该分支活动本身。

Go 语言的接口和组合特性使得将这些模式像乐高积木一样组合起来非常自然。泛型进一步增强了这种组合的类型安全性。

---

### 3.8 工作流引擎扩展 (讨论)

上面实现的模式构成了工作流引擎的核心，但在生产环境中，通常还需要考虑以下扩展功能：

#### 持久化与状态管理

- **需求**: 长时间运行的工作流（如跨越数天或数周的审批流程）需要在执行中断（如服务器重启）后能够恢复。
- **实现思路**:
  - **状态存储**: 将 `WorkflowContext`（包含数据、活动路径、元数据）和当前执行到的 *位置*（例如，下一个要执行的活动、等待的事件）序列化并存储到持久化存储中（如数据库、KV 存储）。
  - **检查点**: 在工作流的关键节点（如活动完成后、进入等待状态前）保存状态。
  - **恢复**: 引擎启动时加载未完成的工作流状态，并从上次中断的位置继续执行。
  - **挑战**: 序列化复杂数据、处理状态版本兼容性、确保状态更新的原子性。

#### 事件驱动与触发器

- **需求**: 工作流通常需要由外部事件触发（如 API 调用、新消息到达、定时器触发），或者在执行过程中需要等待外部事件（如 `Deferred Choice`）。
- **实现思路**:
  - **触发器**: 定义外部事件如何映射到工作流的启动或恢复。
  - **事件总线/消息队列**: 引擎可以监听事件总线或消息队列。
  - **等待活动**: 实现可以挂起工作流并注册事件监听器的活动。当事件发生时，引擎根据事件内容查找并唤醒相应的工作流实例。
  - **关联**: 需要一种机制将外部事件与特定的工作流实例关联起来（例如，使用订单 ID、用户 ID 作为关联键）。

#### 可视化与监控

- **需求**: 理解工作流的执行状态、跟踪历史记录、诊断问题。
- **实现思路**:
  - **日志记录**: 在 `WorkflowContext` 中记录详细的活动执行路径、时间戳和关键数据变化。`Execute` 方法和回调函数中添加日志。
  - **指标**: 收集工作流执行时间、活动执行时间、错误率、资源使用情况等指标，并暴露给监控系统（如 Prometheus）。
  - **可视化**: 根据工作流定义和执行历史，生成流程图，并高亮显示当前状态或历史路径。这通常需要将工作流定义存储为结构化格式（如 JSON, YAML, BPMN）。
  - **追踪 (Tracing)**: 使用 OpenTelemetry 等分布式追踪系统，将工作流执行作为一个 Trace，每个活动作为一个 Span，便于跟踪跨服务的工作流。

#### Saga 模式与分布式事务

- **需求**: 在微服务架构中，一个业务流程可能跨越多个服务，需要保证数据的一致性，即使某些步骤失败。
- **实现思路**:
  - **Saga 模式**: 将长事务分解为一系列本地事务，每个本地事务都有一个对应的补偿操作。如果某个本地事务失败，则按相反顺序执行前面已成功事务的补偿操作。
  - **编排式 Saga (Orchestration)**: 一个中心协调器（可以是工作流引擎）负责调用每个服务的本地事务和补偿操作。工作流引擎可以很好地扮演编排者的角色，使用 `Sequence`, `ErrorBoundary`, `Compensation` 等模式来管理 Saga 流程。
  - **协同式 Saga (Choreography)**: 服务之间通过发布/订阅事件来触发后续步骤和补偿。工作流引擎可以用于实现某个服务内部的逻辑，或者作为事件监听器。

---

## 4. 并发模式在工作流中的应用 (交叉关联)

Go 的并发模式可以与工作流模式结合，以提高工作流引擎的性能和响应能力：

- **使用 Worker Pool 执行活动**:
  - 对于 CPU 密集型或 IO 密集型的活动，可以使用 `WorkerPool` 来并发执行它们，而不是在主工作流 goroutine 中顺序执行。
  - `ParallelActivity` 和 `MultiInstanceActivity` (并行模式) 可以内部利用 `WorkerPool` 或直接启动 goroutine 来实现并行。
- **使用 Pub/Sub 进行状态通知**:
  - 工作流引擎可以在关键事件（如工作流启动、完成、失败、活动状态改变）时发布事件到 `Publisher`。
  - 外部系统或监控服务可以作为 `Subscriber` 来接收这些通知。
  - `OnComplete` 和 `OnError` 回调可以触发事件发布。
- **使用并发控制保护资源或限制速率**:
  - 如果工作流活动需要调用外部 API 或访问共享资源，可以使用 `RateLimiter` 限制调用频率，使用 `CircuitBreaker` 防止调用失败的服务，使用 `Bulkhead` 隔离对不同外部系统的调用。
  - `ResourcePool` 本身可以使用 `Semaphore` 来控制资源的并发访问。
- **使用 Future/Promise 处理异步活动**:
  - 某些工作流活动可能是长时间运行的异步操作（例如，调用外部系统并等待回调）。
  - 可以将这些活动实现为启动异步操作并立即返回一个 `Future`。
  - 工作流引擎可以在后续步骤中使用 `Future.Get()` 来等待并获取结果，或者使用 `Future.ResultChan()` 与 `select` 结合进行非阻塞等待。这使得工作流引擎在等待异步活动时不会被阻塞。

将并发模式融入工作流引擎设计，可以构建出既能清晰编排业务逻辑，又能高效利用系统资源的强大系统。

---

## 5. 总结

本文档深入探讨了 Go 语言中并发、并行以及工作流设计模式的实现。通过结合 Go 1.24+ 的泛型和接口特性，我们展示了如何构建类型安全、可复用且符合 Go 语言习惯的模式库。

- **并发与并行模式**: 涵盖了从基础的 Worker Pool、Pipeline 到高级的同步原语、并发控制（如 Rate Limiter, Circuit Breaker）以及消息通信（Pub/Sub, Actor, CSP）和并行数据处理（Map-Reduce, Fork-Join）模式。这些模式是构建高性能、高弹性 Go 应用的基石。
- **工作流模式**: 实现了控制流、数据流、资源管理和异常处理等核心工作流模式。这些模式提供了一种结构化的方法来编排复杂的业务流程。

关键在于理解各种模式的适用场景和权衡，并学会如何将它们 **组合** 起来解决实际问题。例如，并发模式可以用来优化工作流活动的执行效率，而工作流模式则为复杂的并发协作提供了清晰的结构。

利用 Go 的原生并发能力和泛型，开发者可以构建出既强大又易于维护的并发系统和工作流引擎。

---

## 6. 思维导图 (Text 格式)

```text
Go 语言高级模式：并发、并行与工作流系统设计
│
├── 1. 引言
│   ├── Go 语言特性与模式设计
│   └── 泛型的应用价值
│
├── 2. 并发与并行设计模式
│   ├── 2.1 基础并发模式
│   │   ├── Worker Pool
│   │   ├── Pipeline
│   │   ├── Fan-Out/Fan-In
│   │   └── Future/Promise
│   ├── 2.2 同步模式
│   │   ├── Barrier (含泛型数据交换)
│   │   ├── Mutex (扩展, 含泛型资源保护)
│   │   ├── Read-Write Lock (扩展, 含泛型资源保护)
│   │   ├── Semaphore (含泛型资源池)
│   │   └── sync/atomic 包的应用 (讨论)
│   ├── 2.3 并发控制模式
│   │   ├── Context (含泛型 Value)
│   │   ├── Rate Limiting (令牌桶, 含泛型)
│   │   ├── Circuit Breaker (含泛型)
│   │   └── Bulkhead (含泛型)
│   ├── 2.4 消息通信模式
│   │   ├── Publish-Subscribe (含异步, Listener)
│   │   ├── Actor (含扩展讨论)
│   │   └── CSP (Pipe, Mux, Demux, Filter, Map, ProcessNetwork)
│   ├── 2.5 并行数据处理模式
│   │   ├── Map-Reduce (含并发, Pipeline)
│   │   └── Fork-Join (含 RecursiveTask, ParallelFor/Reduce)
│   ├── 2.6 并发模式选择与权衡 (讨论)
│   └── 2.7 分布式并发模式简介 (讨论)
│
├── 3. 工作流模式与系统实现
│   ├── 3.1 工作流核心概念
│   │   ├── Activity (活动)
│   │   ├── WorkflowContext (上下文)
│   │   ├── Workflow (定义)
│   │   └── 基础架构代码
│   ├── 3.2 控制流模式
│   │   ├── Sequence (顺序)
│   │   ├── Parallel Split/Sync (并行分支/同步)
│   │   ├── Exclusive Choice (排他选择)
│   │   ├── Multi-Choice (多选择)
│   │   ├── Loop (循环)
│   │   ├── Multiple Instances (多实例)
│   │   ├── Deferred Choice (延迟选择) (概念)
│   │   └── Milestone (里程碑) (概念)
│   ├── 3.3 数据流模式
│   │   ├── Data Passing (数据传递) (隐式)
│   │   ├── Data Transformation (数据转换)
│   │   ├── Data Routing (数据路由)
│   │   ├── Data Aggregation (数据合并)
│   │   └── Data Filter (数据过滤)
│   ├── 3.4 资源模式
│   │   ├── Resource & Pool (资源与池)
│   │   ├── Resource Allocation (资源分配)
│   │   ├── Role-based Distribution (角色分配)
│   │   ├── Workload Balancing (负载均衡)
│   │   └── 扩展讨论 (优先级, 预留)
│   ├── 3.5 异常处理模式
│   │   ├── Retry (重试)
│   │   ├── Timeout (超时)
│   │   ├── Compensation (补偿)
│   │   ├── Cancel (取消)
│   │   ├── Error Boundary (错误边界)
│   │   └── Rollback (回滚) (概念)
│   ├── 3.6 工作流示例
│   │   ├── 订单处理
│   │   ├── 数据处理
│   │   └── 审批流程
│   ├── 3.7 模式间关系与组合
│   └── 3.8 工作流引擎扩展 (讨论)
│       ├── 持久化与状态管理
│       ├── 事件驱动与触发器
│       ├── 可视化与监控
│       └── Saga 模式与分布式事务
│
├── 4. 并发模式在工作流中的应用 (交叉关联)
│   ├── Worker Pool 执行活动
│   ├── Pub/Sub 状态通知
│   ├── 并发控制保护资源/限速
│   └── Future/Promise 处理异步活动
│
└── 5. 总结
```
