# Go语言并发并行设计模式全解析

```text
<think>
这个用户请求要:
1. 使用Golang语义模型
2. 使用泛型接口（Go 1.24版本）
3. 实现设计模式中的并发并行模式
4. 以Markdown格式输出，包含目录
5. 可能的话包含思维导图
6. 不输出外部链接，使用纯文本格式
7. 全部用中文回答

首先我需要思考并发并行设计模式的分类，
然后用Go 1.24的特性（特别是泛型）来实现这些模式。

并发并行设计模式可以分为以下几类：

1. **基础并发模式**
   - Worker Pool模式
   - Pipeline模式
   - Fan-Out/Fan-In模式
   - Future/Promise模式

2. **同步模式**
   - Barrier模式
   - Mutex模式
   - Read-Write Lock模式
   - Semaphore模式

3. **并发控制模式**
   - Context模式
   - Rate Limiting模式
   - Circuit Breaker模式
   - Bulkhead模式

4. **消息通信模式**
   - Publish-Subscribe模式
   - Actor模式
   - CSP (Communicating Sequential Processes)模式

5. **并行数据处理模式**
   - Map-Reduce模式
   - Fork-Join模式

我会使用Go 1.24的泛型特性来实现这些模式，以展示更通用和类型安全的实现方式。
由于Go的并发模型主要基于goroutine和channel，
我将充分利用这些特性，同时结合泛型来增强代码的复用性和类型安全性。

现在让我开始构建响应框架，然后为每个模式提供详细的实现。
</think>
```

## 目录

- [Go语言并发并行设计模式全解析](#go语言并发并行设计模式全解析)
  - [目录](#目录)
  - [引言](#引言)
  - [并发并行模式形式模型分类](#并发并行模式形式模型分类)
  - [基础并发模式](#基础并发模式)
    - [Worker Pool模式](#worker-pool模式)
    - [Pipeline模式](#pipeline模式)
    - [Fan-Out/Fan-In模式](#fan-outfan-in模式)
    - [Future/Promise模式](#futurepromise模式)
  - [同步模式](#同步模式)
    - [Barrier模式](#barrier模式)
    - [Mutex模式](#mutex模式)
    - [Read-Write Lock模式](#read-write-lock模式)
    - [Semaphore模式](#semaphore模式)
  - [并发控制模式](#并发控制模式)
    - [Context模式](#context模式)
    - [Rate Limiting模式](#rate-limiting模式)
    - [Circuit Breaker模式](#circuit-breaker模式)
    - [Bulkhead模式](#bulkhead模式)
  - [消息通信模式](#消息通信模式)
    - [Publish-Subscribe模式](#publish-subscribe模式)
    - [Actor模式](#actor模式)
    - [CSP模式](#csp模式)
  - [并行数据处理模式](#并行数据处理模式)
    - [Map-Reduce模式](#map-reduce模式)
    - [Fork-Join模式](#fork-join模式)
  - [总结](#总结)

## 引言

Go语言因其卓越的并发支持而闻名，通过goroutine和channel提供了轻量级并发原语。随着Go 1.18引入泛型，并在后续版本中不断完善，特别是Go 1.24中对接口和泛型的增强，使我们能够更优雅地实现各种并发并行模式。本文将从形式模型角度分析并发并行模式，并使用Go语言的语义模型实现这些模式。

## 并发并行模式形式模型分类

并发并行编程模式可以从以下维度分类：

```tex
并发并行模式
├── 基础并发模式
│   ├── Worker Pool
│   ├── Pipeline
│   ├── Fan-Out/Fan-In
│   └── Future/Promise
├── 同步模式
│   ├── Barrier
│   ├── Mutex
│   ├── Read-Write Lock
│   └── Semaphore
├── 并发控制模式
│   ├── Context
│   ├── Rate Limiting
│   ├── Circuit Breaker
│   └── Bulkhead
├── 消息通信模式
│   ├── Publish-Subscribe
│   ├── Actor
│   └── CSP
└── 并行数据处理模式
    ├── Map-Reduce
    └── Fork-Join
```

## 基础并发模式

### Worker Pool模式

Worker Pool模式管理一组工作协程，处理来自任务队列的工作。

```go
package workerpool

import (
 "context"
 "sync"
)

// Task 表示可以由工作者处理的任务
type Task[T any, R any] interface {
 Execute() R
}

// WorkerPool 管理一组工作者协程
type WorkerPool[T any, R any] struct {
 workerCount int
 taskQueue   chan Task[T, R]
 resultQueue chan R
 wg          sync.WaitGroup
 ctx         context.Context
 cancel      context.CancelFunc
}

// NewWorkerPool 创建一个新的工作池
func NewWorkerPool[T any, R any](workerCount int, queueSize int) *WorkerPool[T, R] {
 ctx, cancel := context.WithCancel(context.Background())
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
   wp.worker(workerID)
  }(i)
 }
}

// 工作者函数
func (wp *WorkerPool[T, R]) worker(id int) {
 for {
  select {
  case <-wp.ctx.Done():
   return
  case task, ok := <-wp.taskQueue:
   if !ok {
    return
   }
   result := task.Execute()
   wp.resultQueue <- result
  }
 }
}

// Submit 提交任务到工作池
func (wp *WorkerPool[T, R]) Submit(task Task[T, R]) {
 wp.taskQueue <- task
}

// Results 返回结果通道
func (wp *WorkerPool[T, R]) Results() <-chan R {
 return wp.resultQueue
}

// Stop 停止工作池
func (wp *WorkerPool[T, R]) Stop() {
 wp.cancel()
 close(wp.taskQueue)
 wp.wg.Wait()
 close(wp.resultQueue)
}

// 使用示例
type SimpleTask[T any] struct {
 Data T
 Fn   func(T) T
}

func (t SimpleTask[T]) Execute() T {
 return t.Fn(t.Data)
}
```

### Pipeline模式

Pipeline模式创建一系列处理阶段，每个阶段处理数据并将结果传递给下一阶段。

```go
package pipeline

// Processor 定义了处理函数接口
type Processor[T any, R any] interface {
 Process(input T) R
}

// ProcessorFunc 允许使用函数作为处理器
type ProcessorFunc[T any, R any] func(input T) R

func (pf ProcessorFunc[T, R]) Process(input T) R {
 return pf(input)
}

// Pipeline 表示一个处理管道
type Pipeline[T any, R any] struct {
 processor Processor[T, R]
}

// NewPipeline 创建一个新的管道
func NewPipeline[T any, R any](processor Processor[T, R]) *Pipeline[T, R] {
 return &Pipeline[T, R]{processor: processor}
}

// Process 处理输入并返回结果
func (p *Pipeline[T, R]) Process(input T) R {
 return p.processor.Process(input)
}

// Then 将当前管道与另一个处理器链接起来
func (p *Pipeline[T, R]) Then(next Processor[R, any]) *Pipeline[T, any] {
 return NewPipeline(ProcessorFunc[T, any](func(input T) any {
  intermediate := p.Process(input)
  return next.Process(intermediate)
 }))
}

// Stream 将管道应用于输入通道并返回输出通道
func (p *Pipeline[T, R]) Stream(input <-chan T) <-chan R {
 output := make(chan R)
 
 go func() {
  defer close(output)
  for item := range input {
   output <- p.Process(item)
  }
 }()
 
 return output
}
```

### Fan-Out/Fan-In模式

Fan-Out/Fan-In模式将工作分发给多个并发进程（fan-out），然后收集所有结果（fan-in）。

```go
package fanoutfanin

import (
 "sync"
)

// Processor 定义可以并行处理数据的接口
type Processor[T any, R any] interface {
 Process(input T) R
}

// ProcessorFunc 允许使用函数作为处理器
type ProcessorFunc[T any, R any] func(input T) R

func (pf ProcessorFunc[T, R]) Process(input T) R {
 return pf(input)
}

// FanOut 将输入分发给多个并发处理器
func FanOut[T any, R any](input <-chan T, processor Processor[T, R], workers int) []<-chan R {
 outputs := make([]<-chan R, workers)
 
 for i := 0; i < workers; i++ {
  outputs[i] = worker(input, processor)
 }
 
 return outputs
}

// worker 启动一个工作协程
func worker[T any, R any](input <-chan T, processor Processor[T, R]) <-chan R {
 output := make(chan R)
 
 go func() {
  defer close(output)
  for item := range input {
   output <- processor.Process(item)
  }
 }()
 
 return output
}

// FanIn 合并多个输入通道为一个输出通道
func FanIn[T any](inputs []<-chan T) <-chan T {
 output := make(chan T)
 var wg sync.WaitGroup
 
 // 为每个输入通道启动一个goroutine
 for _, ch := range inputs {
  wg.Add(1)
  go func(c <-chan T) {
   defer wg.Done()
   for item := range c {
    output <- item
   }
  }(ch)
 }
 
 // 等待所有goroutine完成，然后关闭输出通道
 go func() {
  wg.Wait()
  close(output)
 }()
 
 return output
}

// Process 执行完整的Fan-Out/Fan-In流程
func Process[T any, R any](input <-chan T, processor Processor[T, R], workers int) <-chan R {
 // Fan-out到多个worker
 outputs := FanOut(input, processor, workers)
 // Fan-in收集所有结果
 return FanIn(outputs)
}
```

### Future/Promise模式

Future/Promise模式允许异步计算并在将来获取结果。

```go
package future

import (
 "context"
 "sync"
)

// Future 代表异步计算的最终结果
type Future[T any] interface {
 // Get 返回结果，如果未完成则阻塞
 Get() (T, error)
 // GetWithContext 带有上下文的获取结果
 GetWithContext(ctx context.Context) (T, error)
 // IsDone 检查计算是否完成
 IsDone() bool
}

// Promise 用于设置Future的结果
type Promise[T any] interface {
 // SetResult 设置成功结果
 SetResult(result T)
 // SetError 设置错误结果
 SetError(err error)
 // Future 获取关联的Future
 Future() Future[T]
}

// futureImpl 是Future和Promise的实现
type futureImpl[T any] struct {
 result      T
 err         error
 done        bool
 mu          sync.Mutex
 completeCh  chan struct{}
}

// NewPromise 创建一个新的Promise
func NewPromise[T any]() Promise[T] {
 return &futureImpl[T]{
  completeCh: make(chan struct{}),
 }
}

// Future 获取关联的Future
func (f *futureImpl[T]) Future() Future[T] {
 return f
}

// SetResult 设置成功结果
func (f *futureImpl[T]) SetResult(result T) {
 f.mu.Lock()
 defer f.mu.Unlock()
 
 if !f.done {
  f.result = result
  f.done = true
  close(f.completeCh)
 }
}

// SetError 设置错误结果
func (f *futureImpl[T]) SetError(err error) {
 f.mu.Lock()
 defer f.mu.Unlock()
 
 if !f.done {
  f.err = err
  f.done = true
  close(f.completeCh)
 }
}

// Get 返回结果，如果未完成则阻塞
func (f *futureImpl[T]) Get() (T, error) {
 <-f.completeCh // 等待完成
 
 f.mu.Lock()
 defer f.mu.Unlock()
 return f.result, f.err
}

// GetWithContext 带有上下文的获取结果
func (f *futureImpl[T]) GetWithContext(ctx context.Context) (result T, err error) {
 select {
 case <-f.completeCh:
  f.mu.Lock()
  defer f.mu.Unlock()
  return f.result, f.err
 case <-ctx.Done():
  var zero T
  return zero, ctx.Err()
 }
}

// IsDone 检查计算是否完成
func (f *futureImpl[T]) IsDone() bool {
 f.mu.Lock()
 defer f.mu.Unlock()
 return f.done
}

// RunAsync 异步执行任务并返回Future
func RunAsync[T any](fn func() (T, error)) Future[T] {
 promise := NewPromise[T]()
 
 go func() {
  result, err := fn()
  if err != nil {
   promise.SetError(err)
  } else {
   promise.SetResult(result)
  }
 }()
 
 return promise.Future()
}
```

## 同步模式

### Barrier模式

Barrier模式允许多个goroutine在某个点同步，等待所有goroutine到达后再继续执行。

```go
package barrier

import (
 "context"
 "sync"
)

// Barrier 允许goroutine在某个点同步
type Barrier interface {
 // Wait 阻塞直到所有参与者到达
 Wait() error
 // WaitWithContext 带有上下文的等待
 WaitWithContext(ctx context.Context) error
}

// barrierImpl 实现了Barrier接口
type barrierImpl struct {
 parties     int
 count       int
 generation  int
 mu          sync.Mutex
 cond        *sync.Cond
}

// NewBarrier 创建一个新的barrier
func NewBarrier(parties int) Barrier {
 b := &barrierImpl{
  parties: parties,
 }
 b.cond = sync.NewCond(&b.mu)
 return b
}

// Wait 阻塞直到所有参与者到达
func (b *barrierImpl) Wait() error {
 b.mu.Lock()
 defer b.mu.Unlock()
 
 generation := b.generation
 
 b.count++
 if b.count == b.parties {
  // 最后一个到达的goroutine将重置计数器并增加代
  b.count = 0
  b.generation++
  b.cond.Broadcast()
  return nil
 }
 
 // 等待直到所有goroutine到达
 for generation == b.generation {
  b.cond.Wait()
 }
 
 return nil
}

// WaitWithContext 带有上下文的等待
func (b *barrierImpl) WaitWithContext(ctx context.Context) error {
 // 创建一个结束信号
 done := make(chan struct{})
 
 // 在goroutine中等待
 var err error
 go func() {
  err = b.Wait()
  close(done)
 }()
 
 // 等待结束或上下文取消
 select {
 case <-done:
  return err
 case <-ctx.Done():
  return ctx.Err()
 }
}

// GenericBarrier 泛型版本，支持在同步点交换数据
type GenericBarrier[T any] interface {
 // Exchange 在同步点交换数据
 Exchange(data T) ([]T, error)
 // ExchangeWithContext 带有上下文的数据交换
 ExchangeWithContext(ctx context.Context, data T) ([]T, error)
}

// genericBarrierImpl 实现了GenericBarrier接口
type genericBarrierImpl[T any] struct {
 parties     int
 count       int
 generation  int
 data        []T
 mu          sync.Mutex
 cond        *sync.Cond
}

// NewGenericBarrier 创建一个新的泛型barrier
func NewGenericBarrier[T any](parties int) GenericBarrier[T] {
 b := &genericBarrierImpl[T]{
  parties: parties,
  data:    make([]T, 0, parties),
 }
 b.cond = sync.NewCond(&b.mu)
 return b
}

// Exchange 在同步点交换数据
func (b *genericBarrierImpl[T]) Exchange(data T) ([]T, error) {
 b.mu.Lock()
 defer b.mu.Unlock()
 
 generation := b.generation
 
 // 添加数据
 b.data = append(b.data, data)
 b.count++
 
 if b.count == b.parties {
  // 最后一个到达的goroutine将重置
  result := make([]T, len(b.data))
  copy(result, b.data)
  
  b.count = 0
  b.data = make([]T, 0, b.parties)
  b.generation++
  b.cond.Broadcast()
  return result, nil
 }
 
 // 等待所有goroutine到达
 for generation == b.generation {
  b.cond.Wait()
 }
 
 // 返回收集的数据
 result := make([]T, b.parties)
 copy(result, b.data)
 return result, nil
}

// ExchangeWithContext 带有上下文的数据交换
func (b *genericBarrierImpl[T]) ExchangeWithContext(ctx context.Context, data T) ([]T, error) {
 // 创建一个结束信号
 done := make(chan struct{})
 
 // 在goroutine中等待
 var result []T
 var err error
 go func() {
  result, err = b.Exchange(data)
  close(done)
 }()
 
 // 等待结束或上下文取消
 select {
 case <-done:
  return result, err
 case <-ctx.Done():
  return nil, ctx.Err()
 }
}
```

### Mutex模式

Mutex模式实现互斥访问，确保一次只有一个goroutine可以访问共享资源。

```go
package mutex

import (
 "context"
 "sync"
 "time"
)

// Mutex 扩展了标准库的互斥锁功能
type Mutex interface {
 // Lock 获取锁
 Lock()
 // Unlock 释放锁
 Unlock()
 // TryLock 尝试获取锁，返回是否成功
 TryLock() bool
 // LockWithTimeout 尝试在超时前获取锁
 LockWithTimeout(timeout time.Duration) bool
 // LockWithContext 尝试在上下文取消前获取锁
 LockWithContext(ctx context.Context) bool
}

// mutexImpl 实现Mutex接口
type mutexImpl struct {
 mu       sync.Mutex
 acquired chan struct{}
}

// NewMutex 创建一个新的互斥锁
func NewMutex() Mutex {
 return &mutexImpl{
  acquired: make(chan struct{}, 1),
 }
}

// Lock 获取锁
func (m *mutexImpl) Lock() {
 m.mu.Lock()
 m.acquired <- struct{}{}
}

// Unlock 释放锁
func (m *mutexImpl) Unlock() {
 <-m.acquired
 m.mu.Unlock()
}

// TryLock 尝试获取锁，返回是否成功
func (m *mutexImpl) TryLock() bool {
 if m.mu.TryLock() {
  m.acquired <- struct{}{}
  return true
 }
 return false
}

// LockWithTimeout 尝试在超时前获取锁
func (m *mutexImpl) LockWithTimeout(timeout time.Duration) bool {
 ctx, cancel := context.WithTimeout(context.Background(), timeout)
 defer cancel()
 return m.LockWithContext(ctx)
}

// LockWithContext 尝试在上下文取消前获取锁
func (m *mutexImpl) LockWithContext(ctx context.Context) bool {
 // 创建锁获取信号
 done := make(chan bool, 1)
 
 go func() {
  m.mu.Lock()
  done <- true
 }()
 
 select {
 case <-done:
  // 成功获取锁
  m.acquired <- struct{}{}
  return true
 case <-ctx.Done():
  // 上下文取消
  return false
 }
}

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

// WithLock 在持有锁的情况下执行函数
func (g *GenericMutex[T]) WithLock(fn func(resource T)) {
 g.mu.Lock()
 defer g.mu.Unlock()
 fn(g.resource)
}

// WithLockResult 在持有锁的情况下执行函数并返回结果
func (g *GenericMutex[T]) WithLockResult[R any](fn func(resource T) R) R {
 g.mu.Lock()
 defer g.mu.Unlock()
 return fn(g.resource)
}

// UpdateResource 更新受保护的资源
func (g *GenericMutex[T]) UpdateResource(fn func(resource T) T) {
 g.mu.Lock()
 defer g.mu.Unlock()
 g.resource = fn(g.resource)
}
```

### Read-Write Lock模式

Read-Write Lock模式允许多个读取者或一个写入者访问共享资源。

```go
package rwlock

import (
 "context"
 "sync"
 "time"
)

// RWLock 读写锁接口
type RWLock interface {
 // RLock 获取读锁
 RLock()
 // RUnlock 释放读锁
 RUnlock()
 // Lock 获取写锁
 Lock()
 // Unlock 释放写锁
 Unlock()
 // TryRLock 尝试获取读锁
 TryRLock() bool
 // TryLock 尝试获取写锁
 TryLock() bool
 // RLockWithTimeout 带超时的读锁获取
 RLockWithTimeout(timeout time.Duration) bool
 // LockWithTimeout 带超时的写锁获取
 LockWithTimeout(timeout time.Duration) bool
 // RLockWithContext 带上下文的读锁获取
 RLockWithContext(ctx context.Context) bool
 // LockWithContext 带上下文的写锁获取
 LockWithContext(ctx context.Context) bool
}

// rwLockImpl 读写锁实现
type rwLockImpl struct {
 mu        sync.RWMutex
 writeLock chan struct{}
 readLock  chan struct{}
}

// NewRWLock 创建新的读写锁
func NewRWLock() RWLock {
 return &rwLockImpl{
  writeLock: make(chan struct{}, 1),
  readLock:  make(chan struct{}, 100), // 支持多读者
 }
}

// RLock 获取读锁
func (rw *rwLockImpl) RLock() {
 rw.mu.RLock()
 rw.readLock <- struct{}{}
}

// RUnlock 释放读锁
func (rw *rwLockImpl) RUnlock() {
 <-rw.readLock
 rw.mu.RUnlock()
}

// Lock 获取写锁
func (rw *rwLockImpl) Lock() {
 rw.mu.Lock()
 rw.writeLock <- struct{}{}
}

// Unlock 释放写锁
func (rw *rwLockImpl) Unlock() {
 <-rw.writeLock
 rw.mu.Unlock()
}

// TryRLock 尝试获取读锁
func (rw *rwLockImpl) TryRLock() bool {
 if rw.mu.TryRLock() {
  rw.readLock <- struct{}{}
  return true
 }
 return false
}

// TryLock 尝试获取写锁
func (rw *rwLockImpl) TryLock() bool {
 if rw.mu.TryLock() {
  rw.writeLock <- struct{}{}
  return true
 }
 return false
}

// RLockWithTimeout 带超时的读锁获取
func (rw *rwLockImpl) RLockWithTimeout(timeout time.Duration) bool {
 ctx, cancel := context.WithTimeout(context.Background(), timeout)
 defer cancel()
 return rw.RLockWithContext(ctx)
}

// LockWithTimeout 带超时的写锁获取
func (rw *rwLockImpl) LockWithTimeout(timeout time.Duration) bool {
 ctx, cancel := context.WithTimeout(context.Background(), timeout)
 defer cancel()
 return rw.LockWithContext(ctx)
}

// RLockWithContext 带上下文的读锁获取
func (rw *rwLockImpl) RLockWithContext(ctx context.Context) bool {
 done := make(chan bool, 1)
 
 go func() {
  rw.mu.RLock()
  done <- true
 }()
 
 select {
 case <-done:
  rw.readLock <- struct{}{}
  return true
 case <-ctx.Done():
  return false
 }
}

// LockWithContext 带上下文的写锁获取
func (rw *rwLockImpl) LockWithContext(ctx context.Context) bool {
 done := make(chan bool, 1)
 
 go func() {
  rw.mu.Lock()
  done <- true
 }()
 
 select {
 case <-done:
  rw.writeLock <- struct{}{}
  return true
 case <-ctx.Done():
  return false
 }
}

// GenericRWLock 泛型读写锁
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

// WithRLock 带读锁执行函数
func (g *GenericRWLock[T]) WithRLock(fn func(resource T)) {
 g.mu.RLock()
 defer g.mu.RUnlock()
 fn(g.resource)
}

// WithLock 带写锁执行函数
func (g *GenericRWLock[T]) WithLock(fn func(resource T)) {
 g.mu.Lock()
 defer g.mu.Unlock()
 fn(g.resource)
}

// WithRLockResult 带读锁执行函数并返回结果
func (g *GenericRWLock[T]) WithRLockResult[R any](fn func(resource T) R) R {
 g.mu.RLock()
 defer g.mu.RUnlock()
 return fn(g.resource)
}

// WithLockResult 带写锁执行函数并返回结果
func (g *GenericRWLock[T]) WithLockResult[R any](fn func(resource T) R) R {
 g.mu.Lock()
 defer g.mu.Unlock()
 return fn(g.resource)
}

// UpdateResource 更新资源
func (g *GenericRWLock[T]) UpdateResource(fn func(resource T) T) {
 g.mu.Lock()
 defer g.mu.Unlock()
 g.resource = fn(g.resource)
}
```

### Semaphore模式

Semaphore模式控制访问有限资源的并发程度。

```go
package semaphore

import (
 "context"
 "sync"
 "time"
)

// Semaphore 控制对有限资源的访问
type Semaphore interface {
 // Acquire 获取许可
 Acquire(n int) error
 // Release 释放许可
 Release(n int)
 // TryAcquire 尝试获取许可
 TryAcquire(n int) bool
 // AcquireWithTimeout 带超时的获取许可
 AcquireWithTimeout(n int, timeout time.Duration) error
 // AcquireWithContext 带上下文的获取许可
 AcquireWithContext(ctx context.Context, n int) error
 // AvailablePermits 返回当前可用的许可数
 AvailablePermits() int
}

// semaphoreImpl 信号量实现
type semaphoreImpl struct {
 permits int
 used    int
 mu      sync.Mutex
 cond    *sync.Cond
}

// NewSemaphore 创建一个新的信号量
func NewSemaphore(permits int) Semaphore {
 s := &semaphoreImpl{
  permits: permits,
 }
 s.cond = sync.NewCond(&s.mu)
 return s
}

// Acquire 获取许可
func (s *semaphoreImpl) Acquire(n int) error {
 if n <= 0 || n > s.permits {
  return ErrInvalidPermits
 }
 
 s.mu.Lock()
 defer s.mu.Unlock()
 
 // 等待直到有足够的许可
 for s.used+n > s.permits {
  s.cond.Wait()
 }
 
 s.used += n
 return nil
}

// Release 释放许可
func (s *semaphoreImpl) Release(n int) {
 if n <= 0 {
  return
 }
 
 s.mu.Lock()
 defer s.mu.Unlock()
 
 // 不允许释放超过已使用的许可
 if s.used < n {
  n = s.used
 }
 
 s.used -= n
 s.cond.Broadcast() // 通知等待的goroutine
}

// TryAcquire 尝试获取许可
func (s *semaphoreImpl) TryAcquire(n int) bool {
 if n <= 0 || n > s.permits {
  return false
 }
 
 s.mu.Lock()
 defer s.mu.Unlock()
 
 if s.used+n <= s.permits {
  s.used += n
  return true
 }
 
 return false
}

// AcquireWithTimeout 带超时的获取许可
func (s *semaphoreImpl) AcquireWithTimeout(n int, timeout time.Duration) error {
 ctx, cancel := context.WithTimeout(context.Background(), timeout)
 defer cancel()
 return s.AcquireWithContext(ctx, n)
}

// AcquireWithContext 带上下文的获取许可
func (s *semaphoreImpl) AcquireWithContext(ctx context.Context, n int) error {
 if n <= 0 || n > s.permits {
  return ErrInvalidPermits
 }
 
 // 快速路径尝试获取
 if s.TryAcquire(n) {
  return nil
 }
 
 done := make(chan struct{})
 var err error
 
 go func() {
  s.mu.Lock()
  defer s.mu.Unlock()
  
  for s.used+n > s.permits {
   released := make(chan struct{})
   
   go func() {
    s.cond.Wait()
    close(released)
   }()
   
   s.mu.Unlock()
   
   select {
   case <-released:
    // 有许可被释放，继续尝试
    s.mu.Lock()
   case <-ctx.Done():
    // 上下文取消
    s.mu.Lock()
    err = ctx.Err()
    close(done)
    return
   }
  }
  
  // 成功获取许可
  s.used += n
  close(done)
 }()
 
 <-done
 return err
}

// AvailablePermits 返回当前可用的许可数
func (s *semaphoreImpl) AvailablePermits() int {
 s.mu.Lock()
 defer s.mu.Unlock()
 return s.permits - s.used
}

// ErrInvalidPermits 无效的许可数量错误
var ErrInvalidPermits = NewSemaphoreError("invalid number of permits")

// SemaphoreError 信号量错误类型
type SemaphoreError string

func (e SemaphoreError) Error() string {
 return string(e)
}

// NewSemaphoreError 创建信号量错误
func NewSemaphoreError(message string) SemaphoreError {
 return SemaphoreError(message)
}

// GenericSemaphore 泛型信号量，提供资源池功能
type GenericSemaphore[T any] struct {
 sem      Semaphore
 resources []T
 mu        sync.Mutex
}

// NewGenericSemaphore 创建泛型信号量
func NewGenericSemaphore[T any](resources []T) *GenericSemaphore[T] {
 return &GenericSemaphore[T]{
  sem:      NewSemaphore(len(resources)),
  resources: resources,
 }
}

// Acquire 获取资源
func (g *GenericSemaphore[T]) Acquire() (T, error) {
 err := g.sem.Acquire(1)
 if err != nil {
  var zero T
  return zero, err
 }
 
 g.mu.Lock()
 defer g.mu.Unlock()
 
 resource := g.resources[0]
 g.resources = g.resources[1:]
 return resource, nil
}

// Release 释放资源
func (g *GenericSemaphore[T]) Release(resource T) {
 g.mu.Lock()
 g.resources = append(g.resources, resource)
 g.mu.Unlock()
 
 g.sem.Release(1)
}
```

## 并发控制模式

### Context模式

Context模式提供取消信号、超时和值传递机制，用于控制goroutine的生命周期。

```go
package contextpattern

import (
 "context"
 "sync"
 "time"
)

// Task 表示可以被取消的任务
type Task[T any] interface {
 // Execute 执行任务并返回结果
 Execute(ctx context.Context) (T, error)
}

// TaskFunc 允许使用函数作为任务
type TaskFunc[T any] func(ctx context.Context) (T, error)

func (tf TaskFunc[T]) Execute(ctx context.Context) (T, error) {
 return tf(ctx)
}

// ExecuteWithTimeout 在指定超时内执行任务
func ExecuteWithTimeout[T any](task Task[T], timeout time.Duration) (T, error) {
 ctx, cancel := context.WithTimeout(context.Background(), timeout)
 defer cancel()
 return task.Execute(ctx)
}

// ExecuteWithDeadline 在指定截止时间前执行任务
func ExecuteWithDeadline[T any](task Task[T], deadline time.Time) (T, error) {
 ctx, cancel := context.WithDeadline(context.Background(), deadline)
 defer cancel()
 return task.Execute(ctx)
}

// ParallelExecute 并行执行多个任务，任一任务出错则取消所有任务
func ParallelExecute[T any](tasks []Task[T]) ([]T, error) {
 ctx, cancel := context.WithCancel(context.Background())
 defer cancel()
 
 results := make([]T, len(tasks))
 errors := make(chan error, len(tasks))
 var wg sync.WaitGroup
 
 for i, task := range tasks {
  wg.Add(1)
  go func(i int, t Task[T]) {
   defer wg.Done()
   
   result, err := t.Execute(ctx)
   if err != nil {
    errors <- err
    cancel() // 取消所有其他任务
    return
   }
   
   results[i] = result
  }(i, task)
 }
 
 // 等待所有任务完成或被取消
 wg.Wait()
 
 // 检查是否有错误
 select {
 case err := <-errors:
  return nil, err
 default:
  return results, nil
 }
}

// WithValue 提供一个通用的方式在上下文中存储和检索值
type WithValue[T any] struct {
 key interface{}
}

// NewWithValue 创建一个新的WithValue工具
func NewWithValue[T any](key interface{}) *WithValue[T] {
 return &WithValue[T]{key: key}
}

// Set 在上下文中设置值
func (wv *WithValue[T]) Set(ctx context.Context, val T) context.Context {
 return context.WithValue(ctx, wv.key, val)
}

// Get 从上下文中获取值
func (wv *WithValue[T]) Get(ctx context.Context) (T, bool) {
 val, ok := ctx.Value(wv.key).(T)
 return val, ok
}

// MustGet 从上下文中获取值，如果不存在则触发panic
func (wv *WithValue[T]) MustGet(ctx context.Context) T {
 val, ok := wv.Get(ctx)
 if !ok {
  panic("value not found in context")
 }
 return val
}
```

### Rate Limiting模式

Rate Limiting模式控制操作的速率，防止系统过载。

```go
package ratelimiter

import (
 "context"
 "sync"
 "time"
)

// RateLimiter 限制操作的速率
type RateLimiter interface {
 // Allow 检查是否允许执行操作
 Allow() bool
 // Wait 等待直到操作被允许执行
 Wait(ctx context.Context) error
 // SetRate 设置新的速率
 SetRate(rate float64)
}

// TokenBucketLimiter 使用令牌桶算法实现速率限制
type TokenBucketLimiter struct {
 rate       float64     // 每秒产生的令牌数
 capacity   float64     // 桶容量
 tokens     float64     // 当前令牌数
 lastUpdate time.Time   // 上次更新时间
 mu         sync.Mutex  // 互斥锁
}

// NewTokenBucketLimiter 创建一个新的令牌桶限制器
func NewTokenBucketLimiter(rate, capacity float64) *TokenBucketLimiter {
 return &TokenBucketLimiter{
  rate:       rate,
  capacity:   capacity,
  tokens:     capacity,
  lastUpdate: time.Now(),
 }
}

// Allow 检查是否允许执行操作
func (tb *TokenBucketLimiter) Allow() bool {
 tb.mu.Lock()
 defer tb.mu.Unlock()
 
 now := time.Now()
 tb.update(now)
 
 if tb.tokens >= 1 {
  tb.tokens--
  return true
 }
 
 return false
}

// Wait 等待直到操作被允许执行
func (tb *TokenBucketLimiter) Wait(ctx context.Context) error {
 for {
  waitTime, allow := tb.reserveN(1)
  if allow {
   return nil
  }
  
  select {
  case <-time.After(waitTime):
   // 继续尝试
  case <-ctx.Done():
   return ctx.Err()
  }
 }
}

// SetRate 设置新的速率
func (tb *TokenBucketLimiter) SetRate(rate float64) {
 tb.mu.Lock()
 defer tb.mu.Unlock()
 
 tb.update(time.Now())
 tb.rate = rate
}

// update 更新令牌数量
func (tb *TokenBucketLimiter) update(now time.Time) {
 elapsed := now.Sub(tb.lastUpdate).Seconds()
 newTokens := elapsed * tb.rate
 
 tb.tokens = tb.tokens + newTokens
 if tb.tokens > tb.capacity {
  tb.tokens = tb.capacity
 }
 
 tb.lastUpdate = now
}

// reserveN 尝试预留n个令牌，返回需要等待的时间和是否成功
func (tb *TokenBucketLimiter) reserveN(n float64) (time.Duration, bool) {
 tb.mu.Lock()
 defer tb.mu.Unlock()
 
 now := time.Now()
 tb.update(now)
 
 if tb.tokens >= n {
  tb.tokens -= n
  return 0, true
 }
 
 // 计算需要等待的时间
 tokensNeeded := n - tb.tokens
 waitTime := time.Duration(tokensNeeded / tb.rate * float64(time.Second))
 
 return waitTime, false
}

// GenericRateLimiter 泛型速率限制器
type GenericRateLimiter[T any] struct {
 limiter RateLimiter
}

// NewGenericRateLimiter 创建泛型速率限制器
func NewGenericRateLimiter[T any](limiter RateLimiter) *GenericRateLimiter[T] {
 return &GenericRateLimiter[T]{limiter: limiter}
}

// Execute 在速率限制下执行函数
func (g *GenericRateLimiter[T]) Execute(ctx context.Context, fn func() T) (T, error) {
 err := g.limiter.Wait(ctx)
 if err != nil {
  var zero T
  return zero, err
 }
 
 return fn(), nil
}

// ExecuteBatch 在速率限制下执行一批操作
func (g *GenericRateLimiter[T]) ExecuteBatch(ctx context.Context, fns []func() T) ([]T, error) {
 results := make([]T, len(fns))
 
 for i, fn := range fns {
  result, err := g.Execute(ctx, fn)
  if err != nil {
   return nil, err
  }
  results[i] = result
 }
 
 return results, nil
}
```

### Circuit Breaker模式

Circuit Breaker模式防止系统调用已知失败的服务，从而使服务有时间恢复。

```go
package circuitbreaker

import (
 "errors"
 "sync"
 "time"
)

// CircuitState 表示断路器的状态
type CircuitState int

const (
 // StateClose 闭合状态，允许请求通过
 StateClose CircuitState = iota
 // StateOpen 打开状态，阻断所有请求
 StateOpen
 // StateHalfOpen 半开状态，允许有限请求用于测试
 StateHalfOpen
)

// CircuitBreaker 断路器接口
type CircuitBreaker interface {
 // Execute 执行操作，根据断路器状态可能会阻断
 Execute(operation func() (interface{}, error)) (interface{}, error)
 // GetState 获取当前状态
 GetState() CircuitState
 // Reset 重置断路器到闭合状态
 Reset()
}

// Options 断路器配置选项
type Options struct {
 // Threshold 错误阈值，超过此值断路器打开
 Threshold uint
 // Timeout 超时时间，断路器打开后经过此时间进入半开状态
 Timeout time.Duration
 // HalfOpenMaxRequests 半开状态允许的最大请求数
 HalfOpenMaxRequests uint
}

// DefaultOptions 默认配置
var DefaultOptions = Options{
 Threshold:          5,
 Timeout:            5 * time.Second,
 HalfOpenMaxRequests: 1,
}

// circuitBreakerImpl 断路器实现
type circuitBreakerImpl struct {
 options         Options
 state           CircuitState
 failures        uint
 lastError       error
 lastStateChange time.Time
 halfOpenCount   uint
 mu              sync.RWMutex
}

// NewCircuitBreaker 创建新的断路器
func NewCircuitBreaker(options Options) CircuitBreaker {
 return &circuitBreakerImpl{
  options:         options,
  state:           StateClose,
  lastStateChange: time.Now(),
 }
}

// Execute 执行操作，根据断路器状态可能会阻断
func (cb *circuitBreakerImpl) Execute(operation func() (interface{}, error)) (interface{}, error) {
 if !cb.allowRequest() {
  return nil, ErrCircuitOpen
 }
 
 // 执行操作
 result, err := operation()
 
 cb.handleResult(err)
 
 return result, err
}

// GetState 获取当前状态
func (cb *circuitBreakerImpl) GetState() CircuitState {
 cb.mu.RLock()
 defer cb.mu.RUnlock()
 return cb.state
}

// Reset 重置断路器到闭合状态
func (cb *circuitBreakerImpl) Reset() {
 cb.mu.Lock()
 defer cb.mu.Unlock()
 
 cb.state = StateClose
 cb.failures = 0
 cb.lastError = nil
 cb.lastStateChange = time.Now()
 cb.halfOpenCount = 0
}

// allowRequest 检查是否允许请求通过
func (cb *circuitBreakerImpl) allowRequest() bool {
 cb.mu.Lock()
 defer cb.mu.Unlock()
 
 // 检查状态是否需要从Open过渡到HalfOpen
 now := time.Now()
 if cb.state == StateOpen && now.Sub(cb.lastStateChange) > cb.options.Timeout {
  cb.stateTransition(StateHalfOpen)
 }
 
 switch cb.state {
 case StateClose:
  return true
 case StateOpen:
  return false
 case StateHalfOpen:
  if cb.halfOpenCount < cb.options.HalfOpenMaxRequests {
   cb.halfOpenCount++
   return true
  }
  return false
 default:
  return true
 }
}

// handleResult 处理操作结果
func (cb *circuitBreakerImpl) handleResult(err error) {
 cb.mu.Lock()
 defer cb.mu.Unlock()
 
 if err != nil {
  // 处理失败
  switch cb.state {
  case StateClose:
   cb.failures++
   cb.lastError = err
   if cb.failures >= cb.options.Threshold {
    cb.stateTransition(StateOpen)
   }
  case StateHalfOpen:
   cb.stateTransition(StateOpen)
  }
 } else {
  // 处理成功
  if cb.state == StateHalfOpen {
   cb.stateTransition(StateClose)
  } else if cb.state == StateClose {
   cb.failures = 0
   cb.lastError = nil
  }
 }
}

// stateTransition 执行状态转换
func (cb *circuitBreakerImpl) stateTransition(newState CircuitState) {
 cb.state = newState
 cb.lastStateChange = time.Now()
 
 if newState == StateOpen {
  cb.failures = cb.options.Threshold
 } else if newState == StateClose {
  cb.failures = 0
  cb.lastError = nil
 } else if newState == StateHalfOpen {
  cb.halfOpenCount = 0
 }
}

// ErrCircuitOpen 断路器打开错误
var ErrCircuitOpen = errors.New("circuit breaker is open")

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

// Execute 执行操作
func (gcb *GenericCircuitBreaker[T]) Execute(operation func() (T, error)) (T, error) {
 result, err := gcb.breaker.Execute(func() (interface{}, error) {
  return operation()
 })
 
 if err != nil {
  var zero T
  return zero, err
 }
 
 return result.(T), nil
}
```

### Bulkhead模式

Bulkhead模式将系统隔离成不同的部分，防止一个部分的失败影响整个系统。

```go
package bulkhead

import (
 "context"
 "errors"
 "sync"
 "sync/atomic"
)

// Bulkhead 将系统隔离成不同部分，限制每个部分的并发执行数
type Bulkhead interface {
 // Execute 执行操作，如果超过并发限制则拒绝
 Execute(ctx context.Context, operation func() (interface{}, error)) (interface{}, error)
 // TryExecute 尝试执行操作，如果超过并发限制则返回错误
 TryExecute(operation func() (interface{}, error)) (interface{}, error)
 // GetAvailableConcurrency 获取可用的并发槽数量
 GetAvailableConcurrency() int64
 // GetMaxConcurrency 获取最大并发数
 GetMaxConcurrency() int64
}

// bulkheadImpl Bulkhead实现
type bulkheadImpl struct {
 maxConcurrency int64         // 最大并发数
 queueSize      int64         // 等待队列大小
 active         int64         // 当前活跃任务数
 waitQueue      chan struct{} // 等待队列
 mu             sync.Mutex    // 互斥锁
}

// NewBulkhead 创建新的Bulkhead
func NewBulkhead(maxConcurrency, queueSize int64) Bulkhead {
 return &bulkheadImpl{
  maxConcurrency: maxConcurrency,
  queueSize:      queueSize,
  waitQueue:      make(chan struct{}, queueSize),
 }
}

// TryExecute 尝试执行操作，如果超过并发限制则返回错误
func (b *bulkheadImpl) TryExecute(operation func() (interface{}, error)) (interface{}, error) {
 // 尝试获取许可
 if !b.tryAcquire() {
  return nil, ErrBulkheadFull
 }
 
 // 确保释放许可
 defer b.release()
 
 // 执行操作
 return operation()
}

// Execute 执行操作，如果超过并发限制则等待或拒绝
func (b *bulkheadImpl) Execute(ctx context.Context, operation func() (interface{}, error)) (interface{}, error) {
 // 首先尝试立即执行
 if b.tryAcquire() {
  defer b.release()
  return operation()
 }
 
 // 等待或拒绝
 select {
 case b.waitQueue <- struct{}{}:
  // 成功进入等待队列
  defer func() { <-b.waitQueue }()
  
  // 等待可用槽
  for {
   if b.tryAcquire() {
    defer b.release()
    return operation()
   }
   
   select {
   case <-ctx.Done():
    return nil, ctx.Err()
   default:
    // 继续尝试
   }
  }
 default:
  // 等待队列已满
  return nil, ErrBulkheadQueueFull
 }
}

// GetAvailableConcurrency 获取可用的并发槽数量
func (b *bulkheadImpl) GetAvailableConcurrency() int64 {
 active := atomic.LoadInt64(&b.active)
 available := b.maxConcurrency - active
 if available < 0 {
  return 0
 }
 return available
}

// GetMaxConcurrency 获取最大并发数
func (b *bulkheadImpl) GetMaxConcurrency() int64 {
 return b.maxConcurrency
}

// tryAcquire 尝试获取许可
func (b *bulkheadImpl) tryAcquire() bool {
 // 使用CAS操作尝试增加活跃计数
 for {
  current := atomic.LoadInt64(&b.active)
  if current >= b.maxConcurrency {
   return false
  }
  
  if atomic.CompareAndSwapInt64(&b.active, current, current+1) {
   return true
  }
 }
}

// release 释放许可
func (b *bulkheadImpl) release() {
 atomic.AddInt64(&b.active, -1)
}

// ErrBulkheadFull Bulkhead已满错误
var ErrBulkheadFull = errors.New("bulkhead capacity full")

// ErrBulkheadQueueFull Bulkhead等待队列已满错误
var ErrBulkheadQueueFull = errors.New("bulkhead queue full")

// GenericBulkhead 泛型Bulkhead
type GenericBulkhead[T any] struct {
 bulkhead Bulkhead
}

// NewGenericBulkhead 创建泛型Bulkhead
func NewGenericBulkhead[T any](maxConcurrency, queueSize int64) *GenericBulkhead[T] {
 return &GenericBulkhead[T]{
  bulkhead: NewBulkhead(maxConcurrency, queueSize),
 }
}

// Execute 执行操作
func (gb *GenericBulkhead[T]) Execute(ctx context.Context, operation func() (T, error)) (T, error) {
 result, err := gb.bulkhead.Execute(ctx, func() (interface{}, error) {
  return operation()
 })
 
 if err != nil {
  var zero T
  return zero, err
 }
 
 return result.(T), nil
}

// TryExecute 尝试执行操作
func (gb *GenericBulkhead[T]) TryExecute(operation func() (T, error)) (T, error) {
 result, err := gb.bulkhead.TryExecute(func() (interface{}, error) {
  return operation()
 })
 
 if err != nil {
  var zero T
  return zero, err
 }
 
 return result.(T), nil
}
```

## 消息通信模式

### Publish-Subscribe模式

Publish-Subscribe模式允许发送者向多个接收者广播消息。

```go
package pubsub

import (
 "context"
 "sync"
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
}

// SubscriberFunc 允许使用函数作为订阅者
type SubscriberFunc[T any] func(event Event[T])

func (sf SubscriberFunc[T]) OnEvent(event Event[T]) {
 sf(event)
}

// Publisher 发布者接口
type Publisher[T any] interface {
 // Publish 发布事件到指定主题
 Publish(topic string, payload T)
 // Subscribe 订阅主题
 Subscribe(topic string, subscriber Subscriber[T]) string
 // Unsubscribe 取消订阅
 Unsubscribe(subID string)
}

// pubSubImpl 发布-订阅实现
type pubSubImpl[T any] struct {
 subscribers map[string]map[string]Subscriber[T] // 主题 -> 订阅ID -> 订阅者
 mu          sync.RWMutex
 idCounter   int
}

// NewPublisher 创建新的发布者
func NewPublisher[T any]() Publisher[T] {
 return &pubSubImpl[T]{
  subscribers: make(map[string]map[string]Subscriber[T]),
 }
}

// Publish 发布事件到指定主题
func (ps *pubSubImpl[T]) Publish(topic string, payload T) {
 ps.mu.RLock()
 defer ps.mu.RUnlock()
 
 event := Event[T]{
  Topic:   topic,
  Payload: payload,
 }
 
 // 发布到特定主题
 if subs, ok := ps.subscribers[topic]; ok {
  for _, sub := range subs {
   // 使用goroutine异步通知订阅者
   go sub.OnEvent(event)
  }
 }
 
 // 发布到通配符主题 "*"
 if subs, ok := ps.subscribers["*"]; ok {
  for _, sub := range subs {
   go sub.OnEvent(event)
  }
 }
}

// Subscribe 订阅主题
func (ps *pubSubImpl[T]) Subscribe(topic string, subscriber Subscriber[T]) string {
 ps.mu.Lock()
 defer ps.mu.Unlock()
 
 // 确保主题映射存在
 if _, ok := ps.subscribers[topic]; !ok {
  ps.subscribers[topic] = make(map[string]Subscriber[T])
 }
 
 // 生成唯一订阅ID
 ps.idCounter++
 subID := generateSubID(topic, ps.idCounter)
 
 // 添加订阅者
 ps.subscribers[topic][subID] = subscriber
 
 return subID
}

// Unsubscribe 取消订阅
func (ps *pubSubImpl[T]) Unsubscribe(subID string) {
 ps.mu.Lock()
 defer ps.mu.Unlock()
 
 topic, id := parseSubID(subID)
 
 // 移除订阅者
 if subs, ok := ps.subscribers[topic]; ok {
  delete(subs, id)
  
  // 如果主题没有订阅者了，清理主题映射
  if len(subs) == 0 {
   delete(ps.subscribers, topic)
  }
 }
}

// AsyncPublisher 异步发布者，支持批量发布
type AsyncPublisher[T any] struct {
 publisher Publisher[T]
 eventChan chan Event[T]
 stopChan  chan struct{}
 wg        sync.WaitGroup
}

// NewAsyncPublisher 创建新的异步发布者
func NewAsyncPublisher[T any](bufferSize int) *AsyncPublisher[T] {
 ap := &AsyncPublisher[T]{
  publisher: NewPublisher[T](),
  eventChan: make(chan Event[T], bufferSize),
  stopChan:  make(chan struct{}),
 }
 
 ap.start()
 return ap
}

// start 启动异步发布处理
func (ap *AsyncPublisher[T]) start() {
 ap.wg.Add(1)
 go func() {
  defer ap.wg.Done()
  for {
   select {
   case event := <-ap.eventChan:
    ap.publisher.Publish(event.Topic, event.Payload)
   case <-ap.stopChan:
    return
   }
  }
 }()
}

// Publish 异步发布事件
func (ap *AsyncPublisher[T]) Publish(topic string, payload T) {
 select {
 case ap.eventChan <- Event[T]{Topic: topic, Payload: payload}:
  // 成功放入通道
 default:
  // 通道已满，可以选择丢弃或阻塞
  // 这里选择阻塞
  ap.eventChan <- Event[T]{Topic: topic, Payload: payload}
 }
}

// Subscribe 代理订阅请求
func (ap *AsyncPublisher[T]) Subscribe(topic string, subscriber Subscriber[T]) string {
 return ap.publisher.Subscribe(topic, subscriber)
}

// Unsubscribe 代理取消订阅请求
func (ap *AsyncPublisher[T]) Unsubscribe(subID string) {
 ap.publisher.Unsubscribe(subID)
}

// Stop 停止异步发布处理
func (ap *AsyncPublisher[T]) Stop() {
 close(ap.stopChan)
 ap.wg.Wait()
}

// 生成订阅ID
func generateSubID(topic string, counter int) string {
 return topic + ":" + string(rune(counter))
}

// 解析订阅ID
func parseSubID(subID string) (string, string) {
 // 简化实现，实际中可能需要更复杂的逻辑
 for i := len(subID) - 1; i >= 0; i-- {
  if subID[i] == ':' {
   return subID[:i], subID[i+1:]
  }
 }
 return "", subID
}

// TopicListener 主题监听器，简化订阅管理
type TopicListener[T any] struct {
 publisher Publisher[T]
 subIDs    map[string]string // 主题 -> 订阅ID
 mu        sync.Mutex
}

// NewTopicListener 创建新的主题监听器
func NewTopicListener[T any](publisher Publisher[T]) *TopicListener[T] {
 return &TopicListener[T]{
  publisher: publisher,
  subIDs:    make(map[string]string),
 }
}

// Listen 监听主题
func (tl *TopicListener[T]) Listen(topic string, handler func(T)) {
 tl.mu.Lock()
 defer tl.mu.Unlock()
 
 // 如果已经监听此主题，先取消旧订阅
 if subID, ok := tl.subIDs[topic]; ok {
  tl.publisher.Unsubscribe(subID)
 }
 
 // 创建新订阅
 subID := tl.publisher.Subscribe(topic, SubscriberFunc[T](func(event Event[T]) {
  handler(event.Payload)
 }))
 
 tl.subIDs[topic] = subID
}

// Stop 停止监听所有主题
func (tl *TopicListener[T]) Stop() {
 tl.mu.Lock()
 defer tl.mu.Unlock()
 
 for _, subID := range tl.subIDs {
  tl.publisher.Unsubscribe(subID)
 }
 
 tl.subIDs = make(map[string]string)
}
```

### Actor模式

Actor模式使用独立的执行单元（actors）通过消息传递进行通信。

```go
package actor

import (
 "context"
 "errors"
 "sync"
)

// Message 表示actor可以处理的消息
type Message[T any] struct {
 Sender  *ActorRef[T]
 Content T
}

// Actor 表示一个actor的行为
type Actor[T any] interface {
 // Receive 处理接收到的消息
 Receive(context context.Context, msg Message[T]) error
 // PreStart 在actor启动前调用
 PreStart(context context.Context) error
 // PostStop 在actor停止后调用
 PostStop(context context.Context) error
}

// ActorRef actor的引用，用于发送消息
type ActorRef[T any] struct {
 id        string
 mailbox   chan Message[T]
 system    *ActorSystem[T]
}

// Tell 发送异步消息（发送后不等待响应）
func (ref *ActorRef[T]) Tell(msg T, sender *ActorRef[T]) error {
 select {
 case ref.mailbox <- Message[T]{Content: msg, Sender: sender}:
  return nil
 default:
  return ErrMailboxFull
 }
}

// ID 获取actor ID
func (ref *ActorRef[T]) ID() string {
 return ref.id
}

// Stop 停止actor
func (ref *ActorRef[T]) Stop() {
 ref.system.Stop(ref.id)
}

// ActorSystem 管理actor的生命周期
type ActorSystem[T any] struct {
 actors      map[string]*actorContext[T]
 mu          sync.RWMutex
 ctx         context.Context
 cancel      context.CancelFunc
 idGenerator idGenerator
}

// actorContext 封装actor的运行环境
type actorContext[T any] struct {
 actor      Actor[T]
 ref        *ActorRef[T]
 ctx        context.Context
 cancelFunc context.CancelFunc
 wg         sync.WaitGroup
}

// NewActorSystem 创建新的actor系统
func NewActorSystem[T any]() *ActorSystem[T] {
 ctx, cancel := context.WithCancel(context.Background())
 return &ActorSystem[T]{
  actors:  make(map[string]*actorContext[T]),
  ctx:     ctx,
  cancel:  cancel,
 }
}

// Spawn 创建一个新的actor
func (s *ActorSystem[T]) Spawn(actor Actor[T], mailboxSize int) (*ActorRef[T], error) {
 s.mu.Lock()
 defer s.mu.Unlock()
 
 // 生成唯一ID
 id := s.idGenerator.Next()
 
 // 创建actor引用
 ref := &ActorRef[T]{
  id:      id,
  mailbox: make(chan Message[T], mailboxSize),
  system:  s,
 }
 
 // 创建actor上下文
 actorCtx, cancel := context.WithCancel(s.ctx)
 ctx := &actorContext[T]{
  actor:      actor,
  ref:        ref,
  ctx:        actorCtx,
  cancelFunc: cancel,
 }
 
 // 存储到系统
 s.actors[id] = ctx
 
 // 启动actor
 ctx.wg.Add(1)
 err := actor.PreStart(actorCtx)
 if err != nil {
  cancel()
  delete(s.actors, id)
  return nil, err
 }
 
 go s.runActor(ctx)
 
 return ref, nil
}

// runActor 运行actor处理循环
func (s *ActorSystem[T]) runActor(ctx *actorContext[T]) {
 defer ctx.wg.Done()
 defer func() {
  _ = ctx.actor.PostStop(ctx.ctx)
 }()
 
 for {
  select {
  case msg := <-ctx.ref.mailbox:
   err := ctx.actor.Receive(ctx.ctx, msg)
   if err != nil {
    // 处理错误，可以根据需要重启actor
    // 这里简化处理，只记录错误
    continue
   }
  case <-ctx.ctx.Done():
   // Actor被停止
   return
  }
 }
}

// Stop 停止指定的actor
func (s *ActorSystem[T]) Stop(id string) {
 s.mu.Lock()
 defer s.mu.Unlock()
 
 if ctx, ok := s.actors[id]; ok {
  ctx.cancelFunc()
  ctx.wg.Wait()
  delete(s.actors, id)
 }
}

// StopAll 停止所有actor
func (s *ActorSystem[T]) StopAll() {
 s.mu.Lock()
 defer s.mu.Unlock()
 
 // 取消根上下文，触发所有actor停止
 s.cancel()
 
 // 等待所有actor完成
 for _, ctx := range s.actors {
  ctx.wg.Wait()
 }
 
 // 清空actor映射
 s.actors = make(map[string]*actorContext[T])
}

// idGenerator 简单的ID生成器
type idGenerator struct {
 counter int
 mu      sync.Mutex
}

// Next 获取下一个唯一ID
func (g *idGenerator) Next() string {
 g.mu.Lock()
 defer g.mu.Unlock()
 g.counter++
 return string(rune(g.counter))
}

// 错误定义
var ErrMailboxFull = errors.New("actor mailbox is full")
```

### CSP模式

CSP（Communicating Sequential Processes）模式通过通道在进程间通信，这是Go语言的核心并发模型。

```go
package csp

import (
 "context"
 "sync"
)

// Process 代表一个独立的顺序进程
type Process[In, Out any] interface {
 // Run 启动进程，消费输入并产生输出
 Run(ctx context.Context, in <-chan In, out chan<- Out)
}

// ProcessFunc 允许使用函数作为进程
type ProcessFunc[In, Out any] func(ctx context.Context, in <-chan In, out chan<- Out)

func (pf ProcessFunc[In, Out]) Run(ctx context.Context, in <-chan In, out chan<- Out) {
 pf(ctx, in, out)
}

// Pipe 连接两个进程，将第一个进程的输出作为第二个进程的输入
func Pipe[T1, T2, T3 any](ctx context.Context, 
 first Process[T1, T2], 
 second Process[T2, T3], 
 in <-chan T1, 
 out chan<- T3, 
 bufferSize int) {
 
 // 创建中间通道
 middle := make(chan T2, bufferSize)
 
 var wg sync.WaitGroup
 wg.Add(2)
 
 // 启动第一个进程
 go func() {
  defer wg.Done()
  defer close(middle) // 第一个进程结束后关闭中间通道
  first.Run(ctx, in, middle)
 }()
 
 // 启动第二个进程
 go func() {
  defer wg.Done()
  second.Run(ctx, middle, out)
 }()
 
 // 等待两个进程完成
 wg.Wait()
}

// Multiplexer 将多个输入通道合并为一个输出通道
func Multiplexer[T any](ctx context.Context, inputs []<-chan T) <-chan T {
 var wg sync.WaitGroup
 out := make(chan T)
 
 // 为每个输入通道启动goroutine
 for _, input := range inputs {
  wg.Add(1)
  go func(ch <-chan T) {
   defer wg.Done()
   for {
    select {
    case <-ctx.Done():
     return
    case val, ok := <-ch:
     if !ok {
      return
     }
     select {
     case out <- val:
     case <-ctx.Done():
      return
     }
    }
   }
  }(input)
 }
 
 // 等待所有输入处理完毕，然后关闭输出通道
 go func() {
  wg.Wait()
  close(out)
 }()
 
 return out
}

// Demultiplexer 将一个输入通道分发到多个输出通道
func Demultiplexer[T any](ctx context.Context, input <-chan T, outputs []chan<- T) {
 var wg sync.WaitGroup
 
 // 为每个输出通道启动goroutine
 for _, output := range outputs {
  wg.Add(1)
  go func(out chan<- T) {
   defer wg.Done()
   for {
    select {
    case <-ctx.Done():
     return
    case val, ok := <-input:
     if !ok {
      return
     }
     select {
     case out <- val:
     case <-ctx.Done():
      return
     }
    }
   }
  }(output)
 }
 
 wg.Wait()
}

// Filter 过滤通道中的元素
func Filter[T any](ctx context.Context, input <-chan T, predicate func(T) bool) <-chan T {
 out := make(chan T)
 
 go func() {
  defer close(out)
  for {
   select {
   case <-ctx.Done():
    return
   case val, ok := <-input:
    if !ok {
     return
    }
    if predicate(val) {
     select {
     case out <- val:
     case <-ctx.Done():
      return
     }
    }
   }
  }
 }()
 
 return out
}

// Map 转换通道中的元素
func Map[T, R any](ctx context.Context, input <-chan T, fn func(T) R) <-chan R {
 out := make(chan R)
 
 go func() {
  defer close(out)
  for {
   select {
   case <-ctx.Done():
    return
   case val, ok := <-input:
    if !ok {
     return
    }
    result := fn(val)
    select {
    case out <- result:
    case <-ctx.Done():
     return
    }
   }
  }
 }()
 
 return out
}

// ProcessNetwork 一个CSP进程网络，支持动态添加进程
type ProcessNetwork[T any] struct {
 processes map[string]Process[T, T]
 inputs    map[string]chan T
 outputs   map[string]chan T
 mu        sync.RWMutex
 ctx       context.Context
 cancel    context.CancelFunc
 wg        sync.WaitGroup
}

// NewProcessNetwork 创建一个新的CSP进程网络
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
func (pn *ProcessNetwork[T]) AddProcess(name string, process Process[T, T], bufferSize int) {
 pn.mu.Lock()
 defer pn.mu.Unlock()
 
 pn.processes[name] = process
 pn.inputs[name] = make(chan T, bufferSize)
 pn.outputs[name] = make(chan T, bufferSize)
 
 // 启动进程
 pn.wg.Add(1)
 go func() {
  defer pn.wg.Done()
  process.Run(pn.ctx, pn.inputs[name], pn.outputs[name])
 }()
}

// Connect 连接两个进程
func (pn *ProcessNetwork[T]) Connect(fromProcess, toProcess string) error {
 pn.mu.Lock()
 defer pn.mu.Unlock()
 
 from, fromExists := pn.outputs[fromProcess]
 to, toExists := pn.inputs[toProcess]
 
 if !fromExists || !toExists {
  return ErrProcessNotFound
 }
 
 // 启动转发goroutine
 pn.wg.Add(1)
 go func() {
  defer pn.wg.Done()
  for {
   select {
   case <-pn.ctx.Done():
    return
   case val, ok := <-from:
    if !ok {
     return
    }
    select {
    case to <- val:
    case <-pn.ctx.Done():
     return
    }
   }
  }
 }()
 
 return nil
}

// Send 向指定进程发送数据
func (pn *ProcessNetwork[T]) Send(processName string, data T) error {
 pn.mu.RLock()
 defer pn.mu.RUnlock()
 
 in, exists := pn.inputs[processName]
 if !exists {
  return ErrProcessNotFound
 }
 
 select {
 case in <- data:
  return nil
 case <-pn.ctx.Done():
  return pn.ctx.Err()
 }
}

// Receive 从指定进程接收数据
func (pn *ProcessNetwork[T]) Receive(processName string) (T, error) {
 pn.mu.RLock()
 out, exists := pn.outputs[processName]
 pn.mu.RUnlock()
 
 if !exists {
  var zero T
  return zero, ErrProcessNotFound
 }
 
 select {
 case data := <-out:
  return data, nil
 case <-pn.ctx.Done():
  var zero T
  return zero, pn.ctx.Err()
 }
}

// Stop 停止进程网络
func (pn *ProcessNetwork[T]) Stop() {
 pn.cancel()
 pn.wg.Wait()
}

// 错误定义
var ErrProcessNotFound = StructError("process not found")

// StructError 结构化错误类型
type StructError string

func (e StructError) Error() string {
 return string(e)
}
```

## 并行数据处理模式

### Map-Reduce模式

Map-Reduce模式是一种分布式计算模式，用于大规模数据处理。

```go
package mapreduce

import (
 "context"
 "sync"
)

// MapFunc 映射函数类型
type MapFunc[T, M any] func(item T) M

// ReduceFunc 归约函数类型
type ReduceFunc[M, R any] func(result R, item M) R

// MapReduce 执行Map-Reduce操作
func MapReduce[T, M, R any](
 ctx context.Context,
 data []T,
 mapFn MapFunc[T, M],
 reduceFn ReduceFunc[M, R],
 initialValue R,
 parallelism int,
) R {
 if parallelism <= 0 {
  parallelism = 1
 }
 
 // 计算每个worker应处理的项目数
 itemsPerWorker := (len(data) + parallelism - 1) / parallelism
 if itemsPerWorker < 1 {
  itemsPerWorker = 1
 }
 
 // 执行map阶段
 mapResults := executeMap(ctx, data, mapFn, itemsPerWorker)
 
 // 执行reduce阶段
 return executeReduce(ctx, mapResults, reduceFn, initialValue)
}

// executeMap 执行map阶段
func executeMap[T, M any](
 ctx context.Context,
 data []T,
 mapFn MapFunc[T, M],
 itemsPerWorker int,
) <-chan M {
 results := make(chan M)
 
 var wg sync.WaitGroup
 
 // 启动worker处理数据
 for i := 0; i < len(data); i += itemsPerWorker {
  wg.Add(1)
  
  go func(start int) {
   defer wg.Done()
   
   // 计算该worker的处理范围
   end := start + itemsPerWorker
   if end > len(data) {
    end = len(data)
   }
   
   // 处理数据项
   for j := start; j < end; j++ {
    select {
    case <-ctx.Done():
     return
    default:
     // 应用map函数并发送结果
     result := mapFn(data[j])
     select {
     case results <- result:
     case <-ctx.Done():
      return
     }
    }
   }
  }(i)
 }
 
 // 等待所有map worker完成，然后关闭结果通道
 go func() {
  wg.Wait()
  close(results)
 }()
 
 return results
}

// executeReduce 执行reduce阶段
func executeReduce[M, R any](
 ctx context.Context,
 mapResults <-chan M,
 reduceFn ReduceFunc[M, R],
 initialValue R,
) R {
 result := initialValue
 
 // 读取所有map结果并应用reduce函数
 for {
  select {
  case <-ctx.Done():
   return result
  case item, ok := <-mapResults:
   if !ok {
    return result
   }
   result = reduceFn(result, item)
  }
 }
}

// ConcurrentMapReduce 执行并发Map-Reduce，支持并行reduce
func ConcurrentMapReduce[T, M, R any](
 ctx context.Context,
 data []T,
 mapFn MapFunc[T, M],
 reduceFn ReduceFunc[M, R],
 combinerFn ReduceFunc[R, R],
 initialValue R,
 mapParallelism int,
 reduceParallelism int,
) R {
 if mapParallelism <= 0 {
  mapParallelism = 1
 }
 if reduceParallelism <= 0 {
  reduceParallelism = 1
 }
 
 // 计算每个mapper应处理的项目数
 itemsPerMapper := (len(data) + mapParallelism - 1) / mapParallelism
 if itemsPerMapper < 1 {
  itemsPerMapper = 1
 }
 
 // 执行map阶段
 mapResults := executeMap(ctx, data, mapFn, itemsPerMapper)
 
 // 执行并行reduce阶段
 reducers := executeParallelReduce(ctx, mapResults, reduceFn, initialValue, reduceParallelism)
 
 // 合并reducer结果
 return executeCombine(ctx, reducers, combinerFn, initialValue)
}

// executeParallelReduce 执行并行reduce阶段
func executeParallelReduce[M, R any](
 ctx context.Context,
 mapResults <-chan M,
 reduceFn ReduceFunc[M, R],
 initialValue R,
 parallelism int,
) []R {
 // 创建reducers
 reducers := make([]R, parallelism)
 for i := 0; i < parallelism; i++ {
  reducers[i] = initialValue
 }
 
 // 将map结果分配给reducers
 var wg sync.WaitGroup
 wg.Add(parallelism)
 
 // 创建工作者通道
 workers := make([]chan M, parallelism)
 for i := 0; i < parallelism; i++ {
  workers[i] = make(chan M, 100)
  
  go func(workerID int, worker chan M) {
   defer wg.Done()
   
   // 读取分配给该worker的所有项目并reduce
   for item := range worker {
    reducers[workerID] = reduceFn(reducers[workerID], item)
   }
  }(i, workers[i])
 }
 
 // 分发map结果
 go func() {
  i := 0
  for item := range mapResults {
   workers[i] <- item
   i = (i + 1) % parallelism
  }
  
  // 关闭所有worker通道
  for _, worker := range workers {
   close(worker)
  }
 }()
 
 // 等待所有reducers完成
 wg.Wait()
 
 return reducers
}

// executeCombine 合并reducer结果
func executeCombine[R any](
 ctx context.Context,
 reducers []R,
 combinerFn ReduceFunc[R, R],
 initialValue R,
) R {
 result := initialValue
 
 // 合并所有reducer结果
 for _, r := range reducers {
  select {
  case <-ctx.Done():
   return result
  default:
   result = combinerFn(result, r)
  }
 }
 
 return result
}

// MapReducePipeline 构建可重用的Map-Reduce管道
type MapReducePipeline[T, M, R any] struct {
 mapFn           MapFunc[T, M]
 reduceFn        ReduceFunc[M, R]
 combinerFn      ReduceFunc[R, R]
 initialValue    R
 mapParallelism  int
 reduceParallelism int
}

// NewMapReducePipeline 创建新的Map-Reduce管道
func NewMapReducePipeline[T, M, R any](
 mapFn MapFunc[T, M],
 reduceFn ReduceFunc[M, R],
 combinerFn ReduceFunc[R, R],
 initialValue R,
 mapParallelism int,
 reduceParallelism int,
) *MapReducePipeline[T, M, R] {
 return &MapReducePipeline[T, M, R]{
  mapFn:           mapFn,
  reduceFn:        reduceFn,
  combinerFn:      combinerFn,
  initialValue:    initialValue,
  mapParallelism:  mapParallelism,
  reduceParallelism: reduceParallelism,
 }
}

// Process 处理数据
func (p *MapReducePipeline[T, M, R]) Process(ctx context.Context, data []T) R {
 return ConcurrentMapReduce(
  ctx,
  data,
  p.mapFn,
  p.reduceFn,
  p.combinerFn,
  p.initialValue,
  p.mapParallelism,
  p.reduceParallelism,
 )
}
```

### Fork-Join模式

Fork-Join模式将任务分解为更小的子任务，并行处理后再合并结果。

```go
package forkjoin

import (
 "context"
 "sync"
)

// Task 表示可分解为子任务的任务
type Task[T any] interface {
 // Execute 执行任务
 Execute() T
 // Fork 将任务分解为子任务
 Fork() []Task[T]
 // ShouldFork 判断是否应该分解
 ShouldFork() bool
 // Join 合并子任务结果
 Join(results []T) T
}

// ForkJoinPool 管理并行执行的任务
type ForkJoinPool struct {
 parallelism int
 semaphore   chan struct{}
}

// NewForkJoinPool 创建新的Fork-Join池
func NewForkJoinPool(parallelism int) *ForkJoinPool {
 if parallelism <= 0 {
  parallelism = 1
 }
 
 return &ForkJoinPool{
  parallelism: parallelism,
  semaphore:   make(chan struct{}, parallelism),
 }
}

// Execute 执行任务
func (p *ForkJoinPool) Execute[T any](ctx context.Context, task Task[T]) T {
 // 尝试获取许可
 select {
 case p.semaphore <- struct{}{}:
  // 获取许可成功，异步执行
  defer func() { <-p.semaphore }()
  return p.executeTask(ctx, task)
 default:
  // 无法获取许可，直接在当前goroutine执行
  return task.Execute()
 }
}

// executeTask 执行任务，如可能则进行分解
func (p *ForkJoinPool) executeTask[T any](ctx context.Context, task Task[T]) T {
 if !task.ShouldFork() {
  return task.Execute()
 }
 
 // 分解为子任务
 subTasks := task.Fork()
 if len(subTasks) == 0 {
  return task.Execute()
 }
 
 // 并行执行子任务
 var wg sync.WaitGroup
 results := make([]T, len(subTasks))
 
 for i, subTask := range subTasks {
  wg.Add(1)
  
  go func(i int, t Task[T]) {
   defer wg.Done()
   
   // 递归执行子任务
   select {
   case <-ctx.Done():
    // 上下文取消，使用零值
    var zero T
    results[i] = zero
   default:
    results[i] = p.Execute(ctx, t)
   }
  }(i, subTask)
 }
 
 // 等待所有子任务完成
 wg.Wait()
 
 // 检查上下文是否取消
 select {
 case <-ctx.Done():
  var zero T
  return zero
 default:
  // 合并结果
  return task.Join(results)
 }
}

// RecursiveTask 简化实现递归分解任务的基类
type RecursiveTask[T, R any] struct {
 Data         T
 Threshold    int
 Size         func(T) int
 Split        func(T) []T
 Compute      func(T) R
 Combine      func([]R) R
}

func (rt *RecursiveTask[T, R]) Execute() R {
 return rt.Compute(rt.Data)
}

func (rt *RecursiveTask[T, R]) ShouldFork() bool {
 return rt.Size(rt.Data) > rt.Threshold
}

func (rt *RecursiveTask[T, R]) Fork() []Task[R] {
 parts := rt.Split(rt.Data)
 tasks := make([]Task[R], len(parts))
 
 for i, part := range parts {
  tasks[i] = &RecursiveTask[T, R]{
   Data:      part,
   Threshold: rt.Threshold,
   Size:      rt.Size,
   Split:     rt.Split,
   Compute:   rt.Compute,
   Combine:   rt.Combine,
  }
 }
 
 return tasks
}

func (rt *RecursiveTask[T, R]) Join(results []R) R {
 return rt.Combine(results)
}

// ParallelFor 并行执行循环
func ParallelFor[T any](
 ctx context.Context,
 pool *ForkJoinPool,
 items []T,
 batchSize int,
 fn func([]T),
) {
 // 创建任务
 task := &RecursiveTask[[]T, struct{}]{
  Data:      items,
  Threshold: batchSize,
  Size: func(data []T) int {
   return len(data)
  },
  Split: func(data []T) [][]T {
   mid := len(data) / 2
   return [][]T{data[:mid], data[mid:]}
  },
  Compute: func(data []T) struct{} {
   fn(data)
   return struct{}{}
  },
  Combine: func(results []struct{}) struct{} {
   return struct{}{}
  },
 }
 
 // 执行任务
 pool.Execute(ctx, task)
}

// ParallelReduce 并行归约
func ParallelReduce[T, R any](
 ctx context.Context,
 pool *ForkJoinPool,
 items []T,
 batchSize int,
 mapFn func([]T) R,
 reduceFn func(R, R) R,
 identity R,
) R {
 if len(items) == 0 {
  return identity
 }
 
 // 创建任务
 task := &RecursiveTask[[]T, R]{
  Data:      items,
  Threshold: batchSize,
  Size: func(data []T) int {
   return len(data)
  },
  Split: func(data []T) [][]T {
   mid := len(data) / 2
   return [][]T{data[:mid], data[mid:]}
  },
  Compute: func(data []T) R {
   return mapFn(data)
  },
  Combine: func(results []R) R {
   if len(results) == 0 {
    return identity
   }
   
   result := results[0]
   for i := 1; i < len(results); i++ {
    result = reduceFn(result, results[i])
   }
   return result
  },
 }
 
 // 执行任务
 return pool.Execute(ctx, task)
}
```

## 总结

本文从形式模型角度分析了Go语言中的并发并行设计模式，
并使用Go 1.24的泛型和接口特性实现了这些模式。
这些实现充分利用了Go语言的并发原语（goroutine和channel）以及泛型能力，
提供了类型安全且可重用的并发模式库。

通过这些设计模式，我们可以更好地组织并发代码，提高系统的可靠性、性能和可维护性。
每种模式都有其适用场景，开发者可以根据具体需求选择合适的模式。

Go语言的并发模型本身就建立在CSP理论基础上，使得许多并发模式的实现变得自然而优雅。
结合泛型，这些模式可以在保持类型安全的同时提供更高层次的抽象，
帮助开发者构建强大的并发系统。
