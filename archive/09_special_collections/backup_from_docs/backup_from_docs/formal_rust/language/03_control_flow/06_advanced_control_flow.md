# 06. 高级控制流模式 - Advanced Control Flow Patterns

## 📊 目录

- [06. 高级控制流模式 - Advanced Control Flow Patterns](#06-高级控制流模式---advanced-control-flow-patterns)
  - [📊 目录](#-目录)
  - [概述 - Overview](#概述---overview)
  - [6.1 异步控制流 - Asynchronous Control Flow](#61-异步控制流---asynchronous-control-flow)
    - [6.1.1 `async`, `await`, 与 `Future`](#611-async-await-与-future)
    - [6.1.2 状态机转换的形式化视角](#612-状态机转换的形式化视角)
    - [6.1.3 Rust 1.89 异步生态系统改进](#613-rust-189-异步生态系统改进)
      - [结构化并发控制流](#结构化并发控制流)
      - [异步流处理增强](#异步流处理增强)
      - [异步取消机制改进](#异步取消机制改进)
    - [6.1.4 异步控制流的性能优化](#614-异步控制流的性能优化)
  - [6.2 类型状态模式 - Type State Patterns](#62-类型状态模式---type-state-patterns)
    - [6.2.1 编译时状态机](#621-编译时状态机)
    - [6.2.2 状态转换约束](#622-状态转换约束)
    - [6.2.3 状态相关的API](#623-状态相关的api)
  - [6.3 高级控制流组合模式 - Advanced Control Flow Composition Patterns](#63-高级控制流组合模式---advanced-control-flow-composition-patterns)
    - [6.3.1 异步类型状态模式](#631-异步类型状态模式)
    - [6.3.2 控制流组合器](#632-控制流组合器)
  - [总结 - Summary](#总结---summary)

## 概述 - Overview

除了基础的条件和循环，Rust还提供了更高级的模式来管理复杂的控制流。
本章探讨两种强大的机制：异步控制流和类型状态模式，特别关注Rust 1.89版本中的新特性。

This chapter explores two powerful mechanisms beyond basic conditions and loops: asynchronous control flow and type state patterns, with special attention to new features in Rust 1.89.

## 6.1 异步控制流 - Asynchronous Control Flow

### 6.1.1 `async`, `await`, 与 `Future`

Rust的异步模型主要围绕三个核心概念构建：

```rust
// Rust 1.89 异步控制流增强
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 1. async fn - 异步函数
async fn fetch_data() -> String {
    // 模拟异步操作
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
    String::from("Data fetched successfully")
}

// 2. Future Trait - 未来值抽象
struct CustomFuture {
    state: FutureState,
    data: Option<String>,
}

enum FutureState {
    Pending,
    Ready,
}

impl Future for CustomFuture {
    type Output = String;
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.state {
            FutureState::Pending => {
                // 设置唤醒器
                cx.waker().wake_by_ref();
                Poll::Pending
            }
            FutureState::Ready => {
                Poll::Ready(self.data.take().unwrap())
            }
        }
    }
}

// 3. .await - 等待Future完成
async fn process_data() -> String {
    let data = fetch_data().await; // 等待Future完成
    format!("Processed: {}", data)
}
```

### 6.1.2 状态机转换的形式化视角

在底层，`async fn`被编译器转换为一个状态机：

```rust
// Rust 1.89 状态机转换的形式化定义
trait AsyncStateMachine {
    type State;
    type Input;
    type Output;
    
    // 状态转换函数
    fn transition(&mut self, input: Self::Input) -> Result<Self::State, TransitionError>;
    
    // 获取当前状态
    fn current_state(&self) -> &Self::State;
    
    // 检查是否完成
    fn is_completed(&self) -> bool;
}

// 异步状态机的实现
pub struct AsyncStateMachineImpl {
    current_state: AsyncState,
    local_variables: LocalVariables,
    await_points: Vec<AwaitPoint>,
}

#[derive(Debug, Clone)]
enum AsyncState {
    Initial,
    AwaitingData,
    ProcessingData,
    Completed,
}

impl AsyncStateMachine for AsyncStateMachineImpl {
    type State = AsyncState;
    type Input = AsyncInput;
    type Output = AsyncOutput;
    
    fn transition(&mut self, input: Self::Input) -> Result<Self::State, TransitionError> {
        match (self.current_state.clone(), input) {
            (AsyncState::Initial, AsyncInput::Start) => {
                self.current_state = AsyncState::AwaitingData;
                Ok(AsyncState::AwaitingData)
            }
            (AsyncState::AwaitingData, AsyncInput::DataReceived) => {
                self.current_state = AsyncState::ProcessingData;
                Ok(AsyncState::ProcessingData)
            }
            (AsyncState::ProcessingData, AsyncInput::ProcessingComplete) => {
                self.current_state = AsyncState::Completed;
                Ok(AsyncState::Completed)
            }
            _ => Err(TransitionError::InvalidTransition),
        }
    }
    
    fn current_state(&self) -> &Self::State {
        &self.current_state
    }
    
    fn is_completed(&self) -> bool {
        matches!(self.current_state, AsyncState::Completed)
    }
}
```

### 6.1.3 Rust 1.89 异步生态系统改进

#### 结构化并发控制流

```rust
// Rust 1.89 结构化并发
use tokio::task::JoinSet;
use tokio::time::{timeout, Duration};

async fn structured_concurrency_example() {
    let mut tasks = JoinSet::new();
    
    // 启动多个并发任务
    for i in 0..10 {
        tasks.spawn(async move {
            process_task(i).await
        });
    }
    
    // 等待所有任务完成
    while let Some(result) = tasks.join_next().await {
        match result {
            Ok(value) => println!("Task completed: {:?}", value),
            Err(e) => eprintln!("Task failed: {:?}", e),
        }
    }
}

async fn process_task(id: u32) -> u32 {
    // 模拟工作负载
    tokio::time::sleep(Duration::from_millis(100)).await;
    id * 2
}

// 带超时的结构化并发
async fn timeout_structured_concurrency() {
    let result = timeout(Duration::from_secs(5), async {
        let mut tasks = JoinSet::new();
        
        for i in 0..100 {
            tasks.spawn(async move {
                long_running_task(i).await
            });
        }
        
        let mut results = Vec::new();
        while let Some(result) = tasks.join_next().await {
            results.push(result?);
        }
        
        Ok::<Vec<u32>, Box<dyn std::error::Error>>(results)
    }).await;
    
    match result {
        Ok(Ok(results)) => println!("Completed {} tasks", results.len()),
        Ok(Err(e)) => eprintln!("Task error: {}", e),
        Err(_) => println!("Timeout reached"),
    }
}

async fn long_running_task(id: u32) -> Result<u32, Box<dyn std::error::Error>> {
    tokio::time::sleep(Duration::from_secs(1)).await;
    Ok(id * 2)
}
```

#### 异步流处理增强

```rust
// Rust 1.89 异步流处理
use tokio_stream::{Stream, StreamExt};
use futures::stream::{self, TryStreamExt};

async fn async_stream_processing() {
    // 创建异步流
    let numbers = stream::iter(0..1000);
    
    // 并行处理流
    let processed = numbers
        .map(|x| async move { x * x })
        .buffered(100) // 并行处理100个任务
        .filter(|&x| async move { x % 2 == 0 })
        .collect::<Vec<_>>()
        .await;
    
    println!("Processed {} numbers", processed.len());
}

// 异步流转换
async fn stream_transformations() {
    let input_stream = stream::iter(0..100);
    
    let transformed_stream = input_stream
        .map(|x| async move { process_item(x).await })
        .buffered(50)
        .filter(|&x| async move { x > 100 })
        .map(|x| format!("Processed: {}", x));
    
    let results: Vec<String> = transformed_stream.collect().await;
    println!("Transformed {} items", results.len());
}

async fn process_item(x: i32) -> i32 {
    tokio::time::sleep(Duration::from_millis(10)).await;
    x * 2
}

// 异步流错误处理
async fn stream_error_handling() {
    let fallible_stream = stream::iter(0..100)
        .map(|x| {
            if x % 10 == 0 {
                Err(format!("Error at {}", x))
            } else {
                Ok(x)
            }
        });
    
    let results: Result<Vec<i32>, String> = fallible_stream
        .try_collect()
        .await;
    
    match results {
        Ok(values) => println!("Successfully processed {} items", values.len()),
        Err(e) => eprintln!("Stream error: {}", e),
    }
}
```

#### 异步取消机制改进

```rust
// Rust 1.89 异步取消机制
use tokio_util::sync::CancellationToken;
use std::sync::Arc;

async fn cancellation_example() {
    let token = CancellationToken::new();
    let token_clone = token.clone();
    
    // 启动可取消的任务
    let task = tokio::spawn(async move {
        cancellable_operation(token_clone).await
    });
    
    // 等待一段时间后取消
    tokio::time::sleep(Duration::from_secs(2)).await;
    token.cancel();
    
    // 等待任务完成
    match task.await {
        Ok(result) => println!("Task result: {:?}", result),
        Err(e) => eprintln!("Task error: {:?}", e),
    }
}

async fn cancellable_operation(token: CancellationToken) -> Result<String, Box<dyn std::error::Error>> {
    let mut interval = tokio::time::interval(Duration::from_millis(100));
    
    for i in 0..100 {
        // 检查取消信号
        if token.is_cancelled() {
            return Err("Operation cancelled".into());
        }
        
        interval.tick().await;
        println!("Processing step {}", i);
    }
    
    Ok("Operation completed successfully".to_string())
}

// 级联取消
async fn cascading_cancellation() {
    let parent_token = CancellationToken::new();
    let child_token = CancellationToken::new();
    
    // 设置级联取消
    let parent_clone = parent_token.clone();
    let child_clone = child_token.clone();
    
    tokio::spawn(async move {
        // 监听父级取消信号
        parent_clone.cancelled().await;
        // 级联取消子任务
        child_clone.cancel();
    });
    
    // 启动子任务
    let child_task = tokio::spawn(async move {
        cancellable_operation(child_clone).await
    });
    
    // 等待一段时间后取消父任务
    tokio::time::sleep(Duration::from_secs(1)).await;
    parent_token.cancel();
    
    // 等待子任务完成
    match child_task.await {
        Ok(result) => println!("Child task result: {:?}", result),
        Err(e) => eprintln!("Child task error: {:?}", e),
    }
}
```

### 6.1.4 异步控制流的性能优化

```rust
// Rust 1.89 异步性能优化
use tokio::sync::Semaphore;
use std::sync::Arc;

async fn optimized_async_processing() {
    // 使用信号量限制并发数量
    let semaphore = Arc::new(Semaphore::new(100));
    let mut tasks = Vec::new();
    
    for i in 0..1000 {
        let permit = semaphore.clone().acquire_owned().await.unwrap();
        
        let task = tokio::spawn(async move {
            let _permit = permit; // 持有信号量许可
            process_with_backpressure(i).await
        });
        
        tasks.push(task);
    }
    
    // 等待所有任务完成
    let results = futures::future::join_all(tasks).await;
    let success_count = results.into_iter()
        .filter_map(|r| r.ok())
        .count();
    
    println!("Successfully completed {} tasks", success_count);
}

async fn process_with_backpressure(id: u32) -> u32 {
    // 模拟可变的工作负载
    let sleep_duration = if id % 10 == 0 {
        Duration::from_millis(100) // 慢任务
    } else {
        Duration::from_millis(10)  // 快任务
    };
    
    tokio::time::sleep(sleep_duration).await;
    id * 2
}

// 异步批处理
async fn async_batch_processing() {
    let items: Vec<i32> = (0..10000).collect();
    let batch_size = 100;
    
    let mut results = Vec::new();
    
    for chunk in items.chunks(batch_size) {
        let batch_results = futures::future::join_all(
            chunk.iter().map(|&x| async move { process_item(x).await })
        ).await;
        
        results.extend(batch_results);
    }
    
    println!("Processed {} items in batches", results.len());
}
```

## 6.2 类型状态模式 - Type State Patterns

### 6.2.1 编译时状态机

类型状态模式允许在编译时强制执行状态转换规则：

```rust
// Rust 1.89 类型状态模式增强
use std::marker::PhantomData;

// 状态标记类型
struct Uninitialized;
struct Initialized;
struct Validated;
struct Processed;
struct Completed;

// 类型状态容器
struct DataProcessor<T, S> {
    data: T,
    _state: PhantomData<S>,
}

// 状态转换实现
impl<T> DataProcessor<T, Uninitialized> {
    fn new(data: T) -> Self {
        Self {
            data,
            _state: PhantomData,
        }
    }
    
    fn initialize(self) -> DataProcessor<T, Initialized> {
        DataProcessor {
            data: self.data,
            _state: PhantomData,
        }
    }
}

impl<T> DataProcessor<T, Initialized> {
    fn validate(self) -> Result<DataProcessor<T, Validated>, ValidationError> {
        if Self::is_valid(&self.data) {
            Ok(DataProcessor {
                data: self.data,
                _state: PhantomData,
            })
        } else {
            Err(ValidationError::InvalidData)
        }
    }
    
    fn is_valid(data: &T) -> bool {
        // 验证逻辑
        true
    }
}

impl<T> DataProcessor<T, Validated> {
    fn process(self) -> DataProcessor<T, Processed> {
        DataProcessor {
            data: self.data,
            _state: PhantomData,
        }
    }
}

impl<T> DataProcessor<T, Processed> {
    fn complete(self) -> DataProcessor<T, Completed> {
        DataProcessor {
            data: self.data,
            _state: PhantomData,
        }
    }
    
    fn get_result(self) -> T {
        self.data
    }
}

// 验证错误类型
#[derive(Debug, thiserror::Error)]
pub enum ValidationError {
    #[error("Invalid data")]
    InvalidData,
    #[error("Data format error")]
    FormatError,
}
```

### 6.2.2 状态转换约束

```rust
// Rust 1.89 状态转换约束
trait StateTransition<S1, S2> {
    type TransitionError;
    
    fn can_transition(&self) -> bool;
    fn transition(self) -> Result<S2, Self::TransitionError>;
}

// 状态转换规则
impl<T> StateTransition<DataProcessor<T, Uninitialized>, DataProcessor<T, Initialized>> 
    for DataProcessor<T, Uninitialized> {
    type TransitionError = TransitionError;
    
    fn can_transition(&self) -> bool {
        true // 总是可以初始化
    }
    
    fn transition(self) -> Result<DataProcessor<T, Initialized>, Self::TransitionError> {
        Ok(self.initialize())
    }
}

impl<T> StateTransition<DataProcessor<T, Initialized>, DataProcessor<T, Validated>> 
    for DataProcessor<T, Initialized> {
    type TransitionError = TransitionError;
    
    fn can_transition(&self) -> bool {
        Self::is_valid(&self.data)
    }
    
    fn transition(self) -> Result<DataProcessor<T, Validated>, Self::TransitionError> {
        self.validate().map_err(|_| TransitionError::ValidationFailed)
    }
}

// 转换错误类型
#[derive(Debug, thiserror::Error)]
pub enum TransitionError {
    #[error("Validation failed")]
    ValidationFailed,
    #[error("Invalid state transition")]
    InvalidTransition,
}
```

### 6.2.3 状态相关的API

```rust
// Rust 1.89 状态相关API
trait StateSpecificAPI<S> {
    type Output;
    
    fn state_specific_operation(&self) -> Self::Output;
}

// 为不同状态实现不同的API
impl<T> StateSpecificAPI<Initialized> for DataProcessor<T, Initialized> {
    type Output = String;
    
    fn state_specific_operation(&self) -> Self::Output {
        "Data is initialized".to_string()
    }
}

impl<T> StateSpecificAPI<Validated> for DataProcessor<T, Validated> {
    type Output = bool;
    
    fn state_specific_operation(&self) -> Self::Output {
        true // 已验证的数据
    }
}

impl<T> StateSpecificAPI<Processed> for DataProcessor<T, Processed> {
    type Output = usize;
    
    fn state_specific_operation(&self) -> Self::Output {
        std::mem::size_of::<T>()
    }
}

// 状态查询API
trait StateQuery {
    fn is_initialized(&self) -> bool;
    fn is_validated(&self) -> bool;
    fn is_processed(&self) -> bool;
    fn is_completed(&self) -> bool;
}

impl<T, S> StateQuery for DataProcessor<T, S> {
    fn is_initialized(&self) -> bool {
        std::any::type_name::<S>() == std::any::type_name::<Initialized>()
            || std::any::type_name::<S>() == std::any::type_name::<Validated>()
            || std::any::type_name::<S>() == std::any::type_name::<Processed>()
            || std::any::type_name::<S>() == std::any::type_name::<Completed>()
    }
    
    fn is_validated(&self) -> bool {
        std::any::type_name::<S>() == std::any::type_name::<Validated>()
            || std::any::type_name::<S>() == std::any::type_name::<Processed>()
            || std::any::type_name::<S>() == std::any::type_name::<Completed>()
    }
    
    fn is_processed(&self) -> bool {
        std::any::type_name::<S>() == std::any::type_name::<Processed>()
            || std::any::type_name::<S>() == std::any::type_name::<Completed>()
    }
    
    fn is_completed(&self) -> bool {
        std::any::type_name::<S>() == std::any::type_name::<Completed>()
    }
}
```

## 6.3 高级控制流组合模式 - Advanced Control Flow Composition Patterns

### 6.3.1 异步类型状态模式

```rust
// Rust 1.89 异步类型状态模式
use std::future::Future;
use std::pin::Pin;

// 异步状态处理器
struct AsyncDataProcessor<T, S> {
    data: T,
    _state: PhantomData<S>,
}

// 异步状态转换
impl<T> AsyncDataProcessor<T, Uninitialized> {
    fn new(data: T) -> Self {
        Self {
            data,
            _state: PhantomData,
        }
    }
    
    async fn initialize(self) -> AsyncDataProcessor<T, Initialized> {
        // 异步初始化逻辑
        tokio::time::sleep(Duration::from_millis(100)).await;
        
        AsyncDataProcessor {
            data: self.data,
            _state: PhantomData,
        }
    }
}

impl<T> AsyncDataProcessor<T, Initialized> {
    async fn validate(self) -> Result<AsyncDataProcessor<T, Validated>, ValidationError> {
        // 异步验证逻辑
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        if Self::is_valid(&self.data) {
            Ok(AsyncDataProcessor {
                data: self.data,
                _state: PhantomData,
            })
        } else {
            Err(ValidationError::InvalidData)
        }
    }
    
    fn is_valid(data: &T) -> bool {
        true
    }
}

impl<T> AsyncDataProcessor<T, Validated> {
    async fn process(self) -> AsyncDataProcessor<T, Processed> {
        // 异步处理逻辑
        tokio::time::sleep(Duration::from_millis(300)).await;
        
        AsyncDataProcessor {
            data: self.data,
            _state: PhantomData,
        }
    }
}

// 异步状态机实现
impl<T> AsyncDataProcessor<T, Uninitialized> {
    async fn run_pipeline(self) -> Result<T, Box<dyn std::error::Error>> {
        let processor = self
            .initialize()
            .await
            .validate()
            .await?
            .process()
            .await;
        
        Ok(processor.data)
    }
}
```

### 6.3.2 控制流组合器

```rust
// Rust 1.89 控制流组合器
use std::future::Future;

// 条件异步执行
async fn conditional_async_execution<F, Fut>(
    condition: bool,
    future_fn: F,
) -> Option<Fut::Output>
where
    F: FnOnce() -> Fut,
    Fut: Future,
{
    if condition {
        Some(future_fn().await)
    } else {
        None
    }
}

// 重试机制
async fn retry_with_backoff<F, Fut, T, E>(
    mut operation: F,
    max_retries: usize,
    initial_delay: Duration,
) -> Result<T, E>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: std::fmt::Debug,
{
    let mut delay = initial_delay;
    
    for attempt in 0..=max_retries {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                if attempt == max_retries {
                    return Err(e);
                }
                
                eprintln!("Attempt {} failed: {:?}, retrying in {:?}", attempt, e, delay);
                tokio::time::sleep(delay).await;
                delay *= 2; // 指数退避
            }
        }
    }
    
    unreachable!()
}

// 超时控制
async fn with_timeout<F, Fut, T>(
    future: F,
    timeout_duration: Duration,
) -> Result<T, TimeoutError>
where
    F: Future<Output = T>,
{
    tokio::time::timeout(timeout_duration, future)
        .await
        .map_err(|_| TimeoutError)
}

#[derive(Debug, thiserror::Error)]
#[error("Operation timed out")]
pub struct TimeoutError;

// 示例使用
async fn example_usage() {
    // 条件执行
    let result = conditional_async_execution(
        true,
        || async { fetch_data().await }
    ).await;
    
    // 重试机制
    let data = retry_with_backoff(
        || async { fetch_data().await },
        3,
        Duration::from_millis(100)
    ).await.unwrap();
    
    // 超时控制
    let result = with_timeout(
        async { long_running_operation().await },
        Duration::from_secs(5)
    ).await;
}
```

## 总结 - Summary

本章节完成了Rust高级控制流模式的理论和实践，包括：

1. **异步控制流**: `async`/`await`、`Future`、状态机转换
2. **Rust 1.89新特性**: 结构化并发、异步流处理、取消机制
3. **类型状态模式**: 编译时状态机、状态转换约束、状态相关API
4. **高级组合模式**: 异步类型状态、控制流组合器、重试和超时机制

这些高级控制流模式为Rust程序提供了强大的并发和状态管理能力，同时保持了编译时安全保证。
