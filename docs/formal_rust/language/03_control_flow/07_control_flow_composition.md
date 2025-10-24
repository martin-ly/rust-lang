# 07. 控制流组合模式 - Control Flow Composition Patterns


## 📊 目录

- [概述 - Overview](#概述-overview)
- [7.1 控制流组合器 - Control Flow Combinators](#71-控制流组合器-control-flow-combinators)
  - [7.1.1 基础组合器](#711-基础组合器)
  - [7.1.2 高级组合器](#712-高级组合器)
- [7.2 管道模式 - Pipeline Patterns](#72-管道模式-pipeline-patterns)
  - [7.2.1 基础管道](#721-基础管道)
  - [7.2.2 高级管道模式](#722-高级管道模式)
- [7.3 错误传播组合 - Error Propagation Composition](#73-错误传播组合-error-propagation-composition)
  - [7.3.1 错误传播链](#731-错误传播链)
  - [7.3.2 错误组合器](#732-错误组合器)
- [7.4 并发控制流组合 - Concurrent Control Flow Composition](#74-并发控制流组合-concurrent-control-flow-composition)
  - [7.4.1 并发组合模式](#741-并发组合模式)
- [总结 - Summary](#总结-summary)


## 概述 - Overview

本章节深入探讨Rust控制流组合的高级模式和技术，包括控制流组合器、管道模式、错误传播组合、并发控制流组合等，特别关注Rust 1.89版本中的新特性。

This section delves into advanced patterns and techniques for composing control flows in Rust, including control flow combinators, pipeline patterns, error propagation composition, concurrent control flow composition, and more, with special attention to new features in Rust 1.89.

## 7.1 控制流组合器 - Control Flow Combinators

### 7.1.1 基础组合器

控制流组合器是函数式编程中的核心概念，允许将多个控制流操作组合成更复杂的操作：

```rust
// Rust 1.89 控制流组合器
use std::future::Future;
use tokio::time::{timeout, Duration};

// 1. 序列组合器 - 按顺序执行多个操作
async fn sequence_combinator<F1, F2, Fut1, Fut2, T1, T2>(
    first: F1,
    second: F2,
) -> (T1, T2)
where
    F1: FnOnce() -> Fut1,
    F2: FnOnce(T1) -> Fut2,
    Fut1: Future<Output = T1>,
    Fut2: Future<Output = T2>,
{
    let result1 = first().await;
    let result2 = second(result1).await;
    (result1, result2)
}

// 2. 选择组合器 - 选择第一个完成的操作
async fn select_combinator<F1, F2, Fut1, Fut2, T>(
    first: F1,
    second: F2,
) -> T
where
    F1: FnOnce() -> Fut1,
    F2: FnOnce() -> Fut2,
    Fut1: Future<Output = T>,
    Fut2: Future<Output = T>,
{
    tokio::select! {
        result = first() => result,
        result = second() => result,
    }
}

// 3. 条件组合器 - 根据条件选择执行路径
async fn conditional_combinator<F1, F2, Fut1, Fut2, T>(
    condition: bool,
    if_true: F1,
    if_false: F2,
) -> T
where
    F1: FnOnce() -> Fut1,
    F2: FnOnce() -> Fut2,
    Fut1: Future<Output = T>,
    Fut2: Future<Output = T>,
{
    if condition {
        if_true().await
    } else {
        if_false().await
    }
}

// 4. 重试组合器 - 失败时重试操作
async fn retry_combinator<F, Fut, T, E>(
    operation: F,
    max_retries: usize,
    backoff_strategy: BackoffStrategy,
) -> Result<T, E>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, E>>,
    E: std::fmt::Debug,
{
    let mut attempts = 0;
    let mut delay = backoff_strategy.initial_delay();
    
    loop {
        match operation().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                attempts += 1;
                if attempts > max_retries {
                    return Err(e);
                }
                
                eprintln!("Attempt {} failed: {:?}, retrying in {:?}", attempts, e, delay);
                tokio::time::sleep(delay).await;
                delay = backoff_strategy.next_delay(delay);
            }
        }
    }
}

// 退避策略
trait BackoffStrategy {
    fn initial_delay(&self) -> Duration;
    fn next_delay(&self, current_delay: Duration) -> Duration;
}

struct ExponentialBackoff {
    multiplier: f64,
    max_delay: Duration,
}

impl BackoffStrategy for ExponentialBackoff {
    fn initial_delay(&self) -> Duration {
        Duration::from_millis(100)
    }
    
    fn next_delay(&self, current_delay: Duration) -> Duration {
        let next_millis = (current_delay.as_millis() as f64 * self.multiplier) as u64;
        Duration::from_millis(next_millis.min(self.max_delay.as_millis()))
    }
}
```

### 7.1.2 高级组合器

```rust
// Rust 1.89 高级控制流组合器
use std::sync::Arc;
use tokio::sync::{Semaphore, RwLock};

// 1. 并发限制组合器 - 限制并发执行数量
async fn concurrency_limited_combinator<F, Fut, T>(
    operations: Vec<F>,
    max_concurrent: usize,
) -> Vec<Result<T, Box<dyn std::error::Error + Send + Sync>>>
where
    F: FnOnce() -> Fut + Send + 'static,
    Fut: Future<Output = Result<T, Box<dyn std::error::Error + Send + Sync>>> + Send + 'static,
    T: Send + 'static,
{
    let semaphore = Arc::new(Semaphore::new(max_concurrent));
    let mut tasks = Vec::new();
    
    for operation in operations {
        let permit = semaphore.clone().acquire_owned().await.unwrap();
        
        let task = tokio::spawn(async move {
            let _permit = permit; // 持有信号量许可
            operation().await
        });
        
        tasks.push(task);
    }
    
    // 等待所有任务完成
    let results = futures::future::join_all(tasks).await;
    results.into_iter()
        .map(|r| r.unwrap_or_else(|e| Err(e.into())))
        .collect()
}

// 2. 超时组合器 - 为操作添加超时
async fn timeout_combinator<F, Fut, T>(
    operation: F,
    timeout_duration: Duration,
) -> Result<T, TimeoutError>
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = T>,
{
    match timeout(timeout_duration, operation()).await {
        Ok(result) => Ok(result),
        Err(_) => Err(TimeoutError),
    }
}

// 3. 断路器组合器 - 防止级联失败
struct CircuitBreaker {
    failure_threshold: usize,
    recovery_timeout: Duration,
    state: Arc<RwLock<CircuitBreakerState>>,
}

#[derive(Debug, Clone)]
enum CircuitBreakerState {
    Closed { failure_count: usize },
    Open { opened_at: std::time::Instant },
    HalfOpen,
}

impl CircuitBreaker {
    fn new(failure_threshold: usize, recovery_timeout: Duration) -> Self {
        Self {
            failure_threshold,
            recovery_timeout,
            state: Arc::new(RwLock::new(CircuitBreakerState::Closed { failure_count: 0 })),
        }
    }
    
    async fn execute<F, Fut, T, E>(&self, operation: F) -> Result<T, CircuitBreakerError<E>>
    where
        F: FnOnce() -> Fut,
        Fut: Future<Output = Result<T, E>>,
    {
        let state = self.state.read().await;
        
        match &*state {
            CircuitBreakerState::Closed { failure_count } => {
                if *failure_count >= self.failure_threshold {
                    drop(state);
                    self.open_circuit().await;
                    return Err(CircuitBreakerError::CircuitOpen);
                }
            }
            CircuitBreakerState::Open { opened_at } => {
                if opened_at.elapsed() < self.recovery_timeout {
                    return Err(CircuitBreakerError::CircuitOpen);
                }
                drop(state);
                self.half_open_circuit().await;
            }
            CircuitBreakerState::HalfOpen => {
                // 允许尝试
            }
        }
        
        drop(state);
        
        // 执行操作
        match operation().await {
            Ok(result) => {
                self.on_success().await;
                Ok(result)
            }
            Err(e) => {
                self.on_failure().await;
                Err(CircuitBreakerError::OperationFailed(e))
            }
        }
    }
    
    async fn open_circuit(&self) {
        let mut state = self.state.write().await;
        *state = CircuitBreakerState::Open {
            opened_at: std::time::Instant::now(),
        };
    }
    
    async fn half_open_circuit(&self) {
        let mut state = self.state.write().await;
        *state = CircuitBreakerState::HalfOpen;
    }
    
    async fn on_success(&self) {
        let mut state = self.state.write().await;
        *state = CircuitBreakerState::Closed { failure_count: 0 };
    }
    
    async fn on_failure(&self) {
        let mut state = self.state.write().await;
        match &mut *state {
            CircuitBreakerState::Closed { failure_count } => {
                *failure_count += 1;
            }
            CircuitBreakerState::HalfOpen => {
                self.open_circuit().await;
            }
            _ => {}
        }
    }
}

#[derive(Debug, thiserror::Error)]
pub enum CircuitBreakerError<E> {
    #[error("Circuit breaker is open")]
    CircuitOpen,
    #[error("Operation failed: {0}")]
    OperationFailed(E),
}

#[derive(Debug, thiserror::Error)]
#[error("Operation timed out")]
pub struct TimeoutError;
```

## 7.2 管道模式 - Pipeline Patterns

### 7.2.1 基础管道

管道模式允许将多个操作串联起来，形成数据处理流水线：

```rust
// Rust 1.89 管道模式
use std::future::Future;

// 管道trait
trait Pipeline<T> {
    type Output;
    
    fn pipe<F, Fut, U>(self, f: F) -> Pipe<Self, F, T, U>
    where
        F: FnOnce(T) -> Fut,
        Fut: Future<Output = U>;
    
    fn execute(self) -> impl Future<Output = Self::Output>;
}

// 管道实现
struct Pipe<P, F, T, U> {
    prev: P,
    func: F,
    _phantom: std::marker::PhantomData<(T, U)>,
}

impl<P, F, T, U> Pipeline<T> for Pipe<P, F, T, U>
where
    P: Pipeline<T>,
    F: FnOnce(T) -> U,
{
    type Output = U;
    
    fn pipe<G, Fut, V>(self, g: G) -> Pipe<Self, G, U, V>
    where
        G: FnOnce(U) -> Fut,
        Fut: Future<Output = V>,
    {
        Pipe {
            prev: self,
            func: g,
            _phantom: std::marker::PhantomData,
        }
    }
    
    fn execute(self) -> impl Future<Output = Self::Output> {
        async move {
            let value = self.prev.execute().await;
            (self.func)(value).await
        }
    }
}

// 起始管道
struct StartPipeline<T> {
    value: T,
}

impl<T> Pipeline<T> for StartPipeline<T> {
    type Output = T;
    
    fn pipe<F, Fut, U>(self, f: F) -> Pipe<Self, F, T, U>
    where
        F: FnOnce(T) -> Fut,
        Fut: Future<Output = U>,
    {
        Pipe {
            prev: self,
            func: f,
            _phantom: std::marker::PhantomData,
        }
    }
    
    fn execute(self) -> impl Future<Output = Self::Output> {
        async move { self.value }
    }
}

// 管道构建器
fn pipeline<T>(value: T) -> StartPipeline<T> {
    StartPipeline { value }
}

// 异步管道操作
async fn fetch_data() -> String {
    tokio::time::sleep(Duration::from_millis(100)).await;
    "Raw data".to_string()
}

async fn process_data(data: String) -> String {
    tokio::time::sleep(Duration::from_millis(50)).await;
    format!("Processed: {}", data)
}

async fn validate_data(data: String) -> Result<String, ValidationError> {
    tokio::time::sleep(Duration::from_millis(25)).await;
    if data.contains("Processed") {
        Ok(data)
    } else {
        Err(ValidationError::InvalidData)
    }
}

async fn store_data(data: String) -> usize {
    tokio::time::sleep(Duration::from_millis(75)).await;
    data.len()
}

#[derive(Debug, thiserror::Error)]
pub enum ValidationError {
    #[error("Invalid data")]
    InvalidData,
}

// 管道使用示例
async fn pipeline_example() {
    let result = pipeline(())
        .pipe(|_| async { fetch_data().await })
        .pipe(|data| async { process_data(data).await })
        .pipe(|data| async { validate_data(data).await })
        .pipe(|data| async { 
            match data {
                Ok(valid_data) => store_data(valid_data).await,
                Err(e) => {
                    eprintln!("Validation error: {}", e);
                    0
                }
            }
        })
        .execute()
        .await;
    
    println!("Pipeline result: {}", result);
}
```

### 7.2.2 高级管道模式

```rust
// Rust 1.89 高级管道模式
use tokio_stream::{Stream, StreamExt};
use futures::stream::{self, TryStreamExt};

// 1. 流式管道 - 处理数据流
async fn stream_pipeline_example() {
    let numbers = stream::iter(0..1000);
    
    let processed_stream = numbers
        .map(|x| async move { x * 2 })
        .buffered(100)
        .filter(|&x| async move { x % 2 == 0 })
        .map(|x| format!("Processed: {}", x));
    
    let results: Vec<String> = processed_stream.collect().await;
    println!("Processed {} items", results.len());
}

// 2. 分支管道 - 根据条件分流
async fn branching_pipeline_example() {
    let data = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    
    let (even_results, odd_results) = tokio::join!(
        async {
            let even_stream = stream::iter(data.clone())
                .filter(|&x| async move { x % 2 == 0 })
                .map(|x| async move { process_even(x).await })
                .buffered(10);
            
            even_stream.collect::<Vec<_>>().await
        },
        async {
            let odd_stream = stream::iter(data)
                .filter(|&x| async move { x % 2 == 1 })
                .map(|x| async move { process_odd(x).await })
                .buffered(10);
            
            odd_stream.collect::<Vec<_>>().await
        }
    );
    
    println!("Even results: {:?}", even_results);
    println!("Odd results: {:?}", odd_results);
}

async fn process_even(x: i32) -> String {
    tokio::time::sleep(Duration::from_millis(10)).await;
    format!("Even: {}", x * 2)
}

async fn process_odd(x: i32) -> String {
    tokio::time::sleep(Duration::from_millis(15)).await;
    format!("Odd: {}", x * 3)
}

// 3. 聚合管道 - 收集和聚合结果
async fn aggregation_pipeline_example() {
    let numbers = stream::iter(0..1000);
    
    let result = numbers
        .map(|x| async move { x * x })
        .buffered(100)
        .fold(0, |acc, x| async move { acc + x })
        .await;
    
    println!("Sum of squares: {}", result);
}

// 4. 错误处理管道 - 优雅处理错误
async fn error_handling_pipeline_example() {
    let fallible_data = stream::iter(0..100)
        .map(|x| {
            if x % 10 == 0 {
                Err(format!("Error at {}", x))
            } else {
                Ok(x)
            }
        });
    
    let (successes, errors): (Vec<_>, Vec<_>) = fallible_data
        .partition(|result| result.is_ok());
    
    let success_count = successes.len();
    let error_count = errors.len();
    
    println!("Successfully processed {} items", success_count);
    println!("Encountered {} errors", error_count);
}
```

## 7.3 错误传播组合 - Error Propagation Composition

### 7.3.1 错误传播链

```rust
// Rust 1.89 错误传播组合
use std::error::Error;
use std::fmt;

// 自定义错误类型
#[derive(Debug)]
pub struct PipelineError {
    pub stage: String,
    pub cause: Box<dyn Error + Send + Sync>,
    pub context: String,
}

impl fmt::Display for PipelineError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Pipeline error at stage '{}': {} (Context: {})", 
               self.stage, self.cause, self.context)
    }
}

impl Error for PipelineError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(self.cause.as_ref())
    }
}

// 错误传播trait
trait ErrorPropagator<T, E> {
    type Output;
    
    fn propagate_error<F>(self, error_handler: F) -> Self::Output
    where
        F: FnOnce(E) -> Self::Output;
    
    fn map_error<F, E2>(self, error_mapper: F) -> Result<T, E2>
    where
        F: FnOnce(E) -> E2;
}

impl<T, E> ErrorPropagator<T, E> for Result<T, E> {
    type Output = Result<T, E>;
    
    fn propagate_error<F>(self, _error_handler: F) -> Self::Output {
        self
    }
    
    fn map_error<F, E2>(self, error_mapper: F) -> Result<T, E2>
    where
        F: FnOnce(E) -> E2,
    {
        self.map_err(error_mapper)
    }
}

// 错误恢复策略
trait ErrorRecoveryStrategy<E> {
    type Recovered;
    
    fn can_recover(&self, error: &E) -> bool;
    fn recover(&self, error: E) -> Self::Recovered;
}

// 重试策略
struct RetryStrategy {
    max_attempts: usize,
    backoff_delay: Duration,
}

impl ErrorRecoveryStrategy<Box<dyn Error + Send + Sync>> for RetryStrategy {
    type Recovered = ();
    
    fn can_recover(&self, _error: &Box<dyn Error + Send + Sync>) -> bool {
        true // 总是尝试恢复
    }
    
    fn recover(&self, _error: Box<dyn Error + Send + Sync>) -> Self::Recovered {
        // 在实际实现中，这里会记录错误并准备重试
    }
}

// 降级策略
struct FallbackStrategy<T> {
    fallback_value: T,
}

impl<T: Clone> ErrorRecoveryStrategy<Box<dyn Error + Send + Sync>> for FallbackStrategy<T> {
    type Recovered = T;
    
    fn can_recover(&self, _error: &Box<dyn Error + Send + Sync>) -> bool {
        true
    }
    
    fn recover(&self, _error: Box<dyn Error + Send + Sync>) -> Self::Recovered {
        self.fallback_value.clone()
    }
}

// 错误传播管道
async fn error_propagation_pipeline() -> Result<String, PipelineError> {
    let result = fetch_data()
        .await
        .map_err(|e| PipelineError {
            stage: "fetch".to_string(),
            cause: Box::new(e),
            context: "Failed to fetch data".to_string(),
        })?
        .pipe(|data| async move { 
            process_data(data).await
                .map_err(|e| PipelineError {
                    stage: "process".to_string(),
                    cause: Box::new(e),
                    context: "Failed to process data".to_string(),
                })
        })
        .pipe(|data| async move { 
            validate_data(data?).await
                .map_err(|e| PipelineError {
                    stage: "validate".to_string(),
                    cause: Box::new(e),
                    context: "Failed to validate data".to_string(),
                })
        })
        .execute()
        .await?;
    
    Ok(result)
}
```

### 7.3.2 错误组合器

```rust
// Rust 1.89 错误组合器
use std::future::Future;

// 1. 错误合并组合器 - 合并多个错误源
async fn merge_errors<F1, F2, Fut1, Fut2, T1, T2, E>(
    first: F1,
    second: F2,
) -> Result<(T1, T2), Vec<E>>
where
    F1: FnOnce() -> Fut1,
    F2: FnOnce() -> Fut2,
    Fut1: Future<Output = Result<T1, E>>,
    Fut2: Future<Output = Result<T2, E>>,
    E: Clone,
{
    let (result1, result2) = tokio::join!(first(), second());
    
    match (result1, result2) {
        (Ok(t1), Ok(t2)) => Ok((t1, t2)),
        (Err(e1), Ok(_)) => Err(vec![e1]),
        (Ok(_), Err(e2)) => Err(vec![e2]),
        (Err(e1), Err(e2)) => Err(vec![e1, e2]),
    }
}

// 2. 错误优先组合器 - 返回第一个错误
async fn first_error<F1, F2, Fut1, Fut2, T1, T2, E>(
    first: F1,
    second: F2,
) -> Result<(T1, T2), E>
where
    F1: FnOnce() -> Fut1,
    F2: FnOnce() -> Fut2,
    Fut1: Future<Output = Result<T1, E>>,
    Fut2: Future<Output = Result<T2, E>>,
{
    let (result1, result2) = tokio::join!(first(), second());
    
    let t1 = result1?;
    let t2 = result2?;
    
    Ok((t1, t2))
}

// 3. 错误恢复组合器 - 尝试恢复错误
async fn recover_errors<F, Fut, T, E, R>(
    operation: F,
    recovery_strategies: Vec<Box<dyn ErrorRecoveryStrategy<E, Recovered = T>>>,
) -> Result<T, E>
where
    F: FnOnce() -> Fut,
    Fut: Future<Output = Result<T, E>>,
{
    match operation().await {
        Ok(result) => Ok(result),
        Err(error) => {
            for strategy in recovery_strategies {
                if strategy.can_recover(&error) {
                    return Ok(strategy.recover(error));
                }
            }
            Err(error)
        }
    }
}

// 4. 错误聚合组合器 - 收集所有错误
async fn aggregate_errors<F, Fut, T, E>(
    operations: Vec<F>,
) -> Result<Vec<T>, Vec<E>>
where
    F: FnOnce() -> Fut + Send + 'static,
    Fut: Future<Output = Result<T, E>> + Send + 'static,
    T: Send + 'static,
    E: Send + 'static,
{
    let tasks: Vec<_> = operations
        .into_iter()
        .map(|op| tokio::spawn(async move { op().await }))
        .collect();
    
    let results = futures::future::join_all(tasks).await;
    
    let mut successes = Vec::new();
    let mut errors = Vec::new();
    
    for result in results {
        match result {
            Ok(Ok(value)) => successes.push(value),
            Ok(Err(error)) => errors.push(error),
            Err(_) => {
                // 任务执行失败，这通常不应该发生
                // 但在实际应用中可能需要处理
            }
        }
    }
    
    if errors.is_empty() {
        Ok(successes)
    } else {
        Err(errors)
    }
}
```

## 7.4 并发控制流组合 - Concurrent Control Flow Composition

### 7.4.1 并发组合模式

```rust
// Rust 1.89 并发控制流组合
use tokio::sync::{mpsc, oneshot, broadcast};
use std::sync::Arc;

// 1. 生产者-消费者模式
async fn producer_consumer_pattern() {
    let (tx, mut rx) = mpsc::channel::<String>(100);
    
    // 生产者任务
    let producer = tokio::spawn(async move {
        for i in 0..100 {
            let message = format!("Message {}", i);
            if tx.send(message).await.is_err() {
                break;
            }
            tokio::time::sleep(Duration::from_millis(10)).await;
        }
    });
    
    // 消费者任务
    let consumer = tokio::spawn(async move {
        while let Some(message) = rx.recv().await {
            println!("Received: {}", message);
            tokio::time::sleep(Duration::from_millis(5)).await;
        }
    });
    
    // 等待任务完成
    let _ = tokio::join!(producer, consumer);
}

// 2. 工作池模式
async fn worker_pool_pattern() {
    let (tx, mut rx) = mpsc::channel::<WorkItem>(100);
    let num_workers = 4;
    
    // 启动工作池
    let mut workers = Vec::new();
    for worker_id in 0..num_workers {
        let mut rx_clone = rx.clone();
        let worker = tokio::spawn(async move {
            while let Some(work) = rx_clone.recv().await {
                process_work_item(worker_id, work).await;
            }
        });
        workers.push(worker);
    }
    
    // 发送工作项
    for i in 0..20 {
        let work_item = WorkItem {
            id: i,
            data: format!("Data {}", i),
        };
        tx.send(work_item).await.unwrap();
    }
    
    // 关闭通道
    drop(tx);
    
    // 等待所有工作完成
    for worker in workers {
        worker.await.unwrap();
    }
}

#[derive(Debug)]
struct WorkItem {
    id: u32,
    data: String,
}

async fn process_work_item(worker_id: u32, work: WorkItem) {
    println!("Worker {} processing work item {}: {}", worker_id, work.id, work.data);
    tokio::time::sleep(Duration::from_millis(50)).await;
    println!("Worker {} completed work item {}", worker_id, work.id);
}

// 3. 发布-订阅模式
async fn pub_sub_pattern() {
    let (tx, _rx) = broadcast::channel::<String>(100);
    
    // 创建多个订阅者
    let mut subscribers = Vec::new();
    for subscriber_id in 0..3 {
        let mut rx = tx.subscribe();
        let subscriber = tokio::spawn(async move {
            while let Ok(message) = rx.recv().await {
                println!("Subscriber {} received: {}", subscriber_id, message);
            }
        });
        subscribers.push(subscriber);
    }
    
    // 发布消息
    for i in 0..10 {
        let message = format!("News {}", i);
        let _ = tx.send(message);
        tokio::time::sleep(Duration::from_millis(100)).await;
    }
    
    // 等待订阅者完成
    for subscriber in subscribers {
        let _ = subscriber.await;
    }
}

// 4. 请求-响应模式
async fn request_response_pattern() {
    let (tx, mut rx) = mpsc::channel::<Request>(100);
    
    // 处理器任务
    let processor = tokio::spawn(async move {
        while let Some(request) = rx.recv().await {
            let response = process_request(request).await;
            let _ = request.response_tx.send(response);
        }
    });
    
    // 发送请求
    let mut requests = Vec::new();
    for i in 0..5 {
        let (response_tx, response_rx) = oneshot::channel();
        let request = Request {
            id: i,
            data: format!("Request data {}", i),
            response_tx,
        };
        
        tx.send(request).await.unwrap();
        requests.push(response_rx);
    }
    
    // 等待响应
    for (i, response_rx) in requests.into_iter().enumerate() {
        match response_rx.await {
            Ok(response) => println!("Request {} response: {}", i, response),
            Err(_) => println!("Request {} failed", i),
        }
    }
    
    // 关闭通道
    drop(tx);
    processor.await.unwrap();
}

#[derive(Debug)]
struct Request {
    id: u32,
    data: String,
    response_tx: oneshot::Sender<String>,
}

async fn process_request(request: Request) -> String {
    tokio::time::sleep(Duration::from_millis(100)).await;
    format!("Processed: {}", request.data)
}
```

## 总结 - Summary

本章节完成了Rust控制流组合模式的理论和实践，包括：

1. **控制流组合器**: 基础组合器、高级组合器、错误处理组合器
2. **管道模式**: 基础管道、高级管道、流式管道、分支管道
3. **错误传播组合**: 错误传播链、错误组合器、错误恢复策略
4. **并发控制流组合**: 生产者-消费者、工作池、发布-订阅、请求-响应模式

这些组合模式为Rust程序提供了强大的控制流组合能力，使得复杂的异步操作和并发处理变得更加清晰和可维护。
