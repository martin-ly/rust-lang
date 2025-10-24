# 异步编程语义分析


## 📊 目录

- [概述](#概述)
- [1. 异步编程理论基础](#1-异步编程理论基础)
  - [1.1 异步编程概念](#11-异步编程概念)
  - [1.2 Rust异步编程哲学](#12-rust异步编程哲学)
- [2. Future特征语义](#2-future特征语义)
  - [2.1 Future特征定义](#21-future特征定义)
  - [2.2 Future组合](#22-future组合)
- [3. Async/Await语法](#3-asyncawait语法)
  - [3.1 Async函数](#31-async函数)
  - [3.2 Await表达式](#32-await表达式)
- [4. 异步运行时](#4-异步运行时)
  - [4.1 运行时概念](#41-运行时概念)
  - [4.2 Tokio运行时](#42-tokio运行时)
- [5. 任务调度](#5-任务调度)
  - [5.1 任务调度机制](#51-任务调度机制)
  - [5.2 工作窃取调度](#52-工作窃取调度)
- [6. 并发控制](#6-并发控制)
  - [6.1 异步并发原语](#61-异步并发原语)
  - [6.2 异步通道](#62-异步通道)
- [7. 异步编程模式](#7-异步编程模式)
  - [7.1 常见异步模式](#71-常见异步模式)
  - [7.2 高级异步模式](#72-高级异步模式)
- [8. 测试和验证](#8-测试和验证)
  - [8.1 异步测试](#81-异步测试)
- [9. 总结](#9-总结)


## 概述

本文档详细分析Rust异步编程系统的语义，包括Future特征、async/await语法、异步运行时、任务调度、并发控制和异步编程模式。

## 1. 异步编程理论基础

### 1.1 异步编程概念

**定义 1.1.1 (异步编程)**
异步编程是一种编程范式，允许程序在等待I/O操作或其他长时间运行的任务时继续执行其他工作，而不是阻塞等待。

**异步编程的核心特性**：

1. **非阻塞执行**：不会阻塞线程等待I/O完成
2. **并发处理**：可以同时处理多个异步任务
3. **资源效率**：使用少量线程处理大量并发任务
4. **可组合性**：异步操作可以组合成更复杂的异步流程

### 1.2 Rust异步编程哲学

**Rust异步编程原则**：

```rust
// Rust的异步编程基于Future特征
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 异步函数返回Future
async fn async_function() -> i32 {
    // 模拟异步操作
    std::thread::sleep(std::time::Duration::from_millis(100));
    42
}

// 使用async/await语法
async fn async_chain() -> i32 {
    let result1 = async_function().await;
    let result2 = async_function().await;
    result1 + result2
}

// 异步编程是零成本的
fn zero_cost_async() {
    // 编译后，async/await代码与手写的Future实现性能相同
    let future = async {
        let result = async_function().await;
        println!("Result: {}", result);
    };
}
```

## 2. Future特征语义

### 2.1 Future特征定义

**Future特征语义**：

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// Future特征定义
trait Future {
    type Output;
    
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}

// 基本Future实现
struct SimpleFuture {
    value: Option<i32>,
}

impl SimpleFuture {
    fn new(value: i32) -> Self {
        Self {
            value: Some(value),
        }
    }
}

impl Future for SimpleFuture {
    type Output = i32;
    
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if let Some(value) = self.value.take() {
            Poll::Ready(value)
        } else {
            Poll::Pending
        }
    }
}

// 使用Future
fn use_simple_future() {
    let future = SimpleFuture::new(42);
    // 在实际运行时中，future会被轮询直到完成
}

// 更复杂的Future实现
struct DelayedFuture {
    delay: std::time::Duration,
    start_time: Option<std::time::Instant>,
}

impl DelayedFuture {
    fn new(delay: std::time::Duration) -> Self {
        Self {
            delay,
            start_time: None,
        }
    }
}

impl Future for DelayedFuture {
    type Output = ();
    
    fn poll(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.start_time.is_none() {
            self.start_time = Some(std::time::Instant::now());
        }
        
        if let Some(start_time) = self.start_time {
            if start_time.elapsed() >= self.delay {
                Poll::Ready(())
            } else {
                Poll::Pending
            }
        } else {
            Poll::Pending
        }
    }
}
```

### 2.2 Future组合

**Future组合语义**：

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// 组合两个Future
struct CombinedFuture<A, B> {
    a: Option<A>,
    b: Option<B>,
}

impl<A, B> CombinedFuture<A, B>
where
    A: Future,
    B: Future,
{
    fn new(a: A, b: B) -> Self {
        Self {
            a: Some(a),
            b: Some(b),
        }
    }
}

impl<A, B> Future for CombinedFuture<A, B>
where
    A: Future,
    B: Future,
{
    type Output = (A::Output, B::Output);
    
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        let this = unsafe { self.as_mut().get_unchecked_mut() };
        
        if let (Some(mut a), Some(mut b)) = (this.a.take(), this.b.take()) {
            let a_pinned = unsafe { Pin::new_unchecked(&mut a) };
            let b_pinned = unsafe { Pin::new_unchecked(&mut b) };
            
            match (a_pinned.poll(cx), b_pinned.poll(cx)) {
                (Poll::Ready(a_result), Poll::Ready(b_result)) => {
                    Poll::Ready((a_result, b_result))
                }
                (Poll::Ready(a_result), Poll::Pending) => {
                    this.a = None;
                    this.b = Some(b);
                    Poll::Pending
                }
                (Poll::Pending, Poll::Ready(b_result)) => {
                    this.a = Some(a);
                    this.b = None;
                    Poll::Pending
                }
                (Poll::Pending, Poll::Pending) => {
                    this.a = Some(a);
                    this.b = Some(b);
                    Poll::Pending
                }
            }
        } else {
            Poll::Pending
        }
    }
}

// 使用组合Future
fn use_combined_future() {
    let future1 = SimpleFuture::new(42);
    let future2 = SimpleFuture::new(100);
    let combined = CombinedFuture::new(future1, future2);
    // 在实际运行时中，combined会被轮询直到两个Future都完成
}
```

## 3. Async/Await语法

### 3.1 Async函数

**Async函数语义**：

```rust
// 基本async函数
async fn basic_async_function() -> i32 {
    // 模拟异步操作
    std::thread::sleep(std::time::Duration::from_millis(100));
    42
}

// 带参数的async函数
async fn async_with_params(x: i32, y: i32) -> i32 {
    // 模拟异步计算
    std::thread::sleep(std::time::Duration::from_millis(50));
    x + y
}

// 返回Result的async函数
async fn async_result_function() -> Result<i32, String> {
    // 模拟可能失败的异步操作
    if rand::random::<bool>() {
        Ok(42)
    } else {
        Err("Async operation failed".to_string())
    }
}

// 使用async函数
fn use_async_functions() {
    let future1 = basic_async_function();
    let future2 = async_with_params(5, 3);
    let future3 = async_result_function();
    
    // 这些Future需要在运行时中执行
    println!("Futures created");
}

// Async块
fn async_blocks() {
    let future = async {
        let result1 = basic_async_function().await;
        let result2 = async_with_params(10, 20).await;
        result1 + result2
    };
    
    println!("Async block created");
}
```

### 3.2 Await表达式

**Await表达式语义**：

```rust
// 基本await使用
async fn await_basic() -> i32 {
    let future = basic_async_function();
    let result = future.await; // 等待Future完成
    result
}

// 链式await
async fn await_chain() -> i32 {
    let result1 = basic_async_function().await;
    let result2 = async_with_params(result1, 10).await;
    result2
}

// 并发await
async fn await_concurrent() -> (i32, i32) {
    let future1 = basic_async_function();
    let future2 = async_with_params(5, 3);
    
    // 并发执行两个Future
    let (result1, result2) = tokio::join!(future1, future2);
    (result1, result2)
}

// 条件await
async fn await_conditional() -> i32 {
    let condition = rand::random::<bool>();
    
    if condition {
        basic_async_function().await
    } else {
        async_with_params(1, 2).await
    }
}

// 循环await
async fn await_loop() -> Vec<i32> {
    let mut results = Vec::new();
    
    for i in 0..5 {
        let result = async_with_params(i, i * 2).await;
        results.push(result);
    }
    
    results
}

// 错误处理await
async fn await_error_handling() -> Result<i32, String> {
    match async_result_function().await {
        Ok(result) => Ok(result * 2),
        Err(e) => Err(format!("Error: {}", e)),
    }
}
```

## 4. 异步运行时

### 4.1 运行时概念

**异步运行时语义**：

```rust
// 简单的异步运行时
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;

struct SimpleRuntime {
    ready_queue: Arc<Mutex<VecDeque<Pin<Box<dyn Future<Output = ()> + Send>>>>>,
}

impl SimpleRuntime {
    fn new() -> Self {
        Self {
            ready_queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }
    
    fn spawn<F>(&self, future: F)
    where
        F: Future<Output = ()> + Send + 'static,
    {
        let future = Box::pin(future);
        self.ready_queue.lock().unwrap().push_back(future);
    }
    
    fn run(&self) {
        loop {
            let mut ready_queue = self.ready_queue.lock().unwrap();
            if ready_queue.is_empty() {
                break;
            }
            
            if let Some(mut future) = ready_queue.pop_front() {
                drop(ready_queue);
                
                let waker = Arc::new(SimpleWaker).into();
                let mut cx = Context::from_waker(&waker);
                
                match future.as_mut().poll(&mut cx) {
                    Poll::Ready(()) => {
                        // 任务完成
                    }
                    Poll::Pending => {
                        // 任务未完成，重新加入队列
                        self.ready_queue.lock().unwrap().push_back(future);
                    }
                }
            }
        }
    }
}

struct SimpleWaker;

impl std::task::Wake for SimpleWaker {
    fn wake(self: Arc<Self>) {
        // 简单的唤醒实现
    }
}

// 使用简单运行时
fn use_simple_runtime() {
    let runtime = SimpleRuntime::new();
    
    runtime.spawn(async {
        println!("Task 1 started");
        std::thread::sleep(std::time::Duration::from_millis(100));
        println!("Task 1 completed");
    });
    
    runtime.spawn(async {
        println!("Task 2 started");
        std::thread::sleep(std::time::Duration::from_millis(50));
        println!("Task 2 completed");
    });
    
    runtime.run();
}
```

### 4.2 Tokio运行时

**Tokio运行时语义**：

```rust
// 使用Tokio运行时
use tokio;

async fn tokio_example() {
    // 创建Tokio运行时
    let rt = tokio::runtime::Runtime::new().unwrap();
    
    // 在运行时中执行异步任务
    rt.block_on(async {
        let result = basic_async_function().await;
        println!("Result: {}", result);
    });
}

// 多线程运行时
async fn multi_thread_runtime() {
    let rt = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(4)
        .enable_all()
        .build()
        .unwrap();
    
    rt.block_on(async {
        let handles: Vec<_> = (0..10)
            .map(|i| {
                tokio::spawn(async move {
                    println!("Task {} started", i);
                    std::thread::sleep(std::time::Duration::from_millis(100));
                    println!("Task {} completed", i);
                    i
                })
            })
            .collect();
        
        let results: Vec<_> = futures::future::join_all(handles).await;
        println!("All tasks completed: {:?}", results);
    });
}

// 单线程运行时
async fn single_thread_runtime() {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap();
    
    rt.block_on(async {
        let result = basic_async_function().await;
        println!("Single thread result: {}", result);
    });
}
```

## 5. 任务调度

### 5.1 任务调度机制

**任务调度语义**：

```rust
use tokio;
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;

// 简单的任务调度器
struct TaskScheduler {
    tasks: Arc<Mutex<VecDeque<Box<dyn FnOnce() + Send>>>>,
}

impl TaskScheduler {
    fn new() -> Self {
        Self {
            tasks: Arc::new(Mutex::new(VecDeque::new())),
        }
    }
    
    fn schedule<F>(&self, task: F)
    where
        F: FnOnce() + Send + 'static,
    {
        self.tasks.lock().unwrap().push_back(Box::new(task));
    }
    
    fn run(&self) {
        loop {
            let task = self.tasks.lock().unwrap().pop_front();
            if let Some(task) = task {
                task();
            } else {
                break;
            }
        }
    }
}

// 使用任务调度器
fn use_task_scheduler() {
    let scheduler = TaskScheduler::new();
    
    scheduler.schedule(|| {
        println!("Task 1 executed");
    });
    
    scheduler.schedule(|| {
        println!("Task 2 executed");
    });
    
    scheduler.run();
}

// 优先级任务调度
struct PriorityTaskScheduler {
    high_priority: Arc<Mutex<VecDeque<Box<dyn FnOnce() + Send>>>>,
    low_priority: Arc<Mutex<VecDeque<Box<dyn FnOnce() + Send>>>>,
}

impl PriorityTaskScheduler {
    fn new() -> Self {
        Self {
            high_priority: Arc::new(Mutex::new(VecDeque::new())),
            low_priority: Arc::new(Mutex::new(VecDeque::new())),
        }
    }
    
    fn schedule_high<F>(&self, task: F)
    where
        F: FnOnce() + Send + 'static,
    {
        self.high_priority.lock().unwrap().push_back(Box::new(task));
    }
    
    fn schedule_low<F>(&self, task: F)
    where
        F: FnOnce() + Send + 'static,
    {
        self.low_priority.lock().unwrap().push_back(Box::new(task));
    }
    
    fn run(&self) {
        loop {
            // 优先执行高优先级任务
            if let Some(task) = self.high_priority.lock().unwrap().pop_front() {
                task();
                continue;
            }
            
            // 然后执行低优先级任务
            if let Some(task) = self.low_priority.lock().unwrap().pop_front() {
                task();
                continue;
            }
            
            break;
        }
    }
}
```

### 5.2 工作窃取调度

**工作窃取调度语义**：

```rust
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;
use std::thread;

// 工作窃取队列
struct WorkStealingQueue<T> {
    queue: Arc<Mutex<VecDeque<T>>>,
}

impl<T> WorkStealingQueue<T> {
    fn new() -> Self {
        Self {
            queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }
    
    fn push(&self, item: T) {
        self.queue.lock().unwrap().push_back(item);
    }
    
    fn pop(&self) -> Option<T> {
        self.queue.lock().unwrap().pop_front()
    }
    
    fn steal(&self) -> Option<T> {
        self.queue.lock().unwrap().pop_back()
    }
}

// 工作窃取调度器
struct WorkStealingScheduler {
    queues: Vec<WorkStealingQueue<Box<dyn FnOnce() + Send>>>,
}

impl WorkStealingScheduler {
    fn new(num_workers: usize) -> Self {
        let mut queues = Vec::new();
        for _ in 0..num_workers {
            queues.push(WorkStealingQueue::new());
        }
        
        Self { queues }
    }
    
    fn submit(&self, worker_id: usize, task: Box<dyn FnOnce() + Send>) {
        self.queues[worker_id].push(task);
    }
    
    fn run(&self, worker_id: usize) {
        loop {
            // 尝试从自己的队列获取任务
            if let Some(task) = self.queues[worker_id].pop() {
                task();
                continue;
            }
            
            // 尝试从其他队列窃取任务
            let mut stolen = false;
            for i in 0..self.queues.len() {
                if i != worker_id {
                    if let Some(task) = self.queues[i].steal() {
                        task();
                        stolen = true;
                        break;
                    }
                }
            }
            
            if !stolen {
                // 没有任务可执行，退出
                break;
            }
        }
    }
}

// 使用工作窃取调度器
fn use_work_stealing_scheduler() {
    let scheduler = WorkStealingScheduler::new(4);
    
    // 提交任务到不同工作线程
    for i in 0..10 {
        let worker_id = i % 4;
        scheduler.submit(worker_id, Box::new(move || {
            println!("Task {} executed on worker {}", i, worker_id);
        }));
    }
    
    // 启动工作线程
    let handles: Vec<_> = (0..4)
        .map(|worker_id| {
            let scheduler = &scheduler;
            thread::spawn(move || {
                scheduler.run(worker_id);
            })
        })
        .collect();
    
    // 等待所有工作线程完成
    for handle in handles {
        handle.join().unwrap();
    }
}
```

## 6. 并发控制

### 6.1 异步并发原语

**异步并发原语语义**：

```rust
use tokio::sync::{Mutex, RwLock, Semaphore};
use std::sync::Arc;

// 异步互斥锁
async fn async_mutex_example() {
    let mutex = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..10 {
        let mutex = Arc::clone(&mutex);
        let handle = tokio::spawn(async move {
            let mut value = mutex.lock().await;
            *value += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.await.unwrap();
    }
    
    let final_value = *mutex.lock().await;
    println!("Final value: {}", final_value);
}

// 异步读写锁
async fn async_rwlock_example() {
    let rwlock = Arc::new(RwLock::new(vec![1, 2, 3, 4, 5]));
    let mut handles = vec![];
    
    // 读取者
    for i in 0..5 {
        let rwlock = Arc::clone(&rwlock);
        let handle = tokio::spawn(async move {
            let data = rwlock.read().await;
            println!("Reader {}: {:?}", i, *data);
        });
        handles.push(handle);
    }
    
    // 写入者
    let rwlock = Arc::clone(&rwlock);
    let handle = tokio::spawn(async move {
        let mut data = rwlock.write().await;
        data.push(6);
        println!("Writer: {:?}", *data);
    });
    handles.push(handle);
    
    for handle in handles {
        handle.await.unwrap();
    }
}

// 异步信号量
async fn async_semaphore_example() {
    let semaphore = Arc::new(Semaphore::new(3)); // 最多3个并发
    let mut handles = vec![];
    
    for i in 0..10 {
        let semaphore = Arc::clone(&semaphore);
        let handle = tokio::spawn(async move {
            let _permit = semaphore.acquire().await.unwrap();
            println!("Task {} acquired permit", i);
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            println!("Task {} released permit", i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.await.unwrap();
    }
}
```

### 6.2 异步通道

**异步通道语义**：

```rust
use tokio::sync::mpsc;

// 基本异步通道
async fn basic_async_channel() {
    let (tx, mut rx) = mpsc::channel(100);
    
    // 发送者任务
    let sender = tokio::spawn(async move {
        for i in 0..10 {
            tx.send(i).await.unwrap();
            tokio::time::sleep(tokio::time::Duration::from_millis(50)).await;
        }
    });
    
    // 接收者任务
    let receiver = tokio::spawn(async move {
        while let Some(value) = rx.recv().await {
            println!("Received: {}", value);
        }
    });
    
    sender.await.unwrap();
    receiver.await.unwrap();
}

// 多生产者单消费者
async fn multi_producer_channel() {
    let (tx, mut rx) = mpsc::channel(100);
    let mut handles = vec![];
    
    // 多个发送者
    for i in 0..3 {
        let tx = tx.clone();
        let handle = tokio::spawn(async move {
            for j in 0..5 {
                tx.send(format!("Producer {}: {}", i, j)).await.unwrap();
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            }
        });
        handles.push(handle);
    }
    
    // 接收者
    let receiver = tokio::spawn(async move {
        while let Some(message) = rx.recv().await {
            println!("Received: {}", message);
        }
    });
    
    // 等待所有发送者完成
    for handle in handles {
        handle.await.unwrap();
    }
    
    // 关闭通道
    drop(tx);
    
    receiver.await.unwrap();
}

// 广播通道
use tokio::sync::broadcast;

async fn broadcast_channel() {
    let (tx, mut rx1) = broadcast::channel(100);
    let mut rx2 = tx.subscribe();
    
    // 发送者
    let sender = tokio::spawn(async move {
        for i in 0..5 {
            tx.send(format!("Message {}", i)).unwrap();
            tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
        }
    });
    
    // 接收者1
    let receiver1 = tokio::spawn(async move {
        while let Ok(message) = rx1.recv().await {
            println!("Receiver 1: {}", message);
        }
    });
    
    // 接收者2
    let receiver2 = tokio::spawn(async move {
        while let Ok(message) = rx2.recv().await {
            println!("Receiver 2: {}", message);
        }
    });
    
    sender.await.unwrap();
    receiver1.await.unwrap();
    receiver2.await.unwrap();
}
```

## 7. 异步编程模式

### 7.1 常见异步模式

**异步编程模式语义**：

```rust
// 超时模式
async fn timeout_pattern() {
    let future = basic_async_function();
    
    match tokio::time::timeout(
        tokio::time::Duration::from_millis(50),
        future
    ).await {
        Ok(result) => println!("Completed: {}", result),
        Err(_) => println!("Timeout occurred"),
    }
}

// 重试模式
async fn retry_pattern() {
    let mut attempts = 0;
    let max_attempts = 3;
    
    loop {
        match async_result_function().await {
            Ok(result) => {
                println!("Success: {}", result);
                break;
            }
            Err(e) => {
                attempts += 1;
                if attempts >= max_attempts {
                    println!("Failed after {} attempts: {}", max_attempts, e);
                    break;
                }
                println!("Attempt {} failed: {}", attempts, e);
                tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
            }
        }
    }
}

// 并发限制模式
async fn concurrency_limit_pattern() {
    let semaphore = Arc::new(Semaphore::new(3));
    let mut handles = vec![];
    
    for i in 0..10 {
        let semaphore = Arc::clone(&semaphore);
        let handle = tokio::spawn(async move {
            let _permit = semaphore.acquire().await.unwrap();
            println!("Task {} started", i);
            tokio::time::sleep(tokio::time::Duration::from_millis(200)).await;
            println!("Task {} completed", i);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.await.unwrap();
    }
}

// 取消模式
use tokio::sync::oneshot;

async fn cancellation_pattern() {
    let (cancel_tx, cancel_rx) = oneshot::channel();
    
    let task = tokio::spawn(async move {
        loop {
            tokio::select! {
                _ = tokio::time::sleep(tokio::time::Duration::from_millis(100)) => {
                    println!("Task working...");
                }
                _ = cancel_rx => {
                    println!("Task cancelled");
                    break;
                }
            }
        }
    });
    
    // 等待一段时间后取消任务
    tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
    let _ = cancel_tx.send(());
    
    task.await.unwrap();
}
```

### 7.2 高级异步模式

**高级异步模式语义**：

```rust
// 异步资源池
use std::collections::HashMap;
use tokio::sync::Mutex;

struct AsyncResourcePool<T> {
    resources: Arc<Mutex<HashMap<String, T>>>,
    max_size: usize,
}

impl<T> AsyncResourcePool<T> {
    fn new(max_size: usize) -> Self {
        Self {
            resources: Arc::new(Mutex::new(HashMap::new())),
            max_size,
        }
    }
    
    async fn acquire(&self, key: String) -> Option<T> {
        let mut resources = self.resources.lock().await;
        resources.remove(&key)
    }
    
    async fn release(&self, key: String, resource: T) {
        let mut resources = self.resources.lock().await;
        if resources.len() < self.max_size {
            resources.insert(key, resource);
        }
    }
}

// 异步缓存
use std::collections::HashMap;
use std::time::{Duration, Instant};

struct AsyncCache<K, V> {
    cache: Arc<Mutex<HashMap<K, (V, Instant)>>>,
    ttl: Duration,
}

impl<K, V> AsyncCache<K, V>
where
    K: Clone + Eq + std::hash::Hash,
    V: Clone,
{
    fn new(ttl: Duration) -> Self {
        Self {
            cache: Arc::new(Mutex::new(HashMap::new())),
            ttl,
        }
    }
    
    async fn get(&self, key: &K) -> Option<V> {
        let mut cache = self.cache.lock().await;
        if let Some((value, timestamp)) = cache.get(key) {
            if timestamp.elapsed() < self.ttl {
                return Some(value.clone());
            } else {
                cache.remove(key);
            }
        }
        None
    }
    
    async fn set(&self, key: K, value: V) {
        let mut cache = self.cache.lock().await;
        cache.insert(key, (value, Instant::now()));
    }
}

// 异步事件循环
use tokio::sync::mpsc;

struct AsyncEventLoop {
    tx: mpsc::Sender<Box<dyn FnOnce() + Send>>,
}

impl AsyncEventLoop {
    fn new() -> Self {
        let (tx, mut rx) = mpsc::channel(100);
        
        tokio::spawn(async move {
            while let Some(event) = rx.recv().await {
                event();
            }
        });
        
        Self { tx }
    }
    
    async fn post<F>(&self, event: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let _ = self.tx.send(Box::new(event)).await;
    }
}

// 使用异步事件循环
async fn use_async_event_loop() {
    let event_loop = AsyncEventLoop::new();
    
    event_loop.post(|| {
        println!("Event 1 executed");
    }).await;
    
    event_loop.post(|| {
        println!("Event 2 executed");
    }).await;
    
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
}
```

## 8. 测试和验证

### 8.1 异步测试

**异步测试框架**：

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_basic_async_function() {
        let result = basic_async_function().await;
        assert_eq!(result, 42);
    }

    #[tokio::test]
    async fn test_async_with_params() {
        let result = async_with_params(5, 3).await;
        assert_eq!(result, 8);
    }

    #[tokio::test]
    async fn test_await_chain() {
        let result = await_chain().await;
        assert_eq!(result, 84); // 42 + 42
    }

    #[tokio::test]
    async fn test_await_concurrent() {
        let (result1, result2) = await_concurrent().await;
        assert_eq!(result1, 42);
        assert_eq!(result2, 8);
    }

    #[tokio::test]
    async fn test_async_mutex() {
        let mutex = Arc::new(Mutex::new(0));
        let mut handles = vec![];
        
        for _ in 0..10 {
            let mutex = Arc::clone(&mutex);
            let handle = tokio::spawn(async move {
                let mut value = mutex.lock().await;
                *value += 1;
            });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.await.unwrap();
        }
        
        let final_value = *mutex.lock().await;
        assert_eq!(final_value, 10);
    }

    #[tokio::test]
    async fn test_async_channel() {
        let (tx, mut rx) = mpsc::channel(100);
        
        let sender = tokio::spawn(async move {
            for i in 0..5 {
                tx.send(i).await.unwrap();
            }
        });
        
        let mut received = Vec::new();
        while let Some(value) = rx.recv().await {
            received.push(value);
        }
        
        sender.await.unwrap();
        assert_eq!(received, vec![0, 1, 2, 3, 4]);
    }

    #[tokio::test]
    async fn test_timeout_pattern() {
        let future = tokio::time::sleep(tokio::time::Duration::from_millis(200));
        
        match tokio::time::timeout(
            tokio::time::Duration::from_millis(50),
            future
        ).await {
            Ok(_) => panic!("Should have timed out"),
            Err(_) => {
                // Expected timeout
            }
        }
    }

    #[tokio::test]
    async fn test_async_cache() {
        let cache = AsyncCache::new(Duration::from_millis(100));
        
        cache.set("key1".to_string(), "value1".to_string()).await;
        
        let value = cache.get(&"key1".to_string()).await;
        assert_eq!(value, Some("value1".to_string()));
        
        // Wait for TTL to expire
        tokio::time::sleep(Duration::from_millis(150)).await;
        
        let value = cache.get(&"key1".to_string()).await;
        assert_eq!(value, None);
    }
}
```

## 9. 总结

Rust的异步编程系统提供了强大而高效的并发处理能力。通过Future特征、async/await语法、异步运行时等机制，Rust实现了零成本的异步编程抽象。

异步编程是Rust语言的重要特性，它通过编译时优化和运行时效率，为开发者提供了处理高并发场景的最佳实践。理解异步编程的语义对于编写高性能、可扩展的Rust程序至关重要。

异步编程系统体现了Rust在性能和表达力之间的平衡，为开发者提供了既高效又安全的并发处理工具，是现代Rust编程中不可或缺的重要组成部分。
