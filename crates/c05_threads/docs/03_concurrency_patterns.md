# 并发编程模式

## 目录

- [并发编程模式](#并发编程模式)
  - [目录](#目录)
  - [概述](#概述)
  - [异步编程模式](#异步编程模式)
    - [1. 异步迭代器模式](#1-异步迭代器模式)
    - [2. 异步闭包模式](#2-异步闭包模式)
  - [工作窃取模式](#工作窃取模式)
    - [1. 高性能工作窃取调度器](#1-高性能工作窃取调度器)
    - [2. 自适应工作分配](#2-自适应工作分配)
  - [分治并发模式](#分治并发模式)
    - [1. 并行分治算法](#1-并行分治算法)
    - [2. 流水线并发模式](#2-流水线并发模式)
  - [响应式并发模式](#响应式并发模式)
    - [1. 事件驱动并发](#1-事件驱动并发)
  - [总结](#总结)

## 概述

本文档介绍了Rust 1.89中支持的现代并发编程模式，包括异步编程、工作窃取、分治算法等高级并发技术。

## 异步编程模式

### 1. 异步迭代器模式

Rust 1.89稳定了异步迭代器特性，使得流式数据处理更加高效：

```rust
use std::async_iter::AsyncIterator;
use std::pin::Pin;
use std::task::{Context, Poll};

pub struct AsyncDataStream {
    data: Vec<u64>,
    index: usize,
}

impl AsyncIterator for AsyncDataStream {
    type Item = u64;

    fn poll_next(mut self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        if self.index < self.data.len() {
            let item = self.data[self.index];
            self.index += 1;
            Poll::Ready(Some(item))
        } else {
            Poll::Ready(None)
        }
    }
}

// 使用异步迭代器
async fn process_stream() {
    let mut stream = AsyncDataStream {
        data: vec![1, 2, 3, 4, 5],
        index: 0,
    };
    
    while let Some(item) = stream.next().await {
        println!("Processing: {}", item);
    }
}
```

### 2. 异步闭包模式

利用Rust 1.89改进的异步闭包语法：

```rust
use tokio::time::{sleep, Duration};

pub struct AsyncTaskProcessor {
    tasks: Vec<Box<dyn Fn(u64) -> std::pin::Pin<Box<dyn std::future::Future<Output = u64> + Send>> + Send>>,
}

impl AsyncTaskProcessor {
    pub fn new() -> Self {
        Self { tasks: Vec::new() }
    }
    
    pub fn add_task<F>(&mut self, task: F)
    where
        F: Fn(u64) -> std::pin::Pin<Box<dyn std::future::Future<Output = u64> + Send>> + Send + 'static,
    {
        self.tasks.push(Box::new(task));
    }
    
    pub async fn execute_all(&self, input: u64) -> Vec<u64> {
        let mut futures = Vec::new();
        
        for task in &self.tasks {
            let future = task(input);
            futures.push(future);
        }
        
        let results = futures::future::join_all(futures).await;
        results
    }
}

// 使用示例
async fn example_usage() {
    let mut processor = AsyncTaskProcessor::new();
    
    // 添加异步任务
    processor.add_task(|x| {
        Box::pin(async move {
            sleep(Duration::from_millis(100)).await;
            x * 2
        })
    });
    
    processor.add_task(|x| {
        Box::pin(async move {
            sleep(Duration::from_millis(50)).await;
            x + 10
        })
    });
    
    let results = processor.execute_all(5).await;
    println!("Results: {:?}", results);
}
```

## 工作窃取模式

### 1. 高性能工作窃取调度器

```rust
use std::sync::Arc;
use crossbeam_deque::{Stealer, Worker};
use parking_lot::Mutex;

pub struct WorkStealingScheduler {
    workers: Vec<Worker<Task>>,
    stealers: Vec<Stealer<Task>>,
    global_queue: Arc<Mutex<Vec<Task>>>,
}

impl WorkStealingScheduler {
    pub fn new(num_workers: usize) -> Self {
        let mut workers = Vec::with_capacity(num_workers);
        let mut stealers = Vec::with_capacity(num_workers);
        
        for _ in 0..num_workers {
            let worker = Worker::new_fifo();
            let stealer = worker.stealer();
            workers.push(worker);
            stealers.push(stealer);
        }
        
        Self {
            workers,
            stealers,
            global_queue: Arc::new(Mutex::new(Vec::new())),
        }
    }
    
    pub fn submit(&self, task: Task) {
        // 优先放入本地队列，如果满了则放入全局队列
        if let Some(worker) = self.workers.first() {
            if worker.is_empty() {
                worker.push(task);
            } else {
                self.global_queue.lock().push(task);
            }
        }
    }
    
    pub fn steal_work(&self, worker_id: usize) -> Option<Task> {
        // 尝试从其他worker窃取工作
        for (i, stealer) in self.stealers.iter().enumerate() {
            if i != worker_id {
                if let Some(task) = stealer.steal().success() {
                    return Some(task);
                }
            }
        }
        
        // 从全局队列获取工作
        self.global_queue.lock().pop()
    }
}

#[derive(Debug, Clone)]
pub struct Task {
    pub id: u64,
    pub payload: Vec<u8>,
}
```

### 2. 自适应工作分配

```rust
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

pub struct AdaptiveWorkDistributor {
    worker_loads: Vec<AtomicU64>,
    last_steal_times: Vec<AtomicU64>,
    steal_threshold: Duration,
}

impl AdaptiveWorkDistributor {
    pub fn new(num_workers: usize) -> Self {
        Self {
            worker_loads: (0..num_workers).map(|_| AtomicU64::new(0)).collect(),
            last_steal_times: (0..num_workers).map(|_| AtomicU64::new(0)).collect(),
            steal_threshold: Duration::from_millis(10),
        }
    }
    
    pub fn should_steal(&self, worker_id: usize) -> bool {
        let current_load = self.worker_loads[worker_id].load(Ordering::Relaxed);
        let last_steal = self.last_steal_times[worker_id].load(Ordering::Relaxed);
        let now = Instant::now().duration_since(Instant::UNIX_EPOCH).unwrap().as_millis() as u64;
        
        // 如果负载低且距离上次窃取时间足够长，则允许窃取
        current_load < 5 && (now - last_steal) > self.steal_threshold.as_millis() as u64
    }
    
    pub fn update_load(&self, worker_id: usize, load: u64) {
        self.worker_loads[worker_id].store(load, Ordering::Relaxed);
    }
    
    pub fn record_steal(&self, worker_id: usize) {
        let now = Instant::now().duration_since(Instant::UNIX_EPOCH).unwrap().as_millis() as u64;
        self.last_steal_times[worker_id].store(now, Ordering::Relaxed);
    }
}
```

## 分治并发模式

### 1. 并行分治算法

```rust
use rayon::prelude::*;

pub struct ParallelDivideAndConquer;

impl ParallelDivideAndConquer {
    pub fn parallel_merge_sort<T: Ord + Send + Sync>(data: &mut [T]) {
        if data.len() <= 1 {
            return;
        }
        
        let mid = data.len() / 2;
        let (left, right) = data.split_at_mut(mid);
        
        // 并行排序左右两部分
        rayon::join(
            || Self::parallel_merge_sort(left),
            || Self::parallel_merge_sort(right),
        );
        
        // 合并结果
        Self::merge(data, mid);
    }
    
    fn merge<T: Ord>(data: &mut [T], mid: usize) {
        let mut temp = Vec::with_capacity(data.len());
        let mut left_idx = 0;
        let mut right_idx = mid;
        
        while left_idx < mid && right_idx < data.len() {
            if data[left_idx] <= data[right_idx] {
                temp.push(std::mem::replace(&mut data[left_idx], unsafe { std::mem::zeroed() }));
                left_idx += 1;
            } else {
                temp.push(std::mem::replace(&mut data[right_idx], unsafe { std::mem::zeroed() }));
                right_idx += 1;
            }
        }
        
        // 复制剩余元素
        while left_idx < mid {
            temp.push(std::mem::replace(&mut data[left_idx], unsafe { std::mem::zeroed() }));
            left_idx += 1;
        }
        
        while right_idx < data.len() {
            temp.push(std::mem::replace(&mut data[right_idx], unsafe { std::mem::zeroed() }));
            right_idx += 1;
        }
        
        // 将排序后的数据复制回原数组
        for (i, item) in temp.into_iter().enumerate() {
            data[i] = item;
        }
    }
    
    pub fn parallel_reduce<T, F>(data: &[T], identity: T, op: F) -> T
    where
        T: Send + Sync + Clone,
        F: Fn(T, T) -> T + Send + Sync,
    {
        if data.len() <= 1 {
            return data.first().cloned().unwrap_or(identity);
        }
        
        let mid = data.len() / 2;
        let (left, right) = data.split_at(mid);
        
        let (left_result, right_result) = rayon::join(
            || Self::parallel_reduce(left, identity.clone(), &op),
            || Self::parallel_reduce(right, identity, &op),
        );
        
        op(left_result, right_result)
    }
}
```

### 2. 流水线并发模式

```rust
use std::sync::mpsc;
use std::thread;

pub struct PipelineStage<T> {
    input: mpsc::Receiver<T>,
    output: mpsc::Sender<T>,
    processor: Box<dyn Fn(T) -> T + Send>,
}

impl<T: Send + 'static> PipelineStage<T> {
    pub fn new(
        input: mpsc::Receiver<T>,
        output: mpsc::Sender<T>,
        processor: impl Fn(T) -> T + Send + 'static,
    ) -> Self {
        Self {
            input,
            output,
            processor: Box::new(processor),
        }
    }
    
    pub fn run(mut self) {
        thread::spawn(move || {
            while let Ok(item) = self.input.recv() {
                let processed = (self.processor)(item);
                if self.output.send(processed).is_err() {
                    break;
                }
            }
        });
    }
}

pub struct Pipeline<T> {
    stages: Vec<PipelineStage<T>>,
    input: mpsc::Sender<T>,
    output: mpsc::Receiver<T>,
}

impl<T: Send + 'static> Pipeline<T> {
    pub fn new(num_stages: usize, processor: impl Fn(T) -> T + Send + Clone + 'static) -> Self {
        let (input, mut prev_receiver) = mpsc::channel();
        let mut stages = Vec::new();
        
        for _ in 0..num_stages {
            let (sender, receiver) = mpsc::channel();
            let stage = PipelineStage::new(prev_receiver, sender, processor.clone());
            stages.push(stage);
            prev_receiver = receiver;
        }
        
        let output = prev_receiver;
        
        Self {
            stages,
            input,
            output,
        }
    }
    
    pub fn start(mut self) -> (mpsc::Sender<T>, mpsc::Receiver<T>) {
        for stage in self.stages.drain(..) {
            stage.run();
        }
        
        (self.input, self.output)
    }
}

// 使用示例
pub fn example_pipeline() {
    let pipeline = Pipeline::new(3, |x: u64| x * 2 + 1);
    let (input, output) = pipeline.start();
    
    // 发送数据
    for i in 0..10 {
        input.send(i).unwrap();
    }
    drop(input); // 关闭输入通道
    
    // 接收处理结果
    for result in output {
        println!("Pipeline result: {}", result);
    }
}
```

## 响应式并发模式

### 1. 事件驱动并发

```rust
use std::collections::HashMap;
use std::sync::{Arc, Mutex};
use tokio::sync::mpsc;

#[derive(Debug, Clone)]
pub enum Event {
    DataReceived { id: u64, data: Vec<u8> },
    TimerExpired { timer_id: u64 },
    UserAction { action: String },
}

pub struct EventHandler {
    handlers: HashMap<String, Box<dyn Fn(Event) + Send + Sync>>,
}

impl EventHandler {
    pub fn new() -> Self {
        Self {
            handlers: HashMap::new(),
        }
    }
    
    pub fn register_handler<F>(&mut self, event_type: &str, handler: F)
    where
        F: Fn(Event) + Send + Sync + 'static,
    {
        self.handlers.insert(event_type.to_string(), Box::new(handler));
    }
    
    pub fn handle_event(&self, event: Event) {
        let event_type = match &event {
            Event::DataReceived { .. } => "data_received",
            Event::TimerExpired { .. } => "timer_expired",
            Event::UserAction { .. } => "user_action",
        };
        
        if let Some(handler) = self.handlers.get(event_type) {
            handler(event);
        }
    }
}

pub struct EventLoop {
    event_queue: mpsc::Receiver<Event>,
    handler: Arc<Mutex<EventHandler>>,
}

impl EventLoop {
    pub async fn run(mut self) {
        while let Some(event) = self.event_queue.recv().await {
            let handler = self.handler.lock().unwrap();
            handler.handle_event(event);
        }
    }
}
```

## 总结

Rust 1.89的并发编程模式提供了：

1. **异步编程**: 稳定的异步迭代器和改进的异步闭包
2. **工作窃取**: 高性能的工作窃取调度器和自适应分配
3. **分治算法**: 并行分治和流水线处理
4. **响应式编程**: 事件驱动的并发处理

这些模式充分利用了Rust 1.89的新特性，提供了高效、安全的并发编程解决方案。
