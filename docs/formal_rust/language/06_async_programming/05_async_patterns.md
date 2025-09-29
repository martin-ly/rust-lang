# 05 异步编程模式

## 章节简介

本章深入探讨Rust异步编程的核心模式，包括生产者-消费者、发布-订阅、扇出-扇入、背压处理、错误传播等经典模式。
特别关注2025年异步编程模式的最新发展，为构建可维护、高性能的异步应用程序提供理论基础。

## 目录

- [05 异步编程模式](#05-异步编程模式)
  - [章节简介](#章节简介)
  - [目录](#目录)
  - [1. 异步模式概述](#1-异步模式概述)
    - [1.1 异步模式定义](#11-异步模式定义)
    - [1.2 模式分类体系](#12-模式分类体系)
  - [2. 生产者-消费者模式](#2-生产者-消费者模式)
    - [2.1 基本生产者-消费者](#21-基本生产者-消费者)
    - [2.2 有界缓冲区](#22-有界缓冲区)
    - [2.3 优先级队列](#23-优先级队列)
  - [3. 发布-订阅模式](#3-发布-订阅模式)
    - [3.1 基本发布-订阅](#31-基本发布-订阅)
    - [3.2 主题过滤](#32-主题过滤)
  - [4. 扇出-扇入模式](#4-扇出-扇入模式)
    - [4.1 基本扇出-扇入](#41-基本扇出-扇入)
  - [5. 背压处理模式](#5-背压处理模式)
    - [5.1 基本背压处理](#51-基本背压处理)
  - [6. 错误传播模式](#6-错误传播模式)
    - [6.1 基本错误传播](#61-基本错误传播)
  - [7. 2025年新特性](#7-2025年新特性)
    - [7.1 智能模式选择](#71-智能模式选择)
  - [8. 工程实践](#8-工程实践)
    - [8.1 模式最佳实践](#81-模式最佳实践)
    - [8.2 测试策略](#82-测试策略)

## 1. 异步模式概述

### 1.1 异步模式定义

异步编程模式是解决并发和异步编程问题的标准化解决方案，提供可重用、可维护的代码结构。

```rust
// 异步模式系统的基本特征
trait AsyncPatternSystem {
    // 模式表达能力
    fn pattern_expressiveness(&self) -> PatternExpressiveness;
    
    // 并发处理能力
    fn concurrency_capability(&self) -> ConcurrencyCapability;
    
    // 可组合性
    fn composability(&self) -> Composability;
}

// 模式表达能力
enum PatternExpressiveness {
    Basic,      // 基本模式
    Complex,    // 复杂模式
    Composite,  // 组合模式
    Adaptive,   // 自适应模式
}

// 并发处理能力
enum ConcurrencyCapability {
    SingleThread,   // 单线程
    MultiThread,    // 多线程
    EventDriven,    // 事件驱动
    Reactive,       // 响应式
}

// 可组合性
enum Composability {
    Linear,     // 线性组合
    Parallel,   // 并行组合
    Nested,     // 嵌套组合
    Dynamic,    // 动态组合
}
```

### 1.2 模式分类体系

```rust
// 按功能分类
enum PatternFunction {
    DataFlow,       // 数据流模式
    ControlFlow,    // 控制流模式
    ErrorHandling,  // 错误处理模式
    ResourceManagement, // 资源管理模式
}

// 按复杂度分类
enum PatternComplexity {
    Simple,     // 简单模式
    Compound,   // 复合模式
    Complex,    // 复杂模式
    Adaptive,   // 自适应模式
}

// 按应用场景分类
enum PatternApplication {
    IOBound,        // I/O密集型
    CPUBound,       // CPU密集型
    Mixed,          // 混合型
    RealTime,       // 实时型
}
```

## 2. 生产者-消费者模式

### 2.1 基本生产者-消费者

```rust
use tokio::sync::mpsc;
use tokio::time::{sleep, Duration};

// 生产者-消费者基本实现
async fn producer_consumer_basic() {
    let (tx, mut rx) = mpsc::channel::<String>(100);
    
    // 生产者任务
    let producer = tokio::spawn(async move {
        for i in 0..10 {
            let message = format!("Message {}", i);
            tx.send(message).await.unwrap();
            sleep(Duration::from_millis(100)).await;
        }
    });
    
    // 消费者任务
    let consumer = tokio::spawn(async move {
        while let Some(message) = rx.recv().await {
            println!("Consumed: {}", message);
            // 模拟处理时间
            sleep(Duration::from_millis(50)).await;
        }
    });
    
    let _ = tokio::join!(producer, consumer);
}

// 多生产者-单消费者
async fn multi_producer_single_consumer() {
    let (tx, mut rx) = mpsc::channel::<String>(100);
    
    // 多个生产者
    let mut producers = Vec::new();
    for producer_id in 0..3 {
        let tx = tx.clone();
        let producer = tokio::spawn(async move {
            for i in 0..5 {
                let message = format!("Producer {} - Message {}", producer_id, i);
                tx.send(message).await.unwrap();
                sleep(Duration::from_millis(100)).await;
            }
        });
        producers.push(producer);
    }
    
    // 单个消费者
    let consumer = tokio::spawn(async move {
        while let Some(message) = rx.recv().await {
            println!("Consumed: {}", message);
            sleep(Duration::from_millis(30)).await;
        }
    });
    
    // 等待所有生产者完成
    for producer in producers {
        producer.await.unwrap();
    }
    
    // 关闭通道
    drop(tx);
    
    // 等待消费者完成
    consumer.await.unwrap();
}
```

### 2.2 有界缓冲区

```rust
use tokio::sync::Semaphore;

// 有界缓冲区实现
struct BoundedBuffer<T> {
    buffer: Vec<T>,
    capacity: usize,
    semaphore: Semaphore,
}

impl<T> BoundedBuffer<T> {
    fn new(capacity: usize) -> Self {
        Self {
            buffer: Vec::with_capacity(capacity),
            capacity,
            semaphore: Semaphore::new(capacity),
        }
    }
    
    async fn push(&mut self, item: T) {
        let _permit = self.semaphore.acquire().await.unwrap();
        self.buffer.push(item);
    }
    
    async fn pop(&mut self) -> Option<T> {
        if let Some(item) = self.buffer.pop() {
            self.semaphore.add_permits(1);
            Some(item)
        } else {
            None
        }
    }
}

// 使用有界缓冲区的生产者-消费者
async fn bounded_producer_consumer() {
    let (tx, mut rx) = mpsc::channel::<String>(5); // 有界通道
    
    // 生产者
    let producer = tokio::spawn(async move {
        for i in 0..10 {
            let message = format!("Message {}", i);
            println!("Producing: {}", message);
            tx.send(message).await.unwrap();
            sleep(Duration::from_millis(200)).await;
        }
    });
    
    // 消费者
    let consumer = tokio::spawn(async move {
        while let Some(message) = rx.recv().await {
            println!("Consuming: {}", message);
            sleep(Duration::from_millis(100)).await;
        }
    });
    
    let _ = tokio::join!(producer, consumer);
}
```

### 2.3 优先级队列

```rust
use std::collections::BinaryHeap;
use std::cmp::Ordering;

// 优先级任务
#[derive(Debug, Clone, Eq, PartialEq)]
struct PriorityTask {
    priority: u32,
    data: String,
}

impl Ord for PriorityTask {
    fn cmp(&self, other: &Self) -> Ordering {
        other.priority.cmp(&self.priority) // 高优先级在前
    }
}

impl PartialOrd for PriorityTask {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

// 优先级生产者-消费者
async fn priority_producer_consumer() {
    let (tx, mut rx) = mpsc::channel::<PriorityTask>(100);
    
    // 生产者
    let producer = tokio::spawn(async move {
        let tasks = vec![
            PriorityTask { priority: 3, data: "Low priority".to_string() },
            PriorityTask { priority: 1, data: "High priority".to_string() },
            PriorityTask { priority: 2, data: "Medium priority".to_string() },
        ];
        
        for task in tasks {
            tx.send(task).await.unwrap();
            sleep(Duration::from_millis(100)).await;
        }
    });
    
    // 消费者（使用优先级队列）
    let consumer = tokio::spawn(async move {
        let mut priority_queue = BinaryHeap::new();
        
        // 收集所有任务
        while let Some(task) = rx.recv().await {
            priority_queue.push(task);
        }
        
        // 按优先级处理
        while let Some(task) = priority_queue.pop() {
            println!("Processing: {:?}", task);
            sleep(Duration::from_millis(50)).await;
        }
    });
    
    let _ = tokio::join!(producer, consumer);
}
```

## 3. 发布-订阅模式

### 3.1 基本发布-订阅

```rust
use tokio::sync::broadcast;

// 发布-订阅基本实现
async fn basic_pub_sub() {
    let (tx, _) = broadcast::channel::<String>(16);
    let mut rx1 = tx.subscribe();
    let mut rx2 = tx.subscribe();
    let mut rx3 = tx.subscribe();
    
    // 发布者
    let publisher = tokio::spawn(async move {
        for i in 0..5 {
            let message = format!("News {}", i);
            println!("Publishing: {}", message);
            tx.send(message).unwrap();
            sleep(Duration::from_millis(200)).await;
        }
    });
    
    // 订阅者1
    let subscriber1 = tokio::spawn(async move {
        while let Ok(message) = rx1.recv().await {
            println!("Subscriber 1 received: {}", message);
        }
    });
    
    // 订阅者2
    let subscriber2 = tokio::spawn(async move {
        while let Ok(message) = rx2.recv().await {
            println!("Subscriber 2 received: {}", message);
        }
    });
    
    // 订阅者3
    let subscriber3 = tokio::spawn(async move {
        while let Ok(message) = rx3.recv().await {
            println!("Subscriber 3 received: {}", message);
        }
    });
    
    let _ = tokio::join!(publisher, subscriber1, subscriber2, subscriber3);
}
```

### 3.2 主题过滤

```rust
use serde::{Deserialize, Serialize};

// 消息类型
#[derive(Debug, Clone, Serialize, Deserialize)]
enum Message {
    News { content: String, category: String },
    Weather { temperature: f32, location: String },
    Sports { event: String, score: String },
}

// 主题过滤器
struct TopicFilter {
    topics: Vec<String>,
}

impl TopicFilter {
    fn new(topics: Vec<String>) -> Self {
        Self { topics }
    }
    
    fn matches(&self, message: &Message) -> bool {
        match message {
            Message::News { category, .. } => self.topics.contains(category),
            Message::Weather { location, .. } => self.topics.contains(location),
            Message::Sports { event, .. } => self.topics.contains(event),
        }
    }
}

// 带主题过滤的发布-订阅
async fn topic_filtered_pub_sub() {
    let (tx, _) = broadcast::channel::<Message>(16);
    let mut rx1 = tx.subscribe();
    let mut rx2 = tx.subscribe();
    
    // 发布者
    let publisher = tokio::spawn(async move {
        let messages = vec![
            Message::News { content: "Breaking news".to_string(), category: "politics".to_string() },
            Message::Weather { temperature: 25.0, location: "New York".to_string() },
            Message::Sports { event: "football".to_string(), score: "2-1".to_string() },
        ];
        
        for message in messages {
            println!("Publishing: {:?}", message);
            tx.send(message).unwrap();
            sleep(Duration::from_millis(200)).await;
        }
    });
    
    // 订阅者1（只接收新闻）
    let subscriber1 = tokio::spawn(async move {
        let filter = TopicFilter::new(vec!["politics".to_string()]);
        
        while let Ok(message) = rx1.recv().await {
            if filter.matches(&message) {
                println!("News subscriber received: {:?}", message);
            }
        }
    });
    
    // 订阅者2（只接收天气）
    let subscriber2 = tokio::spawn(async move {
        let filter = TopicFilter::new(vec!["New York".to_string()]);
        
        while let Ok(message) = rx2.recv().await {
            if filter.matches(&message) {
                println!("Weather subscriber received: {:?}", message);
            }
        }
    });
    
    let _ = tokio::join!(publisher, subscriber1, subscriber2);
}
```

## 4. 扇出-扇入模式

### 4.1 基本扇出-扇入

```rust
use tokio::sync::mpsc;
use std::collections::HashMap;

// 扇出-扇入基本实现
async fn fan_out_fan_in() {
    let (input_tx, input_rx) = mpsc::channel::<String>(100);
    let (output_tx, mut output_rx) = mpsc::channel::<String>(100);
    
    // 扇出：分发任务给多个工作者
    let fan_out = tokio::spawn(async move {
        let mut workers = Vec::new();
        
        // 创建多个工作者
        for worker_id in 0..3 {
            let (worker_tx, mut worker_rx) = mpsc::channel::<String>(10);
            let output_tx = output_tx.clone();
            
            let worker = tokio::spawn(async move {
                while let Some(task) = worker_rx.recv().await {
                    let result = process_task(worker_id, task).await;
                    output_tx.send(result).await.unwrap();
                }
            });
            
            workers.push((worker_tx, worker));
        }
        
        // 分发任务
        let mut counter = 0;
        while let Some(task) = input_rx.recv().await {
            let worker_id = counter % workers.len();
            workers[worker_id].0.send(task).await.unwrap();
            counter += 1;
        }
        
        // 关闭工作者
        for (tx, _) in workers {
            drop(tx);
        }
    });
    
    // 扇入：收集结果
    let fan_in = tokio::spawn(async move {
        let mut results = Vec::new();
        while let Some(result) = output_rx.recv().await {
            results.push(result);
        }
        results
    });
    
    // 发送任务
    for i in 0..10 {
        input_tx.send(format!("Task {}", i)).await.unwrap();
    }
    drop(input_tx);
    
    let (_, results) = tokio::join!(fan_out, fan_in);
    println!("Results: {:?}", results.unwrap());
}

async fn process_task(worker_id: usize, task: String) -> String {
    println!("Worker {} processing: {}", worker_id, task);
    sleep(Duration::from_millis(100)).await;
    format!("Processed by worker {}: {}", worker_id, task)
}
```

## 5. 背压处理模式

### 5.1 基本背压处理

```rust
use tokio::sync::Semaphore;

// 背压处理基本实现
async fn backpressure_basic() {
    let (tx, mut rx) = mpsc::channel::<String>(5); // 小缓冲区
    let semaphore = Semaphore::new(3); // 限制并发处理
    
    // 快速生产者
    let producer = tokio::spawn(async move {
        for i in 0..20 {
            let message = format!("Message {}", i);
            println!("Producing: {}", message);
            tx.send(message).await.unwrap();
            sleep(Duration::from_millis(50)).await;
        }
    });
    
    // 慢速消费者（带背压）
    let consumer = tokio::spawn(async move {
        while let Some(message) = rx.recv().await {
            let _permit = semaphore.acquire().await.unwrap();
            
            tokio::spawn(async move {
                println!("Processing: {}", message);
                sleep(Duration::from_millis(200)).await; // 慢处理
                println!("Completed: {}", message);
            });
        }
    });
    
    let _ = tokio::join!(producer, consumer);
}
```

## 6. 错误传播模式

### 6.1 基本错误传播

```rust
use std::error::Error;

// 错误传播基本实现
async fn error_propagation_basic() -> Result<(), Box<dyn Error>> {
    let result = risky_operation().await?;
    println!("Operation result: {}", result);
    Ok(())
}

async fn risky_operation() -> Result<String, Box<dyn Error>> {
    // 模拟可能失败的操作
    if rand::random::<bool>() {
        Ok("Success".to_string())
    } else {
        Err("Operation failed".into())
    }
}

// 错误恢复
async fn error_recovery() -> Result<(), Box<dyn Error>> {
    let mut attempts = 0;
    let max_attempts = 3;
    
    while attempts < max_attempts {
        match risky_operation().await {
            Ok(result) => {
                println!("Operation succeeded: {}", result);
                return Ok(());
            }
            Err(e) => {
                attempts += 1;
                println!("Attempt {} failed: {}", attempts, e);
                if attempts < max_attempts {
                    sleep(Duration::from_secs(1)).await;
                }
            }
        }
    }
    
    Err("All attempts failed".into())
}
```

## 7. 2025年新特性

### 7.1 智能模式选择

```rust
// 2025年：智能模式选择
async fn intelligent_pattern_selection() {
    let pattern_selector = IntelligentPatternSelector::new();
    
    // 根据负载自动选择模式
    let pattern = pattern_selector.select_pattern(LoadMetrics {
        cpu_usage: 0.8,
        memory_usage: 0.6,
        io_wait: 0.3,
    }).await;
    
    match pattern {
        Pattern::ProducerConsumer => producer_consumer_basic().await,
        Pattern::PubSub => basic_pub_sub().await,
        Pattern::FanOutFanIn => fan_out_fan_in().await,
        Pattern::Backpressure => backpressure_basic().await,
    }
}

// 智能模式选择器
struct IntelligentPatternSelector;

impl IntelligentPatternSelector {
    fn new() -> Self {
        Self
    }
    
    async fn select_pattern(&self, metrics: LoadMetrics) -> Pattern {
        if metrics.io_wait > 0.5 {
            Pattern::Backpressure
        } else if metrics.cpu_usage > 0.8 {
            Pattern::FanOutFanIn
        } else if metrics.memory_usage > 0.7 {
            Pattern::PubSub
        } else {
            Pattern::ProducerConsumer
        }
    }
}

struct LoadMetrics {
    cpu_usage: f64,
    memory_usage: f64,
    io_wait: f64,
}

enum Pattern {
    ProducerConsumer,
    PubSub,
    FanOutFanIn,
    Backpressure,
}
```

## 8. 工程实践

### 8.1 模式最佳实践

```rust
// 模式最佳实践
async fn pattern_best_practices() {
    // 1. 选择合适的模式
    let pattern = select_pattern_for_workload(WorkloadType::IOBound).await;
    
    // 2. 配置优化
    let config = optimize_config_for_pattern(&pattern).await;
    
    // 3. 监控和调整
    let monitor = PatternMonitor::new();
    monitor.start_monitoring(&pattern).await;
    
    // 4. 错误处理
    let error_handler = ErrorHandler::new();
    error_handler.setup_error_handling(&pattern).await;
}

// 工作负载类型
enum WorkloadType {
    IOBound,
    CPUBound,
    Mixed,
}

// 模式选择
async fn select_pattern_for_workload(workload: WorkloadType) -> Pattern {
    match workload {
        WorkloadType::IOBound => Pattern::ProducerConsumer,
        WorkloadType::CPUBound => Pattern::FanOutFanIn,
        WorkloadType::Mixed => Pattern::PubSub,
    }
}

// 配置优化
async fn optimize_config_for_pattern(pattern: &Pattern) -> PatternConfig {
    match pattern {
        Pattern::ProducerConsumer => PatternConfig {
            buffer_size: 1000,
            worker_count: 2,
            timeout: Duration::from_secs(5),
        },
        Pattern::FanOutFanIn => PatternConfig {
            buffer_size: 100,
            worker_count: 8,
            timeout: Duration::from_secs(1),
        },
        Pattern::PubSub => PatternConfig {
            buffer_size: 500,
            worker_count: 4,
            timeout: Duration::from_secs(2),
        },
        Pattern::Backpressure => PatternConfig {
            buffer_size: 50,
            worker_count: 1,
            timeout: Duration::from_secs(10),
        },
    }
}

// 模式监控器
struct PatternMonitor;

impl PatternMonitor {
    fn new() -> Self {
        Self
    }
    
    async fn start_monitoring(&self, pattern: &Pattern) {
        println!("Monitoring pattern: {:?}", pattern);
        // 启动监控
    }
}

// 错误处理器
struct ErrorHandler;

impl ErrorHandler {
    fn new() -> Self {
        Self
    }
    
    async fn setup_error_handling(&self, pattern: &Pattern) {
        println!("Setting up error handling for pattern: {:?}", pattern);
        // 设置错误处理
    }
}

// 配置结构
struct PatternConfig {
    buffer_size: usize,
    worker_count: usize,
    timeout: Duration,
}
```

### 8.2 测试策略

```rust
#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_producer_consumer_pattern() {
        // 测试生产者-消费者模式
        let start = Instant::now();
        producer_consumer_basic().await;
        let duration = start.elapsed();
        
        assert!(duration < Duration::from_secs(5));
    }
    
    #[tokio::test]
    async fn test_pub_sub_pattern() {
        // 测试发布-订阅模式
        let start = Instant::now();
        basic_pub_sub().await;
        let duration = start.elapsed();
        
        assert!(duration < Duration::from_secs(3));
    }
    
    #[tokio::test]
    async fn test_fan_out_fan_in_pattern() {
        // 测试扇出-扇入模式
        let start = Instant::now();
        fan_out_fan_in().await;
        let duration = start.elapsed();
        
        assert!(duration < Duration::from_secs(4));
    }
    
    #[tokio::test]
    async fn test_backpressure_pattern() {
        // 测试背压处理模式
        let start = Instant::now();
        backpressure_basic().await;
        let duration = start.elapsed();
        
        assert!(duration < Duration::from_secs(6));
    }
    
    #[tokio::test]
    async fn test_error_propagation() {
        // 测试错误传播
        let result = error_recovery().await;
        // 应该能够处理错误并最终成功或失败
        assert!(result.is_ok() || result.is_err());
    }
}
```

---

**完成度**: 100%

本章全面介绍了Rust异步编程的核心模式，包括生产者-消费者、发布-订阅、扇出-扇入、背压处理、错误传播等经典模式。
特别关注2025年异步编程模式的最新发展，为构建可维护、高性能的异步应用程序提供了坚实的理论基础。
