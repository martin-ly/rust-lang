//! 异步编程模式演示
//! 
//! 本示例展示了常见的异步编程模式：
//! - 生产者-消费者模式
//! - 发布-订阅模式
//! - 工作池模式
//! - 背压处理
//! - 优雅关闭
//! - 错误恢复
//! 
//! 运行方式：
//! ```bash
//! cargo run --example async_patterns_demo
//! ```

use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{mpsc, broadcast, RwLock, Mutex, Notify};
use tokio::time::{sleep, interval};
use tokio::task::JoinSet;
// use futures::StreamExt;
use anyhow::Result;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Message {
    id: u64,
    content: String,
    timestamp: std::time::SystemTime,
}

#[derive(Debug)]
struct ProducerConsumerDemo {
    message_count: Arc<Mutex<u64>>,
    shutdown_notify: Arc<Notify>,
}

impl ProducerConsumerDemo {
    fn new() -> Self {
        Self {
            message_count: Arc::new(Mutex::new(0)),
            shutdown_notify: Arc::new(Notify::new()),
        }
    }

    async fn run(&self) -> Result<()> {
        println!("🔄 生产者-消费者模式演示");
        
        let (tx, rx) = mpsc::channel::<Message>(100);
        let message_count = Arc::clone(&self.message_count);
        let shutdown_notify = Arc::clone(&self.shutdown_notify);

        // 启动生产者
        let producer_handle = tokio::spawn(async move {
            Self::producer_task(tx, message_count).await
        });

        // 启动消费者
        let consumer_handle = tokio::spawn(async move {
            Self::consumer_task(rx, shutdown_notify).await
        });

        // 运行一段时间后关闭
        sleep(Duration::from_secs(3)).await;
        println!("  发送关闭信号...");
        self.shutdown_notify.notify_one();

        // 等待任务完成
        let _ = tokio::join!(producer_handle, consumer_handle);
        
        let final_count = *self.message_count.lock().await;
        println!("  生产者-消费者演示完成，处理消息数: {}", final_count);
        
        Ok(())
    }

    async fn producer_task(tx: mpsc::Sender<Message>, count: Arc<Mutex<u64>>) {
        let mut id = 0;
        let mut interval = interval(Duration::from_millis(100));

        loop {
            interval.tick().await;
            
            let message = Message {
                id,
                content: format!("消息 {}", id),
                timestamp: std::time::SystemTime::now(),
            };

            match tx.try_send(message) {
                Ok(_) => {
                    let mut counter = count.lock().await;
                    *counter += 1;
                    id += 1;
                }
                Err(_) => {
                    println!("    生产者: 通道已满，跳过消息 {}", id);
                    break;
                }
            }

            if id >= 20 {
                println!("    生产者: 已完成 {} 条消息", id);
                break;
            }
        }
    }

    async fn consumer_task(mut rx: mpsc::Receiver<Message>, shutdown: Arc<Notify>) {
        let mut processed_count = 0;

        loop {
            tokio::select! {
                message = rx.recv() => {
                    match message {
                        Some(msg) => {
                            // 模拟处理时间
                            sleep(Duration::from_millis(50)).await;
                            processed_count += 1;
                            println!("    消费者: 处理消息 {} - {}", msg.id, msg.content);
                        }
                        None => {
                            println!("    消费者: 通道已关闭");
                            break;
                        }
                    }
                }
                _ = shutdown.notified() => {
                    println!("    消费者: 收到关闭信号");
                    break;
                }
            }
        }
        
        println!("    消费者: 处理完成，共处理 {} 条消息", processed_count);
    }
}

struct PubSubDemo {
    #[allow(dead_code)]
    subscribers: Arc<RwLock<Vec<broadcast::Sender<String>>>>,
}

impl PubSubDemo {
    fn new() -> Self {
        Self {
            subscribers: Arc::new(RwLock::new(Vec::new())),
        }
    }

    async fn run(&self) -> Result<()> {
        println!("\n📡 发布-订阅模式演示");
        
        // 创建广播通道
        let (tx, _rx) = broadcast::channel(16);
        
        // 添加订阅者
        for i in 0..3 {
            let rx = tx.subscribe();
            let subscriber_id = i;
            tokio::spawn(async move {
                Self::subscriber_task(subscriber_id, rx).await;
            });
        }

        // 发布消息
        for i in 0..5 {
            let message = format!("广播消息 {}", i);
            let _ = tx.send(message);
            sleep(Duration::from_millis(200)).await;
        }

        sleep(Duration::from_secs(1)).await;
        println!("  发布-订阅演示完成");
        
        Ok(())
    }

    async fn subscriber_task(id: usize, mut rx: broadcast::Receiver<String>) {
        while let Ok(message) = rx.recv().await {
            println!("    订阅者 {}: 收到消息 - {}", id, message);
            sleep(Duration::from_millis(100)).await;
        }
        println!("    订阅者 {}: 连接已关闭", id);
    }
}

struct WorkerPoolDemo {
    pool_size: usize,
    task_queue: Arc<Mutex<Vec<Task>>>,
    result_collector: Arc<Mutex<Vec<TaskResult>>>,
}

#[derive(Debug, Clone)]
struct Task {
    id: u64,
    duration_ms: u64,
    #[allow(dead_code)]
    description: String,
}

#[derive(Debug)]
struct TaskResult {
    task_id: u64,
    result: String,
    duration: Duration,
}

impl WorkerPoolDemo {
    fn new(pool_size: usize) -> Self {
        Self {
            pool_size,
            task_queue: Arc::new(Mutex::new(Vec::new())),
            result_collector: Arc::new(Mutex::new(Vec::new())),
        }
    }

    async fn run(&self) -> Result<()> {
        println!("\n👥 工作池模式演示");
        
        let mut join_set = JoinSet::new();
        
        // 启动工作线程
        for worker_id in 0..self.pool_size {
            let task_queue = Arc::clone(&self.task_queue);
            let result_collector = Arc::clone(&self.result_collector);
            
            join_set.spawn(async move {
                Self::worker_task(worker_id, task_queue, result_collector).await;
            });
        }

        // 提交任务
        self.submit_tasks().await;

        // 等待所有工作线程完成
        while join_set.join_next().await.is_some() {
            // 继续等待
        }

        // 显示结果
        let results = self.result_collector.lock().await;
        println!("  工作池演示完成，处理任务数: {}", results.len());
        for result in results.iter() {
            println!("    任务 {} 完成: {} (耗时: {:?})", 
                result.task_id, result.result, result.duration);
        }
        
        Ok(())
    }

    async fn submit_tasks(&self) {
        for i in 0..10 {
            let task = Task {
                id: i,
                duration_ms: 100 + (i * 50),
                description: format!("任务 {}", i),
            };
            
            let mut queue = self.task_queue.lock().await;
            queue.push(task);
            println!("    提交任务 {}", i);
            
            sleep(Duration::from_millis(50)).await;
        }
        
        // 添加结束标记
        for _ in 0..self.pool_size {
            let mut queue = self.task_queue.lock().await;
            queue.push(Task {
                id: 999,
                duration_ms: 0,
                description: "结束标记".to_string(),
            });
        }
    }

    async fn worker_task(
        worker_id: usize,
        task_queue: Arc<Mutex<Vec<Task>>>,
        result_collector: Arc<Mutex<Vec<TaskResult>>>,
    ) {
        loop {
            let task = {
                let mut queue = task_queue.lock().await;
                queue.pop()
            };

            match task {
                Some(task) => {
                    if task.id == 999 {
                        println!("    工作线程 {}: 收到结束信号", worker_id);
                        break;
                    }

                    println!("    工作线程 {}: 开始处理任务 {}", worker_id, task.id);
                    let start = std::time::Instant::now();
                    
                    // 模拟工作
                    sleep(Duration::from_millis(task.duration_ms)).await;
                    
                    let duration = start.elapsed();
                    let result = TaskResult {
                        task_id: task.id,
                        result: format!("任务 {} 完成", task.id),
                        duration,
                    };

                    let mut collector = result_collector.lock().await;
                    collector.push(result);
                    
                    println!("    工作线程 {}: 完成任务 {}", worker_id, task.id);
                }
                None => {
                    sleep(Duration::from_millis(10)).await;
                }
            }
        }
        
        println!("    工作线程 {}: 退出", worker_id);
    }
}

struct BackpressureDemo {
    buffer_size: usize,
}

impl BackpressureDemo {
    fn new(buffer_size: usize) -> Self {
        Self { buffer_size }
    }

    async fn run(&self) -> Result<()> {
        println!("\n🌊 背压处理演示");
        
        let (tx, rx) = mpsc::channel(self.buffer_size);
        let semaphore = Arc::new(tokio::sync::Semaphore::new(self.buffer_size));

        // 快速生产者
        let producer_handle = {
            let tx = tx.clone();
            let semaphore = Arc::clone(&semaphore);
            tokio::spawn(async move {
                Self::fast_producer(tx, semaphore).await;
            })
        };

        // 慢速消费者
        let consumer_handle = {
            let semaphore = Arc::clone(&semaphore);
            tokio::spawn(async move {
                Self::slow_consumer(rx, semaphore).await;
            })
        };

        let _ = tokio::join!(producer_handle, consumer_handle);
        
        println!("  背压处理演示完成");
        Ok(())
    }

    async fn fast_producer(tx: mpsc::Sender<u64>, semaphore: Arc<tokio::sync::Semaphore>) {
        for i in 0..20 {
            // 获取信号量，模拟背压
            let _permit = semaphore.acquire().await.unwrap();
            
            match tx.try_send(i) {
                Ok(_) => {
                    println!("    生产者: 发送消息 {}", i);
                }
                Err(_) => {
                    println!("    生产者: 通道已满，等待...");
                    // 等待消费者处理
                    sleep(Duration::from_millis(100)).await;
                    continue;
                }
            }
            
            sleep(Duration::from_millis(50)).await;
        }
        
        // 发送结束信号
        let _ = tx.send(999).await;
        println!("    生产者: 完成发送");
    }

    async fn slow_consumer(mut rx: mpsc::Receiver<u64>, semaphore: Arc<tokio::sync::Semaphore>) {
        while let Some(message) = rx.recv().await {
            if message == 999 {
                println!("    消费者: 收到结束信号");
                break;
            }

            println!("    消费者: 处理消息 {}", message);
            // 模拟慢速处理
            sleep(Duration::from_millis(200)).await;
            
            // 释放信号量
            semaphore.add_permits(1);
        }
        
        println!("    消费者: 完成处理");
    }
}

struct GracefulShutdownDemo {
    shutdown_tx: mpsc::Sender<()>,
    shutdown_rx: Arc<Mutex<mpsc::Receiver<()>>>,
}

impl GracefulShutdownDemo {
    fn new() -> Self {
        let (tx, rx) = mpsc::channel(1);
        Self {
            shutdown_tx: tx,
            shutdown_rx: Arc::new(Mutex::new(rx)),
        }
    }

    async fn run(&self) -> Result<()> {
        println!("\n🛑 优雅关闭演示");
        
        let mut join_set = JoinSet::new();
        
        // 启动多个长时间运行的任务
        for i in 0..3 {
            let shutdown_rx = Arc::clone(&self.shutdown_rx);
            join_set.spawn(async move {
                Self::long_running_task(i, shutdown_rx).await;
            });
        }

        // 运行一段时间后发送关闭信号
        sleep(Duration::from_secs(2)).await;
        println!("  发送优雅关闭信号...");
        let _ = self.shutdown_tx.send(()).await;

        // 等待所有任务完成
        let mut completed = 0;
        while let Some(result) = join_set.join_next().await {
            match result {
                Ok(_task_id) => {
                    completed += 1;
                    println!("  任务已优雅关闭");
                }
                Err(e) => {
                    println!("  任务执行错误: {}", e);
                }
            }
        }
        
        println!("  优雅关闭演示完成，{} 个任务已关闭", completed);
        Ok(())
    }

    async fn long_running_task(id: usize, shutdown_rx: Arc<Mutex<mpsc::Receiver<()>>>) -> usize {
        let mut interval = interval(Duration::from_millis(500));
        
        loop {
            tokio::select! {
                _ = interval.tick() => {
                    println!("    任务 {}: 正在工作...", id);
                }
                _ = async {
                    let mut rx = shutdown_rx.lock().await;
                    rx.recv().await
                } => {
                    println!("    任务 {}: 收到关闭信号，正在清理...", id);
                    sleep(Duration::from_millis(300)).await; // 模拟清理时间
                    println!("    任务 {}: 清理完成", id);
                    break;
                }
            }
        }
        
        id
    }
}

struct ErrorRecoveryDemo;

impl ErrorRecoveryDemo {
    async fn run() -> Result<()> {
        println!("\n🔄 错误恢复演示");
        
        // 演示重试机制
        Self::retry_mechanism().await?;
        
        // 演示熔断器模式
        Self::circuit_breaker_pattern().await?;
        
        // 演示降级策略
        Self::fallback_strategy().await?;
        
        println!("  错误恢复演示完成");
        Ok(())
    }

    async fn retry_mechanism() -> Result<()> {
        println!("    重试机制演示");
        
        for attempt in 1..=3 {
            match Self::unreliable_operation().await {
                Ok(result) => {
                    println!("      操作成功: {}", result);
                    break;
                }
                Err(e) if attempt < 3 => {
                    println!("      尝试 {} 失败: {}，准备重试...", attempt, e);
                    sleep(Duration::from_millis(200 * attempt as u64)).await;
                }
                Err(e) => {
                    println!("      所有重试都失败: {}", e);
                }
            }
        }
        
        Ok(())
    }

    async fn circuit_breaker_pattern() -> Result<()> {
        println!("    熔断器模式演示");
        
        let mut failure_count = 0;
        let failure_threshold = 3;
        
        for i in 0..10 {
            if failure_count >= failure_threshold {
                println!("      熔断器开启，跳过请求 {}", i);
                sleep(Duration::from_millis(100)).await;
                continue;
            }
            
            match Self::unreliable_operation().await {
                Ok(result) => {
                    println!("      请求 {} 成功: {}", i, result);
                    failure_count = 0; // 重置失败计数
                }
                Err(_) => {
                    failure_count += 1;
                    println!("      请求 {} 失败，失败计数: {}", i, failure_count);
                }
            }
            
            sleep(Duration::from_millis(100)).await;
        }
        
        Ok(())
    }

    async fn fallback_strategy() -> Result<()> {
        println!("    降级策略演示");
        
        match Self::primary_service().await {
            Ok(result) => {
                println!("      主服务可用: {}", result);
            }
            Err(_) => {
                println!("      主服务不可用，使用备用服务");
                match Self::fallback_service().await {
                    Ok(result) => {
                        println!("      备用服务可用: {}", result);
                    }
                    Err(e) => {
                        println!("      备用服务也不可用: {:?}", e);
                    }
                }
            }
        }
        
        Ok(())
    }

    async fn unreliable_operation() -> Result<String> {
        // 模拟不稳定的操作
        if rand::random::<f32>() < 0.6 {
            Err(anyhow::anyhow!("随机失败"))
        } else {
            Ok("操作成功".to_string())
        }
    }

    async fn primary_service() -> Result<String> {
        // 模拟主服务
        if rand::random::<f32>() < 0.7 {
            Err(anyhow::anyhow!("主服务不可用"))
        } else {
            Ok("主服务响应".to_string())
        }
    }

    async fn fallback_service() -> Result<String> {
        // 模拟备用服务
        if rand::random::<f32>() < 0.3 {
            Err(anyhow::anyhow!("备用服务不可用"))
        } else {
            Ok("备用服务响应".to_string())
        }
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    println!("🎯 异步编程模式演示");
    println!("================================");

    // 1. 生产者-消费者模式
    let pc_demo = ProducerConsumerDemo::new();
    pc_demo.run().await?;

    // 2. 发布-订阅模式
    let pubsub_demo = PubSubDemo::new();
    pubsub_demo.run().await?;

    // 3. 工作池模式
    let worker_demo = WorkerPoolDemo::new(3);
    worker_demo.run().await?;

    // 4. 背压处理
    let backpressure_demo = BackpressureDemo::new(5);
    backpressure_demo.run().await?;

    // 5. 优雅关闭
    let shutdown_demo = GracefulShutdownDemo::new();
    shutdown_demo.run().await?;

    // 6. 错误恢复
    ErrorRecoveryDemo::run().await?;

    println!("\n🎉 所有异步编程模式演示完成！");
    Ok(())
}
