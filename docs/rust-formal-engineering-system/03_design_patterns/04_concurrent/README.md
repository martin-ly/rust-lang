# 并发设计模式

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> 内容已整合至： [c09_design_pattern/docs/](../../../../crates/c09_design_pattern/docs/)

[返回主索引](../../00_master_index.md)

---

## 并发安全的设计模式

### 无锁数据结构模式

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

// 原子计数器（无锁）
struct AtomicCounter {
    count: AtomicUsize,
}

impl AtomicCounter {
    fn new() -> Self {
        Self {
            count: AtomicUsize::new(0),
        }
    }

    fn increment(&self) -> usize {
        self.count.fetch_add(1, Ordering::Relaxed)
    }

    fn get(&self) -> usize {
        self.count.load(Ordering::Relaxed)
    }
}

// 使用示例
fn lock_free_demo() {
    use std::thread;
    use std::sync::Arc;

    let counter = Arc::new(AtomicCounter::new());
    let mut handles = vec![];

    for _ in 0..10 {
        let c = Arc::clone(&counter);
        handles.push(thread::spawn(move || {
            for _ in 0..1000 {
                c.increment();
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    assert_eq!(counter.get(), 10000);
}
```

### 线程池模式

```rust
use std::sync::{mpsc, Arc, Mutex};
use std::thread;

// 线程池实现
pub struct ThreadPool {
    workers: Vec<Worker>,
    sender: Option<mpsc::Sender<Job>>,
}

type Job = Box<dyn FnOnce() + Send + 'static>;

impl ThreadPool {
    pub fn new(size: usize) -> Self {
        let (sender, receiver) = mpsc::channel();
        let receiver = Arc::new(Mutex::new(receiver));

        let mut workers = Vec::with_capacity(size);

        for id in 0..size {
            workers.push(Worker::new(id, Arc::clone(&receiver)));
        }

        Self {
            workers,
            sender: Some(sender),
        }
    }

    pub fn execute<F>(&self, f: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let job = Box::new(f);
        self.sender.as_ref().unwrap().send(job).unwrap();
    }
}

impl Drop for ThreadPool {
    fn drop(&mut self) {
        // 关闭发送端，让所有 worker 退出
        drop(self.sender.take());

        for worker in &mut self.workers {
            if let Some(thread) = worker.thread.take() {
                thread.join().unwrap();
            }
        }
    }
}

struct Worker {
    id: usize,
    thread: Option<thread::JoinHandle<()>>,
}

impl Worker {
    fn new(id: usize, receiver: Arc<Mutex<mpsc::Receiver<Job>>>) -> Self {
        let thread = thread::spawn(move || loop {
            let job = receiver.lock().unwrap().recv();

            match job {
                Ok(job) => {
                    println!("Worker {} got a job; executing.", id);
                    job();
                }
                Err(_) => {
                    println!("Worker {} shutting down.", id);
                    break;
                }
            }
        });

        Self {
            id,
            thread: Some(thread),
        }
    }
}

// 使用示例
fn thread_pool_demo() {
    let pool = ThreadPool::new(4);

    for i in 0..8 {
        pool.execute(move || {
            println!("Processing task {}", i);
            thread::sleep(std::time::Duration::from_millis(100));
        });
    }

    // pool 在 drop 时会优雅关闭
}
```

### 读写锁模式

```rust
use std::sync::{Arc, RwLock};
use std::thread;

// 多读单写模式
fn rwlock_pattern() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));

    // 多个读线程
    let mut handles = vec![];
    for _ in 0..5 {
        let data = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let read_guard = data.read().unwrap();
            println!("Read: {:?}", *read_guard);
        }));
    }

    // 一个写线程
    let data = Arc::clone(&data);
    handles.push(thread::spawn(move || {
        let mut write_guard = data.write().unwrap();
        write_guard.push(4);
        println!("Written");
    }));

    for h in handles {
        h.join().unwrap();
    }
}

// 缓存模式（读写锁 + 延迟初始化）
struct Cache<K, V> {
    data: RwLock<std::collections::HashMap<K, V>>,
}

impl<K: std::hash::Hash + Eq + Clone, V: Clone> Cache<K, V> {
    fn new() -> Self {
        Self {
            data: RwLock::new(std::collections::HashMap::new()),
        }
    }

    fn get(&self, key: &K) -> Option<V> {
        self.data.read().unwrap().get(key).cloned()
    }

    fn insert(&self, key: K, value: V) {
        self.data.write().unwrap().insert(key, value);
    }

    fn get_or_insert<F>(&self, key: K, f: F) -> V
    where
        F: FnOnce() -> V,
    {
        // 先尝试读取
        if let Some(value) = self.get(&key) {
            return value;
        }

        // 需要写入
        let mut guard = self.data.write().unwrap();
        // 双重检查
        guard.entry(key).or_insert_with(f).clone()
    }
}
```

### 生产者-消费者模式

```rust
use std::sync::mpsc;
use std::thread;

// 有界通道的生产者-消费者
fn bounded_producer_consumer() {
    let (tx, rx) = mpsc::sync_channel(10); // 缓冲区大小为 10

    // 生产者
    let producer = thread::spawn(move || {
        for i in 0..100 {
            tx.send(i).unwrap();
            println!("Produced: {}", i);
        }
    });

    // 多个消费者
    let mut consumers = vec![];
    for id in 0..3 {
        let rx = rx.clone();
        consumers.push(thread::spawn(move || {
            while let Ok(item) = rx.recv() {
                println!("Consumer {} consumed: {}", id, item);
            }
        }));
    }

    // 关闭原始接收端
    drop(rx);

    producer.join().unwrap();
    for c in consumers {
        c.join().unwrap();
    }
}

// 背压控制的生产者
fn backpressure_producer_consumer() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    use std::time::Duration;

    let (tx, rx) = mpsc::sync_channel(5);
    let processed = Arc::new(AtomicUsize::new(0));

    // 慢消费者
    let processed_clone = processed.clone();
    let consumer = thread::spawn(move || {
        while let Ok(item) = rx.recv() {
            thread::sleep(Duration::from_millis(100)); // 模拟慢处理
            processed_clone.fetch_add(1, Ordering::Relaxed);
            println!("Processed: {}", item);
        }
    });

    // 快生产者（会被阻塞）
    for i in 0..20 {
        tx.send(i).unwrap();
        println!("Sent: {}", i);
    }

    drop(tx);
    consumer.join().unwrap();
    println!("Total processed: {}", processed.load(Ordering::Relaxed));
}
```

### 扇出-扇入模式

```rust
use std::sync::mpsc;
use std::thread;

// 扇出：一个任务分发给多个 worker
// 扇入：多个 worker 的结果汇总
fn fan_out_fan_in() {
    let data: Vec<i32> = (0..100).collect();
    let num_workers = 4;

    // 任务分发通道
    let (task_tx, task_rx) = mpsc::channel::<i32>();
    let task_rx = Arc::new(Mutex::new(task_rx));

    // 结果收集通道
    let (result_tx, result_rx) = mpsc::channel::<i32>();

    // 启动 workers
    for _ in 0..num_workers {
        let rx = Arc::clone(&task_rx);
        let tx = result_tx.clone();
        thread::spawn(move || {
            while let Ok(item) = rx.lock().unwrap().recv() {
                // 处理任务
                let result = item * item; // 计算平方
                tx.send(result).unwrap();
            }
        });
    }

    // 扇出：分发任务
    for item in &data {
        task_tx.send(*item).unwrap();
    }
    drop(task_tx);
    drop(result_tx); // 关闭原始发送端

    // 扇入：收集结果
    let mut results = vec![];
    while let Ok(result) = result_rx.recv() {
        results.push(result);
    }

    println!("Processed {} items", results.len());
}
```

### 信号量模式

```rust
use std::sync::Arc;
use tokio::sync::Semaphore;

// 使用信号量限制并发数
async fn semaphore_limited_concurrency() {
    let semaphore = Arc::new(Semaphore::new(3)); // 最多 3 个并发
    let mut handles = vec![];

    for i in 0..10 {
        let sem = semaphore.clone();
        handles.push(tokio::spawn(async move {
            // 获取许可
            let _permit = sem.acquire().await.unwrap();
            println!("Task {} started", i);

            // 模拟工作
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;

            println!("Task {} completed", i);
            // 许可在 _permit drop 时自动释放
        }));
    }

    for handle in handles {
        handle.await.unwrap();
    }
}

// 带权重的信号量
async fn weighted_semaphore() {
    let semaphore = Arc::new(Semaphore::new(10));

    // 小任务占用 1 个许可
    let sem1 = semaphore.clone();
    let small_task = tokio::spawn(async move {
        let _permit = sem1.acquire().await.unwrap();
        println!("Small task running");
    });

    // 大任务占用 5 个许可
    let sem2 = semaphore.clone();
    let large_task = tokio::spawn(async move {
        let _permit = sem2.acquire_many(5).await.unwrap();
        println!("Large task running");
    });

    small_task.await.unwrap();
    large_task.await.unwrap();
}
```

---

## 使用场景

| 场景 | 并发模式 | 关键技术 |
| :--- | :--- | :--- |
| 高并发计数 | 无锁数据结构 | `AtomicUsize` |
| CPU 密集型任务 | 线程池 | 固定工作线程数 |
| 多读少写缓存 | 读写锁 | `RwLock<HashMap>` |
| 任务队列 | 生产者-消费者 | `mpsc` 通道 |
| 并行处理 | 扇出-扇入 | 多 worker + 结果聚合 |
| 资源限制 | 信号量 | `Semaphore` |
| 流式处理 | 背压控制 | 有界通道 |
| 批量提交 | 批量处理 | 定时/定量触发 |

---

## 相关研究笔记

### 软件设计理论

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 并发执行模型 | 并发模型理论 | [../../../research_notes/software_design_theory/03_execution_models/03_concurrent.md](../../../research_notes/software_design_theory/03_execution_models/03_concurrent.md) |
| 并行执行模型 | 并行模型理论 | [../../../research_notes/software_design_theory/03_execution_models/04_parallel.md](../../../research_notes/software_design_theory/03_execution_models/04_parallel.md) |
| 边界矩阵 | 并发安全边界 | [../../../research_notes/software_design_theory/01_design_patterns_formal/04_boundary_matrix.md](../../../research_notes/software_design_theory/01_design_patterns_formal/04_boundary_matrix.md) |

### 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| Send/Sync 形式化 | 线程安全形式化 | [../../../research_notes/formal_methods/send_sync_formalization.md](../../../research_notes/formal_methods/send_sync_formalization.md) |
| 所有权模型 | 所有权与并发 | [../../../research_notes/formal_methods/ownership_model.md](../../../research_notes/formal_methods/ownership_model.md) |

### 实验分析

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 并发性能 | 并发性能测试 | [../../../research_notes/experiments/concurrency_performance.md](../../../research_notes/experiments/concurrency_performance.md) |

---

## 相关 crates

| crate | 描述 | 路径 |
| :--- | :--- | :--- |
| c09_design_pattern | 并发设计模式实现 | [../../../../crates/c09_design_pattern/docs/](../../../../crates/c09_design_pattern/docs/) |
| c05_threads | 线程并发 | [../../../../crates/c05_threads/](../../../../crates/c05_threads/) |
| c06_async | 异步并发 | [../../../../crates/c06_async/](../../../../crates/c06_async/) |
