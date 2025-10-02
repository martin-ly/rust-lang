//! CSP 模型对比分析 - CSP (Communicating Sequential Processes) Model Comparison
//!
//! # 概述 (Overview)
//!
//! 本模块深入对比 Rust 和 Golang 的并发模型，重点分析：
//! - CSP 理论基础
//! - Golang 的 goroutine + channel 模型
//! - Rust 的 async/await + channel 模型
//! - 两者的语义差异与等价关系
//!
//! # CSP 理论基础
//!
//! ## 1. CSP 的形式化定义
//!
//! ### 1.1 基本概念
//!
//! ```text
//! CSP (Communicating Sequential Processes) 由 Tony Hoare (1978) 提出
//!
//! 核心思想:
//! - 进程 (Process): 独立的计算单元
//! - 通信 (Communication): 进程间通过 channel 交换消息
//! - 同步 (Synchronization): 通信隐含同步
//!
//! 形式化语法:
//! P ::= STOP                    (停止进程)
//!     | SKIP                    (空进程)
//!     | a -> P                  (前缀: 执行动作 a 然后执行 P)
//!     | P □ Q                   (外部选择)
//!     | P ⊓ Q                   (内部选择)
//!     | P || Q                  (并行组合)
//!     | P ||| Q                 (交错组合)
//! ```
//!
//! ### 1.2 Channel 语义
//!
//! ```text
//! Channel 是进程间通信的媒介:
//!
//! c!v  : 在 channel c 上发送值 v (输出)
//! c?x  : 从 channel c 接收值到变量 x (输入)
//!
//! 同步语义:
//! - 发送者等待接收者
//! - 接收者等待发送者
//! - 通信是原子操作
//!
//! 缓冲语义:
//! - 无缓冲: 严格同步 (Golang 默认)
//! - 有缓冲: 异步通信 (容量有限)
//! ```
//!
//! ### 1.3 并发组合
//!
//! ```text
//! 并行组合 (P || Q):
//! - P 和 Q 并发执行
//! - 共享 channel 上的通信需要同步
//! - 独立事件可以交错执行
//!
//! 示例:
//! P = c!1 -> d!2 -> STOP
//! Q = c?x -> e!x -> STOP
//!
//! P || Q 的可能执行:
//! 1. c 上通信 (P 发送 1, Q 接收)
//! 2. P 执行 d!2
//! 3. Q 执行 e!1
//! ```
//!
//! ## 2. Golang CSP 模型
//!
//! ### 2.1 Goroutine
//!
//! ```text
//! Goroutine 是轻量级线程:
//! - 栈大小动态增长 (初始 ~2KB)
//! - M:N 调度模型 (M goroutines on N OS threads)
//! - 抢占式调度 (Go 1.14+)
//!
//! 语法:
//! go func() { ... }()  // 启动新 goroutine
//! ```
//!
//! ### 2.2 Channel
//!
//! ```text
//! Channel 类型:
//! - 无缓冲: make(chan T)       // 同步通信
//! - 有缓冲: make(chan T, n)    // 异步通信，容量 n
//!
//! 操作:
//! - ch <- v      // 发送
//! - v := <-ch    // 接收
//! - close(ch)    // 关闭
//!
//! select 语句:
//! select {
//! case v := <-ch1:
//!     // 处理 ch1
//! case ch2 <- v:
//!     // 发送到 ch2
//! default:
//!     // 非阻塞
//! }
//! ```
//!
//! ## 3. Rust CSP 模型
//!
//! ### 3.1 Async/Await
//!
//! ```text
//! Rust 的异步基于状态机:
//! - async fn 返回 Future
//! - .await 挂起 Future
//! - 非抢占式调度 (cooperative)
//!
//! 语法:
//! async fn foo() { ... }       // 异步函数
//! foo().await                  // 等待完成
//! tokio::spawn(async { ... })  // 生成任务
//! ```
//!
//! ### 3.2 Channel
//!
//! ```text
//! Channel 类型:
//! - mpsc: 多生产者单消费者
//!   - unbounded: 无界队列
//!   - bounded: 有界队列
//! - oneshot: 一次性通信
//! - broadcast: 广播
//! - watch: 观察值变化
//!
//! Tokio mpsc:
//! let (tx, mut rx) = mpsc::channel(100);
//! tx.send(v).await?;
//! let v = rx.recv().await;
//! ```
//!
//! ## 4. Golang vs Rust 对比
//!
//! ```text
//! ┌─────────────────┬──────────────────────────┬──────────────────────────┐
//! │ 特性            │ Golang                   │ Rust                     │
//! ├─────────────────┼──────────────────────────┼──────────────────────────┤
//! │ 并发原语        │ goroutine                │ async task               │
//! │ 启动开销        │ ~2KB 栈                  │ ~64 bytes Future         │
//! │ 调度模型        │ 抢占式                   │ 协作式                   │
//! │ Channel 类型    │ 统一类型                 │ 多种特化类型             │
//! │ select          │ 内置 select 语句         │ tokio::select! 宏        │
//! │ 错误处理        │ panic + recover          │ Result<T, E>             │
//! │ 内存安全        │ GC                       │ 所有权 + 借用检查        │
//! │ 性能            │ GC 暂停                  │ 零成本抽象               │
//! └─────────────────┴──────────────────────────┴──────────────────────────┘
//! ```

use std::time::Duration;
use tokio::sync::mpsc;
use tokio::time::sleep;

/// # 示例 1: 基本 CSP 模式
///
/// 经典的生产者-消费者模式
pub mod producer_consumer {
    use super::*;

    /// Golang 风格的实现 (模拟)
    ///
    /// ```go
    /// func producer(ch chan int) {
    ///     for i := 0; i < 5; i++ {
    ///         ch <- i
    ///         time.Sleep(100 * time.Millisecond)
    ///     }
    ///     close(ch)
    /// }
    ///
    /// func consumer(ch chan int) {
    ///     for v := range ch {
    ///         fmt.Println("消费:", v)
    ///     }
    /// }
    ///
    /// func main() {
    ///     ch := make(chan int, 2)  // 缓冲大小 2
    ///     go producer(ch)
    ///     consumer(ch)
    /// }
    /// ```
    pub mod golang_style {
        use super::*;

        pub async fn producer(tx: mpsc::Sender<i32>) {
            for i in 0..5 {
                println!("  [Go-Producer] 发送: {}", i);
                tx.send(i).await.unwrap();
                sleep(Duration::from_millis(100)).await;
            }
            println!("  [Go-Producer] 完成，关闭 channel");
            drop(tx); // 关闭 channel
        }

        pub async fn consumer(mut rx: mpsc::Receiver<i32>) {
            println!("  [Go-Consumer] 启动");
            while let Some(v) = rx.recv().await {
                println!("  [Go-Consumer] 消费: {}", v);
            }
            println!("  [Go-Consumer] Channel 已关闭，退出");
        }

        pub async fn demo() {
            println!("\n=== Golang 风格: 生产者-消费者 ===");
            let (tx, rx) = mpsc::channel(2); // 缓冲大小 2

            // 启动 goroutine (Rust 中用 tokio::spawn)
            let producer_handle = tokio::spawn(producer(tx));
            let consumer_handle = tokio::spawn(consumer(rx));

            // 等待完成
            let _ = tokio::join!(producer_handle, consumer_handle);
            println!("✓ 完成");
        }
    }

    /// Rust 惯用风格
    pub mod rust_style {
        use super::*;

        /// 使用 Iterator + Stream 的组合
        pub async fn demo() {
            println!("\n=== Rust 惯用风格: 生产者-消费者 ===");

            use tokio_stream::{wrappers::ReceiverStream, StreamExt};

            let (tx, rx) = mpsc::channel(2);

            // 生产者任务
            let producer = tokio::spawn(async move {
                for i in 0..5 {
                    println!("  [Rust-Producer] 发送: {}", i);
                    tx.send(i).await.unwrap();
                    sleep(Duration::from_millis(100)).await;
                }
                println!("  [Rust-Producer] 完成");
            });

            // 消费者: 使用 Stream API
            let consumer = tokio::spawn(async move {
                let mut stream = ReceiverStream::new(rx);
                println!("  [Rust-Consumer] 启动");
                while let Some(v) = stream.next().await {
                    println!("  [Rust-Consumer] 消费: {}", v);
                }
                println!("  [Rust-Consumer] Stream 结束");
            });

            let _ = tokio::join!(producer, consumer);
            println!("✓ 完成");
        }
    }

    pub async fn compare() {
        golang_style::demo().await;
        rust_style::demo().await;
    }
}

/// # 示例 2: Select 模式
///
/// 多路复用 channel 操作
pub mod select_pattern {
    use super::*;

    /// Golang select 示例
    ///
    /// ```go
    /// func main() {
    ///     ch1 := make(chan string)
    ///     ch2 := make(chan string)
    ///
    ///     go func() { ch1 <- "from ch1" }()
    ///     go func() { ch2 <- "from ch2" }()
    ///
    ///     select {
    ///     case msg1 := <-ch1:
    ///         fmt.Println(msg1)
    ///     case msg2 := <-ch2:
    ///         fmt.Println(msg2)
    ///     case <-time.After(1 * time.Second):
    ///         fmt.Println("timeout")
    ///     }
    /// }
    /// ```
    pub mod golang_style {
        use super::*;

        pub async fn demo() {
            println!("\n=== Golang 风格: Select ===");

            let (tx1, mut rx1) = mpsc::channel::<String>(1);
            let (tx2, mut rx2) = mpsc::channel::<String>(1);

            // 启动发送任务
            tokio::spawn(async move {
                sleep(Duration::from_millis(50)).await;
                tx1.send("from ch1".to_string()).await.unwrap();
            });

            tokio::spawn(async move {
                sleep(Duration::from_millis(100)).await;
                tx2.send("from ch2".to_string()).await.unwrap();
            });

            // Rust 的 tokio::select! 宏模拟 Go 的 select
            tokio::select! {
                msg1 = rx1.recv() => {
                    if let Some(msg1) = msg1 {
                        println!("  [Select] 收到 ch1: {}", msg1);
                    }
                }
                msg2 = rx2.recv() => {
                    if let Some(msg2) = msg2 {
                        println!("  [Select] 收到 ch2: {}", msg2);
                    }
                }
                _ = sleep(Duration::from_secs(1)) => {
                    println!("  [Select] 超时");
                }
            }

            println!("✓ 完成");
        }
    }

    /// Rust 的模式匹配增强
    pub mod rust_enhanced {
        use super::*;

        pub async fn demo() {
            println!("\n=== Rust 增强: Select with Pattern Matching ===");

            let (tx1, mut rx1) = mpsc::channel::<Result<i32, String>>(1);
            let (tx2, mut rx2) = mpsc::channel::<Result<i32, String>>(1);

            tokio::spawn(async move {
                sleep(Duration::from_millis(50)).await;
                tx1.send(Ok(42)).await.unwrap();
            });

            tokio::spawn(async move {
                sleep(Duration::from_millis(100)).await;
                tx2.send(Err("error".to_string())).await.unwrap();
            });

            // Rust 的优势: 结合 Result 和模式匹配
            tokio::select! {
                result = rx1.recv() => {
                    match result {
                        Some(Ok(value)) => println!("  [Select] ch1 成功: {}", value),
                        Some(Err(e)) => println!("  [Select] ch1 错误: {}", e),
                        None => println!("  [Select] ch1 已关闭"),
                    }
                }
                result = rx2.recv() => {
                    match result {
                        Some(Ok(value)) => println!("  [Select] ch2 成功: {}", value),
                        Some(Err(e)) => println!("  [Select] ch2 错误: {}", e),
                        None => println!("  [Select] ch2 已关闭"),
                    }
                }
            }

            println!("✓ 完成");
        }
    }

    pub async fn compare() {
        golang_style::demo().await;
        rust_enhanced::demo().await;
    }
}

/// # 示例 3: Worker Pool 模式
///
/// 工作池并发处理任务
pub mod worker_pool {
    use super::*;
    use std::sync::Arc;

    /// Golang 风格
    ///
    /// ```go
    /// func worker(id int, jobs <-chan int, results chan<- int) {
    ///     for j := range jobs {
    ///         fmt.Printf("worker %d processing job %d\n", id, j)
    ///         time.Sleep(time.Second)
    ///         results <- j * 2
    ///     }
    /// }
    ///
    /// func main() {
    ///     jobs := make(chan int, 100)
    ///     results := make(chan int, 100)
    ///
    ///     for w := 1; w <= 3; w++ {
    ///         go worker(w, jobs, results)
    ///     }
    ///
    ///     for j := 1; j <= 5; j++ {
    ///         jobs <- j
    ///     }
    ///     close(jobs)
    ///
    ///     for a := 1; a <= 5; a++ {
    ///         <-results
    ///     }
    /// }
    /// ```
    pub mod golang_style {
        use super::*;

        #[allow(dead_code)]
        async fn worker(id: usize, mut jobs: mpsc::Receiver<i32>, results: mpsc::Sender<i32>) {
            while let Some(j) = jobs.recv().await {
                println!("  [Worker {}] 处理任务 {}", id, j);
                sleep(Duration::from_millis(100)).await;
                results.send(j * 2).await.unwrap();
            }
            println!("  [Worker {}] 退出", id);
        }

        pub async fn demo() {
            println!("\n=== Golang 风格: Worker Pool ===");

            let (job_tx, job_rx) = mpsc::channel(100);
            let (result_tx, mut result_rx) = mpsc::channel(100);

            // 创建 3 个 worker
            let mut workers = vec![];

            // 简化版本: 使用 Arc + tokio::sync::Mutex
            use tokio::sync::Mutex;
            let shared_rx = Arc::new(Mutex::new(job_rx));

            for worker_id in 1..=3 {
                let rx = shared_rx.clone();
                let tx = result_tx.clone();
                let handle = tokio::spawn(async move {
                    loop {
                        let job = {
                            let mut rx_guard = rx.lock().await;
                            rx_guard.recv().await
                        };
                        match job {
                            Some(j) => {
                                println!("  [Worker {}] 处理任务 {}", worker_id, j);
                                sleep(Duration::from_millis(100)).await;
                                tx.send(j * 2).await.unwrap();
                            }
                            None => {
                                println!("  [Worker {}] 退出", worker_id);
                                break;
                            }
                        }
                    }
                });
                workers.push(handle);
            }

            drop(result_tx); // 关闭发送端

            // 发送任务
            for j in 1..=5 {
                println!("  [Main] 提交任务 {}", j);
                job_tx.send(j).await.unwrap();
            }
            drop(job_tx); // 关闭任务 channel

            // 收集结果
            let mut count = 0;
            while let Some(r) = result_rx.recv().await {
                println!("  [Main] 收到结果: {}", r);
                count += 1;
            }

            // 等待 workers
            for handle in workers {
                handle.await.unwrap();
            }

            println!("  总共收到 {} 个结果", count);
            println!("✓ 完成");
        }
    }

    /// Rust 惯用风格: 使用 Semaphore
    pub mod rust_style {
        use super::*;
        use tokio::sync::Semaphore;

        pub async fn demo() {
            println!("\n=== Rust 惯用风格: Worker Pool with Semaphore ===");

            let semaphore = Arc::new(Semaphore::new(3)); // 限制并发数为 3
            let mut handles = vec![];

            for j in 1..=5 {
                let sem = semaphore.clone();
                let handle = tokio::spawn(async move {
                    let _permit = sem.acquire().await.unwrap();
                    println!("  [Task {}] 开始处理", j);
                    sleep(Duration::from_millis(100)).await;
                    let result = j * 2;
                    println!("  [Task {}] 完成，结果: {}", j, result);
                    result
                });
                handles.push(handle);
            }

            // 收集结果
            for handle in handles {
                let result = handle.await.unwrap();
                println!("  [Main] 收到结果: {}", result);
            }

            println!("✓ 完成");
        }
    }

    pub async fn compare() {
        golang_style::demo().await;
        rust_style::demo().await;
    }
}

/// # 示例 4: Pipeline 模式
///
/// 流水线处理数据
pub mod pipeline {
    use super::*;

    /// Golang 风格
    ///
    /// ```go
    /// func gen(nums ...int) <-chan int {
    ///     out := make(chan int)
    ///     go func() {
    ///         for _, n := range nums {
    ///             out <- n
    ///         }
    ///         close(out)
    ///     }()
    ///     return out
    /// }
    ///
    /// func sq(in <-chan int) <-chan int {
    ///     out := make(chan int)
    ///     go func() {
    ///         for n := range in {
    ///             out <- n * n
    ///         }
    ///         close(out)
    ///     }()
    ///     return out
    /// }
    /// ```
    pub mod golang_style {
        use super::*;

        async fn generate_numbers(nums: Vec<i32>) -> mpsc::Receiver<i32> {
            let (tx, rx) = mpsc::channel(10);
            tokio::spawn(async move {
                for n in nums {
                    println!("  [Gen] 生成: {}", n);
                    tx.send(n).await.unwrap();
                }
                println!("  [Gen] 完成");
            });
            rx
        }

        async fn square(mut input: mpsc::Receiver<i32>) -> mpsc::Receiver<i32> {
            let (tx, rx) = mpsc::channel(10);
            tokio::spawn(async move {
                while let Some(n) = input.recv().await {
                    let result = n * n;
                    println!("  [Square] {} -> {}", n, result);
                    tx.send(result).await.unwrap();
                }
                println!("  [Square] 完成");
            });
            rx
        }

        async fn sum(mut input: mpsc::Receiver<i32>) -> i32 {
            let mut total = 0;
            while let Some(n) = input.recv().await {
                total += n;
                println!("  [Sum] 累加: {}, 当前总和: {}", n, total);
            }
            println!("  [Sum] 最终总和: {}", total);
            total
        }

        pub async fn demo() {
            println!("\n=== Golang 风格: Pipeline ===");

            let nums = vec![1, 2, 3, 4, 5];
            let rx1 = generate_numbers(nums).await;
            let rx2 = square(rx1).await;
            let result = sum(rx2).await;

            println!("  结果: {}", result);
            println!("✓ 完成");
        }
    }

    /// Rust 惯用风格: 使用 Stream
    pub mod rust_style {
        use super::*;
            use tokio_stream::{wrappers::ReceiverStream, StreamExt};

            pub async fn demo() {
                println!("\n=== Rust 惯用风格: Pipeline with Stream ===");

                let (tx, rx) = mpsc::channel(10);

                // 生成器
                tokio::spawn(async move {
                    for n in 1..=5 {
                        println!("  [Gen] 生成: {}", n);
                        tx.send(n).await.unwrap();
                    }
                    println!("  [Gen] 完成");
                });

                // 使用 Stream API 构建流水线
                let mut total = 0;
                let mut stream = ReceiverStream::new(rx).map(|n| {
                    let sq = n * n;
                    println!("  [Square] {} -> {}", n, sq);
                    sq
                });

                while let Some(n) = stream.next().await {
                    total += n;
                    println!("  [Sum] 累加: {}, 当前总和: {}", n, total);
                }

                let result = total;

            println!("  结果: {}", result);
            println!("✓ 完成");
        }
    }

    pub async fn compare() {
        golang_style::demo().await;
        rust_style::demo().await;
    }
}

/// # 示例 5: 扇入/扇出模式 (Fan-in/Fan-out)
///
/// 多个生产者，多个消费者
pub mod fan_in_out {
    use super::*;

    pub async fn demo() {
        println!("\n=== 扇入/扇出模式 ===");

        let (tx, mut rx) = mpsc::channel(100);

        // 扇出: 3 个生产者
        println!("  启动 3 个生产者...");
        for i in 0..3 {
            let tx = tx.clone();
            tokio::spawn(async move {
                for j in 0..3 {
                    let value = i * 10 + j;
                    println!("    [Producer {}] 发送: {}", i, value);
                    tx.send(value).await.unwrap();
                    sleep(Duration::from_millis(50)).await;
                }
                println!("    [Producer {}] 完成", i);
            });
        }
        drop(tx); // 关闭原始发送端

        // 扇入: 收集所有结果
        println!("  消费者收集结果...");
        let mut results = vec![];
        while let Some(v) = rx.recv().await {
            println!("    [Consumer] 收到: {}", v);
            results.push(v);
        }

        results.sort();
        println!("  所有结果 (排序后): {:?}", results);
        println!("✓ 完成");
    }
}

/// # 综合示例: 运行所有演示
pub async fn run_all_examples() {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║       CSP 模型对比分析 (Rust vs Golang)                 ║");
    println!("║       CSP Model Comparison Analysis                      ║");
    println!("╚══════════════════════════════════════════════════════════╝");

    // 1. 生产者-消费者
    producer_consumer::compare().await;

    // 2. Select 模式
    select_pattern::compare().await;

    // 3. Worker Pool
    worker_pool::compare().await;

    // 4. Pipeline
    pipeline::compare().await;

    // 5. 扇入/扇出
    fan_in_out::demo().await;

    println!("\n════════════════════════════════════════════════════════════");
    println!("语义对比总结:");
    println!("════════════════════════════════════════════════════════════");
    println!("
1. 基本等价性:
   ✓ Golang goroutine <-> Rust async task
   ✓ Golang channel <-> Rust mpsc channel
   ✓ Golang select <-> Rust tokio::select!

2. 语义差异:
   • Golang: 抢占式调度，更接近系统线程
   • Rust: 协作式调度，更轻量级

3. 类型安全:
   • Golang: 运行时检查
   • Rust: 编译期检查 (所有权、借用)

4. 性能特性:
   • Golang: GC 暂停
   • Rust: 零成本抽象，无 GC

5. 开发体验:
   • Golang: 语法更简洁，内置支持
   • Rust: 类型系统更强大，错误处理更显式
    ");
    println!("════════════════════════════════════════════════════════════\n");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_producer_consumer() {
        producer_consumer::golang_style::demo().await;
    }

    #[tokio::test]
    async fn test_select() {
        select_pattern::golang_style::demo().await;
    }

    #[tokio::test]
    async fn test_pipeline() {
        pipeline::golang_style::demo().await;
    }

    #[tokio::test]
    async fn test_fan_in_out() {
        fan_in_out::demo().await;
    }
}

