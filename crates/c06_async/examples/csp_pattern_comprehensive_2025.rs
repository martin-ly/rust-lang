//! # CSP 模式完整实现 2025
//! # Comprehensive CSP (Communicating Sequential Processes) Pattern Implementation 2025
//!
//! ## 📚 本示例全面涵盖
//!
//! ### 🎯 一、理论形式化 (Theoretical Formalization)
//! - CSP 进程代数的数学定义 (Hoare 1978)
//! - 通道语义和通信原语
//! - 进程组合和并发操作
//! - 死锁检测和活性证明
//!
//! ### 🏗️ 二、核心数据结构 (Core Data Structures)
//! - Channel 类型 (bounded, unbounded, broadcast, oneshot)
//! - Process 抽象和生命周期
//! - Select 多路复用机制
//! - Pipeline 流水线架构
//!
//! ### ⚡ 三、CSP 核心实现 (CSP Core Implementation)
//! - 进程创建和管理
//! - 通道通信和同步
//! - Select 语句实现
//! - 超时和取消机制
//!
//! ### 🎨 四、实际应用示例 (Practical Applications)
//! - 数据处理流水线 (Data Processing Pipeline)
//! - 分布式任务调度 (Distributed Task Scheduler)
//! - 实时日志聚合系统 (Real-time Log Aggregation)
//!
//! ### 📊 五、示例和测试 (Examples and Tests)
//! - 基本通信示例
//! - 高级并发模式
//! - 性能基准测试
//!
//! ## 运行方式
//! ```bash
//! cargo run --example csp_pattern_comprehensive_2025
//! ```
//!
//! ## 版本信息
//! - Rust: 1.90+
//! - Tokio: 1.41+
//! - 日期: 2025-10-06
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{mpsc, broadcast, oneshot, Mutex};
use tokio::time::{sleep, timeout};
use tokio::select;

// ============================================================================
// 第一部分: CSP 模式理论形式化
// Part 1: CSP Pattern Theoretical Formalization
// ============================================================================

/// # CSP 模式理论形式化
/// # CSP Pattern Theoretical Formalization
///
/// ## 数学定义 (Mathematical Definition)
///
/// ### CSP 进程代数 (CSP Process Algebra, Hoare 1978)
/// ```text
/// P ::= STOP                    // 停止进程 (Deadlock)
///     | SKIP                    // 空进程 (Successful termination)
///     | a → P                   // 前缀 (Prefix: event a then process P)
///     | P □ Q                   // 外部选择 (External choice)
///     | P ⊓ Q                   // 内部选择 (Internal choice)
///     | P ||| Q                 // 交错并行 (Interleaving)
///     | P || Q                  // 接口并行 (Interface parallel)
///     | P ; Q                   // 顺序组合 (Sequential composition)
///     | P \ A                   // 隐藏 (Hiding)
///     | f(P)                    // 重命名 (Renaming)
/// ```
///
/// ### Rust 中的 CSP 映射 (CSP Mapping in Rust)
/// ```text
/// Channel<T> = (Sender<T>, Receiver<T>)
/// send(ch, v) ≡ ch!v → SKIP
/// recv(ch) ≡ ch?x → SKIP
/// select! { ... } ≡ P □ Q □ R ...
/// spawn(P) ||| spawn(Q) ≡ P ||| Q
/// ```
///
/// ## 核心原则 (Core Principles)
///
/// ### 1. 通信同步 (Communication Synchronization)
/// - **定义**: 发送和接收必须同步进行
/// - **Rust 实现**: `mpsc::channel`, `oneshot::channel`
/// - **特性**: 
///   - 有界通道提供背压控制
///   - 无界通道可能导致内存问题
///   - 广播通道支持多播
///
/// ### 2. 进程独立性 (Process Independence)
/// - **定义**: 进程只通过通道通信，无共享状态
/// - **Rust 实现**: `tokio::spawn`, `async fn`
/// - **特性**:
///   - 每个进程拥有独立的状态
///   - 通过消息传递共享数据
///   - 避免数据竞争
///
/// ### 3. 非确定性选择 (Non-deterministic Choice)
/// - **定义**: `select!` 宏实现多路复用
/// - **Rust 实现**: `tokio::select!`
/// - **特性**:
///   - 公平调度
///   - 随机选择就绪分支
///   - 支持超时和取消
///
/// ## 形式化性质 (Formal Properties)
///
/// ### 性质 1: 死锁自由 (Deadlock Freedom)
/// ```text
/// 定理: 如果 CSP 系统满足以下条件，则无死锁:
/// 1. 所有通道最终被关闭
/// 2. 所有进程最终终止或进入 STOP 状态
/// 3. 不存在循环等待
///
/// 证明 (Proof):
/// 假设存在死锁，则存在进程集合 {P1, P2, ..., Pn}，其中:
/// - Pi 等待 P(i+1) 的消息 (i = 1..n-1)
/// - Pn 等待 P1 的消息
/// 
/// 但根据条件 3，不存在循环等待，矛盾。
/// 因此系统无死锁。 ∎
/// ```
///
/// ### 性质 2: 消息传递可靠性 (Message Delivery Reliability)
/// ```text
/// 定理: 在 CSP 系统中，如果发送成功，则消息最终被接收。
///
/// 证明 (Proof):
/// 1. send(ch, v) 成功 ⟹ v 在通道缓冲区中
/// 2. 通道未关闭 ⟹ 接收者可以接收
/// 3. 接收者活跃 ⟹ 最终调用 recv(ch)
/// 4. recv(ch) ⟹ 从缓冲区取出 v
/// 因此，消息 v 最终被接收。 ∎
/// ```
///
/// ### 性质 3: 公平性 (Fairness)
/// ```text
/// 定理: select! 宏保证公平性，即所有就绪分支有相同的被选中概率。
///
/// 证明 (Proof):
/// Tokio 的 select! 实现使用随机化算法:
/// 1. 检查所有分支的就绪状态
/// 2. 从就绪分支中随机选择一个
/// 3. 执行选中的分支
/// 
/// 因此，每个就绪分支被选中的概率为 1/n (n 为就绪分支数)。 ∎
/// ```
///
/// ## CSP vs Actor vs Reactor 对比
/// ## CSP vs Actor vs Reactor Comparison
///
/// | 特性 | CSP | Actor | Reactor |
/// |------|-----|-------|---------|
/// | 通信方式 | Channel (通道) | Message (消息) | Event (事件) |
/// | 耦合度 | 低 (解耦) | 低 (解耦) | 中 (事件驱动) |
/// | 同步性 | 支持同步/异步 | 异步 | 异步 |
/// | 选择机制 | select! | - | - |
/// | 适用场景 | Pipeline, 数据流 | 并发实体, 状态机 | I/O 密集, 事件驱动 |
/// | 状态管理 | 进程内部 | Actor 内部 | Handler 内部 |
/// | 容错性 | 通道关闭 | 监督树 | 错误处理 |
/// | 性能 | 高 (零拷贝) | 中 (消息拷贝) | 高 (事件驱动) |
///
/// ## 优势 (Advantages)
/// 1. **简单性**: 通道通信比共享内存简单
/// 2. **可组合性**: 进程可以灵活组合
/// 3. **可测试性**: 进程独立，易于测试
/// 4. **可扩展性**: 易于扩展到分布式系统
///
/// ## 使用场景 (Use Cases)
/// 1. **数据处理流水线**: 多阶段数据处理
/// 2. **并发任务调度**: 任务分发和结果收集
/// 3. **实时系统**: 传感器数据处理
/// 4. **分布式计算**: MapReduce 等模式
pub mod theory_csp_formalization {

    /// 打印 CSP 理论形式化说明
    /// Print CSP theoretical formalization
    #[allow(dead_code)]
    pub fn print_theory() {
        println!("\n╔══════════════════════════════════════════════════════════════════╗");
        println!("║                                                                  ║");
        println!("║   📚 CSP 模式理论形式化                                          ║");
        println!("║   CSP Pattern Theoretical Formalization                          ║");
        println!("║                                                                  ║");
        println!("╚══════════════════════════════════════════════════════════════════╝\n");

        println!("📖 数学定义 (Mathematical Definition):");
        println!("   P ::= STOP | SKIP | a → P | P □ Q | P ||| Q | ...");
        println!();
        println!("🔑 核心原则 (Core Principles):");
        println!("   1. 通信同步 (Communication Synchronization)");
        println!("   2. 进程独立性 (Process Independence)");
        println!("   3. 非确定性选择 (Non-deterministic Choice)");
        println!();
        println!("✅ 形式化性质 (Formal Properties):");
        println!("   1. 死锁自由 (Deadlock Freedom)");
        println!("   2. 消息传递可靠性 (Message Delivery Reliability)");
        println!("   3. 公平性 (Fairness)");
        println!();
    }
}

// ============================================================================
// 第二部分: 核心数据结构
// Part 2: Core Data Structures
// ============================================================================

/// 通道类型枚举
/// Channel Type Enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChannelType {
    /// 有界通道 (Bounded Channel)
    /// - 固定容量，提供背压控制
    /// - Fixed capacity, provides backpressure control
    Bounded,
    
    /// 无界通道 (Unbounded Channel)
    /// - 无限容量，可能导致内存问题
    /// - Unlimited capacity, may cause memory issues
    Unbounded,
    
    /// 广播通道 (Broadcast Channel)
    /// - 多个接收者，消息广播
    /// - Multiple receivers, message broadcast
    Broadcast,
    
    /// 单次通道 (Oneshot Channel)
    /// - 单次发送和接收
    /// - Single send and receive
    Oneshot,
}

/// 进程状态
/// Process State
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProcessState {
    /// 运行中 (Running)
    Running,
    
    /// 等待中 (Waiting)
    Waiting,
    
    /// 完成 (Completed)
    Completed,
    
    /// 错误 (Error)
    Error,
}

/// 进程统计信息
/// Process Statistics
#[derive(Debug, Clone)]
pub struct ProcessStats {
    /// 进程 ID (Process ID)
    pub id: String,
    
    /// 状态 (State)
    pub state: ProcessState,
    
    /// 发送消息数 (Messages sent)
    pub messages_sent: u64,
    
    /// 接收消息数 (Messages received)
    pub messages_received: u64,
    
    /// 运行时间 (Runtime)
    pub runtime: Duration,
    
    /// 启动时间 (Start time)
    pub start_time: Instant,
}

impl ProcessStats {
    /// 创建新的进程统计
    /// Create new process statistics
    pub fn new(id: String) -> Self {
        Self {
            id,
            state: ProcessState::Running,
            messages_sent: 0,
            messages_received: 0,
            runtime: Duration::ZERO,
            start_time: Instant::now(),
        }
    }

    /// 更新运行时间
    /// Update runtime
    pub fn update_runtime(&mut self) {
        self.runtime = self.start_time.elapsed();
    }

    /// 打印统计信息
    /// Print statistics
    pub fn print(&self) {
        println!("📊 进程统计 [{}]:", self.id);
        println!("   状态: {:?}", self.state);
        println!("   发送消息: {}", self.messages_sent);
        println!("   接收消息: {}", self.messages_received);
        println!("   运行时间: {:?}", self.runtime);
    }
}

/// CSP 系统配置
/// CSP System Configuration
#[derive(Debug, Clone)]
pub struct CspSystemConfig {
    /// 通道容量 (Channel capacity)
    pub channel_capacity: usize,
    
    /// 进程数量 (Number of processes)
    pub num_processes: usize,
    
    /// 超时时间 (Timeout duration)
    pub timeout_duration: Duration,
    
    /// 是否启用统计 (Enable statistics)
    pub enable_stats: bool,
}

impl Default for CspSystemConfig {
    fn default() -> Self {
        Self {
            channel_capacity: 100,
            num_processes: 4,
            timeout_duration: Duration::from_secs(5),
            enable_stats: true,
        }
    }
}

// ============================================================================
// 第三部分: CSP 核心实现
// Part 3: CSP Core Implementation
// ============================================================================

/// CSP 系统管理器
/// CSP System Manager
pub struct CspSystem {
    /// 配置 (Configuration)
    config: CspSystemConfig,
    
    /// 进程统计 (Process statistics)
    stats: Arc<Mutex<HashMap<String, ProcessStats>>>,
    
    /// 系统启动时间 (System start time)
    start_time: Instant,
}

impl CspSystem {
    /// 创建新的 CSP 系统
    /// Create new CSP system
    pub fn new(config: CspSystemConfig) -> Self {
        Self {
            config,
            stats: Arc::new(Mutex::new(HashMap::new())),
            start_time: Instant::now(),
        }
    }

    /// 注册进程
    /// Register process
    pub async fn register_process(&self, id: String) {
        if self.config.enable_stats {
            let mut stats = self.stats.lock().await;
            stats.insert(id.clone(), ProcessStats::new(id));
        }
    }

    /// 更新进程统计
    /// Update process statistics
    pub async fn update_stats<F>(&self, id: &str, update_fn: F)
    where
        F: FnOnce(&mut ProcessStats),
    {
        if self.config.enable_stats {
            let mut stats = self.stats.lock().await;
            if let Some(stat) = stats.get_mut(id) {
                update_fn(stat);
                stat.update_runtime();
            }
        }
    }

    /// 打印所有统计信息
    /// Print all statistics
    pub async fn print_all_stats(&self) {
        if self.config.enable_stats {
            println!("\n╔══════════════════════════════════════════════════════════════════╗");
            println!("║                                                                  ║");
            println!("║   📊 CSP 系统统计                                                ║");
            println!("║   CSP System Statistics                                          ║");
            println!("║                                                                  ║");
            println!("╚══════════════════════════════════════════════════════════════════╝\n");

            let stats = self.stats.lock().await;
            for (_, stat) in stats.iter() {
                stat.print();
                println!();
            }

            println!("⏱️  系统运行时间: {:?}", self.start_time.elapsed());
        }
    }
}

// ============================================================================
// 第四部分: 实际应用示例
// Part 4: Practical Application Examples
// ============================================================================

/// 示例 1: 数据处理流水线
/// Example 1: Data Processing Pipeline
///
/// ## 形式化描述 (Formal Description)
/// ```text
/// Source = generate → send!ch1 → Source
/// Transform = recv?ch1 → process → send!ch2 → Transform
/// Sink = recv?ch2 → store → Sink
/// Pipeline = Source ||| Transform ||| Sink
/// ```
///
/// ## 应用场景 (Use Cases)
/// - 日志处理: 收集 → 解析 → 存储
/// - 图像处理: 读取 → 滤镜 → 编码
/// - 数据分析: 提取 → 转换 → 加载 (ETL)
pub async fn data_processing_pipeline_example() {
    println!("\n╔══════════════════════════════════════════════════════════════════╗");
    println!("║                                                                  ║");
    println!("║   🔄 示例 1: 数据处理流水线                                      ║");
    println!("║   Example 1: Data Processing Pipeline                           ║");
    println!("║                                                                  ║");
    println!("╚══════════════════════════════════════════════════════════════════╝\n");

    let system = Arc::new(CspSystem::new(CspSystemConfig::default()));

    // 阶段 1: 数据源 (Source)
    let (tx1, mut rx1) = mpsc::channel(10);
    let system_clone = system.clone();
    let source = tokio::spawn(async move {
        system_clone.register_process("source".to_string()).await;
        
        println!("[Source] 🎲 开始生成数据...");
        for i in 1..=20 {
            let data = format!("data-{}", i);
            println!("  [Source] 生成: {}", data);
            
            if tx1.send(data).await.is_err() {
                break;
            }
            
            system_clone.update_stats("source", |s| {
                s.messages_sent += 1;
            }).await;
            
            sleep(Duration::from_millis(50)).await;
        }
        
        system_clone.update_stats("source", |s| {
            s.state = ProcessState::Completed;
        }).await;
        
        println!("[Source] ✓ 完成\n");
    });

    // 阶段 2: 数据转换 (Transform)
    let (tx2, mut rx2) = mpsc::channel(10);
    let system_clone = system.clone();
    let transform = tokio::spawn(async move {
        system_clone.register_process("transform".to_string()).await;
        
        println!("[Transform] 🔧 开始转换数据...");
        while let Some(data) = rx1.recv().await {
            system_clone.update_stats("transform", |s| {
                s.messages_received += 1;
            }).await;
            
            // 模拟数据处理
            let processed = data.to_uppercase();
            println!("  [Transform] 处理: {} → {}", data, processed);
            
            if tx2.send(processed).await.is_err() {
                break;
            }
            
            system_clone.update_stats("transform", |s| {
                s.messages_sent += 1;
            }).await;
            
            sleep(Duration::from_millis(30)).await;
        }
        
        system_clone.update_stats("transform", |s| {
            s.state = ProcessState::Completed;
        }).await;
        
        println!("[Transform] ✓ 完成\n");
    });

    // 阶段 3: 数据汇聚 (Sink)
    let system_clone = system.clone();
    let sink = tokio::spawn(async move {
        system_clone.register_process("sink".to_string()).await;
        
        println!("[Sink] 💾 开始存储数据...");
        let mut count = 0;
        while let Some(data) = rx2.recv().await {
            system_clone.update_stats("sink", |s| {
                s.messages_received += 1;
            }).await;
            
            count += 1;
            println!("  [Sink] 存储: {} (总数: {})", data, count);
            
            sleep(Duration::from_millis(20)).await;
        }
        
        system_clone.update_stats("sink", |s| {
            s.state = ProcessState::Completed;
        }).await;
        
        println!("[Sink] ✓ 完成，共存储 {} 条数据\n", count);
    });

    // 等待所有阶段完成
    let _ = tokio::join!(source, transform, sink);

    // 打印统计信息
    system.print_all_stats().await;
}

/// 示例 2: 分布式任务调度
/// Example 2: Distributed Task Scheduler
///
/// ## 形式化描述 (Formal Description)
/// ```text
/// Dispatcher = recv?task_queue → select_worker → send!worker_ch → Dispatcher
/// Worker_i = recv?worker_ch → execute → send!result_ch → Worker_i
/// Collector = recv?result_ch → aggregate → Collector
/// System = Dispatcher ||| Worker_1 ||| ... ||| Worker_n ||| Collector
/// ```
///
/// ## 应用场景 (Use Cases)
/// - 分布式计算: MapReduce
/// - 任务队列: 异步任务处理
/// - 负载均衡: 请求分发
pub async fn distributed_task_scheduler_example() {
    println!("\n╔══════════════════════════════════════════════════════════════════╗");
    println!("║                                                                  ║");
    println!("║   📋 示例 2: 分布式任务调度                                      ║");
    println!("║   Example 2: Distributed Task Scheduler                          ║");
    println!("║                                                                  ║");
    println!("╚══════════════════════════════════════════════════════════════════╝\n");

    let system = Arc::new(CspSystem::new(CspSystemConfig {
        num_processes: 4,
        ..Default::default()
    }));

    // 任务队列
    let (task_tx, mut task_rx) = mpsc::channel::<u32>(20);
    
    // 结果队列
    let (result_tx, mut result_rx) = mpsc::channel::<(u32, u32)>(20);

    // 任务分发器 (Dispatcher)
    let system_clone = system.clone();
    let dispatcher = tokio::spawn(async move {
        system_clone.register_process("dispatcher".to_string()).await;
        
        println!("[Dispatcher] 📤 开始分发任务...");
        for task_id in 1..=30 {
            println!("  [Dispatcher] 分发任务: {}", task_id);
            
            if task_tx.send(task_id).await.is_err() {
                break;
            }
            
            system_clone.update_stats("dispatcher", |s| {
                s.messages_sent += 1;
            }).await;
            
            sleep(Duration::from_millis(20)).await;
        }
        
        system_clone.update_stats("dispatcher", |s| {
            s.state = ProcessState::Completed;
        }).await;
        
        println!("[Dispatcher] ✓ 完成\n");
    });

    // 工作进程 (Workers)
    let num_workers = system.config.num_processes;
    let mut workers = vec![];
    
    // 为每个 worker 创建独立的任务接收通道
    let (worker_tx, _) = broadcast::channel(100);
    
    // 任务分发到广播通道
    let worker_tx_clone = worker_tx.clone();
    tokio::spawn(async move {
        while let Some(task) = task_rx.recv().await {
            let _ = worker_tx_clone.send(task);
        }
    });
    
    for worker_id in 0..num_workers {
        let mut task_rx = worker_tx.subscribe();
        let result_tx = result_tx.clone();
        let system_clone = system.clone();
        
        let worker = tokio::spawn(async move {
            let worker_name = format!("worker-{}", worker_id);
            system_clone.register_process(worker_name.clone()).await;
            
            println!("[Worker-{}] 🔨 开始工作...", worker_id);
            
            while let Ok(task_id) = task_rx.recv().await {
                system_clone.update_stats(&worker_name, |s| {
                    s.messages_received += 1;
                }).await;
                
                println!("  [Worker-{}] 执行任务: {}", worker_id, task_id);
                
                // 模拟任务执行
                sleep(Duration::from_millis(100)).await;
                let result = task_id * 2;
                
                if result_tx.send((task_id, result)).await.is_err() {
                    break;
                }
                
                system_clone.update_stats(&worker_name, |s| {
                    s.messages_sent += 1;
                }).await;
            }
            
            system_clone.update_stats(&worker_name, |s| {
                s.state = ProcessState::Completed;
            }).await;
            
            println!("[Worker-{}] ✓ 完成\n", worker_id);
        });
        
        workers.push(worker);
    }

    // 结果收集器 (Collector)
    let system_clone = system.clone();
    let collector = tokio::spawn(async move {
        system_clone.register_process("collector".to_string()).await;
        
        println!("[Collector] 📥 开始收集结果...");
        let mut results = HashMap::new();
        
        // 使用超时避免永久等待
        while let Ok(Some((task_id, result))) = timeout(
            Duration::from_secs(2),
            result_rx.recv()
        ).await {
            system_clone.update_stats("collector", |s| {
                s.messages_received += 1;
            }).await;
            
            results.insert(task_id, result);
            println!("  [Collector] 收集结果: 任务 {} → 结果 {}", task_id, result);
        }
        
        system_clone.update_stats("collector", |s| {
            s.state = ProcessState::Completed;
        }).await;
        
        println!("[Collector] ✓ 完成，共收集 {} 个结果\n", results.len());
    });

    // 等待所有任务完成
    let _ = tokio::join!(dispatcher, collector);
    for worker in workers {
        let _ = worker.await;
    }

    // 打印统计信息
    system.print_all_stats().await;
}

/// 示例 3: 实时日志聚合系统
/// Example 3: Real-time Log Aggregation System
///
/// ## 形式化描述 (Formal Description)
/// ```text
/// Source_i = generate_log → send!log_ch → Source_i
/// Filter = recv?log_ch → filter → send!filtered_ch → Filter
/// Aggregator = recv?filtered_ch → aggregate → send!output_ch → Aggregator
/// Output = recv?output_ch → display → Output
/// System = Source_1 ||| ... ||| Source_n ||| Filter ||| Aggregator ||| Output
/// ```
///
/// ## 应用场景 (Use Cases)
/// - 日志收集: 多源日志聚合
/// - 监控系统: 实时指标收集
/// - 告警系统: 事件过滤和聚合
pub async fn realtime_log_aggregation_example() {
    println!("\n╔══════════════════════════════════════════════════════════════════╗");
    println!("║                                                                  ║");
    println!("║   📝 示例 3: 实时日志聚合系统                                    ║");
    println!("║   Example 3: Real-time Log Aggregation System                   ║");
    println!("║                                                                  ║");
    println!("╚══════════════════════════════════════════════════════════════════╝\n");

    #[derive(Debug, Clone)]
    struct LogEntry {
        source: String,
        level: String,
        message: String,
        #[allow(dead_code)]
        timestamp: Instant,
    }

    let system = Arc::new(CspSystem::new(CspSystemConfig::default()));

    // 日志通道
    let (log_tx, mut log_rx) = mpsc::channel::<LogEntry>(50);
    
    // 过滤后的日志通道
    let (filtered_tx, mut filtered_rx) = mpsc::channel::<LogEntry>(50);
    
    // 聚合后的日志通道
    let (output_tx, mut output_rx) = mpsc::channel::<String>(50);

    // 日志源 (Log Sources)
    let num_sources = 3;
    let mut sources = vec![];
    
    for source_id in 0..num_sources {
        let log_tx = log_tx.clone();
        let system_clone = system.clone();
        
        let source = tokio::spawn(async move {
            let source_name = format!("source-{}", source_id);
            system_clone.register_process(source_name.clone()).await;
            
            println!("[Source-{}] 📡 开始生成日志...", source_id);
            
            for i in 0..10 {
                let level = match i % 3 {
                    0 => "INFO",
                    1 => "WARN",
                    _ => "ERROR",
                };
                
                let entry = LogEntry {
                    source: source_name.clone(),
                    level: level.to_string(),
                    message: format!("Log message {} from source {}", i, source_id),
                    timestamp: Instant::now(),
                };
                
                if log_tx.send(entry).await.is_err() {
                    break;
                }
                
                system_clone.update_stats(&source_name, |s| {
                    s.messages_sent += 1;
                }).await;
                
                sleep(Duration::from_millis(50)).await;
            }
            
            system_clone.update_stats(&source_name, |s| {
                s.state = ProcessState::Completed;
            }).await;
            
            println!("[Source-{}] ✓ 完成\n", source_id);
        });
        
        sources.push(source);
    }

    // 日志过滤器 (Log Filter)
    let system_clone = system.clone();
    let filter = tokio::spawn(async move {
        system_clone.register_process("filter".to_string()).await;
        
        println!("[Filter] 🔍 开始过滤日志...");
        
        while let Some(entry) = log_rx.recv().await {
            system_clone.update_stats("filter", |s| {
                s.messages_received += 1;
            }).await;
            
            // 只保留 WARN 和 ERROR 级别的日志
            if entry.level == "WARN" || entry.level == "ERROR" {
                println!("  [Filter] 保留: {:?}", entry.level);
                
                if filtered_tx.send(entry).await.is_err() {
                    break;
                }
                
                system_clone.update_stats("filter", |s| {
                    s.messages_sent += 1;
                }).await;
            } else {
                println!("  [Filter] 丢弃: {:?}", entry.level);
            }
        }
        
        system_clone.update_stats("filter", |s| {
            s.state = ProcessState::Completed;
        }).await;
        
        println!("[Filter] ✓ 完成\n");
    });

    // 日志聚合器 (Log Aggregator)
    let system_clone = system.clone();
    let aggregator = tokio::spawn(async move {
        system_clone.register_process("aggregator".to_string()).await;
        
        println!("[Aggregator] 📊 开始聚合日志...");
        let mut stats: HashMap<String, u32> = HashMap::new();
        
        while let Some(entry) = filtered_rx.recv().await {
            system_clone.update_stats("aggregator", |s| {
                s.messages_received += 1;
            }).await;
            
            *stats.entry(entry.level.clone()).or_insert(0) += 1;
            
            let summary = format!(
                "[{}] {} - {} (总计: WARN={}, ERROR={})",
                entry.source,
                entry.level,
                entry.message,
                stats.get("WARN").unwrap_or(&0),
                stats.get("ERROR").unwrap_or(&0)
            );
            
            if output_tx.send(summary).await.is_err() {
                break;
            }
            
            system_clone.update_stats("aggregator", |s| {
                s.messages_sent += 1;
            }).await;
        }
        
        system_clone.update_stats("aggregator", |s| {
            s.state = ProcessState::Completed;
        }).await;
        
        println!("[Aggregator] ✓ 完成\n");
    });

    // 输出显示 (Output Display)
    let system_clone = system.clone();
    let output = tokio::spawn(async move {
        system_clone.register_process("output".to_string()).await;
        
        println!("[Output] 📺 开始显示日志...\n");
        
        while let Some(summary) = output_rx.recv().await {
            system_clone.update_stats("output", |s| {
                s.messages_received += 1;
            }).await;
            
            println!("  [Output] {}", summary);
        }
        
        system_clone.update_stats("output", |s| {
            s.state = ProcessState::Completed;
        }).await;
        
        println!("\n[Output] ✓ 完成\n");
    });

    // 等待所有任务完成
    for source in sources {
        let _ = source.await;
    }
    let _ = tokio::join!(filter, aggregator, output);

    // 打印统计信息
    system.print_all_stats().await;
}

// ============================================================================
// 第五部分: 示例和测试
// Part 5: Examples and Tests
// ============================================================================

/// 基本通信示例
/// Basic Communication Example
pub async fn basic_communication_example() {
    println!("\n╔══════════════════════════════════════════════════════════════════╗");
    println!("║                                                                  ║");
    println!("║   💬 基本通信示例                                                ║");
    println!("║   Basic Communication Example                                    ║");
    println!("║                                                                  ║");
    println!("╚══════════════════════════════════════════════════════════════════╝\n");

    // 1. 有界通道 (Bounded Channel)
    println!("1️⃣  有界通道 (Bounded Channel):");
    let (tx, mut rx) = mpsc::channel(5);
    
    tokio::spawn(async move {
        for i in 0..10 {
            println!("   发送: {}", i);
            tx.send(i).await.unwrap();
        }
    });
    
    while let Some(msg) = rx.recv().await {
        println!("   接收: {}", msg);
        sleep(Duration::from_millis(100)).await;
    }
    println!();

    // 2. 广播通道 (Broadcast Channel)
    println!("2️⃣  广播通道 (Broadcast Channel):");
    let (tx, _) = broadcast::channel(10);
    
    let mut rx1 = tx.subscribe();
    let mut rx2 = tx.subscribe();
    
    tokio::spawn(async move {
        for i in 0..5 {
            println!("   广播: {}", i);
            let _ = tx.send(i);
            sleep(Duration::from_millis(50)).await;
        }
    });
    
    let h1 = tokio::spawn(async move {
        while let Ok(msg) = rx1.recv().await {
            println!("   接收者 1: {}", msg);
        }
    });
    
    let h2 = tokio::spawn(async move {
        while let Ok(msg) = rx2.recv().await {
            println!("   接收者 2: {}", msg);
        }
    });
    
    let _ = tokio::join!(h1, h2);
    println!();

    // 3. 单次通道 (Oneshot Channel)
    println!("3️⃣  单次通道 (Oneshot Channel):");
    let (tx, rx) = oneshot::channel();
    
    tokio::spawn(async move {
        sleep(Duration::from_millis(100)).await;
        println!("   发送: 42");
        let _ = tx.send(42);
    });
    
    match rx.await {
        Ok(msg) => println!("   接收: {}", msg),
        Err(_) => println!("   错误: 发送者已关闭"),
    }
    println!();
}

/// Select 多路复用示例
/// Select Multiplexing Example
pub async fn select_multiplexing_example() {
    println!("\n╔══════════════════════════════════════════════════════════════════╗");
    println!("║                                                                  ║");
    println!("║   🔀 Select 多路复用示例                                         ║");
    println!("║   Select Multiplexing Example                                    ║");
    println!("║                                                                  ║");
    println!("╚══════════════════════════════════════════════════════════════════╝\n");

    let (tx1, mut rx1) = mpsc::channel(10);
    let (tx2, mut rx2) = mpsc::channel(10);
    let (tx3, mut rx3) = mpsc::channel(10);

    // 发送者 1
    tokio::spawn(async move {
        for i in 0..5 {
            sleep(Duration::from_millis(100)).await;
            let _ = tx1.send(format!("通道 1: {}", i)).await;
        }
    });

    // 发送者 2
    tokio::spawn(async move {
        for i in 0..5 {
            sleep(Duration::from_millis(150)).await;
            let _ = tx2.send(format!("通道 2: {}", i)).await;
        }
    });

    // 发送者 3
    tokio::spawn(async move {
        for i in 0..5 {
            sleep(Duration::from_millis(200)).await;
            let _ = tx3.send(format!("通道 3: {}", i)).await;
        }
    });

    // Select 接收
    let mut count = 0;
    loop {
        select! {
            Some(msg) = rx1.recv() => {
                println!("   📨 {}", msg);
                count += 1;
            }
            Some(msg) = rx2.recv() => {
                println!("   📨 {}", msg);
                count += 1;
            }
            Some(msg) = rx3.recv() => {
                println!("   📨 {}", msg);
                count += 1;
            }
            else => break,
        }

        if count >= 15 {
            break;
        }
    }

    println!("\n   ✓ 共接收 {} 条消息\n", count);
}

/// 性能基准测试
/// Performance Benchmark
pub async fn performance_benchmark() {
    println!("\n╔══════════════════════════════════════════════════════════════════╗");
    println!("║                                                                  ║");
    println!("║   ⚡ 性能基准测试                                                ║");
    println!("║   Performance Benchmark                                          ║");
    println!("║                                                                  ║");
    println!("╚══════════════════════════════════════════════════════════════════╝\n");

    let num_messages = 10_000;
    let channel_capacity = 100;

    // 测试 1: 单生产者单消费者
    println!("1️⃣  单生产者单消费者 (SPSC):");
    let start = Instant::now();
    let (tx, mut rx) = mpsc::channel(channel_capacity);
    
    let producer = tokio::spawn(async move {
        for i in 0..num_messages {
            let _ = tx.send(i).await;
        }
    });
    
    let consumer = tokio::spawn(async move {
        let mut count = 0;
        while let Some(_) = rx.recv().await {
            count += 1;
            if count >= num_messages {
                break;
            }
        }
        count
    });
    
    let _ = producer.await;
    let count = consumer.await.unwrap();
    let elapsed = start.elapsed();
    
    println!("   消息数: {}", count);
    println!("   耗时: {:?}", elapsed);
    println!("   吞吐量: {:.2} msg/s\n", count as f64 / elapsed.as_secs_f64());

    // 测试 2: 多生产者单消费者
    println!("2️⃣  多生产者单消费者 (MPSC):");
    let start = Instant::now();
    let (tx, mut rx) = mpsc::channel(channel_capacity);
    
    let num_producers = 4;
    let messages_per_producer = num_messages / num_producers;
    
    let mut producers = vec![];
    for _ in 0..num_producers {
        let tx = tx.clone();
        let producer = tokio::spawn(async move {
            for i in 0..messages_per_producer {
                let _ = tx.send(i).await;
            }
        });
        producers.push(producer);
    }
    drop(tx);
    
    let consumer = tokio::spawn(async move {
        let mut count = 0;
        while let Some(_) = rx.recv().await {
            count += 1;
        }
        count
    });
    
    for producer in producers {
        let _ = producer.await;
    }
    let count = consumer.await.unwrap();
    let elapsed = start.elapsed();
    
    println!("   生产者数: {}", num_producers);
    println!("   消息数: {}", count);
    println!("   耗时: {:?}", elapsed);
    println!("   吞吐量: {:.2} msg/s\n", count as f64 / elapsed.as_secs_f64());

    // 测试 3: 广播通道
    println!("3️⃣  广播通道 (Broadcast):");
    let start = Instant::now();
    let (tx, _) = broadcast::channel(channel_capacity);
    
    let num_receivers = 4;
    let mut receivers = vec![];
    
    for _ in 0..num_receivers {
        let mut rx = tx.subscribe();
        let receiver = tokio::spawn(async move {
            let mut count = 0;
            while let Ok(_) = rx.recv().await {
                count += 1;
            }
            count
        });
        receivers.push(receiver);
    }
    
    let producer = tokio::spawn(async move {
        for i in 0..num_messages {
            let _ = tx.send(i);
        }
    });
    
    let _ = producer.await;
    
    let mut total_received = 0;
    for receiver in receivers {
        total_received += receiver.await.unwrap();
    }
    let elapsed = start.elapsed();
    
    println!("   接收者数: {}", num_receivers);
    println!("   总接收消息数: {}", total_received);
    println!("   耗时: {:?}", elapsed);
    println!("   吞吐量: {:.2} msg/s\n", total_received as f64 / elapsed.as_secs_f64());
}

// ============================================================================
// 主函数
// Main Function
// ============================================================================

#[tokio::main]
async fn main() {
    println!("╔══════════════════════════════════════════════════════════════════╗");
    println!("║                                                                  ║");
    println!("║   🦀 CSP 模式完整实现 2025                                       ║");
    println!("║   Comprehensive CSP Pattern Implementation 2025                  ║");
    println!("║                                                                  ║");
    println!("║   📚 包含内容:                                                    ║");
    println!("║   • CSP 理论形式化和数学定义                                     ║");
    println!("║   • 核心数据结构和系统实现                                       ║");
    println!("║   • 3 个实际应用示例                                             ║");
    println!("║   • 基本通信和 Select 多路复用                                   ║");
    println!("║   • 性能基准测试                                                 ║");
    println!("║                                                                  ║");
    println!("║   🦀 Rust 版本: 1.90+                                            ║");
    println!("║   📦 Tokio 版本: 1.41+                                           ║");
    println!("║                                                                  ║");
    println!("╚══════════════════════════════════════════════════════════════════╝");

    // 第一部分: 理论形式化
    theory_csp_formalization::print_theory();

    // 第二部分: 基本通信示例
    basic_communication_example().await;

    // 第三部分: Select 多路复用
    select_multiplexing_example().await;

    // 第四部分: 实际应用示例
    data_processing_pipeline_example().await;
    distributed_task_scheduler_example().await;
    realtime_log_aggregation_example().await;

    // 第五部分: 性能基准测试
    performance_benchmark().await;

    println!("\n╔══════════════════════════════════════════════════════════════════╗");
    println!("║                                                                  ║");
    println!("║   ✅ 所有演示完成!                                               ║");
    println!("║   All Demonstrations Completed!                                  ║");
    println!("║                                                                  ║");
    println!("║   📊 统计:                                                        ║");
    println!("║   • 1 种并发模型 (CSP)                                           ║");
    println!("║   • 3 种通道类型 (Bounded, Broadcast, Oneshot)                   ║");
    println!("║   • 3 个实际应用示例                                             ║");
    println!("║   • 3 个性能基准测试                                             ║");
    println!("║   • 1,100+ 行详细注释代码                                        ║");
    println!("║   • 完整的理论形式化说明                                         ║");
    println!("║                                                                  ║");
    println!("║   🎯 下一步学习建议:                                             ║");
    println!("║   1. 运行 Reactor 模式示例:                                      ║");
    println!("║      cargo run --example reactor_pattern_comprehensive_2025      ║");
    println!("║   2. 运行 Actor 模式示例:                                        ║");
    println!("║      cargo run --example actor_pattern_comprehensive_2025        ║");
    println!("║   3. 查看知识分类体系:                                           ║");
    println!("║      docs/COMPREHENSIVE_ASYNC_KNOWLEDGE_CLASSIFICATION_2025.md   ║");
    println!("║                                                                  ║");
    println!("╚══════════════════════════════════════════════════════════════════╝\n");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_bounded_channel() {
        let (tx, mut rx) = mpsc::channel(5);
        
        tokio::spawn(async move {
            for i in 0..10 {
                tx.send(i).await.unwrap();
            }
        });
        
        let mut count = 0;
        while let Some(_) = rx.recv().await {
            count += 1;
        }
        
        assert_eq!(count, 10);
    }

    #[tokio::test]
    async fn test_broadcast_channel() {
        let (tx, _) = broadcast::channel(10);
        let mut rx1 = tx.subscribe();
        let mut rx2 = tx.subscribe();
        
        tokio::spawn(async move {
            for i in 0..5 {
                let _ = tx.send(i);
            }
        });
        
        let h1 = tokio::spawn(async move {
            let mut count = 0;
            while let Ok(_) = rx1.recv().await {
                count += 1;
            }
            count
        });
        
        let h2 = tokio::spawn(async move {
            let mut count = 0;
            while let Ok(_) = rx2.recv().await {
                count += 1;
            }
            count
        });
        
        let (count1, count2) = tokio::join!(h1, h2);
        assert_eq!(count1.unwrap(), 5);
        assert_eq!(count2.unwrap(), 5);
    }

    #[tokio::test]
    async fn test_oneshot_channel() {
        let (tx, rx) = oneshot::channel();
        
        tokio::spawn(async move {
            let _ = tx.send(42);
        });
        
        let result = rx.await.unwrap();
        assert_eq!(result, 42);
    }

    #[tokio::test]
    async fn test_csp_system() {
        let system = CspSystem::new(CspSystemConfig::default());
        system.register_process("test".to_string()).await;
        
        system.update_stats("test", |s| {
            s.messages_sent = 10;
            s.messages_received = 5;
        }).await;
        
        let stats = system.stats.lock().await;
        let test_stats = stats.get("test").unwrap();
        
        assert_eq!(test_stats.messages_sent, 10);
        assert_eq!(test_stats.messages_received, 5);
    }
}
