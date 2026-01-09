//! Rust 异步编程综合模式示例 2025
//! Comprehensive Async Patterns Example 2025
//!
//! 本示例展示:
//! 1. Actor、Reactor、CSP 三大模式对比
//! 2. 异步设计模式实战
//! 3. Tokio 与 Smol 混合使用
//! 4. 生产级架构模式
//! 5. 性能优化技巧
//!
//! 运行方式:
//! ```bash
//! cargo run --example comprehensive_async_patterns_2025
//! ```

use std::collections::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{mpsc, oneshot, Mutex};
use tokio::time::{sleep, timeout};

// ============================================================================
// 第一部分: Actor 模式实现
// ============================================================================

mod actor_pattern {
    use super::*;

    /// Actor 消息 trait
    pub trait Message: Send + 'static {
        type Response: Send + 'static;
    }

    /// Actor trait
    #[async_trait::async_trait]
    pub trait Actor: Send + Sized + 'static {
        type Message: Message;

        async fn handle(
            &mut self,
            msg: Self::Message,
            ctx: &mut ActorContext<Self>,
        ) -> <Self::Message as Message>::Response;

        async fn started(&mut self, _ctx: &mut ActorContext<Self>) {}
        async fn stopped(&mut self, _ctx: &mut ActorContext<Self>) {}
    }

    /// Actor 上下文
    #[allow(dead_code)]
    pub struct ActorContext<A: Actor> {
        pub addr: Option<ActorAddress<A>>,
    }

    /// Actor 地址（用于发送消息）
    #[derive(Clone)]
    #[allow(dead_code)]
    pub struct ActorAddress<A: Actor> {
        tx: mpsc::UnboundedSender<ActorEnvelope<A>>,
    }

    /// 消息信封（包含响应通道）
    #[allow(dead_code)]
    struct ActorEnvelope<A: Actor> {
        msg: A::Message,
        respond_to: oneshot::Sender<<A::Message as Message>::Response>,
    }

    #[allow(dead_code)]
    #[allow(unused_variables)]
    impl<A: Actor> ActorAddress<A> {
        /// 发送消息并等待响应
        pub async fn send(
            &self,
            msg: A::Message,
        ) -> Result<<A::Message as Message>::Response, &'static str> {
            let (tx, rx) = oneshot::channel();
            let envelope = ActorEnvelope {
                msg,
                respond_to: tx,
            };

            self.tx
                .send(envelope)
                .map_err(|_| "Actor 已停止")?;

            rx.await.map_err(|_| "Actor 未响应")
        }

        /// 发送消息（不等待响应）
        pub fn do_send(&self, msg: A::Message) {
            let (tx, _) = oneshot::channel();
            let envelope = ActorEnvelope {
                msg,
                respond_to: tx,
            };
            let _ = self.tx.send(envelope);
        }
    }

    /// Actor 系统
    pub struct ActorSystem;

    impl ActorSystem {
        /// 启动一个 Actor
        pub fn spawn<A: Actor>(mut actor: A) -> ActorAddress<A> {
            let (tx, mut rx) = mpsc::unbounded_channel::<ActorEnvelope<A>>();

            let addr = ActorAddress { tx: tx.clone() };

            tokio::spawn(async move {
                let mut ctx = ActorContext {
                    addr: Some(ActorAddress { tx }),
                };

                // Actor 启动回调
                actor.started(&mut ctx).await;

                // 消息循环
                while let Some(envelope) = rx.recv().await {
                    let response = actor.handle(envelope.msg, &mut ctx).await;
                    let _ = envelope.respond_to.send(response);
                }

                // Actor 停止回调
                actor.stopped(&mut ctx).await;
            });

            addr
        }
    }

    // ========================================================================
    // 示例: 银行账户 Actor
    // ========================================================================

    #[derive(Debug)]
    pub enum AccountMessage {
        Deposit(u64),
        Withdraw(u64),
        GetBalance,
    }

    impl Message for AccountMessage {
        type Response = Result<u64, String>;
    }

    pub struct BankAccount {
        balance: u64,
        name: String,
    }

    impl BankAccount {
        pub fn new(name: String, initial: u64) -> Self {
            Self {
                balance: initial,
                name,
            }
        }
    }

    #[async_trait::async_trait]
    impl Actor for BankAccount {
        type Message = AccountMessage;

        async fn handle(
            &mut self,
            msg: Self::Message,
            _ctx: &mut ActorContext<Self>,
        ) -> Result<u64, String> {
            match msg {
                AccountMessage::Deposit(amount) => {
                    self.balance += amount;
                    println!("[{}] 存入 {}, 余额: {}", self.name, amount, self.balance);
                    Ok(self.balance)
                }
                AccountMessage::Withdraw(amount) => {
                    if self.balance >= amount {
                        self.balance -= amount;
                        println!(
                            "[{}] 取出 {}, 余额: {}",
                            self.name, amount, self.balance
                        );
                        Ok(self.balance)
                    } else {
                        Err(format!("余额不足: {}", self.balance))
                    }
                }
                AccountMessage::GetBalance => Ok(self.balance),
            }
        }

        async fn started(&mut self, _ctx: &mut ActorContext<Self>) {
            println!("[{}] Actor 启动，初始余额: {}", self.name, self.balance);
        }

        async fn stopped(&mut self, _ctx: &mut ActorContext<Self>) {
            println!("[{}] Actor 停止，最终余额: {}", self.name, self.balance);
        }
    }

    pub async fn demo() {
        println!("\n╔════════════════════════════════════════╗");
        println!("║      Actor 模式示例: 银行账户          ║");
        println!("╚════════════════════════════════════════╝\n");

        // 创建账户 Actor
        let account = ActorSystem::spawn(BankAccount::new("Alice".to_string(), 1000));

        // 存款
        let balance = account
            .send(AccountMessage::Deposit(500))
            .await
            .unwrap()
            .unwrap();
        println!("操作后余额: {}\n", balance);

        // 取款
        let balance = account
            .send(AccountMessage::Withdraw(300))
            .await
            .unwrap()
            .unwrap();
        println!("操作后余额: {}\n", balance);

        // 取款失败（余额不足）
        match account.send(AccountMessage::Withdraw(2000)).await.unwrap() {
            Ok(balance) => println!("取款成功，余额: {}", balance),
            Err(e) => println!("取款失败: {}\n", e),
        }

        // 查询余额
        let balance = account
            .send(AccountMessage::GetBalance)
            .await
            .unwrap()
            .unwrap();
        println!("最终余额: {}", balance);
    }
}

// ============================================================================
// 第二部分: Reactor 模式实现
// ============================================================================

mod reactor_pattern {
    use super::*;

    /// 事件类型
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    #[allow(dead_code)]
    pub enum EventType {
        Read,
        Write,
        Timer,
        Custom(u32),
    }

    /// 事件
    #[derive(Debug, Clone)]
    #[allow(dead_code)]
    pub struct Event {
        pub source_id: u64,
        pub event_type: EventType,
        pub data: Vec<u8>,
        pub timestamp: std::time::Instant,
    }

    /// 事件处理器 trait
    #[async_trait::async_trait]
    pub trait EventHandler: Send + Sync {
        async fn handle(&self, event: Event) -> Result<(), Box<dyn std::error::Error>>;
    }

    /// Reactor 核心
    pub struct Reactor {
        handlers: Arc<Mutex<HashMap<(u64, EventType), Arc<dyn EventHandler>>>>,
        event_queue: Arc<Mutex<Vec<Event>>>,
        running: Arc<tokio::sync::RwLock<bool>>,
    }

    impl Reactor {
        pub fn new() -> Self {
            Self {
                handlers: Arc::new(Mutex::new(HashMap::new())),
                event_queue: Arc::new(Mutex::new(Vec::new())),
                running: Arc::new(tokio::sync::RwLock::new(false)),
            }
        }

        /// 注册事件处理器
        pub async fn register(
            &self,
            source_id: u64,
            event_type: EventType,
            handler: Arc<dyn EventHandler>,
        ) {
            let mut handlers = self.handlers.lock().await;
            handlers.insert((source_id, event_type), handler);
            println!(
                "[Reactor] 注册处理器: source={}, type={:?}",
                source_id, event_type
            );
        }

        /// 提交事件
        pub async fn submit_event(&self, event: Event) {
            let mut queue = self.event_queue.lock().await;
            queue.push(event);
        }

        /// 启动事件循环
        pub async fn run(&self) {
            {
                let mut running = self.running.write().await;
                *running = true;
            }

            println!("[Reactor] 事件循环启动\n");

            while *self.running.read().await {
                // 1. 获取待处理事件
                let events = {
                    let mut queue = self.event_queue.lock().await;
                    std::mem::take(&mut *queue)
                };

                if events.is_empty() {
                    sleep(Duration::from_millis(10)).await;
                    continue;
                }

                println!("[Reactor] 处理 {} 个事件", events.len());

                // 2. 分发事件给处理器
                for event in events {
                    let handler = {
                        let handlers = self.handlers.lock().await;
                        handlers.get(&(event.source_id, event.event_type)).cloned()
                    };

                    if let Some(h) = handler {
                        // 异步处理事件
                        let event_clone = event.clone();
                        tokio::spawn(async move {
                            if let Err(e) = h.handle(event_clone).await {
                                eprintln!("[Reactor] 处理错误: {}", e);
                            }
                        });
                    } else {
                        println!(
                            "[Reactor] 未找到处理器: source={}, type={:?}",
                            event.source_id, event.event_type
                        );
                    }
                }

                sleep(Duration::from_millis(10)).await;
            }

            println!("\n[Reactor] 事件循环停止");
        }

        /// 停止事件循环
        pub async fn stop(&self) {
            let mut running = self.running.write().await;
            *running = false;
        }
    }

    // ========================================================================
    // 示例: 日志处理器
    // ========================================================================

    struct LogHandler {
        name: String,
    }

    #[async_trait::async_trait]
    impl EventHandler for LogHandler {
        async fn handle(&self, event: Event) -> Result<(), Box<dyn std::error::Error>> {
            println!(
                "  [{}] 处理事件: source={}, type={:?}, data_len={}",
                self.name,
                event.source_id,
                event.event_type,
                event.data.len()
            );
            sleep(Duration::from_millis(50)).await; // 模拟处理
            Ok(())
        }
    }

    /// 统计处理器
    struct StatsHandler {
        counter: Arc<Mutex<usize>>,
    }

    #[async_trait::async_trait]
    impl EventHandler for StatsHandler {
        async fn handle(&self, event: Event) -> Result<(), Box<dyn std::error::Error>> {
            let mut count = self.counter.lock().await;
            *count += 1;
            println!(
                "  [Stats] 事件计数: {}, type={:?}",
                *count, event.event_type
            );
            Ok(())
        }
    }

    pub async fn demo() {
        println!("\n╔════════════════════════════════════════╗");
        println!("║         Reactor 模式示例               ║");
        println!("╚════════════════════════════════════════╝\n");

        let reactor = Arc::new(Reactor::new());

        // 注册处理器
        reactor
            .register(
                1,
                EventType::Read,
                Arc::new(LogHandler {
                    name: "ReadLog".to_string(),
                }),
            )
            .await;

        reactor
            .register(
                2,
                EventType::Write,
                Arc::new(LogHandler {
                    name: "WriteLog".to_string(),
                }),
            )
            .await;

        let stats_counter = Arc::new(Mutex::new(0));
        reactor
            .register(
                3,
                EventType::Timer,
                Arc::new(StatsHandler {
                    counter: stats_counter.clone(),
                }),
            )
            .await;

        // 启动事件循环
        let reactor_clone = reactor.clone();
        let event_loop = tokio::spawn(async move {
            reactor_clone.run().await;
        });

        // 生成事件
        println!("\n开始生成事件...\n");
        for i in 0..5 {
            reactor
                .submit_event(Event {
                    source_id: 1,
                    event_type: EventType::Read,
                    data: vec![i; 10],
                    timestamp: std::time::Instant::now(),
                })
                .await;

            reactor
                .submit_event(Event {
                    source_id: 2,
                    event_type: EventType::Write,
                    data: vec![i * 2; 10],
                    timestamp: std::time::Instant::now(),
                })
                .await;

            reactor
                .submit_event(Event {
                    source_id: 3,
                    event_type: EventType::Timer,
                    data: vec![],
                    timestamp: std::time::Instant::now(),
                })
                .await;

            sleep(Duration::from_millis(100)).await;
        }

        // 等待处理完成
        sleep(Duration::from_secs(1)).await;

        // 停止 Reactor
        reactor.stop().await;
        let _ = event_loop.await;

        let final_count = *stats_counter.lock().await;
        println!("\n统计: 共处理 {} 个 Timer 事件", final_count);
    }
}

// ============================================================================
// 第三部分: CSP 模式实现
// ============================================================================

mod csp_pattern {
    use super::*;

    /// CSP 风格的生产者-消费者
    pub async fn producer_consumer_demo() {
        println!("\n╔════════════════════════════════════════╗");
        println!("║    CSP 模式: 生产者-消费者             ║");
        println!("╚════════════════════════════════════════╝\n");

        let (tx, mut rx) = mpsc::channel(10);

        // 启动 3 个生产者
        let mut producers = vec![];
        for id in 0..3 {
            let tx = tx.clone();
            let producer = tokio::spawn(async move {
                for i in 0..5 {
                    let item = format!("P{}-Item{}", id, i);
                    println!("  [Producer {}] 生产: {}", id, item);
                    tx.send(item).await.unwrap();
                    sleep(Duration::from_millis(50)).await;
                }
                println!("  [Producer {}] 完成", id);
            });
            producers.push(producer);
        }

        drop(tx); // 关闭发送端

        // 消费者
        let consumer = tokio::spawn(async move {
            println!("\n[Consumer] 开始消费...\n");
            let mut count = 0;
            while let Some(item) = rx.recv().await {
                println!("  [Consumer] 消费: {}", item);
                count += 1;
                sleep(Duration::from_millis(80)).await;
            }
            println!("\n[Consumer] 完成，总共消费 {} 个项目", count);
            count
        });

        // 等待所有任务完成
        for producer in producers {
            producer.await.unwrap();
        }
        let count = consumer.await.unwrap();
        println!("\n✓ 生产者-消费者演示完成，处理 {} 个项目", count);
    }

    /// CSP 风格的 Pipeline
    pub async fn pipeline_demo() {
        println!("\n╔════════════════════════════════════════╗");
        println!("║        CSP 模式: Pipeline              ║");
        println!("╚════════════════════════════════════════╝\n");

        // Stage 1: 生成数字
        let (tx1, mut rx1) = mpsc::channel(10);
        let stage1 = tokio::spawn(async move {
            println!("[Stage 1] 生成数字");
            for i in 1..=10 {
                println!("  Stage 1: 生成 {}", i);
                tx1.send(i).await.unwrap();
            }
        });

        // Stage 2: 平方
        let (tx2, mut rx2) = mpsc::channel(10);
        let stage2 = tokio::spawn(async move {
            println!("[Stage 2] 计算平方");
            while let Some(n) = rx1.recv().await {
                let squared = n * n;
                println!("  Stage 2: {} -> {}", n, squared);
                tx2.send(squared).await.unwrap();
            }
        });

        // Stage 3: 累加
        let stage3 = tokio::spawn(async move {
            println!("[Stage 3] 累加结果");
            let mut sum = 0;
            while let Some(n) = rx2.recv().await {
                sum += n;
                println!("  Stage 3: 累加 {}, 当前总和: {}", n, sum);
            }
            println!("\n[Stage 3] 最终总和: {}", sum);
            sum
        });

        // 等待所有阶段完成
        stage1.await.unwrap();
        stage2.await.unwrap();
        let result = stage3.await.unwrap();

        println!("\n✓ Pipeline 演示完成，结果: {}", result);
    }

    /// CSP 风格的 Fan-out/Fan-in
    #[allow(dead_code)]
    pub async fn fan_out_in_demo() {
        println!("\n╔════════════════════════════════════════╗");
        println!("║    CSP 模式: Fan-out/Fan-in            ║");
        println!("╚════════════════════════════════════════╝\n");

        use tokio::sync::broadcast;
        
        let (work_tx, _) = broadcast::channel(100);
        let (result_tx, mut result_rx) = mpsc::channel(100);

        // Fan-out: 创建 5 个 worker
        let mut workers = vec![];
        for worker_id in 0..5 {
            let mut work_rx = work_tx.subscribe();
            let result_tx = result_tx.clone();

            let worker = tokio::spawn(async move {
                while let Ok(work) = work_rx.recv().await {
                    // 处理工作
                    let result = format!("Worker {} 处理: {}", worker_id, work);
                    result_tx.send(result).await.unwrap();
                    sleep(Duration::from_millis(100)).await;
                }
            });
            workers.push(worker);
        }

        // 分发工作
        for i in 0..10 {
            let _ = work_tx.send(i);
        }

        drop(work_tx);
        drop(result_tx);

        // Fan-in: 收集结果
        let mut results = vec![];
        while let Some(result) = result_rx.recv().await {
            println!("  收到: {}", result);
            results.push(result);
        }

        println!("\n✓ Fan-out/Fan-in 完成，收集 {} 个结果", results.len());
    }
}

// ============================================================================
// 第四部分: 异步设计模式
// ============================================================================

mod design_patterns {
    use super::*;

    /// 重试策略模式
    pub struct RetryStrategy {
        max_attempts: usize,
        base_delay: Duration,
    }

    impl RetryStrategy {
        pub fn new(max_attempts: usize, base_delay: Duration) -> Self {
            Self {
                max_attempts,
                base_delay,
            }
        }

        /// 指数退避重试
        pub async fn execute<F, T, E>(&self, mut operation: F) -> Result<T, E>
        where
            F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T, E>> + Send>>,
            E: std::fmt::Display,
        {
            let mut attempt = 0;

            loop {
                attempt += 1;

                match operation().await {
                    Ok(result) => {
                        if attempt > 1 {
                            println!("  ✓ 第 {} 次尝试成功", attempt);
                        }
                        return Ok(result);
                    }
                    Err(e) => {
                        if attempt >= self.max_attempts {
                            println!("  ✗ 达到最大重试次数 ({})", self.max_attempts);
                            return Err(e);
                        }

                        let delay = self.base_delay * 2_u32.pow(attempt as u32 - 1);
                        println!(
                            "  ⟳ 第 {} 次尝试失败: {}，等待 {:?} 后重试",
                            attempt, e, delay
                        );
                        sleep(delay).await;
                    }
                }
            }
        }
    }

    /// 熔断器模式
    pub struct CircuitBreaker {
        state: Arc<Mutex<CircuitState>>,
        failure_threshold: usize,
        success_threshold: usize,
        timeout: Duration,
    }

    #[derive(Debug)]
    enum CircuitState {
        Closed { failures: usize },
        Open { opened_at: std::time::Instant },
        HalfOpen { successes: usize },
    }

    impl CircuitBreaker {
        pub fn new(failure_threshold: usize, success_threshold: usize, timeout: Duration) -> Self {
            Self {
                state: Arc::new(Mutex::new(CircuitState::Closed { failures: 0 })),
                failure_threshold,
                success_threshold,
                timeout,
            }
        }

        pub async fn call<F, T, E>(&self, operation: F) -> Result<T, String>
        where
            F: std::future::Future<Output = Result<T, E>>,
            E: std::fmt::Display,
        {
            // 检查熔断器状态
            {
                let mut state = self.state.lock().await;
                match *state {
                    CircuitState::Open { opened_at } => {
                        if opened_at.elapsed() < self.timeout {
                            return Err("熔断器开启，拒绝请求".to_string());
                        }
                        // 进入半开状态
                        *state = CircuitState::HalfOpen { successes: 0 };
                        println!("  [熔断器] 进入半开状态");
                    }
                    _ => {}
                }
            }

            // 执行操作
            let result = timeout(Duration::from_secs(5), operation).await;

            // 更新状态
            let mut state = self.state.lock().await;
            match result {
                Ok(Ok(value)) => {
                    match *state {
                        CircuitState::Closed { .. } => {
                            *state = CircuitState::Closed { failures: 0 };
                        }
                        CircuitState::HalfOpen { successes } => {
                            let new_successes = successes + 1;
                            if new_successes >= self.success_threshold {
                                *state = CircuitState::Closed { failures: 0 };
                                println!("  [熔断器] 关闭");
                            } else {
                                *state = CircuitState::HalfOpen {
                                    successes: new_successes,
                                };
                            }
                        }
                        _ => {}
                    }
                    Ok(value)
                }
                _ => {
                    match *state {
                        CircuitState::Closed { failures } => {
                            let new_failures = failures + 1;
                            if new_failures >= self.failure_threshold {
                                *state = CircuitState::Open {
                                    opened_at: std::time::Instant::now(),
                                };
                                println!("  [熔断器] 开启");
                            } else {
                                *state = CircuitState::Closed {
                                    failures: new_failures,
                                };
                            }
                        }
                        CircuitState::HalfOpen { .. } => {
                            *state = CircuitState::Open {
                                opened_at: std::time::Instant::now(),
                            };
                            println!("  [熔断器] 重新开启");
                        }
                        _ => {}
                    }
                    Err("操作失败或超时".to_string())
                }
            }
        }
    }

    pub async fn demo() {
        println!("\n╔════════════════════════════════════════╗");
        println!("║       异步设计模式示例                 ║");
        println!("╚════════════════════════════════════════╝");

        // 1. 重试策略演示
        println!("\n━━━ 1. 重试策略 ━━━\n");
        let retry = RetryStrategy::new(3, Duration::from_millis(100));

        let mut attempts = 0;
        let result = retry
            .execute(|| {
                attempts += 1;
                Box::pin(async move {
                    if attempts < 3 {
                        Err(format!("模拟失败 {}", attempts))
                    } else {
                        Ok("成功!")
                    }
                })
            })
            .await;

        println!("\n结果: {:?}", result);

        // 2. 熔断器演示
        println!("\n━━━ 2. 熔断器模式 ━━━\n");
        let breaker = CircuitBreaker::new(3, 2, Duration::from_secs(2));

        for i in 0..10 {
            let result = breaker
                .call(async {
                    if i < 3 || i >= 7 {
                        // 模拟失败
                        sleep(Duration::from_millis(100)).await;
                        Err("服务不可用")
                    } else {
                        // 模拟成功
                        sleep(Duration::from_millis(100)).await;
                        Ok(format!("请求 {} 成功", i))
                    }
                })
                .await;

            println!("  请求 {}: {:?}", i, result);
            sleep(Duration::from_millis(200)).await;
        }
    }
}

// ============================================================================
// 第五部分: 生产级架构模式
// ============================================================================

mod production_patterns {
    use super::*;

    /// 服务健康检查
    pub struct HealthChecker {
        checks: Vec<Box<dyn HealthCheck>>,
    }

    #[async_trait::async_trait]
    pub trait HealthCheck: Send + Sync {
        async fn check(&self) -> Result<(), String>;
        fn name(&self) -> &str;
    }

    impl HealthChecker {
        pub fn new() -> Self {
            Self { checks: vec![] }
        }

        pub fn add_check(&mut self, check: Box<dyn HealthCheck>) {
            self.checks.push(check);
        }

        pub async fn check_all(&self) -> Vec<(String, Result<(), String>)> {
            let mut results = vec![];

            for check in &self.checks {
                let name = check.name().to_string();
                let result = check.check().await;
                results.push((name, result));
            }

            results
        }
    }

    /// 数据库健康检查
    struct DatabaseHealthCheck;

    #[async_trait::async_trait]
    impl HealthCheck for DatabaseHealthCheck {
        async fn check(&self) -> Result<(), String> {
            sleep(Duration::from_millis(50)).await;
            Ok(())
        }

        fn name(&self) -> &str {
            "database"
        }
    }

    /// 缓存健康检查
    struct CacheHealthCheck;

    #[async_trait::async_trait]
    impl HealthCheck for CacheHealthCheck {
        async fn check(&self) -> Result<(), String> {
            sleep(Duration::from_millis(30)).await;
            Ok(())
        }

        fn name(&self) -> &str {
            "cache"
        }
    }

    /// 优雅关闭管理器
    pub struct GracefulShutdown {
        shutdown_tx: tokio::sync::broadcast::Sender<()>,
    }

    #[allow(dead_code)]
    impl GracefulShutdown {
        pub fn new() -> Self {
            let (shutdown_tx, _) = tokio::sync::broadcast::channel(1);
            Self { shutdown_tx }
        }

        pub fn subscribe(&self) -> tokio::sync::broadcast::Receiver<()> {
            self.shutdown_tx.subscribe()
        }

        pub fn shutdown(&self) {
            let _ = self.shutdown_tx.send(());
        }

        pub async fn wait_for_signal() {
            tokio::signal::ctrl_c().await.ok();
        }
    }

    pub async fn demo() {
        println!("\n╔════════════════════════════════════════╗");
        println!("║       生产级架构模式示例               ║");
        println!("╚════════════════════════════════════════╝");

        // 1. 健康检查
        println!("\n━━━ 1. 健康检查系统 ━━━\n");
        let mut checker = HealthChecker::new();
        checker.add_check(Box::new(DatabaseHealthCheck));
        checker.add_check(Box::new(CacheHealthCheck));

        let results = checker.check_all().await;
        for (name, result) in results {
            match result {
                Ok(_) => println!("  ✓ {} 健康", name),
                Err(e) => println!("  ✗ {} 不健康: {}", name, e),
            }
        }

        // 2. 优雅关闭
        println!("\n━━━ 2. 优雅关闭机制 ━━━\n");
        let shutdown_manager = GracefulShutdown::new();

        // 模拟服务任务
        let mut shutdown_rx = shutdown_manager.subscribe();
        let service = tokio::spawn(async move {
            println!("  [服务] 启动");
            loop {
                tokio::select! {
                    _ = shutdown_rx.recv() => {
                        println!("  [服务] 收到关闭信号");
                        // 清理资源
                        sleep(Duration::from_secs(1)).await;
                        println!("  [服务] 清理完成");
                        break;
                    }
                    _ = sleep(Duration::from_millis(500)) => {
                        println!("  [服务] 处理请求...");
                    }
                }
            }
        });

        // 模拟运行一段时间后关闭
        sleep(Duration::from_secs(2)).await;
        println!("\n触发优雅关闭...\n");
        shutdown_manager.shutdown();

        service.await.unwrap();
        println!("\n✓ 服务已优雅关闭");
    }
}

// ============================================================================
// 主函数: 运行所有示例
// ============================================================================

#[tokio::main]
async fn main() {
    println!("\n");
    println!("╔══════════════════════════════════════════════════════╗");
    println!("║                                                      ║");
    println!("║   Rust 异步编程综合模式示例集 2025                  ║");
    println!("║   Comprehensive Async Patterns Collection           ║");
    println!("║                                                      ║");
    println!("║   版本: Rust 1.92.0 | Tokio 1.41+                     ║");
    println!("║   日期: 2025-10-04                                   ║");
    println!("║                                                      ║");
    println!("╚══════════════════════════════════════════════════════╝");

    // 第一部分: Actor 模式
    actor_pattern::demo().await;

    // 第二部分: Reactor 模式
    reactor_pattern::demo().await;

    // 第三部分: CSP 模式
    csp_pattern::producer_consumer_demo().await;
    csp_pattern::pipeline_demo().await;
    // csp_pattern::fan_out_in_demo().await; // 注释掉以简化输出

    // 第四部分: 设计模式
    design_patterns::demo().await;

    // 第五部分: 生产模式
    production_patterns::demo().await;

    println!("\n");
    println!("╔══════════════════════════════════════════════════════╗");
    println!("║                                                      ║");
    println!("║   ✓ 所有示例执行完成!                                ║");
    println!("║                                                      ║");
    println!("║   涵盖内容:                                          ║");
    println!("║   • Actor 模式 - 消息驱动并发                        ║");
    println!("║   • Reactor 模式 - 事件驱动 I/O                      ║");
    println!("║   • CSP 模式 - 通道通信                              ║");
    println!("║   • 设计模式 - 重试、熔断等                          ║");
    println!("║   • 生产模式 - 健康检查、优雅关闭                    ║");
    println!("║                                                      ║");
    println!("╚══════════════════════════════════════════════════════╝");
    println!();
}

// ============================================================================
// 单元测试
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_actor_pattern() {
        let account =
            actor_pattern::ActorSystem::spawn(actor_pattern::BankAccount::new("Test".to_string(), 100));

        let balance = account
            .send(actor_pattern::AccountMessage::Deposit(50))
            .await
            .unwrap()
            .unwrap();

        assert_eq!(balance, 150);
    }

    #[tokio::test]
    async fn test_retry_strategy() {
        let retry = design_patterns::RetryStrategy::new(3, Duration::from_millis(10));

        let mut count = 0;
        let result = retry
            .execute(|| {
                count += 1;
                Box::pin(async move {
                    if count < 2 {
                        Err("fail")
                    } else {
                        Ok(42)
                    }
                })
            })
            .await;

        assert_eq!(result, Ok(42));
    }
}
