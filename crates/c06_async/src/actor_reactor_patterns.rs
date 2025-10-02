//! Actor 与 Reactor 模式深度分析 - Actor and Reactor Patterns Deep Analysis
//!
//! # 概述 (Overview)
//!
//! 本模块深入分析异步编程中的两种核心并发模式：
//! - Actor 模式: 基于消息传递的并发模型
//! - Reactor 模式: 基于事件驱动的 I/O 模型
//!
//! # Actor 模式理论基础
//!
//! ## 1. Actor 模型的形式化定义
//!
//! ### 1.1 基本组成
//!
//! ```text
//! Actor = (State, Mailbox, Behavior)
//!
//! 其中:
//! - State: 私有状态 σ ∈ Σ
//! - Mailbox: 消息队列 M = [m₁, m₂, ..., mₙ]
//! - Behavior: 行为函数 β: Σ × Message → (Σ, [Action])
//!
//! Action 可以是:
//! 1. Send(actor, message): 发送消息
//! 2. Create(actor_spec): 创建新 Actor
//! 3. Become(new_behavior): 改变行为
//! ```
//!
//! ### 1.2 Actor 系统的语义规则
//!
//! ```text
//! 配置: C = (A, M)
//! - A: Actor 集合
//! - M: 消息传输中的集合
//!
//! 转换规则:
//! ────────────────────────────────────────────────────
//! actor a ∈ A, mailbox(a) = [m | ms], β_a(σ_a, m) = (σ', actions)
//! ────────────────────────────────────────────────────
//! C → C' where:
//!   - state(a) := σ'
//!   - mailbox(a) := ms
//!   - M := M ∪ {messages from actions}
//!   - A := A ∪ {new actors from actions}
//! ```
//!
//! ### 1.3 Actor 模型的特性
//!
//! ```text
//! 1. 封装性 (Encapsulation):
//!    ∀ a ∈ Actors: state(a) is private
//!
//! 2. 位置透明 (Location Transparency):
//!    send(addr, msg) 不依赖于 actor 的物理位置
//!
//! 3. 异步通信 (Asynchronous Communication):
//!    send(addr, msg) 立即返回，不等待处理
//!
//! 4. 无共享状态 (No Shared State):
//!    actors 之间只通过消息通信
//! ```
//!
//! ## 2. Reactor 模式理论基础
//!
//! ### 2.1 基本组成
//!
//! ```text
//! Reactor = (EventDemultiplexer, EventHandlers, EventLoop)
//!
//! 其中:
//! - EventDemultiplexer: 事件多路分解器（如 epoll, kqueue）
//! - EventHandlers: 事件处理器集合 {h₁, h₂, ..., hₙ}
//! - EventLoop: 事件循环
//!
//! 事件: e = (source, event_type, data)
//! 处理器: handler: Event → Action
//! ```
//!
//! ### 2.2 Reactor 的执行模型
//!
//! ```text
//! loop:
//!   1. events := demultiplexer.select(registered_sources)
//!   2. for each event in events:
//!        handler := lookup_handler(event.source)
//!        handler.handle(event)
//!   3. goto loop
//!
//! 特点:
//! - 单线程执行（一般情况）
//! - 非阻塞 I/O
//! - 事件驱动
//! ```
//!
//! ### 2.3 Reactor vs Proactor
//!
//! ```text
//! Reactor 模式（同步 I/O 多路复用）:
//! 1. 注册事件
//! 2. 等待事件就绪
//! 3. 处理就绪的事件（同步读写）
//!
//! Proactor 模式（异步 I/O）:
//! 1. 发起异步 I/O 操作
//! 2. 等待完成通知
//! 3. 处理完成的操作（数据已准备好）
//!
//! Rust 的 tokio 结合了两者:
//! - 底层使用 epoll/kqueue (Reactor)
//! - 上层提供异步 API (Proactor 风格)
//! ```
//!
//! ## 3. Actor vs Reactor
//!
//! ```text
//! ┌──────────────┬─────────────────────────┬──────────────────────────┐
//! │ 特性         │ Actor                   │ Reactor                  │
//! ├──────────────┼─────────────────────────┼──────────────────────────┤
//! │ 抽象层次     │ 高层并发抽象            │ 低层 I/O 抽象            │
//! │ 通信方式     │ 消息传递                │ 事件通知                 │
//! │ 状态管理     │ 封装在 Actor 内         │ 分散在各处理器           │
//! │ 典型应用     │ 业务逻辑、有状态服务    │ 网络服务器、I/O 密集型   │
//! │ Rust 实现    │ actix, bastion, xtra    │ tokio, async-std, smol   │
//! └──────────────┴─────────────────────────┴──────────────────────────┘
//! ```

use std::sync::Arc;
use std::time::Duration;
use tokio::sync::mpsc;
use tokio::time::sleep;

/// # 示例 1: 手写 Actor 系统
///
/// 从零实现一个简单的 Actor 系统，理解其核心机制
pub mod simple_actor_system {
    use super::*;
    use std::collections::HashMap;
    use tokio::sync::RwLock;

    /// Actor 地址（唯一标识符）
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct ActorId(u64);

    /// 消息 trait
    pub trait Message: Send + 'static {
        type Result: Send + 'static;
    }

    /// Actor trait
    #[async_trait::async_trait]
    pub trait Actor: Send + 'static {
        /// 处理消息
        #[allow(unused_variables)]
        async fn handle(&mut self, msg: Box<dyn std::any::Any + Send>) -> Box<dyn std::any::Any + Send>;

        /// Actor 启动时调用
        async fn started(&mut self) {}

        /// Actor 停止时调用
        async fn stopped(&mut self) {}
    }

    /// Actor 上下文
    pub struct Context {
        id: ActorId,
        #[allow(dead_code)]
        system: Arc<ActorSystem>,
    }

    impl Context {
        /// 发送消息给其他 Actor
        pub async fn send<M>(&self, target: ActorId, _msg: M)
        where
            M: Message,
        {
            // 实现省略
            println!("  [Context] Actor {:?} 发送消息到 {:?}", self.id, target);
        }

        /// 停止当前 Actor
        pub async fn stop(&self) {
            println!("  [Context] Actor {:?} 请求停止", self.id);
        }
    }

    /// Actor 地址（用于发送消息）
    pub struct Addr<A: Actor> {
        id: ActorId,
        tx: mpsc::UnboundedSender<Box<dyn std::any::Any + Send>>,
        _phantom: std::marker::PhantomData<A>,
    }

    impl<A: Actor> Clone for Addr<A> {
        fn clone(&self) -> Self {
            Self {
                id: self.id,
                tx: self.tx.clone(),
                _phantom: std::marker::PhantomData,
            }
        }
    }

    impl<A: Actor> Addr<A> {
        /// 发送消息（不等待响应）
        pub fn do_send<M>(&self, msg: M)
        where
            M: Message,
            A: Handler<M>,
        {
            let boxed = Box::new(msg) as Box<dyn std::any::Any + Send>;
            let _ = self.tx.send(boxed);
        }

        /// 发送消息并等待响应
        pub async fn send<M>(&self, msg: M) -> Result<M::Result, &'static str>
        where
            M: Message,
            A: Handler<M>,
        {
            // 简化实现：实际需要 oneshot channel
            self.do_send(msg);
            Err("简化实现，不支持响应")
        }
    }

    /// Handler trait: Actor 处理特定消息类型
    pub trait Handler<M: Message>: Actor {
        fn handle_message(&mut self, msg: M, ctx: &mut Context) -> impl std::future::Future<Output = M::Result> + Send;
    }

    /// Actor 系统
    pub struct ActorSystem {
        next_id: Arc<RwLock<u64>>,
        actors: Arc<RwLock<HashMap<ActorId, mpsc::UnboundedSender<Box<dyn std::any::Any + Send>>>>>,
    }

    impl ActorSystem {
        /// 创建新的 Actor 系统
        pub fn new() -> Arc<Self> {
            Arc::new(Self {
                next_id: Arc::new(RwLock::new(0)),
                actors: Arc::new(RwLock::new(HashMap::new())),
            })
        }

        /// 生成 Actor
        pub async fn spawn<A>(&self, mut actor: A) -> Addr<A>
        where
            A: Actor,
        {
            let id = {
                let mut next = self.next_id.write().await;
                let id = *next;
                *next += 1;
                ActorId(id)
            };

            let (tx, mut rx) = mpsc::unbounded_channel::<Box<dyn std::any::Any + Send>>();

            {
                let mut actors = self.actors.write().await;
                actors.insert(id, tx.clone());
            }

            // 启动 Actor 的消息循环
            let system_clone = Arc::new(self.clone());
            tokio::spawn(async move {
                let _ctx = Context {
                    id,
                    system: system_clone.clone(),
                };

                actor.started().await;

                while let Some(msg) = rx.recv().await {
                    let _result = actor.handle(msg).await;
                    // 在真实实现中，这里会处理响应
                }

                actor.stopped().await;
            });

            Addr {
                id,
                tx,
                _phantom: std::marker::PhantomData,
            }
        }
    }

    impl Clone for ActorSystem {
        fn clone(&self) -> Self {
            Self {
                next_id: self.next_id.clone(),
                actors: self.actors.clone(),
            }
        }
    }

    /// 示例 Actor: 计数器
    pub struct Counter {
        count: i32,
    }

    impl Counter {
        pub fn new() -> Self {
            Self { count: 0 }
        }
    }

    #[async_trait::async_trait]
    impl Actor for Counter {
        async fn handle(&mut self, _msg: Box<dyn std::any::Any + Send>) -> Box<dyn std::any::Any + Send> {
            // 简化实现：实际应根据消息类型分发
            println!("  [Counter] 处理消息");
            Box::new(())
        }

        async fn started(&mut self) {
            println!("  [Counter] Actor 启动，初始计数: {}", self.count);
        }

        async fn stopped(&mut self) {
            println!("  [Counter] Actor 停止，最终计数: {}", self.count);
        }
    }

    /// 消息: 增加计数
    pub struct Increment(pub i32);

    impl Message for Increment {
        type Result = i32;
    }

    impl Handler<Increment> for Counter {
        async fn handle_message(&mut self, msg: Increment, _ctx: &mut Context) -> i32 {
            self.count += msg.0;
            println!("  [Counter] 增加 {}, 当前计数: {}", msg.0, self.count);
            self.count
        }
    }

    /// 演示简单 Actor 系统
    pub async fn demo() {
        println!("\n=== 简单 Actor 系统示例 ===");

        let system = ActorSystem::new();
        let addr = system.spawn(Counter::new()).await;

        // 发送消息
        addr.do_send(Increment(1));
        addr.do_send(Increment(5));
        addr.do_send(Increment(10));

        sleep(Duration::from_millis(100)).await;
        println!("✓ Actor 系统演示完成");
    }
}

/// # 示例 2: Actix 框架分析
///
/// 分析 Actix Actor 框架的实现原理
pub mod actix_analysis {
    use actix::prelude::*;

    /// 消息定义
    #[derive(Message)]
    #[rtype(result = "i32")]
    pub struct Add(pub i32, pub i32);

    #[derive(Message)]
    #[rtype(result = "i32")]
    pub struct Multiply(pub i32, pub i32);

    /// Calculator Actor
    pub struct Calculator {
        total: i32,
    }

    impl Calculator {
        pub fn new() -> Self {
            Self { total: 0 }
        }
    }

    impl Actor for Calculator {
        type Context = Context<Self>;

        fn started(&mut self, _ctx: &mut Self::Context) {
            println!("  [Calculator] Actor 启动，初始值: {}", self.total);
        }

        fn stopped(&mut self, _ctx: &mut Self::Context) {
            println!("  [Calculator] Actor 停止，最终值: {}", self.total);
        }
    }

    /// 处理 Add 消息
    impl Handler<Add> for Calculator {
        type Result = i32;

        fn handle(&mut self, msg: Add, _ctx: &mut Context<Self>) -> Self::Result {
            let result = msg.0 + msg.1;
            self.total += result;
            println!("  [Calculator] {} + {} = {}, 累计: {}", msg.0, msg.1, result, self.total);
            result
        }
    }

    /// 处理 Multiply 消息
    impl Handler<Multiply> for Calculator {
        type Result = i32;

        fn handle(&mut self, msg: Multiply, _ctx: &mut Context<Self>) -> Self::Result {
            let result = msg.0 * msg.1;
            self.total += result;
            println!("  [Calculator] {} × {} = {}, 累计: {}", msg.0, msg.1, result, self.total);
            result
        }
    }

    /// Actix 的关键特性分析
    ///
    /// ## 1. 类型安全的消息传递
    /// ```text
    /// - 消息类型通过 #[rtype] 指定返回类型
    /// - 编译期检查消息类型
    /// - 运行时保证类型安全
    /// ```
    ///
    /// ## 2. 异步消息处理
    /// ```text
    /// Actor::handle() 可以返回:
    /// - 同步值: i32
    /// - Future: impl Future<Output = i32>
    /// - MessageResponse: 自定义响应
    /// ```
    ///
    /// ## 3. Actor 生命周期
    /// ```text
    /// 生命周期钩子:
    /// - started(): Actor 启动时
    /// - stopping(): Actor 即将停止
    /// - stopped(): Actor 已停止
    /// ```
    pub async fn analyze_actix_features() {
        println!("\n=== Actix 框架特性分析 ===");

        let sys = System::new();

        sys.block_on(async {
            let addr = Calculator::new().start();

            // 发送消息并等待响应
            let result1 = addr.send(Add(10, 20)).await.unwrap();
            println!("  返回值: {}", result1);

            let result2 = addr.send(Multiply(5, 6)).await.unwrap();
            println!("  返回值: {}", result2);

            // 停止 Actor
            System::current().stop();
        });

        let _ = sys.run();
        println!("✓ Actix 特性分析完成");
    }
}

/// # 示例 3: Reactor 模式实现
///
/// 展示 Reactor 模式的核心概念
pub mod reactor_pattern {
    use super::*;
    use std::collections::HashMap;
    use std::sync::Mutex;

    /// 事件类型
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub enum EventType {
        Read,
        Write,
        Timer,
    }

    /// 事件
    #[derive(Debug)]
    pub struct Event {
        pub source: u64,
        pub event_type: EventType,
        pub data: Vec<u8>,
    }

    /// 事件处理器 trait
    #[async_trait::async_trait]
    pub trait EventHandler: Send + Sync {
        async fn handle(&self, event: Event);
    }

    /// 简单的 Reactor 实现
    pub struct SimpleReactor {
        handlers: Arc<Mutex<HashMap<(u64, EventType), Arc<dyn EventHandler>>>>,
        event_queue: Arc<Mutex<Vec<Event>>>,
    }

    impl SimpleReactor {
        pub fn new() -> Self {
            Self {
                handlers: Arc::new(Mutex::new(HashMap::new())),
                event_queue: Arc::new(Mutex::new(Vec::new())),
            }
        }

        /// 注册事件处理器
        pub fn register(&self, source: u64, event_type: EventType, handler: Arc<dyn EventHandler>) {
            let mut handlers = self.handlers.lock().unwrap();
            handlers.insert((source, event_type), handler);
            println!("  [Reactor] 注册处理器: source={}, type={:?}", source, event_type);
        }

        /// 提交事件（模拟）
        pub fn submit_event(&self, event: Event) {
            let mut queue = self.event_queue.lock().unwrap();
            queue.push(event);
        }

        /// 事件循环
        ///
        /// ## 伪代码
        /// ```text
        /// loop:
        ///   events = demultiplexer.select()
        ///   for event in events:
        ///     handler = lookup(event.source, event.type)
        ///     handler.handle(event)
        /// ```
        pub async fn run(&self, iterations: usize) {
            println!("  [Reactor] 启动事件循环");

            for i in 0..iterations {
                // 模拟事件多路分解器
                let events = {
                    let mut queue = self.event_queue.lock().unwrap();
                    std::mem::take(&mut *queue)
                };

                if events.is_empty() {
                    // 模拟等待
                    sleep(Duration::from_millis(10)).await;
                    continue;
                }

                println!("  [Reactor] 迭代 {}: 处理 {} 个事件", i, events.len());

                // 分发事件
                for event in events {
                    let handler = {
                        let handlers = self.handlers.lock().unwrap();
                        handlers.get(&(event.source, event.event_type)).cloned()
                    };

                    if let Some(handler) = handler {
                        handler.handle(event).await;
                    }
                }
            }

            println!("  [Reactor] 事件循环结束");
        }
    }

    /// 示例处理器: 回显
    pub struct EchoHandler;

    #[async_trait::async_trait]
    impl EventHandler for EchoHandler {
        async fn handle(&self, event: Event) {
            println!(
                "    [EchoHandler] 处理事件: source={}, type={:?}, data={:?}",
                event.source, event.event_type, event.data
            );
        }
    }

    /// 示例处理器: 计数
    pub struct CounterHandler {
        count: Arc<Mutex<usize>>,
    }

    impl CounterHandler {
        pub fn new() -> Self {
            Self {
                count: Arc::new(Mutex::new(0)),
            }
        }

        pub fn get_count(&self) -> usize {
            *self.count.lock().unwrap()
        }
    }

    #[async_trait::async_trait]
    impl EventHandler for CounterHandler {
        async fn handle(&self, event: Event) {
            let mut count = self.count.lock().unwrap();
            *count += 1;
            println!(
                "    [CounterHandler] 计数: {}, 事件: source={}, type={:?}",
                *count, event.source, event.event_type
            );
        }
    }

    /// 演示 Reactor 模式
    pub async fn demo() {
        println!("\n=== Reactor 模式示例 ===");

        let reactor = SimpleReactor::new();

        // 注册处理器
        reactor.register(1, EventType::Read, Arc::new(EchoHandler));
        reactor.register(2, EventType::Write, Arc::new(EchoHandler));
        let counter = Arc::new(CounterHandler::new());
        reactor.register(3, EventType::Timer, counter.clone());

        // 提交事件
        reactor.submit_event(Event {
            source: 1,
            event_type: EventType::Read,
            data: vec![1, 2, 3],
        });

        reactor.submit_event(Event {
            source: 2,
            event_type: EventType::Write,
            data: vec![4, 5, 6],
        });

        reactor.submit_event(Event {
            source: 3,
            event_type: EventType::Timer,
            data: vec![],
        });

        reactor.submit_event(Event {
            source: 3,
            event_type: EventType::Timer,
            data: vec![],
        });

        // 运行事件循环
        reactor.run(5).await;

        println!("  计数器最终值: {}", counter.get_count());
        println!("✓ Reactor 模式演示完成");
    }
}

/// # 示例 4: Tokio 的 Reactor 分析
///
/// 分析 Tokio 运行时的 Reactor 实现
pub mod tokio_reactor_analysis {
    use super::*;

    /// Tokio Reactor 的层次结构
    ///
    /// ```text
    /// ┌─────────────────────────────────────────┐
    /// │     Runtime (多线程调度器)              │
    /// │  ┌─────────────┬─────────────────────┐ │
    /// │  │  Worker 1   │   Worker 2  │ ...   │ │
    /// │  │  ┌────────┐ │  ┌────────┐ │       │ │
    /// │  │  │TaskQueue│ │  │TaskQueue│ │       │ │
    /// │  │  └────────┘ │  └────────┘ │       │ │
    /// │  └─────────────┴─────────────────────┘ │
    /// └─────────────────────────────────────────┘
    ///         ↓
    /// ┌─────────────────────────────────────────┐
    /// │        Reactor (事件循环)               │
    /// │  ┌──────────────────────────────────┐  │
    /// │  │  epoll/kqueue/IOCP (OS level)    │  │
    /// │  └──────────────────────────────────┘  │
    /// └─────────────────────────────────────────┘
    /// ```
    ///
    /// ## 关键组件
    ///
    /// 1. **Driver**: 驱动 I/O 事件
    /// 2. **Parker**: 线程停放机制
    /// 3. **Waker**: 唤醒机制
    /// 4. **Handle**: 运行时句柄
    pub fn explain_tokio_architecture() {
        println!("\n=== Tokio Reactor 架构分析 ===");

        println!("
1. Runtime 层:
   - 管理工作线程池
   - 任务调度与负载均衡
   - 支持 current_thread 和 multi_thread

2. Reactor 层:
   - 基于操作系统的 I/O 多路复用
   - Linux: epoll
   - macOS/BSD: kqueue
   - Windows: IOCP (I/O Completion Ports)

3. Driver 层:
   - Time Driver: 定时器管理
   - IO Driver: I/O 事件管理
   - Signal Driver: 信号处理

4. 异步原语:
   - TcpListener/TcpStream: 异步 TCP
   - UdpSocket: 异步 UDP
   - File: 异步文件 I/O (基于线程池)
        ");

        println!("✓ 架构分析完成");
    }

    /// 演示 Tokio 的事件循环
    pub async fn demo_event_loop() {
        println!("\n=== Tokio 事件循环示例 ===");

        println!("  创建多个异步任务...");

        // 任务1: 定时器
        let task1 = tokio::spawn(async {
            for i in 0..3 {
                sleep(Duration::from_millis(50)).await;
                println!("    [Task1] 定时器触发: {}", i);
            }
            "Task1 完成"
        });

        // 任务2: 另一个定时器
        let task2 = tokio::spawn(async {
            for i in 0..3 {
                sleep(Duration::from_millis(70)).await;
                println!("    [Task2] 定时器触发: {}", i);
            }
            "Task2 完成"
        });

        // 等待任务完成
        let (r1, r2) = tokio::join!(task1, task2);
        println!("  结果: {:?}, {:?}", r1, r2);

        println!("✓ 事件循环演示完成");
    }
}

/// # 示例 5: Actor vs Reactor 对比
///
/// 直接对比两种模式的实现
pub mod actor_vs_reactor {

    /// 场景: 处理多个并发请求
    ///
    /// ## Actor 方式
    pub mod actor_approach {
        use actix::prelude::*;

        #[derive(Message)]
        #[rtype(result = "String")]
        pub struct Request {
            pub id: u32,
            pub data: String,
        }

        pub struct RequestProcessor;

        impl Actor for RequestProcessor {
            type Context = Context<Self>;
        }

        impl Handler<Request> for RequestProcessor {
            type Result = String;

            fn handle(&mut self, msg: Request, _ctx: &mut Context<Self>) -> Self::Result {
                println!("    [Actor] 处理请求 #{}: {}", msg.id, msg.data);
                format!("已处理: {}", msg.data)
            }
        }

        pub async fn demo() {
            println!("\n  === Actor 方式 ===");
            let sys = System::new();
            sys.block_on(async {
                let addr = RequestProcessor.start();

                let mut handles = vec![];
                for i in 0..5 {
                    let addr = addr.clone();
                    let handle = tokio::spawn(async move {
                        addr.send(Request {
                            id: i,
                            data: format!("请求数据 {}", i),
                        })
                        .await
                    });
                    handles.push(handle);
                }

                for handle in handles {
                    let _ = handle.await;
                }

                System::current().stop();
            });
            let _ = sys.run();
            println!("  ✓ Actor 方式完成");
        }
    }

    /// ## Reactor 方式
    pub mod reactor_approach {
        use tokio::time::sleep;
        use std::time::Duration;

        pub async fn demo() {
            println!("\n  === Reactor 方式 ===");

            let mut handles = vec![];
            for i in 0..5 {
                let handle = tokio::spawn(async move {
                    // 模拟异步 I/O 操作
                    sleep(Duration::from_millis(10)).await;
                    println!("    [Reactor] 处理请求 #{}: 请求数据 {}", i, i);
                    format!("已处理: 请求数据 {}", i)
                });
                handles.push(handle);
            }

            for handle in handles {
                let _ = handle.await;
            }

            println!("  ✓ Reactor 方式完成");
        }
    }

    /// 对比分析
    pub async fn compare() {
        println!("\n=== Actor vs Reactor 对比 ===");

        actor_approach::demo().await;
        reactor_approach::demo().await;

        println!("\n对比总结:");
        println!("  Actor 方式:");
        println!("    ✓ 封装状态管理");
        println!("    ✓ 类型安全的消息");
        println!("    ✓ 适合有状态的业务逻辑");
        println!("    ✗ 额外的抽象开销");

        println!("\n  Reactor 方式:");
        println!("    ✓ 直接的异步操作");
        println!("    ✓ 低层次的控制");
        println!("    ✓ 适合 I/O 密集型任务");
        println!("    ✗ 状态管理需要手动处理");
    }
}

/// # 综合示例: 运行所有演示
pub async fn run_all_examples() {
    println!("╔══════════════════════════════════════════════════════════╗");
    println!("║       Actor 与 Reactor 模式深度分析                      ║");
    println!("║       Actor and Reactor Patterns Deep Analysis           ║");
    println!("╚══════════════════════════════════════════════════════════╝");

    // 1. 简单 Actor 系统
    simple_actor_system::demo().await;

    // 2. Actix 框架分析
    actix_analysis::analyze_actix_features().await;

    // 3. Reactor 模式
    reactor_pattern::demo().await;

    // 4. Tokio Reactor 分析
    tokio_reactor_analysis::explain_tokio_architecture();
    tokio_reactor_analysis::demo_event_loop().await;

    // 5. Actor vs Reactor 对比
    actor_vs_reactor::compare().await;

    println!("\n════════════════════════════════════════════════════════════");
    println!("所有模式示例执行完成！");
    println!("════════════════════════════════════════════════════════════\n");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_simple_actor() {
        simple_actor_system::demo().await;
    }

    #[tokio::test]
    async fn test_reactor() {
        reactor_pattern::demo().await;
    }

    #[tokio::test]
    async fn test_tokio_event_loop() {
        tokio_reactor_analysis::demo_event_loop().await;
    }
}

