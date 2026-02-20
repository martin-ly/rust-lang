# Actor 模型理论

> **创建日期**: 2026-02-20
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

> 内容已整合至： [c05_threads/](../../../../crates/c05_threads/)、[c06_async/](../../../../crates/c06_async/)

[返回主索引](../../00_master_index.md)

---

## Actor 模型核心概念

Actor 模型是一种并发计算模型，其中：

- 每个 Actor 是一个独立的计算实体
- Actor 之间通过异步消息传递通信
- 每个 Actor 有自己的状态，不共享内存

### 基本 Actor 实现

```rust
use std::sync::mpsc::{channel, Sender, Receiver};
use std::thread;

// 消息类型
#[derive(Debug)]
enum Message {
    Increment,
    GetValue(Sender<usize>),
    Stop,
}

// Actor 结构
pub struct CounterActor {
    sender: Sender<Message>,
}

impl CounterActor {
    pub fn new() -> Self {
        let (sender, receiver) = channel::<Message>();

        thread::spawn(move || {
            let mut count = 0usize;

            while let Ok(msg) = receiver.recv() {
                match msg {
                    Message::Increment => count += 1,
                    Message::GetValue(reply) => {
                        let _ = reply.send(count);
                    }
                    Message::Stop => break,
                }
            }

            println!("Actor stopped with final count: {}", count);
        });

        Self { sender }
    }

    pub fn increment(&self) {
        let _ = self.sender.send(Message::Increment);
    }

    pub fn get_value(&self) -> usize {
        let (tx, rx) = channel();
        let _ = self.sender.send(Message::GetValue(tx));
        rx.recv().unwrap_or(0)
    }

    pub fn stop(&self) {
        let _ = self.sender.send(Message::Stop);
    }
}

// 使用示例
fn demo() {
    let actor = CounterActor::new();

    for _ in 0..10 {
        actor.increment();
    }

    println!("Count: {}", actor.get_value());  // 10
    actor.stop();
}
```

### 异步 Actor

```rust
use tokio::sync::mpsc::{channel, Sender, Receiver};

// 消息类型
#[derive(Debug)]
enum AsyncMessage {
    Process(String),
    GetResult(Sender<String>),
    Shutdown,
}

// 异步 Actor
pub struct AsyncProcessor {
    sender: Sender<AsyncMessage>,
}

impl AsyncProcessor {
    async fn run(mut receiver: Receiver<AsyncMessage>) {
        let mut processed_count = 0usize;

        while let Some(msg) = receiver.recv().await {
            match msg {
                AsyncMessage::Process(data) => {
                    // 异步处理
                    println!("Processing: {}", data);
                    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;
                    processed_count += 1;
                    println!("Completed: {} (total: {})", data, processed_count);
                }
                AsyncMessage::GetResult(reply) => {
                    let _ = reply.send(format!("Processed {} items", processed_count)).await;
                }
                AsyncMessage::Shutdown => {
                    println!("Shutting down actor");
                    break;
                }
            }
        }
    }

    pub fn new() -> Self {
        let (sender, receiver) = channel(100);
        tokio::spawn(Self::run(receiver));
        Self { sender }
    }

    pub async fn process(&self, data: String) {
        let _ = self.sender.send(AsyncMessage::Process(data)).await;
    }

    pub async fn get_stats(&self) -> String {
        let (tx, rx) = tokio::sync::oneshot::channel();
        let _ = self.sender.send(AsyncMessage::GetResult(tx)).await;
        rx.await.unwrap_or_default()
    }

    pub async fn shutdown(&self) {
        let _ = self.sender.send(AsyncMessage::Shutdown).await;
    }
}
```

### Actor 监督与容错

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

// 监督策略
#[derive(Clone, Copy)]
pub enum SupervisionStrategy {
    OneForOne,   // 一个 Actor 失败，只重启该 Actor
    OneForAll,   // 一个 Actor 失败，重启所有 Actor
    RestForOne,  // 一个 Actor 失败，重启后续启动的 Actor
}

// 重启策略
#[derive(Clone, Copy)]
pub enum RestartPolicy {
    Permanent,   // 总是重启
    Temporary,   // 不重启
    Transient,   // 异常时重启，正常退出不重启
}

// Actor 引用
pub struct ActorRef<M> {
    id: usize,
    sender: Sender<M>,
    restart_policy: RestartPolicy,
}

// 简单的监督器
pub struct Supervisor {
    actors: Vec<Box<dyn Fn() -> thread::JoinHandle<()> + Send + Sync>>,
    strategy: SupervisionStrategy,
    max_restarts: usize,
    restart_window: std::time::Duration,
    restart_count: AtomicUsize,
    last_restart: std::sync::Mutex<std::time::Instant>,
}

impl Supervisor {
    pub fn new(strategy: SupervisionStrategy, max_restarts: usize) -> Self {
        Self {
            actors: Vec::new(),
            strategy,
            max_restarts,
            restart_window: std::time::Duration::from_secs(60),
            restart_count: AtomicUsize::new(0),
            last_restart: std::sync::Mutex::new(std::time::Instant::now()),
        }
    }

    pub fn add_actor<F>(&mut self, factory: F)
    where
        F: Fn() -> thread::JoinHandle<()> + Send + Sync + 'static,
    {
        self.actors.push(Box::new(factory));
    }

    pub fn start(&self) {
        for actor_factory in &self.actors {
            let handle = actor_factory();
            // 在实际实现中，这里应该监控线程状态并在失败时重启
            std::mem::drop(handle);
        }
    }

    fn should_restart(&self) -> bool {
        let mut last = self.last_restart.lock().unwrap();
        let now = std::time::Instant::now();

        if now.duration_since(*last) > self.restart_window {
            // 重置计数
            self.restart_count.store(0, Ordering::Relaxed);
            *last = now;
        }

        let count = self.restart_count.fetch_add(1, Ordering::Relaxed);
        count < self.max_restarts
    }
}
```

### 路由与负载均衡

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

// 轮询路由
pub struct RoundRobinRouter<M: Send + 'static> {
    actors: Vec<Sender<M>>,
    counter: AtomicUsize,
}

impl<M: Send + 'static> RoundRobinRouter<M> {
    pub fn new(actors: Vec<Sender<M>>) -> Self {
        Self {
            actors,
            counter: AtomicUsize::new(0),
        }
    }

    pub fn route(&self, msg: M) -> Result<(), M> {
        let index = self.counter.fetch_add(1, Ordering::Relaxed) % self.actors.len();
        self.actors[index].send(msg)
            .map_err(|e| e.0)
    }
}

// 哈希路由（基于 key 路由到特定 Actor）
pub struct HashRouter<M: Send + 'static> {
    actors: Vec<Sender<M>>,
}

impl<M: Send + 'static> HashRouter<M> {
    pub fn new(actors: Vec<Sender<M>>) -> Self {
        Self { actors }
    }

    pub fn route_by_key<K: std::hash::Hash>(&self, key: K, msg: M) -> Result<(), M> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        let index = (hasher.finish() as usize) % self.actors.len();

        self.actors[index].send(msg)
            .map_err(|e| e.0)
    }
}

// 广播路由
pub struct BroadcastRouter<M: Clone + Send + 'static> {
    actors: Vec<Sender<M>>,
}

impl<M: Clone + Send + 'static> BroadcastRouter<M> {
    pub fn new(actors: Vec<Sender<M>>) -> Self {
        Self { actors }
    }

    pub fn broadcast(&self, msg: M) -> Vec<Result<(), M>> {
        self.actors.iter()
            .map(|actor| actor.send(msg.clone()).map_err(|e| e.0))
            .collect()
    }
}
```

### 请求-响应模式

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::sync::{Arc, Mutex};

// 请求 ID
pub type RequestId = u64;

// 带响应的请求
pub struct Request<M, R> {
    id: RequestId,
    message: M,
    response_tx: Sender<R>,
}

// 响应句柄
pub struct ResponseHandle<R> {
    id: RequestId,
    receiver: Receiver<R>,
}

impl<R> Future for ResponseHandle<R> {
    type Output = R;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.receiver.try_recv() {
            Ok(response) => Poll::Ready(response),
            Err(_) => {
                cx.waker().wake_by_ref();
                Poll::Pending
            }
        }
    }
}

// Actor 请求客户端
pub struct ActorClient<M, R> {
    sender: Sender<Request<M, R>>,
    next_id: Arc<Mutex<RequestId>>,
}

impl<M: Send + 'static, R: Send + 'static> ActorClient<M, R> {
    pub fn new(sender: Sender<Request<M, R>>) -> Self {
        Self {
            sender,
            next_id: Arc::new(Mutex::new(0)),
        }
    }

    pub fn ask(&self, message: M) -> ResponseHandle<R> {
        let id = {
            let mut guard = self.next_id.lock().unwrap();
            *guard += 1;
            *guard
        };

        let (tx, rx) = channel();
        let request = Request {
            id,
            message,
            response_tx: tx,
        };

        let _ = self.sender.send(request);

        ResponseHandle { id, receiver: rx }
    }

    pub fn tell(&self, message: M) -> Result<(), M> {
        let (tx, _) = channel();
        let request = Request {
            id: 0,
            message,
            response_tx: tx,
        };
        self.sender.send(request).map_err(|e| e.0.message)
    }
}
```

---

## 使用场景

| 场景 | Actor 模式 | 优势 |
| :--- | :--- | :--- |
| 分布式系统 | 远程 Actor | 位置透明，网络容错 |
| 高可用服务 | 监督树 | 自动故障恢复 |
| 状态机实现 | 状态 Actor | 状态隔离，消息驱动 |
| 事件溯源 | 持久化 Actor | 状态可重放 |
| 工作流引擎 | Actor 编排 | 并发安全，可组合 |
| 游戏服务器 | 实体 Actor | 每个玩家/实体独立 |
| 实时聊天 | 路由器模式 | 负载均衡，广播 |
| 任务队列 | 工作池 Actor | 背压控制，容错 |

---

## 相关研究笔记

### 软件设计理论

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| 分布式执行模型 | 分布式模型理论 | [../../../../research_notes/software_design_theory/03_execution_models/05_distributed.md](../../../../research_notes/software_design_theory/03_execution_models/05_distributed.md) |
| 组合工程 | 组件组合理论 | [../../../../research_notes/software_design_theory/04_compositional_engineering/README.md](../../../../research_notes/software_design_theory/04_compositional_engineering/README.md) |

### 形式化方法

| 文档 | 描述 | 路径 |
| :--- | :--- | :--- |
| Send/Sync 形式化 | 消息传递安全 | [../../../../research_notes/formal_methods/send_sync_formalization.md](../../../../research_notes/formal_methods/send_sync_formalization.md) |
| 所有权模型 | 状态隔离形式化 | [../../../../research_notes/formal_methods/ownership_model.md](../../../../research_notes/formal_methods/ownership_model.md) |

---

## 相关 crates

| crate | 描述 | 路径 |
| :--- | :--- | :--- |
| c05_threads | 线程并发实现 | [../../../../crates/c05_threads/](../../../../crates/c05_threads/) |
| c06_async | 异步并发实现 | [../../../../crates/c06_async/](../../../../crates/c06_async/) |
