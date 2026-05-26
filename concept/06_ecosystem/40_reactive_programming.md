# Reactive Programming & FRP（响应式编程与函数式响应编程）

> **Bloom 层级**: 应用 → 分析
> **A/S/P 标记**: **A+P** — Application + Procedure
> **双维定位**: C×Ana — 分析异步数据流的声明式组合模式
> **前置依赖**: [Async/Await](../03_advanced/02_async.md) ·
> [Stream Processing Semantics](../03_advanced/20_stream_processing_semantics.md) ·
> [事件驱动架构](./32_event_driven_architecture.md)
> **后置延伸**: [CQRS & Event Sourcing](./33_cqrs_event_sourcing.md) ·
> [流处理生态](./36_stream_processing_ecosystem.md)

---

> **来源**: [Reactive Manifesto](https://www.reactivemanifesto.org/) ·
> [来源: [Reactive Streams Spec](https://www.reactive-streams.org/)] · [来源: [Elliott & Hudak 1997](https://haskell.cs.yale.edu/wp-content/uploads/2011/02/frp.pdf)]
> [Reactive Streams Specification](https://www.reactive-streams.org/) ·
> [Elliott & Hudak 1997 — Functional Reactive Animation](https://haskell.cs.yale.edu/wp-content/uploads/2011/02/frp.pdf) ·
> [Elliott 2009 — Push-Pull FRP](https://conal.net/papers/push-pull-frp/push-pull-frp.pdf) ·
> [Tokio Streams](https://docs.rs/tokio-stream/latest/tokio_stream/) ·
> [futures-rs Stream](https://docs.rs/futures/latest/futures/stream/trait.Stream.html) ·
> [RxRust](https://docs.rs/rxrust/latest/rxrust/)

## 📑 目录

- [Reactive Programming \& FRP（响应式编程与函数式响应编程）](#reactive-programming--frp响应式编程与函数式响应编程)
  - [📑 目录](#-目录)
  - [一、权威定义（Definition）](#一权威定义definition)
    - [1.1 Reactive Manifesto：响应式系统的四大特质](#11-reactive-manifesto响应式系统的四大特质)
    - [1.2 Reactive Streams：背压感知的异步数据流](#12-reactive-streams背压感知的异步数据流)
    - [1.3 FRP：函数式响应编程](#13-frp函数式响应编程)
  - [二、概念属性矩阵](#二概念属性矩阵)
    - [2.1 Reactive 编程模型对比矩阵](#21-reactive-编程模型对比矩阵)
  - [三、Reactive Streams 核心](#三reactive-streams-核心)
    - [3.1 四元接口模型](#31-四元接口模型)
    - [3.2 Rust 中的 Stream trait](#32-rust-中的-stream-trait)
    - [3.3 组合子代数](#33-组合子代数)
  - [四、背压机制](#四背压机制)
    - [4.1 背压策略对比](#41-背压策略对比)
    - [4.2 Rust 实现](#42-rust-实现)
  - [五、FRP 模型](#五frp-模型)
    - [5.1 Signal vs Event](#51-signal-vs-event)
    - [5.2 连续语义 vs 离散语义](#52-连续语义-vs-离散语义)
    - [5.3 Rust 中的 FRP 限制](#53-rust-中的-frp-限制)
  - [六、数据流编程](#六数据流编程)
    - [6.1 推模型 vs 拉模型](#61-推模型-vs-拉模型)
    - [6.2 与 Rust Stream 的对应](#62-与-rust-stream-的对应)
  - [七、Rust 实现](#七rust-实现)
    - [7.1 tokio-stream](#71-tokio-stream)
    - [7.2 async-stream](#72-async-stream)
    - [7.3 完整数据流处理骨架](#73-完整数据流处理骨架)
  - [八、反命题与边界](#八反命题与边界)
    - [8.1 反命题树](#81-反命题树)
    - [8.2 边界极限](#82-边界极限)
  - [九、边界测试](#九边界测试)
    - [9.1 边界测试：无背压导致内存溢出（运行时错误）](#91-边界测试无背压导致内存溢出运行时错误)
    - [9.2 边界测试：跨线程 Stream 发送违反 Send（编译错误）](#92-边界测试跨线程-stream-发送违反-send编译错误)
    - [9.3 边界测试：FRP 信号循环引用导致死锁（运行时错误）](#93-边界测试frp-信号循环引用导致死锁运行时错误)
  - [相关概念文件](#相关概念文件)

> **Bloom 层级**: 应用 → 评价
**变更日志**:

> **补充来源**: [Reactive Streams JVM](https://github.com/reactive-streams/reactive-streams-jvm) · [Tokio Stream Internals](https://tokio.rs/tokio/topics/internals)

> **补充来源**: [来源: [RxRust](https://docs.rs/rxrust/latest/rxrust/)] · [来源: [futures-signals](https://docs.rs/futures-signals/latest/futures_signals/)]

- v1.0 (2026-05-25): 初始创建——Reactive Streams、FRP、数据流编程专题，覆盖背压机制、Stream trait 组合子、Rust 实现骨架

---

## 一、权威定义（Definition）

### 1.1 Reactive Manifesto：响应式系统的四大特质

> **[The Reactive Manifesto](https://www.reactivemanifesto.org/)** 响应式系统具备四个核心特质：
> **Responsive（响应性）**、**Resilient（弹性）**、**Elastic（弹性扩展）**、**Message Driven（消息驱动）**。
> 这些特质共同构成一个**连贯的设计哲学**，而非独立特性的堆砌。

```text
Reactive Manifesto 四特质（2014）:
┌─────────────────────────────────────────────────────────────┐
│                        Responsive                           │
│         系统在合理时间内响应，提供一致的响应质量                │
│              ↑ 依赖 ↓                                       │
│  Resilient ←────→ Elastic                                   │
│  故障隔离、   自动扩展、                                      │
│  自动恢复     负载均衡                                       │
│              ↑ 依赖 ↓                                       │
│                   Message Driven                            │
│         异步消息传递、无阻塞、背压感知                         │
└─────────────────────────────────────────────────────────────┘
```

> **关键洞察**: Reactive Manifesto 的**响应性**（Responsive）是最终目标，而其他三个特质是**手段**：
>
> - **弹性**（Resilience）保证系统部分故障时不完全崩溃 → 从而保持响应
> - **弹性扩展**（Elasticity）保证负载变化时自动调整资源 → 从而保持响应
> - **消息驱动**（Message Driven）是前两者实现的**基础机制**——通过异步、非阻塞、背压感知的消息传递解耦组件
>
> **来源**: [Reactive Manifesto](https://www.reactivemanifesto.org/) · [Reactive Streams Specification](https://www.reactive-streams.org/)
> [来源: [Elliott 2009 — Push-Pull FRP](https://conal.net/papers/push-pull-frp/push-pull-frp.pdf)] · [来源: [Tokio Stream](https://docs.rs/tokio-stream/latest/tokio_stream/)]

### 1.2 Reactive Streams：背压感知的异步数据流

> **[Reactive Streams Specification](https://www.reactive-streams.org/)** 定义了一组用于异步流处理的最小接口，核心目标是**标准化 JVM 平台上的背压机制**。
> 规范包含四个接口：`Publisher<T>`、`Subscriber<T>`、`Subscription`、`Processor<T,R>`。

```text
Reactive Streams 四元接口:

Publisher<T>          Subscriber<T>
  │                       │
  │  onSubscribe(sub)     │
  │ ─────────────────────>│
  │                       │
  │  onNext(T)            │
  │ ─────────────────────>│
  │  onNext(T)            │
  │ ─────────────────────>│
  │  onError(Throwable)   │
  │ ─────────────────────>│
  │  onComplete()         │
  │ ─────────────────────>│
  │                       │
  │        request(n)     │
  │ <─────────────────────│  ← 背压控制：Subscriber 按需请求

Subscription:
  - request(n): 请求 n 个元素
  - cancel(): 取消订阅

Processor<T,R>:
  - 同时实现 Publisher<R> 和 Subscriber<T>
  - 用于转换/过滤/映射数据流
```

> **来源**: [Reactive Streams Specification](https://www.reactive-streams.org/) ·
> [来源: [futures-rs Stream](https://docs.rs/futures/latest/futures/stream/trait.Stream.html)] · [来源: [Tokio mpsc](https://docs.rs/tokio/latest/tokio/sync/mpsc/index.html)]
> [Reactive Streams JVM](https://github.com/reactive-streams/reactive-streams-jvm)

### 1.3 FRP：函数式响应编程

> **[Elliott & Hudak 1997 — Functional Reactive Animation](https://haskell.cs.yale.edu/wp-content/uploads/2011/02/frp.pdf)**
> FRP（Functional Reactive Programming）是一种将**时间变化值**（Signals/Behaviors）作为一等公民的编程范式。
> 核心抽象是 `Behavior a = Time → a`（时间到值的连续函数）和 `Event a = [(Time, a)]`（带时间戳的离散事件序列）。

```text
FRP 核心抽象（Elliott & Hudak 1997）:

Behavior a = Time → a       -- 连续信号：任意时刻都有值
                             例: mousePosition :: Behavior (Float, Float)
                             含义: 任意时刻 t，mousePosition(t) = 当前鼠标坐标

Event a = [(Time, a)]       -- 离散事件：带时间戳的值序列
                             例: mouseClick :: Event ()
                             含义: [(t1, ()), (t2, ()), ...] —— 每次点击的时间戳

FRP 组合子:
  stepper :: a → Event a → Behavior a
    -- 用初始值和事件构建行为
    例: stepper 0 counterIncrement  → 从0开始，每次事件发生时递增

  sample :: Behavior a → Event b → Event a
    -- 在事件触发时采样行为的值
    例: sample mousePosition mouseClick → 点击时的鼠标坐标

  accumE :: a → Event (a → a) → Event a
    -- 累积事件，类似 fold
```

> **Push-Pull FRP**（Elliott 2009）区分两种求值策略：
>
> - **Push**（推）：事件驱动，事件发生时主动推送更新
> - **Pull**（拉）：需求驱动，消费者请求时才计算值
> - **混合**：信号（Signal）按需拉取（懒计算），事件（Event）主动推送（ eager）
>
> **来源**: [Elliott & Hudak 1997](https://haskell.cs.yale.edu/wp-content/uploads/2011/02/frp.pdf) ·
> [Elliott 2009 — Push-Pull FRP](https://conal.net/papers/push-pull-frp/push-pull-frp.pdf)

---

## 二、概念属性矩阵

### 2.1 Reactive 编程模型对比矩阵

| **维度** | **Reactive Streams** | **FRP (Signal/Event)** | **Dataflow** | **Rust Stream** |
| :--- | :--- | :--- | :--- | :--- |
| **抽象单位** | `Publisher<T>` | `Behavior a` / `Event a` | 变量/节点 | `Stream<Item = T>` |
| **时间模型** | 离散异步 | 连续 + 离散 | 离散传播 | 离散异步 |
| **背压** | ✅ 核心设计 | ❌ 通常无 | 隐式（DAG 拓扑）| ✅ `poll_next` + buffer |
| **组合子** | map/filter/merge | lift/sample/switch | 自动传播 | map/filter/merge/fold |
| **内存模型** | 无状态 / 冷流 | 有状态 / 热信号 | 节点状态 | 无状态（默认）|
| **适用场景** | 服务端 IO | UI/GUI/动画 | 电子表格/编译器 | 异步网络 IO |
| **Rust 生态** | N/A (JVM 规范) | futures-signals, relm | N/A (语言内置) | tokio-stream, futures |

> **来源**: [Reactive Streams Spec](https://www.reactive-streams.org/) ·
> [Elliott & Hudak 1997](https://haskell.cs.yale.edu/wp-content/uploads/2011/02/frp.pdf) ·
> [Tokio Stream](https://docs.rs/tokio-stream/latest/tokio_stream/)

---

## 三、Reactive Streams 核心

### 3.1 四元接口模型

Reactive Streams 规范定义了四个核心接口，标准化了**发布-订阅-背压**的交互协议：

```rust
// Reactive Streams 规范的 Rust 精神等价（futures-rs 的 Stream 是更 Rust 化的设计）

// Publisher: 数据生产者
pub trait Publisher<T> {
    fn subscribe(&self, subscriber: Box<dyn Subscriber<T>>);
}

// Subscriber: 数据消费者
pub trait Subscriber<T> {
    fn on_subscribe(&self, subscription: Box<dyn Subscription>);
    fn on_next(&self, item: T);
    fn on_error(&self, error: Box<dyn std::error::Error>);
    fn on_complete(&self);
}

// Subscription: 背压控制句柄
pub trait Subscription {
    fn request(&self, n: usize);  // 请求 n 个元素
    fn cancel(&self);             // 取消订阅
}

// Processor: 转换器（Publisher + Subscriber）
pub trait Processor<T, R>: Publisher<R> + Subscriber<T> {}
```

> **与 Rust Stream trait 的区别**: Rust 的 `futures::Stream` 是**拉模型**（Pull-based），而 Reactive Streams 是**推-拉混合**（Push-Pull hybrid）：
>
> - `Stream::poll_next()` → 消费者主动拉取（Pull）
> - Reactive Streams `onNext` → 生产者主动推送（Push），但受 `request(n)` 限制
>
> **来源**: [Reactive Streams Spec](https://www.reactive-streams.org/) ·
> [futures-rs Stream](https://docs.rs/futures/latest/futures/stream/trait.Stream.html)

### 3.2 Rust 中的 Stream trait

```rust
// Rust 的标准 Stream trait（futures crate）
use std::pin::Pin;
use std::task::{Context, Poll};

pub trait Stream {
    type Item;
    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>>;
}
```

Rust 的 `Stream` trait 设计哲学：

```text
Stream trait 设计决策:
  1. Pull-based: 消费者驱动 → 天然背压（消费者不 poll，生产者不工作）
  2. Pin<&mut Self>: 支持自引用结构（如递归异步生成器）
  3. Poll<Option<T>>: Ready(Some)/Ready(None)/Pending 三态
     - Some(T): 下一个元素就绪
     - None: 流结束
     - Pending: 元素尚未就绪，注册 waker 后异步唤醒
  4. 零成本: Stream 组合子是零成本抽象（编译期内联）
```

```rust
use futures::stream::{self, StreamExt};

// Stream 的基本使用
let mut st = stream::iter(vec![1, 2, 3, 4, 5]);

while let Some(item) = st.next().await {
    println!("{}", item);
}
```

> **来源**: [futures-rs Stream](https://docs.rs/futures/latest/futures/stream/trait.Stream.html) ·
> [Tokio Stream](https://docs.rs/tokio-stream/latest/tokio_stream/)

### 3.3 组合子代数
>

Stream 组合子构成一个**单子**（Monad-like）代数结构：

```rust
use futures::stream::{self, StreamExt, TryStreamExt};

// 核心组合子（与 Iterator 高度一致）
let pipeline = stream::iter(0..1000)
    .map(|x| x * 2)           // Functor map: Stream<A> → Stream<B>
    .filter(|x| x % 3 == 0)   // 过滤
    .take(10)                  // 只取前 10 个
    .enumerate()               // 附加索引
    .then(|(i, x)| async move {  // 异步 map（返回 Future）
        fetch_data(x).await
    })
    .buffer_unordered(5)       // 最多 5 个并发
    .filter_map(|x| async move {  // 异步 filter + map
        if x.is_ok() { Some(x.unwrap()) } else { None }
    });

// 收集结果
let results: Vec<_> = pipeline.collect().await;
```

| **组合子** | **类型签名** | **语义** | **背压影响** |
|:---|:---|:---|:---|
| `map` | `Stream<A> → (A→B) → Stream<B>` | Functor | 1:1 |
| `filter` | `Stream<A> → (A→bool) → Stream<A>` | 过滤 | 输入 > 输出 |
| `take` | `Stream<A> → n → Stream<A>` | 截取 | 提前终止 |
| `then` | `Stream<A> → (A→Future<B>) → Stream<B>` | 异步映射 | 并发控制 |
| `buffer_unordered` | `Stream<Future<B>> → n → Stream<B>` | 并发限制 | 缓冲 n 个 |
| `fold` | `Stream<A> → b → (b→A→b) → Future<b>` | 聚合 | 消费全部 |
| `merge` | `Stream<A> × Stream<A> → Stream<A>` | 合并 | 竞争消费 |

> **来源**: [futures-rs StreamExt](https://docs.rs/futures/latest/futures/stream/trait.StreamExt.html) ·
> [Tokio StreamExt](https://docs.rs/tokio-stream/latest/tokio_stream/trait.StreamExt.html)

---

## 四、背压机制

### 4.1 背压策略对比
>

背压（Backpressure）是 Reactive 系统的核心问题：当**生产者速度快于消费者**时，如何防止消费者被压垮？

```text
生产者速率: ████████████████████  (1000 msg/s)
消费者速率: ████████              (400 msg/s)
            ↑
        差距: 600 msg/s 每秒积累
        无背压 → 内存溢出（OOM）
        有背压 → 系统稳定运行
```

| **背压策略** | **机制** | **优点** | **缺点** | **Rust 实现** |
|:---|:---|:---|:---|:---|
| **Buffer** | 有界队列缓冲 | 简单、吞吐高 | 队列满时仍需决策 | `mpsc::channel(n)` |
| **Drop** | 丢弃溢出消息 | 低延迟保证 | 数据丢失 | `broadcast` |
| **Block** | 生产者阻塞等待 | 不丢数据 | 阻塞影响吞吐 | `send().await` |
| **Rate Limit** | 生产者限速 | 可预测 | 需要调参 | `tokio::time::interval` |
| **Credit-Based** | 消费者授予配额 | 精确控制 | 协议复杂 | 手动实现 |

> **来源**: [来源: [Reactive Streams — Backpressure](https://www.reactive-streams.org/)]

### 4.2 Rust 实现
>

```rust
use tokio::sync::mpsc;

// 策略 1: Buffer（有界 channel）
// 生产者速度快时，send().await 阻塞直到有空间
let (tx, mut rx) = mpsc::channel::<i32>(100);  // 缓冲 100 个

tokio::spawn(async move {
    for i in 0..1_000_000 {
        tx.send(i).await.unwrap();  // 满时自动阻塞（背压）
    }
});

while let Some(msg) = rx.recv().await {
    process_slow(msg).await;  // 慢消费者
}

// 策略 2: Drop（丢弃旧消息）
use tokio::sync::broadcast;
let (tx, _rx) = broadcast::channel::<i32>(16);
// 慢消费者会自动被移除（lagging receiver dropped）

// 策略 3: Rate Limit（生产者限速）
use tokio::time::{interval, Duration};
let mut tick = interval(Duration::from_millis(100));  // 10 msg/s
loop {
    tick.tick().await;
    tx.send(generate_data()).await.unwrap();
}

// 策略 4: 自定义 Credit-Based（精细控制）
use std::sync::atomic::{AtomicUsize, Ordering};

struct CreditBasedChannel<T> {
    tx: mpsc::Sender<T>,
    rx: mpsc::Receiver<T>,
    credits: AtomicUsize,
}

impl<T> CreditBasedChannel<T> {
    fn new(capacity: usize) -> Self {
        let (tx, rx) = mpsc::channel(capacity);
        Self { tx, rx, credits: AtomicUsize::new(capacity) }
    }

    async fn send_with_credit(&self, item: T) -> Result<(), mpsc::error::SendError<T>> {
        // 等待 credits > 0
        while self.credits.load(Ordering::Relaxed) == 0 {
            tokio::task::yield_now().await;
        }
        self.credits.fetch_sub(1, Ordering::Relaxed);
        self.tx.send(item).await
    }

    async fn recv_and_grant_credit(&mut self, grant: usize) -> Option<T> {
        let item = self.rx.recv().await;
        self.credits.fetch_add(grant, Ordering::Relaxed);
        item
    }
}
```

> **来源**: [Reactive Streams Spec — Backpressure](https://www.reactive-streams.org/) ·
> [Tokio mpsc](https://docs.rs/tokio/latest/tokio/sync/mpsc/index.html) ·
> [Tokio broadcast](https://docs.rs/tokio/latest/tokio/sync/broadcast/index.html)

---

## 五、FRP 模型

### 5.1 Signal vs Event
>

FRP 的核心区分是 **Signal**（行为/Behavior）与 **Event**（事件）：

```text
Signal (Behavior) a = Time → a     -- 连续语义
  ├── 任意时刻都有值
  ├── 例: 温度传感器读数、鼠标位置、股票价格
  └── 组合: lift :: (a → b) → Signal a → Signal b

Event a = [(Time, a)]              -- 离散语义
  ├── 只在特定时刻有值
  ├── 例: 按钮点击、HTTP 请求到达、交易成交
  └── 组合: merge :: Event a → Event a → Event a

关系:
  stepper :: a → Event a → Signal a      -- 事件 → 信号（采样保持）
  sample :: Signal a → Event b → Event a -- 信号 → 事件（事件触发采样）
```

```rust
// Rust 中的 Signal/Event 近似（使用 futures-signals 或手动实现）

// Signal: 有状态、可订阅的值
use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicI32, Ordering};

struct Signal<T> {
    value: Arc<Mutex<T>>,
    subscribers: Arc<Mutex<Vec<Box<dyn Fn(&T) + Send>>>>,
}

impl<T: Clone + Send + 'static> Signal<T> {
    fn new(initial: T) -> Self {
        Self {
            value: Arc::new(Mutex::new(initial)),
            subscribers: Arc::new(Mutex::new(vec![])),
        }
    }

    fn get(&self) -> T {
        self.value.lock().unwrap().clone()
    }

    fn set(&self, new_value: T) {
        let mut val = self.value.lock().unwrap();
        *val = new_value.clone();
        drop(val);  // 释放锁后再通知，避免死锁

        for subscriber in self.subscribers.lock().unwrap().iter() {
            subscriber(&new_value);
        }
    }

    fn subscribe(&self, f: Box<dyn Fn(&T) + Send>) {
        self.subscribers.lock().unwrap().push(f);
    }
}

// Event: 无状态、可订阅的离散通知
struct Event<T> {
    subscribers: Arc<Mutex<Vec<Box<dyn Fn(&T) + Send>>>>,
}

impl<T: Send + 'static> Event<T> {
    fn new() -> Self {
        Self { subscribers: Arc::new(Mutex::new(vec![])) }
    }

    fn emit(&self, value: T) {
        for subscriber in self.subscribers.lock().unwrap().iter() {
            subscriber(&value);
        }
    }

    fn subscribe(&self, f: Box<dyn Fn(&T) + Send>) {
        self.subscribers.lock().unwrap().push(f);
    }
}
```

> **来源**: [Elliott & Hudak 1997](https://haskell.cs.yale.edu/wp-content/uploads/2011/02/frp.pdf) · [futures-signals](https://docs.rs/futures-signals/latest/futures_signals/)

### 5.2 连续语义 vs 离散语义
>

| **维度** | **Signal（连续）** | **Event（离散）** |
|:---|:---|:---|
| **时间模型** | 连续时间 ℝ | 离散时间点序列 |
| **存在性** | 任意时刻有值 | 只在发生时有值 |
| **组合方式** | 函数提升（lift）| 合并/过滤（merge/filter）|
| **典型应用** | UI 状态、传感器数据 | 用户输入、网络消息 |
| **Rust 表达** | `Arc<Mutex<T>>` + watch | `Stream` / `mpsc::channel` |

```text
连续语义的问题（Time Leak）:
  Signal a = Time → a 意味着 "任意时刻" 可采样
  但在数字计算机中，Time 是离散的（事件循环/帧率）

  解决方案（Elliott 2009 Push-Pull FRP）:
    ├── Push: 事件发生时主动推送更新
    ├── Pull: 信号值按需计算（懒加载）
    └── 混合: 事件用 Push，信号用 Pull

Rust 的现实:
  - 没有真正的连续时间（计算机是离散事件驱动的）
  - tokio::time::interval 模拟连续采样
  - Stream 是离散事件序列的抽象
```

> **来源**: [Elliott 2009 — Push-Pull FRP](https://conal.net/papers/push-pull-frp/push-pull-frp.pdf)

### 5.3 Rust 中的 FRP 限制
>

Rust 的所有权系统与 FRP 的**有状态信号**存在根本张力：

```rust
// FRP 的核心问题：信号网络中的共享可变状态
// 在 Haskell 中: Signal 是不可变的，更新创建新 Signal
// 在 Rust 中: 需要 Arc<Mutex<T>> 或 RwLock，带来运行时开销

// 问题 1: 循环依赖（Signal A 依赖 Signal B，Signal B 又依赖 Signal A）
// Haskell: 通过 laziness 解决（声明式定义，求值时展开）
// Rust: 循环引用导致死锁或内存泄漏

// 问题 2: 生命周期管理
// FRP 框架需要长期存在的订阅关系
// Rust: 需要 'static 生命周期，限制灵活性

// 问题 3: 组合子的所有权转移
// map/filter/merge 等组合子需要消费 Stream
// 但 FRP 中信号是长期存在的，不能一次性消费
```

| **FRP 特性** | **Haskell** | **Rust** | **限制原因** |
|:---|:---|:---|:---|
| 不可变信号 | ✅ 原生 | ⚠️ `Arc<Mutex<T>>` | 所有权 vs 共享 |
| 循环信号图 | ✅ Laziness | ❌ 难实现 | 借用检查器 |
| 垃圾回收 | ✅ GC | ❌ 无 GC | 信号网络生命周期 |
| 零成本抽象 | ⚠️ 惰性开销 | ✅ 编译期优化 | 设计权衡 |

> **来源**: [Rust FRP Survey](https://github.com/rust-unofficial/awesome-rust#frp) · [futures-signals crate](https://docs.rs/futures-signals/latest/futures_signals/)

---

## 六、数据流编程

> **来源**: [Tokio Internals](https://tokio.rs/tokio/topics/internals)

### 6.1 推模型 vs 拉模型
>

```text
推模型（Push）:                拉模型（Pull）:
生产者 ──数据──> 消费者         生产者 <──请求── 消费者
  │                              │
  ├── 主动发送                    ├── 按需请求
  ├── 低延迟（数据就绪即发送）     ├── 消费者控制速率
  ├── 需要背压机制                 ├── 天然背压
  └── 例: mpsc::send             └── 例: Stream::poll_next

混合模型（Push-Pull）:
  事件（Event）: Push → 主动通知
  信号（Signal）: Pull → 按需采样
  例: tokio::select! {
      event = rx.recv() => { /* Push: 事件到达 */ }
      tick = interval.tick() => { /* Pull: 定时采样 */ }
  }
```

> **来源**: [来源: [Tokio Internals](https://tokio.rs/tokio/topics/internals)]

### 6.2 与 Rust Stream 的对应
>

```text
Rust Stream = Pull-based 的数据流抽象

数据流编程在 Rust 中的映射:
  数据流节点    →   async fn / Stream
  数据流边      →   mpsc::channel / Stream adapter
  节点计算      →   map/filter/then 组合子
  数据流调度    →   Tokio runtime / async executor

声明式 vs 命令式:
  声明式: events.map(f).filter(g).merge(other).collect()
          → 定义 "什么" 而非 "如何"
  命令式: while let Some(e) = rx.recv().await { ... }
          → 显式控制流
```

> **来源**: [Tokio Stream](https://docs.rs/tokio-stream/latest/tokio_stream/) · [futures-rs](https://docs.rs/futures/latest/futures/stream/index.html)

---

## 七、Rust 实现

> **来源**: [async-stream](https://docs.rs/async-stream/latest/async_stream/) · [futures-rs Stream](https://docs.rs/futures/latest/futures/stream/trait.Stream.html)

### 7.1 tokio-stream
>

```rust
use tokio_stream::{self, StreamExt};
use tokio::time::{interval, Duration};

// tokio-stream 提供的实用 Stream

// 1. 定时器 Stream
let mut ticker = interval(Duration::from_secs(1));
let tick_stream = tokio_stream::wrappers::IntervalStream::new(interval(Duration::from_secs(1)));

// 2. 异步迭代器转 Stream
let async_iter = async_stream::stream! {
    for i in 0..10 {
        yield i;
    }
};

// 3. Channel 转 Stream
let (tx, rx) = tokio::sync::mpsc::channel::<i32>(10);
let stream = tokio_stream::wrappers::ReceiverStream::new(rx);

// 4. 组合子管道
let pipeline = stream
    .filter(|x| *x > 0)
    .map(|x| x * 2)
    .take(100)
    .timeout(Duration::from_secs(5));  // tokio-stream 扩展
```

> **来源**: [来源: [tokio-stream](https://docs.rs/tokio-stream/latest/tokio_stream/)]

### 7.2 async-stream
>

```rust
use async_stream::stream;
use futures_util::pin_mut;
use futures_util::stream::StreamExt;

// async-stream: 用 async/await 语法生成 Stream
let st = stream! {
    for i in 0..3 {
        yield i;
    }
};

pin_mut!(st);
while let Some(value) = st.next().await {
    println!("got {}", value);
}

// 更复杂的场景：从异步源生成 Stream
let network_stream = stream! {
    let mut page = 1;
    loop {
        match fetch_page(page).await {
            Ok(items) if !items.is_empty() => {
                for item in items {
                    yield item;
                }
                page += 1;
            }
            _ => break,
        }
    }
};
```

> **来源**: [来源: [async-stream](https://docs.rs/async-stream/latest/async_stream/)]

### 7.3 完整数据流处理骨架
>

```rust
use tokio::sync::mpsc;
use futures::stream::{self, StreamExt};
use std::time::Duration;

// 完整的数据流处理管道：日志收集 → 解析 → 过滤 → 聚合 → 存储

struct LogEntry {
    timestamp: chrono::DateTime<chrono::Utc>,
    level: LogLevel,
    message: String,
    service: String,
}

#[derive(Clone, Copy)]
enum LogLevel { Debug, Info, Warn, Error }

async fn log_processing_pipeline() {
    // 1. 数据源：多个服务的日志流
    let (error_tx, error_rx) = mpsc::channel::<LogEntry>(1000);
    let (metric_tx, metric_rx) = mpsc::channel::<LogEntry>(1000);

    // 2. 错误日志处理管道
    let error_pipeline = tokio_stream::wrappers::ReceiverStream::new(error_rx)
        .filter(|log| matches!(log.level, LogLevel::Error))
        .map(|log| async move {
            // 发送告警
            send_alert(&log).await;
            log
        })
        .buffer_unordered(10)
        .fold(0, |count, _| async move { count + 1 });

    // 3. 指标聚合管道
    let metric_pipeline = tokio_stream::wrappers::ReceiverStream::new(metric_rx)
        .filter(|log| !matches!(log.level, LogLevel::Debug))
        .then(|log| async move {
            let key = format!("{}/{:?}", log.service, log.level);
            (key, 1u64)
        })
        .fold(
            std::collections::HashMap::<String, u64>::new(),
            |mut acc, (key, count)| async move {
                *acc.entry(key).or_insert(0) += count;
                acc
            },
        );

    // 4. 并行运行两个管道
    let (error_count, metrics) = tokio::join!(error_pipeline, metric_pipeline);

    println!("Total errors: {}", error_count);
    println!("Metrics: {:?}", metrics);
}

async fn send_alert(log: &LogEntry) -> Result<(), AlertError> {
    // 发送告警通知...
    Ok(())
}
```

> **来源**: [tokio-stream](https://docs.rs/tokio-stream/latest/tokio_stream/) ·
> [async-stream](https://docs.rs/async-stream/latest/async_stream/) ·
> [futures-rs](https://docs.rs/futures/latest/futures/stream/index.html)

---

## 八、反命题与边界

### 8.1 反命题树
>

```text
反命题 1: "Reactive Streams 比 Rust Stream trait 更先进"
├── 前提: Push-Pull 混合模型优于纯 Pull 模型
├── 反驳:
│   ├── Rust Stream 的 Pull 模型天然提供背压（不 poll 不生产）
│   ├── Reactive Streams 的 Push 模型需要显式 request(n) 背压 → 协议复杂
│   ├── Rust Stream 与 async/await 语义无缝集成
│   └── Reactive Streams 是 JVM 生态规范，Rust 有更原生的抽象
└── 根结论: ❌ 各有适用场景。Rust Stream 更适合 Rust 的所有权+异步模型。

反命题 2: "FRP 可以完全替代命令式事件处理"
├── 前提: FRP 的声明式组合优于显式循环
├── 反驳:
│   ├── FRP 的 Signal 网络在 Rust 中需要 Arc<Mutex<T>> → 运行时开销
│   ├── 复杂控制流（如 break/continue/early return）在 FRP 中表达困难
│   ├── 调试困难：信号网络的执行顺序不透明
│   └── Rust 的所有权模型与 FRP 的共享可变信号存在根本张力
└── 根结论: ❌ FRP 适合 UI/数据流场景，但不适合通用编程。Rust 中 Stream + async/await 是更实用的折中。

反命题 3: "无界 channel 在高吞吐场景下性能更好"
├── 前提: 不阻塞生产者 → 最大吞吐
├── 反驳:
│   ├── 无界 channel = 内存泄漏风险（生产者快于消费者时无限增长）
│   ├── 内存分配开销随队列增长而增加
│   ├── 缓存失效（cache miss）随队列长度增加
│   └── "性能更好"只在消费者能追上的短暂窗口成立
└── 根结论: ❌ 无界 channel 是反模式。生产环境应始终使用有界 channel + 背压策略。
```

> **来源**: [来源: [Reactive Streams Spec](https://www.reactive-streams.org/)]

### 8.2 边界极限
>

| **边界** | **现状** | **理论极限** | **工程影响** |
|:---|:---|:---|:---|
| **Stream 组合子嵌套深度** | 通常 < 10 层 | 过深导致编译时间指数增长 | 拆分管道为多个阶段 |
| **并发 buffer_unordered** | tokio 默认 | 超过 CPU 核心数无收益 | 与 CPU 核心数对齐 |
| **FRP 信号网络规模** | 数十个信号 | 大规模网络（> 1000）调度复杂 | Rust 无成熟 FRP 框架 |
| **背压延迟** | 阻塞/缓冲引入 | 无法为零（物理限制）| 选择适合业务的策略 |
| **跨线程 Stream** | 需要 Send + Sync | 自引用 Stream 不能跨线程 | 使用 channel 解耦 |

> **来源**: [Reactive Streams Spec](https://www.reactive-streams.org/) ·
> [Elliott 2009](https://conal.net/papers/push-pull-frp/push-pull-frp.pdf) ·
> [Tokio Internals](https://tokio.rs/tokio/topics/internals)

---

## 九、边界测试

### 9.1 边界测试：无背压导致内存溢出（运行时错误）

```rust,ignore
// ❌ 错误：无界 channel 导致内存无限增长
use tokio::sync::mpsc;

async fn unbounded_channel_oom() {
    // 无界 channel：无背压，内存无限增长
    let (tx, mut rx) = mpsc::unbounded_channel::<Vec<u8>>();

    tokio::spawn(async move {
        loop {
            // 生产者：每秒产生 100MB 数据
            let data = vec![0u8; 100_000_000];  // 100MB
            tx.send(data).unwrap();  // 永不阻塞！
        }
    });

    // 消费者：每秒处理 1MB
    while let Some(data) = rx.recv().await {
        tokio::time::sleep(Duration::from_secs(100)).await;
        drop(data);
    }
    // 结果: 内存以 ~99MB/s 的速度增长 → OOM killed
}
```

> **修正**: 始终使用**有界 channel**：
>
> ```rust
> let (tx, mut rx) = mpsc::channel::<Vec<u8>>(10);  // 最多缓冲 10 条
> tx.send(data).await.unwrap();  // 满时阻塞 → 背压传递给上游
> ```
>
> **来源**: [Tokio mpsc](https://docs.rs/tokio/latest/tokio/sync/mpsc/index.html) ·
> [Reactive Streams — Backpressure](https://www.reactive-streams.org/)

### 9.2 边界测试：跨线程 Stream 发送违反 Send（编译错误）

```rust,compile_fail
// ❌ 错误：包含非 Send 类型的 Stream 不能跨线程
use std::rc::Rc;
use futures::stream::{self, StreamExt};

fn bad_stream_send() {
    let local = Rc::new(42);  // Rc 不是 Send！
    let st = stream::iter(0..10).map(move |x| x + *local);

    // ❌ 编译错误: `Rc<i32>` cannot be sent between threads safely
    tokio::spawn(async move {
        let _: Vec<_> = st.collect().await;
    });
}

// ✅ 修正: 使用 Arc 替代 Rc
use std::sync::Arc;

fn good_stream_send() {
    let shared = Arc::new(42);  // Arc 是 Send + Sync
    let st = stream::iter(0..10).map(move |x| x + *shared);

    tokio::spawn(async move {
        let _: Vec<_> = st.collect().await;
    });
}
```

> **来源**: [Rust Send/Sync](https://doc.rust-lang.org/std/marker/trait.Send.html) ·
> [futures-rs Stream](https://docs.rs/futures/latest/futures/stream/trait.Stream.html)

### 9.3 边界测试：FRP 信号循环引用导致死锁（运行时错误）

```rust,ignore
// ❌ 错误：FRP 信号网络中的循环依赖导致死锁
use std::sync::{Arc, Mutex};

struct Signal<T> {
    value: Arc<Mutex<T>>,
    compute: Box<dyn Fn() -> T + Send>,
}

impl<T: Clone + Default + Send + 'static> Signal<T> {
    fn new<F: Fn() -> T + Send + 'static>(f: F) -> Self {
        Self {
            value: Arc::new(Mutex::new(T::default())),
            compute: Box::new(f),
        }
    }

    fn get(&self) -> T {
        let val = (self.compute)();
        *self.value.lock().unwrap() = val.clone();
        val
    }
}

fn circular_signal_deadlock() {
    // 创建两个相互依赖的信号
    let a: Arc<Mutex<Option<Signal<i32>>>> = Arc::new(Mutex::new(None));
    let b: Arc<Mutex<Option<Signal<i32>>>> = Arc::new(Mutex::new(None));

    let a_clone = a.clone();
    let b_clone = b.clone();

    // a = b + 1
    *a.lock().unwrap() = Some(Signal::new(move || {
        let b_sig = b_clone.lock().unwrap();
        b_sig.as_ref().unwrap().get() + 1  // ⚠️ 获取 b 时，b 可能正在获取 a
    }));

    // b = a * 2
    *b.lock().unwrap() = Some(Signal::new(move || {
        let a_sig = a_clone.lock().unwrap();
        a_sig.as_ref().unwrap().get() * 2  // ⚠️ 循环依赖！死锁！
    }));

    // a.get() → 需要 b → b.get() → 需要 a → 死锁！
    // println!("{}", a.lock().unwrap().as_ref().unwrap().get());
}
```

> **修正**: FRP 信号网络必须是无环 DAG（有向无环图）。如果需要循环反馈，应使用：
>
> 1. **延迟节点**（Delay node）：引入一个时间步的延迟，打破即时循环
> 2. **事件驱动更新**：用 Event 触发更新，而非 Signal 的自动传播
> 3. **显式状态管理**：用 `Arc<Atomic*>` 或 channel 替代自动信号传播
>
> **来源**: [Elliott & Hudak 1997](https://haskell.cs.yale.edu/wp-content/uploads/2011/02/frp.pdf) ·
> [FRP Cyclic Dependencies](https://wiki.haskell.org/Functional_Reactive_Programming)

---

> **补充来源索引**: [来源: [Reactive Streams JVM](https://github.com/reactive-streams/reactive-streams-jvm)] · [来源: [Tokio broadcast](https://docs.rs/tokio/latest/tokio/sync/broadcast/index.html)]

> **来源**: [futures-rs Stream](https://docs.rs/futures/latest/futures/stream/trait.Stream.html)
> **来源**: [Tokio mpsc](https://docs.rs/tokio/latest/tokio/sync/mpsc/index.html)

## 相关概念文件

- [事件驱动架构](./32_event_driven_architecture.md) — 发布-订阅、消息队列、Reactive Streams
- [CQRS & Event Sourcing](./33_cqrs_event_sourcing.md) — 事件流、投影处理器
- [流处理生态](./36_stream_processing_ecosystem.md) — timely/differential dataflow、Materialize
- [架构设计模式](./35_architecture_patterns.md) — 分层/六边形/洋葱/整洁架构
- [Stream Processing Semantics](../03_advanced/20_stream_processing_semantics.md) — 流处理语义学
- [Async/Await](../03_advanced/02_async.md) — 异步编程基础
- [并发编程](../03_advanced/01_concurrency.md) — Send/Sync、线程安全
- [范型矩阵](../05_comparative/03_paradigm_matrix.md) — 多语言范式对比
