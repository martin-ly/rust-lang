> **内容分级**: [专家级]

# 并行与分布式模式谱系：从线程池到共识算法
>
> **EN**: Parallel Distributed Pattern Spectrum
> **Summary**: Parallel Distributed Pattern Spectrum: advanced Rust topics, performance/runtime considerations, and ecosystem patterns.
> **受众**: [专家]
> **层级**: L3 高级概念 — 并发/分布式系统设计
> **A/S/P 标记**: **S+A** — Structure + Application
> **双维定位**: C×Ana — 分析并行与分布式模式的演进谱系与统一框架
> **前置概念**:
> [Concurrency](./01_concurrency.md) ·
> [Async](./02_async.md) ·
> [Lock-free](../03_advanced/16_lock_free.md) ·
> [Distributed Systems](../06_ecosystem/18_distributed_systems.md)
> **后置概念**:
> [Pattern Composition Algebra](../06_ecosystem/35_pattern_composition_algebra.md) ·
> [System Design Principles](../06_ecosystem/05_system_design_principles.md)
> **主要来源**:
> [Herlihy & Shavit — The Art of Multiprocessor Programming] ·
> [Lynch — Distributed Algorithms] · [Tanenbaum — Distributed Systems] ·
> [Amazon Science — Must Framework] ·
> [Rust Atomics and Locks](https://marabos.nl/atomics/)
>
> **来源**: [std::thread](https://doc.rust-lang.org/std/thread/) · [Rayon Docs](https://docs.rs/rayon/) · [TRPL — Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)
---

> **Bloom 层级**: 分析 → 评价 → 创造

> **对应 Crate**: [`c05_threads`](../../crates/c05_threads/)
> **对应练习**: [`exercises/src/concurrency/`](../../exercises/src/concurrency/)

## 📑 目录

- [并行与分布式模式谱系：从线程池到共识算法](#并行与分布式模式谱系从线程池到共识算法)
  - [📑 目录](#-目录)
  - [一、核心命题](#一核心命题)
  - [二、并行/分布式模式的统一谱系](#二并行分布式模式的统一谱系)
    - [2.1 谱系总览](#21-谱系总览)
    - [2.2 统一分析框架](#22-统一分析框架)
  - [三、L1 单机共享内存模式](#三l1-单机共享内存模式)
    - [3.1 线程池模式](#31-线程池模式)
    - [3.2 Fork-Join 模式](#32-fork-join-模式)
    - [3.3 无锁数据结构](#33-无锁数据结构)
  - [四、L2 单机消息传递模式](#四l2-单机消息传递模式)
    - [4.1 Actor 模型](#41-actor-模型)
    - [4.2 CSP（Communicating Sequential Processes）](#42-cspcommunicating-sequential-processes)
    - [4.3 数据流与背压（Backpressure）](#43-数据流与背压backpressure)
  - [五、L3 多机分布式模式](#五l3-多机分布式模式)
    - [5.1 共识算法：Raft](#51-共识算法raft)
    - [5.2 Gossip 协议](#52-gossip-协议)
    - [5.3 CRDT（Conflict-free Replicated Data Types）](#53-crdtconflict-free-replicated-data-types)
  - [六、模式谱系的统一理论视角](#六模式谱系的统一理论视角)
    - [6.1 从并发到分布式的统一连续体](#61-从并发到分布式的统一连续体)
    - [6.2 一致性谱系](#62-一致性谱系)
  - [七、Rust 生态的并发/分布式工具谱系](#七rust-生态的并发分布式工具谱系)
  - [八、反例与边界测试](#八反例与边界测试)
    - [8.1 反例：在 Actor 中使用共享可变状态](#81-反例在-actor-中使用共享可变状态)
    - [8.2 边界测试：`!Send` 类型跨线程（编译错误）](#82-边界测试send-类型跨线程编译错误)
    - [8.3 边界测试：Raft 在网络分区下的行为](#83-边界测试raft-在网络分区下的行为)
    - [8.3 边界测试：CRDT 的合并顺序独立性](#83-边界测试crdt-的合并顺序独立性)
  - [九、知识来源关系](#九知识来源关系)
  - [十、边界测试：并行与分布式模式的编译错误](#十边界测试并行与分布式模式的编译错误)
    - [10.1 边界测试：`rayon::join` 闭包返回值生命周期（编译错误）](#101-边界测试rayonjoin-闭包返回值生命周期编译错误)
    - [10.2 边界测试：分布式 Actor 的消息类型未实现 `Serialize`（编译错误）](#102-边界测试分布式-actor-的消息类型未实现-serialize编译错误)
    - [10.3 边界测试：`rayon` 的线程池饥饿与任务粒度（运行时性能下降）](#103-边界测试rayon-的线程池饥饿与任务粒度运行时性能下降)
    - [10.4 边界测试：rayon 的并行迭代与顺序依赖（运行时逻辑错误）](#104-边界测试rayon-的并行迭代与顺序依赖运行时逻辑错误)
    - [10.8 边界测试：生命周期参数的不匹配返回](#108-边界测试生命周期参数的不匹配返回)
  - [逆向推理链（Backward Reasoning）](#逆向推理链backward-reasoning)
  - [参考来源](#参考来源)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：`std::thread::spawn` 与 `tokio::spawn` 创建的"任务"有什么本质区别？（理解层）](#测验-1stdthreadspawn-与-tokiospawn-创建的任务有什么本质区别理解层)
    - [测验 2：Rayon 的 `par_iter()` 与标准库的 `iter()` 在 API 使用上有什么区别？（理解层）](#测验-2rayon-的-par_iter-与标准库的-iter-在-api-使用上有什么区别理解层)
    - [测验 3：Actor 模型在 Rust 中的典型实现方式是什么？（理解层）](#测验-3actor-模型在-rust-中的典型实现方式是什么理解层)
    - [测验 4：分布式系统中，Rust 的 Serde + 强类型系统在消息序列化上有什么优势？（理解层）](#测验-4分布式系统中rust-的-serde--强类型系统在消息序列化上有什么优势理解层)
    - [测验 5：`crossbeam::channel` 与 `std::sync::mpsc` 的主要改进是什么？（理解层）](#测验-5crossbeamchannel-与-stdsyncmpsc-的主要改进是什么理解层)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)
  - [实践](#实践)
    - [对应代码示例](#对应代码示例)
    - [建议练习](#建议练习)
  - [导航：下一步去哪？](#导航下一步去哪)

## 一、核心命题

> **并行与分布式模式不是孤立的技巧集合，而是一个从"共享内存线程协作"到"广域网共识达成"的连续谱系。
> 理解这一谱系的统一结构——从 Fork-Join 到 Actor 到 CSP 到数据流再到分布式共识——是设计高性能、高可用系统的必要认知框架。**

---

## 二、并行/分布式模式的统一谱系

### 2.1 谱系总览

```text
并行/分布式模式谱系:

L1: 单机共享内存
├── 线程池（Thread Pool）
├── Fork-Join（分治并行）
├── 锁与条件变量（Mutex / Condvar）
├── 读写锁（RwLock）
└── 无锁数据结构（Lock-free）

L2: 单机消息传递
├── Actor 模型（Actix / akka）
├── CSP 通道（Channel / goroutine）
├── 数据流（Dataflow / rayon）
└── 响应式流（Reactive Streams / backpressure）

L3: 多机分布式
├── 主从复制（Master-Slave Replication）
├── 分片（Sharding / Partitioning）
├── 共识算法（Consensus / Raft / Paxos）
├── Gossip 协议（Epidemic Broadcast）
└── CRDT（Conflict-free Replicated Data Types）

L4: 广域网/边缘
├── CDN / 边缘缓存
├── 联邦学习（Federated Learning）
└── 区块链共识（PoW / PoS / BFT）
```

### 2.2 统一分析框架

所有并行/分布式模式都可以通过四个维度分析：

| 维度 | 说明 | 线程池 | Actor | Raft | CRDT |
|:---|:---|:---|:---|:---|:---|
| **通信模型** | 如何交换信息 | 共享内存 | 消息传递 | RPC + 日志复制 | 操作传播 |
| **同步机制** | 如何协调执行 | 锁 / 原子操作（Atomic Operations） | 邮箱顺序 | Leader 选举 + 日志 | 无同步（最终一致） |
| **故障模型** | 假设何种故障 | 崩溃停止 | 崩溃停止 | 崩溃停止 / 拜占庭 | 网络分区 |
| **一致性模型** | 保证何种一致性 | 顺序一致 | 单 Actor 顺序 | 线性一致 | 最终一致 |

---

## 三、L1 单机共享内存模式

### 3.1 线程池模式

```rust
use rayon::ThreadPoolBuilder;

// 线程池: 固定数量的工作线程 + 任务队列
let pool = ThreadPoolBuilder::new()
    .num_threads(4)
    .build()
    .unwrap();

pool.spawn(|| {
    println!("Task executed on worker thread");
});
```

**核心设计**: 避免线程创建/销毁的开销，复用固定数量的工作线程。

**与进程池的对比**:

| 维度 | 线程池 | 进程池 |
|:---|:---|:---|
| 内存共享 | 共享地址空间 | 隔离地址空间 |
| 通信开销 | 低（直接访问内存） | 高（IPC） |
| 容错 | 一个线程崩溃可能拖垮整个进程 | 一个进程崩溃不影响其他进程 |
| GIL 问题 | 无（Rust 无 GIL） | 无 |
| 适用场景 | CPU 密集型 | IO 密集型 / 需要隔离的场景 |

### 3.2 Fork-Join 模式

```rust
use rayon::prelude::*;

// Fork-Join: 递归分解任务，并行执行子任务，合并结果
fn parallel_sum(data: &[i32]) -> i32 {
    if data.len() <= 1000 {
        return data.iter().sum(); // 基例: 串行
    }

    let mid = data.len() / 2;
    let (left, right) = data.split_at(mid);

    let (sum_left, sum_right) = rayon::join(
        || parallel_sum(left),
        || parallel_sum(right),
    );

    sum_left + sum_right
}

// 更简洁: rayon 的并行迭代器
fn parallel_sum_v2(data: &[i32]) -> i32 {
    data.par_iter().sum()
}
```

**与算法层的联系**: Fork-Join 是**分治算法**的并行实现。见 [语义桥 — 分治 ↔ Composite ↔ Parallel Split](../00_meta/semantic_bridge_algorithms_patterns.md)。

### 3.3 无锁数据结构

```rust
use crossbeam::queue::ArrayQueue;

// Michael-Scott 无锁队列（FIFO）
let queue = ArrayQueue::new(100);

// 多生产者多消费者，无锁操作
queue.push(42).unwrap();
let value = queue.pop();
```

**锁 vs 无锁的决策树**:

```text
需要并发数据结构？
├── 读多写少？ → RwLock（读并发，写独占）
├── 写操作简单（单个 CAS）？ → Lock-free（无阻塞，高吞吐）
├── 需要阻塞等待？ → Mutex + Condvar
└── 需要等待-free 保证？ → Wait-free（ hardest to implement）
```

---

## 四、L2 单机消息传递模式

### 4.1 Actor 模型

```rust,ignore
use actix::prelude::*;

// Actor: 封装状态 + 邮箱 + 消息处理
struct Counter {
    count: usize,
}

impl Actor for Counter {
    type Context = Context<Self>;
}

// 消息定义
struct Increment;
impl Message for Increment {
    type Result = usize;
}

// 消息处理
impl Handler<Increment> for Counter {
    fn handle(&mut self, _msg: Increment, _ctx: &mut Context<Self>) -> usize {
        self.count += 1;
        self.count
    }
}
```

**Actor 模型的核心原则**:

1. **封装**: Actor 的状态不共享，只能通过消息访问
2. **异步（Async）**: 消息发送非阻塞，Actor 按顺序处理邮箱中的消息
3. **容错**: Actor 崩溃不影响其他 Actor（监督树机制）

**与共享内存的对比**:

| 维度 | 共享内存 + 锁 | Actor 模型 |
|:---|:---|:---|
| 状态共享 | 显式共享，需要同步 | 不共享，通过消息传递 |
| 死锁 | 可能 | **不可能**（无共享状态） |
| 数据竞争 | 可能（需正确使用锁） | **不可能**（单线程处理） |
| 性能 | 低延迟（直接内存访问） | 较高延迟（消息序列化） |
| 扩展性 | 单机 | 天然分布式 |

### 4.2 CSP（Communicating Sequential Processes）

```rust
use std::sync::mpsc;
use std::thread;

// CSP: 通过通道通信的并发进程
let (tx, rx) = mpsc::channel::<i32>();

thread::spawn(move || {
    for i in 0..10 {
        tx.send(i * i).unwrap(); // 发送消息
    }
});

for received in rx { // 接收消息
    println!("Got: {}", received);
}
```

**CSP 的核心原则**:

1. **不要通过共享内存通信；通过通信共享内存**
2. 通道是同步或异步的消息队列
3. 发送和接收是显式操作

**Actor vs CSP 对比**:

| 维度 | Actor | CSP |
|:---|:---|:---|
| 通信方式 | 直接发送到 Actor 邮箱（命名目标） | 发送到通道（匿名目标） |
| 耦合度 | Actor 知道接收者 | 发送者不知道接收者 |
| 消息顺序 | 每个 Actor 内部有序 | 通道内有序 |
| 典型实现 | Actix、Erlang、Akka | Go、Rust channels、Occam |

### 4.3 数据流与背压（Backpressure）

```rust
use tokio::sync::mpsc;

// 有界通道: 背压机制 —— 发送者阻塞/等待当缓冲区满
let (tx, mut rx) = mpsc::channel::<i32>(100); // 容量 100

// 生产者
 tokio::spawn(async move {
    for i in 0..1000 {
        tx.send(i).await.unwrap(); // 当通道满时，await 阻塞
    }
});

// 消费者
while let Some(value) = rx.recv().await {
    process(value).await;
}
```

**背压的必要性**: 无背压的系统在快生产者 + 慢消费者场景下会导致内存耗尽。

---

## 五、L3 多机分布式模式

### 5.1 共识算法：Raft

```rust,ignore
// Raft 的核心状态机（简化概念模型）
enum NodeState {
    Follower { leader_id: Option<NodeId> },
    Candidate { votes_received: usize },
    Leader { next_index: HashMap<NodeId, usize> },
}

// Raft 保证的性质:
// 1. Election Safety: 每个任期最多一个 Leader
// 2. Leader Append-Only: Leader 从不覆盖/删除日志条目
// 3. Log Matching: 若两个日志条目索引和任期相同，则内容相同
// 4. Leader Completeness: 已提交的条目存在于所有未来 Leader 的日志中
// 5. State Machine Safety: 若节点应用了某索引的日志，则所有节点应用的该索引内容相同
```

**CAP 定理与 Raft 的定位**:

Raft 是 **CP 系统**（Consistency + Partition tolerance，牺牲 Availability）：

- 网络分区时，少数派节点不可用（不响应读写请求）
- 保证强一致性（线性一致性）

### 5.2 Gossip 协议

Gossip 协议是 **AP 系统**（Availability + Partition tolerance，牺牲 Consistency）：

```text
Gossip 传播模型:
  每个节点周期性地随机选择 k 个邻居，交换状态信息
  传播速度: O(log N) 轮覆盖全网（类似传染病模型）

  类型:
    - Anti-entropy: 全量同步，修复不一致
    - Rumor-mongering: 增量传播，新信息像谣言一样扩散
```

**与 Raft 的对比**:

| 维度 | Raft | Gossip |
|:---|:---|:---|
| 一致性 | 强一致（线性一致） | 最终一致 |
| 可用性 | 分区时不可用 | 始终可用 |
| 节点数 | 3-7 个（小集群） | 100-10000 个（大规模） |
| 收敛速度 | 立即（Leader 写入即提交） | O(log N) 轮 |
| 适用场景 | 配置管理、元数据存储 | 成员发现、状态传播、缓存失效 |

### 5.3 CRDT（Conflict-free Replicated Data Types）

> **[来源: Shapiro et al. 2011 — A Comprehensive Study of Convergent and Commutative Replicated Data Types] · [Rust crdt crate] · [Wikipedia: CRDT](https://en.wikipedia.org/wiki/Conflict-free_replicated_data_type)** ✅

CRDT 是**无需同步**即可保证最终一致性的数据结构：

```rust,ignore
// G-Counter（Grow-only Counter）: 单调递增的分布式计数器
use crdt::GCounter;

let mut counter_a = GCounter::new();
let mut counter_b = GCounter::new();

counter_a.increment("node_a", 5);
counter_b.increment("node_b", 3);

// 合并: 取每个节点的最大值
counter_a.merge(&counter_b);
assert_eq!(counter_a.value(), 8); // 5 + 3
```

**CRDT 的数学基础**:

```text
CRDT 必须满足:
  1. 交换律（Commutativity）: A ⊔ B = B ⊔ A
  2. 结合律（Associativity）: (A ⊔ B) ⊔ C = A ⊔ (B ⊔ C)
  3. 幂等律（Idempotence）: A ⊔ A = A

∴ CRDT 的合并操作构成一个**联结半格（Join Semilattice）**
```

> **定理** [Tier 2]: 若两个 CRDT 副本独立演化后合并，其结果等价于它们所有更新按某种顺序顺序应用的结果。
>
> **来源**: [Shapiro et al., 2011] ✅

---

## 六、模式谱系的统一理论视角

### 6.1 从并发到分布式的统一连续体

并行与分布式计算的区别不是二元的，而是连续谱系：

```text
并发连续体:

共享内存 ──────────────────────────────────────── 消息传递
  │                                                  │
  ├── 同一进程的多线程（std::thread）                  ├── 同一机器的多进程（IPC）
  ├── NUMA 架构（非均匀内存访问）                      ├── 同一数据中心的 RPC
  ├── 分布式共享内存（DSM）                           ├── 广域网的 REST/gRPC
  └── "分布式系统就是网络延迟足够高的并行系统"         └── "并行系统就是网络延迟足够低的分布式系统"
```

### 6.2 一致性谱系

```text
一致性强度谱系（从强到弱）:

线性一致性（Linearizability）
  └── 顺序一致性（Sequential Consistency）
        └── 因果一致性（Causal Consistency）
              └── 会话一致性（Session Consistency）
                    └── 最终一致性（Eventual Consistency）
                          └── 弱一致性（Weak Consistency）

Rust 生态映射:
  - 线性一致: `std::sync::atomic` (SeqCst), Raft
  - 顺序一致: `Mutex`, `RwLock`
  - 因果一致: Vector Clock, Lamport Clock
  - 最终一致: Gossip, CRDT
```

---

## 七、Rust 生态的并发/分布式工具谱系

| 层级 | 工具/Crate | 模式 | 一致性 | 适用场景 |
|:---|:---|:---|:---:|:---|
| **L1 共享内存** | `std::sync` | Mutex/RwLock/Condvar | 顺序一致 | 简单并发 |
| | `parking_lot` | 优化的锁 | 顺序一致 | 高性能锁 |
| | `crossbeam` | Lock-free / Epoch GC | 顺序一致 | 无锁数据结构 |
| | `rayon` | Fork-Join / Work Stealing | 顺序一致 | 数据并行 |
| **L2 消息传递** | `std::sync::mpsc` | CSP Channel | 顺序一致 | 线程间通信 |
| | `tokio::sync::mpsc` | Async CSP | 顺序一致 | 异步通信 |
| | `actix` | Actor | Actor 内部顺序 | 并发服务 |
| | `futures::Stream` | 数据流 / 背压 | 顺序一致 | 流处理 |
| **L2.5 流处理** | `tokio-stream` | 异步流组合子 | 处理时间语义 | 异步应用流管道 |
| | `timely-dataflow` | 分布式数据流图 | 逻辑时间戳 | 流引擎构建 |
| | `differential-dataflow` | 增量 diff 代数 | 严格串行化 | 增量查询引擎 |
| | `fluvio` | 分布式流平台 | 至少一次 | Kafka 替代 |
| **L3 分布式** | `tikv/raft-rs` | Raft 共识 | 线性一致 | 分布式 KV |
| | `libp2p` | Gossip / Kademlia | 最终一致 | P2P 网络 |
| | `crdt` crate | CRDT | 最终一致 | 协同编辑 |
| | `tonic` | gRPC | 依赖后端 | 微服务通信 |

---

## 八、反例与边界测试

### 8.1 反例：在 Actor 中使用共享可变状态

```rust,compile_fail
// 错误: Actor 内部使用共享可变状态，破坏 Actor 模型的保证
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

struct BadActor {
    shared: Arc<AtomicUsize>, // ❌ 与其他 Actor 共享可变状态
}

impl Actor for BadActor {
    type Context = Context<Self>;
}

impl Handler<Message> for BadActor {
    fn handle(&mut self, _msg: Message, _ctx: &mut Context<Self>) {
        self.shared.fetch_add(1, Ordering::Relaxed); // 数据竞争！
    }
}
```

> **修正**: Actor 的状态应完全封装，不共享。

### 8.2 边界测试：`!Send` 类型跨线程（编译错误）

```rust,compile_fail
use std::rc::Rc;
use std::thread;

fn main() {
    let data = Rc::new(42);
    // ❌ 编译错误: `Rc<i32>` cannot be sent between threads safely
    // Rc 不是 Send，因为它使用非原子引用计数
    thread::spawn(move || {
        println!("{}", *data);
    });
}
```

> **修正**: 使用 `Arc<T>`（原子引用计数）替代 `Rc<T>`，即可安全跨线程共享。

```rust
use std::sync::Arc;
use std::thread;

fn main() {
    let data = Arc::new(42);
    thread::spawn(move || {
        println!("{}", *data); // ✅ Arc<i32> 是 Send + Sync
    });
}
```

### 8.3 边界测试：Raft 在网络分区下的行为

```text
场景: 5 节点 Raft 集群，网络分区为 [A,B] 和 [C,D,E]

[A,B] 分区:
  - 只有 2 个节点，无法选举 Leader（需要 3 票）
  - 读写请求被拒绝（保证一致性）

[C,D,E] 分区:
  - 3 个节点，可以选举 Leader
  - 正常处理读写请求

分区恢复后:
  - [A,B] 节点的日志落后于 [C,D,E]
  - Leader 向 [A,B] 复制缺失的日志条目
  - 所有节点最终达成一致
```

### 8.3 边界测试：CRDT 的合并顺序独立性

```rust,ignore
use crdt::GCounter;

fn crdt_commutativity() {
    let mut a = GCounter::new();
    let mut b = GCounter::new();

    a.increment("x", 5);
    b.increment("y", 3);

    let mut ab = a.clone();
    ab.merge(&b); // a ⊔ b

    let mut ba = b.clone();
    ba.merge(&a); // b ⊔ a

    assert_eq!(ab.value(), ba.value()); // ✅ 交换律保证
}
```

---

## 九、知识来源关系

| **论断** | **来源** | **可信度** | **Tier** |
|:---|:---|:---:|:---:|
| Actor 模型 | [Hewitt et al. 1973] | ✅ | Tier 1 |
| CSP | [Hoare 1978](https://en.wikipedia.org/wiki/Communicating_sequential_processes) | ✅ | Tier 1 |
| Raft 算法 | [Ongaro & Ousterhout 2014] | ✅ | Tier 1 |
| CAP 定理 | [Brewer 2000] · [Gilbert & Lynch 2002] | ✅ | Tier 1 |
| CRDT 理论 | [Shapiro et al. 2011] | ✅ | Tier 1 |
| Gossip 协议 | [Demers et al. 1987] | ✅ | Tier 1 |
| 并发连续体 | [Lynch, §1.2] · [💡 原创分析] | ✅/💡 | Tier 2 |
| Rust 生态工具谱系 | [💡 原创分析] | ⚠️ | Tier 3 |

---

> **权威来源**:
> [Herlihy & Shavit — The Art of Multiprocessor Programming](https://www.cs.brown.edu/~mph/HerlihyShavit/) ·
> [Lynch — Distributed Algorithms](https://mitpress.mit.edu/books/distributed-algorithms) ·
> [Ongaro & Ousterhout — Raft](https://raft.github.io/raft.pdf) ·
> [Shapiro et al. — CRDT](https://hal.inria.fr/hal-00932836/document) ·
> [Rust Atomics and Locks](https://marabos.nl/atomics/)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.90.0+ (Edition 2024)
> **最后更新**: 2026-05-24
> **状态**: ✅ 新建 — 表征空间坐标系

## 十、边界测试：并行与分布式模式的编译错误

### 10.1 边界测试：`rayon::join` 闭包返回值生命周期（编译错误）

```rust,compile_fail
use rayon::join;

fn parallel_bad() {
    let data = vec![1, 2, 3];
    let r = &data;
    // ❌ 编译错误: `r` 的生命周期不够长
    // join 的两个闭包可能在不同线程执行，引用栈数据不安全
    join(
        || println!("{}", r[0]),
        || println!("{}", r[1]),
    );
}

// 正确: 使用所有权转移
fn parallel_fixed() {
    let data = vec![1, 2, 3];
    join(
        move || println!("{}", data[0]), // ✅ 所有权移入闭包
        move || println!("{}", data[1]), // ❌ 编译错误: data 被 move 两次
    );
}

// 正确: 使用 Arc
use std::sync::Arc;

fn parallel_arc() {
    let data = Arc::new(vec![1, 2, 3]);
    let data2 = Arc::clone(&data);
    join(
        move || println!("{}", data[0]),  // ✅ Arc 可 Clone
        move || println!("{}", data2[1]), // ✅ 两个独立的 Arc
    );
}
```

> **修正**: `rayon::join` 将两个闭包并行执行（若可用），闭包必须满足 `'static` 或从环境中转移所有权。引用栈数据的闭包不能安全传递给 `join`。`rayon` 的并行迭代器（`par_iter()`）通过数据分割避免此问题——每个子闭包处理数据切片，而非共享引用。[来源: [Rayon Documentation](https://docs.rs/rayon/)]

### 10.2 边界测试：分布式 Actor 的消息类型未实现 `Serialize`（编译错误）

```rust,compile_fail
use serde::Serialize;

struct Message {
    data: String,
}

// ❌ 编译错误: `Message` 未实现 `Serialize`
// 分布式 Actor 系统（如 Actix、Riker）要求消息可序列化
fn send_message<M: Serialize>(msg: M) {
    // 序列化后通过网络发送
}

fn main() {
    let msg = Message { data: "hello".to_string() };
    send_message(msg);
}

// 正确: 为 Message 实现 Serialize
#[derive(Serialize)] // ✅ serde derive
struct MessageFixed {
    data: String,
}
```

> **修正**:
> 分布式系统中的消息传递要求类型可序列化（`Serialize`/`Deserialize`）。
> Rust 的类型系统通过 trait bound 在编译期强制这一约束——未实现 `Serialize` 的类型不能作为网络消息。
> 这与 Erlang 的动态序列化或 Java 的默认 `Serializable` 不同：Rust 要求显式 opt-in（通过 derive 或手动实现），确保类型变化时序列化格式同步更新，避免版本不兼容导致的运行时错误。
> [来源: [Serde Documentation](https://serde.rs/)]

### 10.3 边界测试：`rayon` 的线程池饥饿与任务粒度（运行时性能下降）

```rust,compile_fail
use rayon::prelude::*;

fn main() {
    let v: Vec<i32> = (0..100).collect();
    // ❌ 运行时性能问题: 任务过小，线程同步开销超过并行收益
    let sum: i32 = v.par_iter()
        .map(|x| x * 2)
        .sum();
    println!("{}", sum);
}
```

> **修正**:
> `rayon` 是 Rust 的数据并行库，基于 **work-stealing** 线程池自动并行化迭代器。
> 但**任务粒度**是关键：
>
> 1) 任务太小（如 `x * 2`）→ 线程调度开销 > 并行收益；
> 2) 任务太大 → 负载不均衡，某些线程空闲。
>
> `rayon` 的启发式：通过 `join` 递归分割任务，但无法控制最小分割粒度。
>
> 优化：
>
> 1) `par_chunks` 增加每任务工作量；
> 2) `with_min_len(n)` 设置最小长度；
> 3) 只在计算密集型操作中使用 `par_iter`（I/O 密集型用 `tokio`）。
> 这与 Java 的 `ForkJoinPool`（类似 work-stealing）或 C++ 的 `std::execution::par`（C++17，类似抽象）类似——数据并行的性能取决于任务粒度，无万能配置。
> [来源: [rayon Documentation](https://docs.rs/rayon/)] · [来源: [Rust Performance Book](https://nnethercote.github.io/perf-book/)]

### 10.4 边界测试：rayon 的并行迭代与顺序依赖（运行时逻辑错误）

```rust,compile_fail
use rayon::prelude::*;

fn main() {
    let mut sum = 0;
    // ❌ 编译错误: 不能在 par_iter 闭包中捕获 &mut sum（非 Send + Sync）
    (0..100).into_par_iter().for_each(|i| {
        sum += i; // sum 是 &mut i32，不能跨线程共享
    });
    println!("{}", sum);
}
```

> **修正**:
> **`rayon`** 的**并行迭代器**：
>
> 1) `par_iter()` / `into_par_iter()` — 将工作负载分片到线程池；
> 2) 闭包必须是 `Send`（跨线程安全）和 `Fn`（无 `&mut` 环境捕获）；
> 3) 顺序结果需使用 `reduce`、`fold` + `sum`、或原子变量。
>
> 正确模式：
>
> 1) `(0..100).into_par_iter().sum::<i32>()` — 内置求和；
> 2) `fold` + `reduce`（分片累积后合并）；
> 3) `AtomicUsize` / `Mutex`（共享可变状态，但不推荐）。
>
> `rayon` 的线程池：
>
> 1) 全局线程池（默认线程数 = CPU 核心数）；
> 2) `ThreadPoolBuilder` 自定义；
> 3) `join`（分治并行）。
> 这与 OpenMP 的 `parallel for`（编译指令，隐式 reduction）或 C++ 的 `std::execution::par`（类似 rayon，但标准库支持）不同——Rust 的 rayon 是库级并行，类型安全。
> [来源: [Rayon](https://docs.rs/rayon/)] · [来源: [Data Parallelism](https://doc.rust-lang.org/book/)]

### 10.8 边界测试：生命周期参数的不匹配返回

```rust,compile_fail
fn longest<'a, 'b>(x: &'a str, y: &'b str) -> &'a str {
    // ❌ 编译错误: 不能返回 y，因为 y 的生命周期 'b 可能短于 'a
    y
}

fn main() {}
```

> **修正**: **生命周期标注**：1) `&'a str` 表示引用至少存活 `'a`；2) 返回 `'a` 要求数据存活至少 `'a`；3) `y` 的 lifetime `'b` 可能短于 `'a`，返回会导致悬垂引用。

## 逆向推理链（Backward Reasoning）

> **从编译错误反推**：
>
> ```text
> 分布式安全 ⟸ 一致性模型 + 故障隔离
> ```
>
## 参考来源

> [来源: [Herlihy & Shavit — The Art of Multiprocessor Programming](https://www.cs.brown.edu/~mph/HerlihyShavit/)]
> [来源: [Lynch — Distributed Algorithms](https://mitpress.mit.edu/books/distributed-algorithms)]
> [来源: [Ongaro & Ousterhout — Raft](https://raft.github.io/raft.pdf)]
> [来源: [Shapiro et al. — CRDT](https://hal.inria.fr/hal-00932836/document)]
> [来源: [Rust Atomics and Locks](https://marabos.nl/atomics/)]
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
> [来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]
> [来源: [RFC 2349 — Async Closures](https://rust-lang.github.io/rfcs/)]
> [来源: [Data Parallelism in Rust](https://doc.rust-lang.org/std/thread/)]
> [来源: [MPI for Rust](https://docs.rs/mpi/)]
> [来源: [Apache Arrow Rust](https://arrow.apache.org/rust/)]
> [来源: [Rust Concurrency Patterns](https://rust-lang.github.io/async-book/)]
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [The Rust Programming Language](https://doc.rust-lang.org/book/) · [Rust Standard Library](https://doc.rust-lang.org/std/)
> **对应 Rust 版本**: 1.96.0+ (Edition 2024)

## 嵌入式测验（Embedded Quiz）

### 测验 1：`std::thread::spawn` 与 `tokio::spawn` 创建的"任务"有什么本质区别？（理解层）

**题目**: `std::thread::spawn` 与 `tokio::spawn` 创建的"任务"有什么本质区别？

<details>
<summary>✅ 答案与解析</summary>

`std::thread::spawn` 创建 OS 线程，由操作系统调度，切换成本高。`tokio::spawn` 创建异步任务（绿色线程/协程），由 Tokio runtime 在用户态调度，切换成本极低。
</details>

---

### 测验 2：Rayon 的 `par_iter()` 与标准库的 `iter()` 在 API 使用上有什么区别？（理解层）

**题目**: Rayon 的 `par_iter()` 与标准库的 `iter()` 在 API 使用上有什么区别？

<details>
<summary>✅ 答案与解析</summary>

API 几乎相同（得益于相同的 `Iterator`/`ParallelIterator` 接口），但 `par_iter()` 自动将工作负载分发到线程池并行执行。无需手动管理线程。
</details>

---

### 测验 3：Actor 模型在 Rust 中的典型实现方式是什么？（理解层）

**题目**: Actor 模型在 Rust 中的典型实现方式是什么？

<details>
<summary>✅ 答案与解析</summary>

通常通过 `tokio::sync::mpsc` 通道实现消息传递，每个 actor 是一个异步任务 + 一个接收端，通过消息循环处理 mailbox。也可用 `actix` 等框架。
</details>

---

### 测验 4：分布式系统中，Rust 的 Serde + 强类型系统在消息序列化上有什么优势？（理解层）

**题目**: 分布式系统中，Rust 的 Serde + 强类型系统在消息序列化上有什么优势？

<details>
<summary>✅ 答案与解析</summary>

编译期保证消息结构与 schema 一致，反序列化失败在类型层面可处理。相比动态语言，消除了"字段名拼写错误导致运行时错误"的问题。
</details>

---

### 测验 5：`crossbeam::channel` 与 `std::sync::mpsc` 的主要改进是什么？（理解层）

**题目**: `crossbeam::channel` 与 `std::sync::mpsc` 的主要改进是什么？

<details>
<summary>✅ 答案与解析</summary>

`crossbeam` 提供更高效的 MP/MC（多生产者多消费者）通道、支持 select 操作（`Select`）、无锁/低锁实现，性能通常优于标准库通道。
</details>

## 认知路径

> **认知路径**: 从 L0 基础概念出发，经由本节的 **并行与分布式模式谱系：从线程池到共识算法** 核心原理，通向 L2 进阶模式与 L3 工程实践。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
| :--- | :--- | :--- | :--- |
| 并行与分布式模式谱系：从线程池到共识算法 基础定义 ⟹ 正确用法 | 理解语法与语义 | 能写出符合惯用法的代码 | 高 |
| 并行与分布式模式谱系：从线程池到共识算法 正确用法 ⟹ 常见陷阱 | 忽略边界条件 | 编译错误或运行时 bug | 高 |
| 并行与分布式模式谱系：从线程池到共识算法 常见陷阱 ⟹ 深度掌握 | 系统学习反模式 | 能进行代码审查与优化 | 高 |

> 分布式容错 ⟸ 错误传播边界 ⟸ 效果系统追踪
> 并行计算正确 ⟸ rayon 工作窃取 ⟸ Send 边界
> **过渡**: 掌握 并行与分布式模式谱系：从线程池到共识算法 的基础语法后，下一步需要理解其在类型系统中的位置与与其他概念的交互关系。
> **过渡**: 在实践中应用 并行与分布式模式谱系：从线程池到共识算法 时，务必关注边界条件与异常处理，这是从"能编译"到"能生产"的关键跃迁。
> **过渡**: 并行与分布式模式谱系：从线程池到共识算法 的设计理念体现了 Rust 零成本抽象与安全保证的核心权衡，理解这一权衡有助于迁移到更高级的并发与形式化验证领域。

### 反命题与边界

> **反命题**: "并行与分布式模式谱系：从线程池到共识算法 在所有场景下都是最佳选择" —— 错误。需要根据具体上下文权衡性能、可读性与安全性，某些场景下显式替代方案可能更优。

---

---

## 实践

> 将本节概念转化为可编译代码。

### 对应代码示例

- **[crates/c05_threads](../../../crates/c05_threads/)** — 与本节概念对应的可编译 crate 示例

### 建议练习

1. 阅读 `crates/c05_threads/` 中与"并行与分布式模式"相关的源码和示例
2. 运行 `cargo test -p c05_threads` 验证理解

---

## 导航：下一步去哪？

> **自检**：你当前掌握的核心概念是否已能独立应用？

| 选择 | 条件 | 目标 |
|:---|:---|:---|
| 🔙 巩固基础 | 仍有模糊概念 | 回到 [L2 对应主题](../02_intermediate/) 或 [MVP 学习路径](../00_meta/LEARNING_MVP_PATH.md) |
| 🔜 深入 L3 其他主题 | 想扩展高级技能 | [L3 README](./README.md) 选择其他主题 |
| 🎓 进入 L4 形式化 | 想理解"为什么"的数学证明 | [L4 形式化](../04_formal/README.md) |
| 🏗️ 进入 L6 生态 | 想掌握生产工具链 | [L6 生态](../06_ecosystem/README.md) |
