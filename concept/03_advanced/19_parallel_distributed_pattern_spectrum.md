# 并行与分布式模式谱系：从线程池到共识算法

> **层级**: L3 高级概念 — 并发/分布式系统设计
> **A/S/P 标记**: **S+A** — Structure + Application
> **双维定位**: C×Ana — 分析并行与分布式模式的演进谱系与统一框架
> **前置概念**: [Concurrency](./01_concurrency.md) · [Async](./02_async.md) · [Lock-free](../03_advanced/16_lock_free.md) · [Distributed Systems](../06_ecosystem/18_distributed_systems.md)
> **后置概念**: [Pattern Composition Algebra](../06_ecosystem/35_pattern_composition_algebra.md) · [System Design Principles](../06_ecosystem/05_system_design_principles.md)
> **主要来源**: [Herlihy & Shavit — The Art of Multiprocessor Programming] · [Lynch — Distributed Algorithms] · [Tanenbaum — Distributed Systems] · [Amazon Science — Must Framework] · [Rust Atomics and Locks](https://marabos.nl/atomics/)

---

> **Bloom 层级**: 分析 → 评价 → 创造

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

> **[来源: Herlihy & Shavit — The Art of Multiprocessor Programming, Ch. 1] · [Lynch — Distributed Algorithms, §1] · [💡 原创分析]** ✅

所有并行/分布式模式都可以通过四个维度分析：

| 维度 | 说明 | 线程池 | Actor | Raft | CRDT |
|:---|:---|:---|:---|:---|:---|
| **通信模型** | 如何交换信息 | 共享内存 | 消息传递 | RPC + 日志复制 | 操作传播 |
| **同步机制** | 如何协调执行 | 锁 / 原子操作 | 邮箱顺序 | Leader 选举 + 日志 | 无同步（最终一致） |
| **故障模型** | 假设何种故障 | 崩溃停止 | 崩溃停止 | 崩溃停止 / 拜占庭 | 网络分区 |
| **一致性模型** | 保证何种一致性 | 顺序一致 | 单 Actor 顺序 | 线性一致 | 最终一致 |

---

## 三、L1 单机共享内存模式

### 3.1 线程池模式

> **[来源: Rust std::thread] · [rayon docs] · [Java ThreadPoolExecutor]** ✅

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

> **[来源: CLRS — Introduction to Algorithms, Ch. 27] · [rayon::join]** ✅

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

> **[来源: Herlihy & Shavit, Ch. 10-11] · [Rust Atomics and Locks, Ch. 7] · [crossbeam docs]** ✅

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

> **[来源: Hewitt et al. 1973 — A Universal Modular Actor Formalism] · [Actix docs] · [Erlang/OTP]** ✅

```rust
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
2. **异步**: 消息发送非阻塞，Actor 按顺序处理邮箱中的消息
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

> **[来源: Hoare 1978 — Communicating Sequential Processes] · [Go channels] · [Rust std::sync::mpsc]** ✅

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

> **[来源: Reactive Streams Specification] · [tokio::sync::mpsc] · [futures::Stream]** ✅

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

> **[来源: Ongaro & Ousterhout 2014 — In Search of an Understandable Consensus Algorithm (USENIX ATC)] · [Raft Consensus Paper]** ✅

```rust
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

> **[来源: Demers et al. 1987 — Epidemic Algorithms for Replicated Database Maintenance] · [SWIM 协议] · [Cassandra Gossip]** ✅

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

```rust
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

> **[来源: Lynch — Distributed Algorithms, §1.2] · [💡 原创分析]** ✅

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

> **[来源: Brewer 2000 — CAP Twelve Years Later] · [Viotti & Vukolić 2016 — Consistency in Non-Transactional Distributed Storage]** ✅

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

```rust
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
| CSP | [Hoare 1978] | ✅ | Tier 1 |
| Raft 算法 | [Ongaro & Ousterhout 2014] | ✅ | Tier 1 |
| CAP 定理 | [Brewer 2000] · [Gilbert & Lynch 2002] | ✅ | Tier 1 |
| CRDT 理论 | [Shapiro et al. 2011] | ✅ | Tier 1 |
| Gossip 协议 | [Demers et al. 1987] | ✅ | Tier 1 |
| 并发连续体 | [Lynch, §1.2] · [💡 原创分析] | ✅/💡 | Tier 2 |
| Rust 生态工具谱系 | [💡 原创分析] | ⚠️ | Tier 3 |

---

> **权威来源**: [Herlihy & Shavit — The Art of Multiprocessor Programming](https://www.cs.brown.edu/~mph/HerlihyShavit/) · [Lynch — Distributed Algorithms](https://mitpress.mit.edu/books/distributed-algorithms) · [Ongaro & Ousterhout — Raft](https://raft.github.io/raft.pdf) · [Shapiro et al. — CRDT](https://hal.inria.fr/hal-00932836/document) · [Rust Atomics and Locks](https://marabos.nl/atomics/)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.90.0+ (Edition 2024)
> **最后更新**: 2026-05-24
> **状态**: ✅ 新建 — 表征空间坐标系
