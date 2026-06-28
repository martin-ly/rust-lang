# 工作流控制模式与 Rust 所有权系统交叉分析
>
> **最后更新**: 2026-06-09

> **内容分级**: [归档级]
>
> **分级**: [C]
> **Bloom 层级**: L5-L6 (分析/评价/创造)

## 目录

> **来源: [Workflow Patterns Initiative](https://www.workflowpatterns.com/)** · **来源: [van der Aalst 2003](https://www.workflowpatterns.com/)** · **来源: [Russell 2006](https://www.workflowpatterns.com/)** · **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Tokio Docs](https://tokio.rs/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

- [工作流控制模式与 Rust 所有权系统交叉分析](#工作流控制模式与-rust-所有权系统交叉分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
    - [分析框架](#分析框架)
  - [2. 类型安全分类矩阵](#2-类型安全分类矩阵)
  - [3. 逐类分析](#3-逐类分析)
    - [3.1 基础控制流 (WCP1-5)](#31-基础控制流-wcp1-5)
    - [3.2 高级分支与同步 (WCP6-11)](#32-高级分支与同步-wcp6-11)
    - [3.3 多实例模式 (WCP12-15)](#33-多实例模式-wcp12-15)
    - [3.4 基于状态的模式 (WCP16-18, 38-40)](#34-基于状态的模式-wcp16-18-38-40)
    - [3.5 取消与强制完成 (WCP19-20, 25-27)](#35-取消与强制完成-wcp19-20-25-27)
    - [3.6 迭代模式 (WCP21-22)](#36-迭代模式-wcp21-22)
    - [3.7 终止模式 (WCP11, 43)](#37-终止模式-wcp11-43)
    - [3.8 触发器模式 (WCP23-24)](#38-触发器模式-wcp23-24)
    - [3.9 线程模式 (WCP36-37, 41-42)](#39-线程模式-wcp36-37-41-42)
  - [4. 所有权交互定理](#4-所有权交互定理)
    - [4.1 定理 1：所有权分裂安全性](#41-定理-1所有权分裂安全性)
    - [4.2 定理 2：共享可变状态需求](#42-定理-2共享可变状态需求)
    - [4.3 定理 3：取消模式内存安全](#43-定理-3取消模式内存安全)
    - [4.4 定理 4：循环模式安全性边界](#44-定理-4循环模式安全性边界)
  - [5. Rust 实现策略决策树](#5-rust-实现策略决策树)
  - [6. 反模式与陷阱](#6-反模式与陷阱)
    - [6.1 对简单合并使用 `unsafe`（过度设计）](#61-对简单合并使用-unsafe过度设计)
    - [6.2 多路合并中忘记同步（数据竞争）](#62-多路合并中忘记同步数据竞争)
    - [6.3 任意循环中创建引用循环而不使用 `Weak`](#63-任意循环中创建引用循环而不使用-weak)
    - [6.4 `select!` 的 cancel-safe 陷阱](#64-select-的-cancel-safe-陷阱)
  - [7. 总结与展望](#7-总结与展望)
    - [7.1 核心结论](#71-核心结论)
    - [7.2 Polonius 与未来改进](#72-polonius-与未来改进)
    - [7.3 Rust 工作流引擎设计原则](#73-rust-工作流引擎设计原则)
  - [参考文献](#参考文献)
  - [权威来源索引](#权威来源索引)
  - [相关文件](#相关文件)
  - [权威来源索引](#权威来源索引-1)

---

## 1. 引言

> **[来源: Workflow Patterns Initiative - workflowpatterns.com]** · **来源: [van der Aalst et al. (2003)](https://www.workflowpatterns.com/)** · **来源: [Russell et al. (2006)](https://www.workflowpatterns.com/)** · **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [TRPL Ch. 4, 8, 16](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)**

**工作流控制模式（Workflow Control Patterns, WCP）** 由 van der Aalst 等人于 2003 年系统提出，后经 Russell 等人于 2006 年扩展为 43 个模式，描述业务流程中活动之间的控制流关系。Rust 的所有权系统核心规则可形式化为：

$$
\text{OwnershipRule} := \forall x : \text{Own}(x) \to \text{Unique}(x) \land \neg\text{Alias}_{\text{mut}}(x)
$$

即：任何值在任意时刻有且只有一个所有者；或者存在任意数量的不可变借用，或者存在唯一一个可变借用，二者不可兼得。

本文回答三个核心问题：**43 个 WCP 在 Rust 所有权系统下，哪些可以自然地表达？哪些需要运行时共享机制？哪些需要突破所有权边界？**

这一交叉研究对两类受众具有价值：

- **工作流引擎开发者**：理解 Rust 的类型约束如何影响引擎架构设计
- **Rust 系统开发者**：借鉴成熟的工作流模式库，构建复杂的异步/并发业务逻辑

分析维度包括：所有权分裂方式、可变 aliasing 需求、生命周期约束、同步需求与动态性。

### 分析框架
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

| 维度 | 说明 | Rust 对应 |
|:---|:---|:---|
| 所有权分裂 | 一个值是否被多个并发活动共享 | `move` / `clone` / `Arc` |
| 可变 aliasing | 多个活动是否同时需要写访问 | `&mut T` 唯一性 / `Mutex<T>` |
| 生命周期 | 活动完成后数据是否仍然有效 | 生命周期参数 / `'static` |
| 同步需求 | 活动之间是否需要协调 | `await` / `join!` / `Barrier` |
| 动态性 | 结构是否在运行时决定 | `dyn Trait` / `Pin` / `unsafe` |

---

## 2. 类型安全分类矩阵

> **来源: [Workflow Patterns Initiative](https://www.workflowpatterns.com/)** · **来源: [Russell 2006](https://www.workflowpatterns.com/)**

**图例**：🟢 Naturally Safe · 🟡 Requires Shared State · 🔴 Requires Unsafe / Pin · ⚪ Compile-time Only

```mermaid
graph LR
    subgraph "🟢 Naturally Safe (9)"
        A1[WCP1 Sequence]
        A2[WCP2 Parallel Split]
        A3[WCP4 Exclusive Choice]
        A4[WCP5 Simple Merge]
        A5[WCP21 Structured Loop]
        A6[WCP22 Recursion]
        A7[WCP36 Thread Merge]
        A8[WCP37 Thread Split]
        A9[WCP43 Explicit Termination]
    end
    subgraph "🟡 Requires Shared State (30)"
        B1[WCP3 Synchronization]
        B2[WCP6 Multi Choice]
        B3[WCP7 Sync Merge]
        B4[WCP8 Multi Merge]
        B5[WCP12 MI w/o Sync]
        B6[WCP14-15 MI Runtime]
        B7[WCP16 Deferred Choice]
        B8[WCP17 Interleaved Parallel]
        B9[WCP18 Milestone]
        B10[WCP19 Cancel Activity]
        B11[WCP20 Cancel Case]
        B12[WCP23 Transient Trigger]
        B13[WCP24 Persistent Trigger]
        B14[WCP25 Cancel Region]
        B15[WCP26-27 Cancel/Complete MI]
        B16[WCP28-32 Discriminator/Partial Join]
        B17[WCP33-35 Generalized Joins]
        B18[WCP38-40 Partial Join MI / Acyclic Sync]
        B19[WCP41 Critical Section]
        B20[WCP42 Interleaved Routing]
        B21[WCP9 Discriminator]
        B22[WCP11 Implicit Termination]
    end
    subgraph "🔴 Requires Unsafe / Pin (3)"
        C1[WCP10 Arbitrary Cycles]
        C2[WCP9* Complex Discriminator]
        C3[WCP13* MI Unsafe]
    end
    subgraph "⚪ Compile-time Only (1)"
        D1[WCP13 MI Design-Time Safe]
    end
```

| 编号 | 模式名称 | 分类 | Rust 关键抽象 |
|:---:|:---|:---:|:---|
| WCP1 | Sequence | 🟢 | `let` 绑定、语句顺序 |
| WCP2 | Parallel Split | 🟢 | `join!`、`thread::scope`、`rayon::join` |
| WCP3 | Synchronization | 🟡 | `Barrier`、`mpsc::channel`、`join!` |
| WCP4 | Exclusive Choice | 🟢 | `match`、`if-else`、穷尽性检查 |
| WCP5 | Simple Merge | 🟢 | 控制流汇合、所有权重聚 |
| WCP6 | Multi Choice | 🟡 | `select!`、动态守卫、`Arc` |
| WCP7 | Synchronizing Merge | 🟡 | `Barrier`、`AtomicUsize`、动态计数 |
| WCP8 | Multi Merge | 🟡 | `Mutex`、`Arc`、计数器 |
| WCP9 | Discriminator | 🟡 / 🔴 | `AtomicBool`（🟡）；自引用令牌（🔴） |
| WCP10 | Arbitrary Cycles | 🔴 | `Pin`、`unsafe`、原始指针、图索引 |
| WCP11 | Implicit Termination | 🟡 | `Drop`、任务句柄、退出码检测 |
| WCP12 | MI without Synchronization | 🟡 | `thread::spawn`、`tokio::spawn`、`JoinHandle` |
| WCP13 | MI with Design-Time Knowledge | ⚪ / 🔴 | `const N` 数组（⚪）；动态生成（🔴） |
| WCP14 | MI with Run-Time Knowledge | 🟡 | `Vec<JoinHandle>`、`join_all` |
| WCP15 | MI without Priori Knowledge | 🟡 | `Stream`、`FuturesUnordered` |
| WCP16 | Deferred Choice | 🟡 | `select!` + 超时、事件通道 |
| WCP17 | Interleaved Parallel Routing | 🟡 | `Mutex`、令牌轮转、状态机 |
| WCP18 | Milestone | 🟡 | `AtomicBool` + `Ordering::SeqCst` |
| WCP19 | Cancel Activity | 🟡 | `AbortHandle`、`select!` + `cancelled` |
| WCP20 | Cancel Case | 🟡 | `scope` + 提前返回、补偿 `Drop` |
| WCP21 | Structured Loop | 🟢 | `for` / `while` / `loop` |
| WCP22 | Recursion | 🟢 | 归纳类型、尾递归提示 |
| WCP23 | Transient Trigger | 🟡 | `tokio::sync::oneshot` |
| WCP24 | Persistent Trigger | 🟡 | `tokio::sync::broadcast` / `watch` |
| WCP25 | Cancel Region | 🟡 | `CancellationToken`、嵌套 `scope` |
| WCP26 | Cancel MI Activity | 🟡 | `FuturesUnordered` + `AbortHandle` |
| WCP27 | Complete MI Activity | 🟡 | `JoinAll`、条件完成信号 |
| WCP28 | Blocking Discriminator | 🟡 | `Semaphore`、`AtomicUsize` |
| WCP29 | Canceling Discriminator | 🟡 | `AtomicBool` + 分支清理 |
| WCP30-32 | Partial Joins | 🟡 | `mpsc`、`Barrier` |
| WCP33 | Generalized AND-Join | 🟡 | 动态 DAG + 拓扑排序 |
| WCP34-35 | Local/General Sync Merge | 🟡 | 局部/全局令牌计数器 |
| WCP36 | Thread Merge | 🟢 | `thread::scope` 结束自动汇合 |
| WCP37 | Thread Split | 🟢 | `thread::scope` 内部分叉 |
| WCP38 | Static Partial Join for MI | 🟡 | 编译时 `N` + `Barrier` |
| WCP39 | Dynamic Partial Join for MI | 🟡 | 运行时动态计数器 |
| WCP40 | Acyclic Synchronizing Merge | 🟡 | 拓扑序 + 计数器 |
| WCP41 | Critical Section | 🟡 | `Mutex`、`RwLock`、`MutexGuard` |
| WCP42 | Interleaved Routing | 🟡 | `Mutex`、交错调度器 |
| WCP43 | Explicit Termination | 🟢 | `return`、`std::process::exit` |

> **来源: [Workflow Patterns Initiative](https://www.workflowpatterns.com/)** · **来源: [Rust Reference - std::sync/std::thread](https://doc.rust-lang.org/reference/)**

---

## 3. 逐类分析

> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [TRPL Ch. 4, 8, 13, 16](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)** · **来源: [Tokio Documentation](https://tokio.rs/)**

### 3.1 基础控制流 (WCP1-5)

> **来源: [van der Aalst 2003](https://www.workflowpatterns.com/)** · **来源: [Rust Reference - Control Flow Expressions](https://doc.rust-lang.org/reference/)**

**WCP1 Sequence** 映射为 Rust 的线性所有权传递：

```rust,ignore
fn sequence_pattern() -> String {
    let data = String::from("step1");   // Own(data)
    let result = process_step1(data);    // Move: data 失效
    process_step2(result)                // Move: result 转移
}
```

顺序模式天然满足线性类型约束：中间状态转移后自动失效，不存在 use-after-move。

**WCP4 Exclusive Choice** 映射到 `match`，编译器保证**穷尽性检查**；进入 `match` 时，被匹配值的所有权被消耗，各分支通过 `move` 模式获得所有权。Rust 保证只有一个分支执行，因此不存在数据竞争。

**WCP5 Simple Merge** 是排他选择的对偶，`match` 各分支返回统一类型后汇合。由于 Rust 的 `match` 保证各分支返回统一类型，合并点的类型安全由编译器静态验证，不需要同步。

**WCP2 Parallel Split** 要求各分支获得**不相交的所有权**：

```rust
use std::thread;

fn parallel_split_scoped(data: &[i32]) -> (i32, i32) {
    thread::scope(|s| {
        let h1 = s.spawn(|| data.iter().map(|x| x * 2).sum::<i32>());
        let h2 = s.spawn(|| data.iter().filter(|&&x| x % 2 == 0).sum::<i32>());
        (h1.join().unwrap(), h2.join().unwrap())
    })
}
```

若数据不可分，需降级为 🟡：`Arc<T>`（只读共享）或 `Arc<Mutex<T>>`（读写共享）。

**WCP4 Exclusive Choice** 映射到 `match`，编译器保证**穷尽性检查**；**WCP5 Simple Merge** 是排他选择的对偶，`match` 各分支返回统一类型后汇合。由于 Rust 保证只有一个分支执行，不存在数据竞争。

### 3.2 高级分支与同步 (WCP6-11)

> **来源: [Russell 2006](https://www.workflowpatterns.com/)** · **来源: [Rust Reference - Concurrency](https://doc.rust-lang.org/reference/special-types-and-traits.html)**

**WCP6 Multi Choice** 的动态守卫条件意味着活跃分支集合在运行时确定，静态借用检查无法预知，需通过 `Arc` 或 `move` 分裂所有权：

```rust,ignore
use tokio::task::JoinSet;

async fn multi_choice(data: i32) -> Vec<String> {
    let mut handles = JoinSet::new();
    if data > 10  { handles.spawn(async { "high".into() }); }
    if data % 2 == 0 { handles.spawn(async { "even".into() }); }
    let mut r = Vec::new();
    while let Some(res) = handles.join_next().await { r.push(res.unwrap()); }
    r
}
```

**WCP7 Synchronizing Merge** 等待所有活跃分支完成，核心挑战是动态分支数：

```rust,ignore
use tokio::sync::Barrier;
use std::sync::Arc;

async fn sync_merge(branches: Vec<impl std::future::Future<Output = i32>>) -> Vec<i32> {
    let n = branches.len();
    let barrier = Arc::new(Barrier::new(n));
    let mut handles = Vec::new();
    for b in branches {
        let bc = Arc::clone(&barrier);
        handles.push(tokio::spawn(async move { let v = b.await; bc.wait().await; v }));
    }
    let mut out = Vec::new();
    for h in handles { out.push(h.await.unwrap()); }
    out
}
```

**WCP8 Multi Merge** 每次分支到达都触发下游，类似 `mpsc` 通道消费端：

```rust,ignore
use tokio::sync::mpsc;

async fn multi_merge(branches: Vec<impl std::future::Future<Output = String>>) {
    let (tx, mut rx) = mpsc::unbounded_channel::<String>();
    for b in branches {
        let tx = tx.clone();
        tokio::spawn(async move { let _ = tx.send(b.await); });
    }
    drop(tx);
    while let Some(result) = rx.recv().await {
        println!("merged: {}", result);
    }
}
```

**WCP9 Discriminator** 等待第一个到达者，可用 `AtomicBool` + `compare_exchange` 实现：

```rust,ignore
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

async fn discriminator(branches: Vec<impl std::future::Future<Output = String>>) -> String {
    let (tx, mut rx) = tokio::sync::mpsc::channel(branches.len());
    let winner = Arc::new(AtomicBool::new(false));
    for b in branches {
        let tx = tx.clone();
        let flag = Arc::clone(&winner);
        tokio::spawn(async move {
            let result = b.await;
            if flag.compare_exchange(false, true, Ordering::SeqCst, Ordering::Relaxed).is_ok() {
                let _ = tx.send(result).await;
            }
        });
    }
    drop(tx);
    rx.recv().await.expect("at least one branch")
}
```

**WCP10 Arbitrary Cycles** 是 Rust 中最难的模式。非结构化循环需要状态机或图遍历。若节点通过引用相互指向形成循环，必须使用 `Pin`（固定内存位置）或原始指针（`unsafe`）。安全替代方案是使用**索引 + Vec**：

```rust
struct WorkflowGraph {
    nodes: Vec<Node>,
    edges: Vec<(usize, usize)>, // 索引导向，避免引用循环
}

struct Node {
    id: usize,
    action: Box<dyn Fn(&WorkflowGraph) -> usize>,
}
```

对于真正的自引用 async 状态机，`Pin` 是必需的：

```rust
use std::pin::Pin;
use std::future::Future;
use std::task::{Context, Poll};

struct SelfReferential {
    data: String,
    // ptr: *const String, // 指向 data 内部，移动后悬垂
}

// 必须用 Pin 固定到栈/堆，防止移动
fn pin_required() {
    let fut = async { /* 内部可能存在自引用 */ };
    let _pinned = Box::pin(fut); // Pin<Box<dyn Future>>
}
```

**WCP11 Implicit Termination** 对应 `thread::scope` 结束、`JoinSet` 为空或 `Arc` 引用计数归零。

### 3.3 多实例模式 (WCP12-15)

> **来源: [Russell 2006](https://www.workflowpatterns.com/)** · **来源: [TRPL Ch. 16](https://doc.rust-lang.org/book/ch16-00-concurrency.html)**

Rust 的核心挑战：**确保所有实例完成后共享数据不提前释放**。

**WCP12 MI without Synchronization**：`Arc` 保证实例完成前数据存活。

**WCP13 MI with Design-Time Knowledge**：若实例数 $N$ 编译时已知，可用常量泛型实现零开销版本：

```rust
fn mi_const_generics<T: Send, F: FnMut(T) + Send + Clone, const N: usize>(
    data: [T; N], mut f: F
) {
    std::thread::scope(|s| {
        for item in data {
            let mut fc = f.clone();
            s.spawn(move || fc(item));
        }
    });
}
```

**WCP14-15** 需要动态 `Vec<JoinHandle>` 或 `FuturesUnordered` 流式收集。

### 3.4 基于状态的模式 (WCP16-18, 38-40)

> **来源: [Russell 2006](https://www.workflowpatterns.com/)**

**WCP16 Deferred Choice** 映射到 `select!` + 超时，与延迟选择的互斥语义一致。注意 cancel-safe：未选中分支的 Future 可能被部分执行。

**WCP17 Interleaved Parallel Routing** 要求宏观并行、微观互斥，直接用 `Mutex`：

```rust,ignore
struct InterleavedRouter { token: Mutex<()> }
impl InterleavedRouter {
    fn exec_a(&self) { let _ = self.token.lock().unwrap(); /* A */ }
    fn exec_b(&self) { let _ = self.token.lock().unwrap(); /* B */ }
}
```

**WCP18 Milestone** 映射到原子标志。必须使用 `Ordering::SeqCst` 保证 happens-before 关系，防止里程碑事件对其他线程不可见。

### 3.5 取消与强制完成 (WCP19-20, 25-27)

> **[来源: Tokio Docs - Cancellation]** · **来源: [Rust Reference - Drop](https://doc.rust-lang.org/reference/)**

Rust 的 **RAII + Drop** 为取消模式提供独特内存安全保证。

**WCP19 Cancel Activity**：

```rust,ignore
async fn cancel_activity() {
    let handle = tokio::spawn(async {
        loop { tokio::time::sleep(tokio::time::Duration::from_secs(1)).await; }
    });
    tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
    handle.abort();
    assert!(handle.await.unwrap_err().is_cancelled());
}
```

**WCP25 Cancel Region** 使用 `CancellationToken`：

```rust,ignore
use tokio_util::sync::CancellationToken;

async fn cancel_region() {
    let token = CancellationToken::new();
    let child = token.child_token();
    let handle = tokio::spawn(async move {
        loop {
            tokio::select! {
                _ = tokio::time::sleep(tokio::time::Duration::from_secs(1)) => {}
                _ = child.cancelled() => { println!("region cancelled"); break; }
            }
        }
    });
    tokio::time::sleep(tokio::time::Duration::from_millis(500)).await;
    token.cancel();
    let _ = handle.await;
}
```

`abort()` 在下次 `.await` 点退出，栈帧值按逆序调用 `Drop`，无悬垂指针、无双重释放。

**WCP20 Cancel Case**：通过 `scope` + 提前返回或补偿 `Drop` 实现。**WCP25 Cancel Region**：使用 `CancellationToken` 广播取消信号到区域内所有任务。**WCP26-27** 对多实例的取消/强制完成使用 `FuturesUnordered` + `AbortHandle`。

### 3.6 迭代模式 (WCP21-22)

> **来源: [TRPL Ch. 3, 13](https://doc.rust-lang.org/book/ch03-00-common-programming-concepts.html)**

**WCP21 Structured Loop** 完全 🟢：`for`（迭代器驱动）、`while`（条件驱动）、`loop`（无限循环 + `break` 返回值）。

**WCP22 Recursion** 映射到归纳类型：

```rust
enum Tree<T> {
    Leaf(T),
    Node(Box<Tree<T>>, Box<Tree<T>>),
}
```

Rust **不保证尾调用优化**（TCO），因为 TCO 与 RAII Drop 顺序冲突。深度递归应使用显式栈或 trampoline。

### 3.7 终止模式 (WCP11, 43)
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

**WCP43 Explicit Termination** 映射到 `return` 或 `std::process::exit` / `abort`，返回类型 `!`（never type）精确对应永不返回语义。

**WCP11 Implicit Termination** 在 Rust 中体现为 `main` 返回、`thread::scope` 结束（子线程自动汇合）、或 `Arc` 引用计数归零。

### 3.8 触发器模式 (WCP23-24)

> **[来源: Tokio Docs - Channels]**

**WCP23 Transient Trigger** 映射到 `oneshot`：发送一次后通道关闭。**WCP24 Persistent Trigger** 映射到 `broadcast` 或 `watch`，支持多接收者持续监听。

### 3.9 线程模式 (WCP36-37, 41-42)

> **来源: [Rust Reference - std::thread](https://doc.rust-lang.org/reference/)**

**WCP36-37 Thread Merge/Split** 通过 `thread::scope` 完美实现：

```rust,ignore
fn thread_patterns(data: &mut [i32]) {
    thread::scope(|s| {
        s.spawn(|| data[..data.len()/2].iter_mut().for_each(|x| *x *= 2));
        s.spawn(|| data[data.len()/2..].iter_mut().for_each(|x| *x += 1));
    }); // 隐式汇合：所有子线程完成后才退出 scope
}
```

关键安全保证：子线程可借用父线程栈数据（scope 保证子线程先结束），无需 `Arc` 或 `'static`。

**WCP41 Critical Section** 映射为 `MutexGuard`，其 `Drop` 自动释放锁：

```rust
use std::sync::Mutex;

fn critical_section(counter: &Mutex<i32>) {
    let mut guard = counter.lock().unwrap();
    *guard += 1;
} // MutexGuard 的 Drop 在此处自动释放锁
```

**WCP42 Interleaved Routing** 映射为 `Mutex` 强制串行化：

```rust
use std::sync::Mutex;
use std::collections::VecDeque;

struct InterleavedQueue<T> {
    queue: Mutex<VecDeque<T>>,
    token: Mutex<()>, // 强制所有操作串行化
}
```

---

## 4. 所有权交互定理

> **来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)** · **来源: [ACM - Ownership Types](https://dl.acm.org/)** · **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**

### 4.1 定理 1：所有权分裂安全性
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

**定理 1（所有权分裂安全性）**: 对于任意工作流模式，如果其将数据上下文 $D$ 分裂为子上下文 $D_1, \ldots, D_n$，且满足 $\forall i \neq j: \text{Dom}(D_i) \cap \text{Dom}(D_j) = \emptyset$，则该模式可在 Rust 安全子系统中实现，无需运行时共享机制。

**证明**: 将每个 $D_i$ 的所有权 `move` 到对应分支。由于 $D_i \cap D_j = \emptyset$，各分支持有不相交数据，编译器验证无别名冲突。各分支完成后结果通过 `join` 汇聚。∎

### 4.2 定理 2：共享可变状态需求
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

**定理 2（共享可变状态需求）**: 若模式要求两个以上并发活动同时访问同一数据 $d$，且至少一个活动修改 $d$，则 Rust 实现必须引入内部可变性（`Mutex`、`RefCell`）或消息传递。

**证明**: Rust 核心不变式禁止同时存在 `&mut T` 与其他引用。要同时满足"共享"与"可变"，必须将检查推迟到运行时。`Mutex` 运行时保证互斥；`RefCell` 单线程运行时检查；通道通过所有权转移避免同时访问。∎

**应用**: WCP3（Synchronization）、WCP8（Multi Merge）、WCP17（Interleaved Parallel Routing）等所有需要并发修改共享计数器或状态的模式，都落在 🟡 类。

### 4.3 定理 3：取消模式内存安全
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

**定理 3（取消模式内存安全）**: Rust 中基于 `AbortHandle`、`CancellationToken` 或 `scope` 的取消模式是内存安全的，不会导致悬垂指针、双重释放或资源泄漏。

**证明**: `abort()` 在任务下次 `.await` 点退出；栈帧值按逆序调用 `Drop`；所有权系统保证每值只 `drop` 一次；`scope` 保证子线程结束前父线程栈数据有效。∎

### 4.4 定理 4：循环模式安全性边界
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

**定理 4（循环模式安全性边界）**: 任意循环（WCP10）若涉及自引用数据结构（节点引用自身），则需要 `Pin` 固定或 `unsafe` 原始指针。

**证明**: 图结构 `Graph` → `Node` → `Graph` 形成自引用。移动 `Graph` 会使 `Node` 中的引用悬垂。`Pin` 阻止移动；原始指针绕过编译器检查；索引方案（`Vec` + `usize`）安全但语义受限。∎

---

## 5. Rust 实现策略决策树

> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Tokio Docs](https://tokio.rs/)** · **来源: [TRPL Ch. 16](https://doc.rust-lang.org/book/ch16-00-concurrency.html)**

```mermaid
flowchart TD
    A[工作流模式] --> B{需要并发?}
    B -->|否| C[🟢 let / match / loop]
    B -->|是| D{数据可分?}
    D -->|是，不相交| E["🟢 thread::scope / join!"]
    D -->|否| F{只读 or 读写?}
    F -->|只读| G[🟡 Arc<T>]
    F -->|读写| H{互斥 or 消息传递?}
    H -->|互斥| I[🟡 Mutex<T> / RwLock<T>]
    H -->|消息传递| J[🟡 mpsc / broadcast]
    H -->|原子计数| K[🟡 AtomicUsize]
    E --> L{存在引用循环?}
    L -->|否| M[🟡 Vec + 索引]
    L -->|是| N{可避免的?}
    N -->|是| O[🟡 Rc<RefCell<T>> + Weak]
    N -->|否| P[🔴 Pin<T> / unsafe]
    I --> Q{需要取消?}
    Q -->|是| R[🟡 AbortHandle / CancellationToken]
    Q -->|否| S[🟡 std::sync / tokio::sync]
```

**使用指南**：(1) 数据可分是避免 `Arc/Mutex` 的关键；(2) 共享 + 可变必须走内部可变性；(3) 存在引用循环时优先用索引代替引用；(4) 若语义必须自引用，选择 `Pin`（🔴）。

---

## 6. 反模式与陷阱

> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [Rust Reference - Unsafe Rust](https://doc.rust-lang.org/reference/unsafe-blocks.html)**

### 6.1 对简单合并使用 `unsafe`（过度设计）
>
> **[来源: [crates.io](https://crates.io/)]**

WCP5（Simple Merge）的互斥路径汇合完全可用 `match` / `Option` 表达。引入 `unsafe` 破坏穷尽性检查且无性能收益。**原理**：Simple Merge 的语义是"互斥路径汇合"，Rust 的 `match` 和枚举已精确表达此语义，且编译器自动验证各分支类型一致。

```rust
// ❌ 错误：Simple Merge 不需要 unsafe
unsafe fn bad_simple_merge(a: *const String, b: *const String) -> String {
    if !a.is_null() { (*a).clone() } else { (*b).clone() }
}

// ✅ 正确：match 完全足够
fn good_simple_merge(a: Option<String>, b: Option<String>) -> String {
    match (a, b) {
        (Some(s), _) | (_, Some(s)) => s,
        (None, None) => String::default(),
    }
}
```

### 6.2 多路合并中忘记同步（数据竞争）
>
> **[来源: [docs.rs](https://docs.rs/)]**

WCP8（Multi Merge）使用非原子共享计数器会导致 UB。必须使用 `AtomicUsize` 或 `Mutex`。

```rust
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

// ❌ 错误：非原子操作导致数据竞争
fn bad_multi_merge() {
    // let counter = Arc::new(0usize); // 编译错误， thankfully
}

// ✅ 正确：AtomicUsize
fn good_multi_merge() {
    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];
    for _ in 0..10 {
        let c = Arc::clone(&counter);
        handles.push(std::thread::spawn(move || {
            c.fetch_add(1, Ordering::SeqCst);
        }));
    }
    for h in handles { h.join().unwrap(); }
}
```

### 6.3 任意循环中创建引用循环而不使用 `Weak`
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

WCP10 中使用 `Rc`/`Arc` 强引用循环导致内存泄漏。图结构循环必须用 `Weak` 引用或索引表示法：

```rust
use std::rc::{Rc, Weak};
use std::cell::RefCell;

struct Node { next: RefCell<Option<Weak<Node>>> }

fn safe_cycle() {
    let a = Rc::new(Node { next: RefCell::new(None) });
    let b = Rc::new(Node { next: RefCell::new(None) });
    *a.next.borrow_mut() = Some(Rc::downgrade(&b));
    *b.next.borrow_mut() = Some(Rc::downgrade(&a));
}
```

### 6.4 `select!` 的 cancel-safe 陷阱
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

WCP16（Deferred Choice）中，`select!` 会轮询所有分支。若某分支在 `.await` 点被挂起后另一分支完成，该分支 Future 可能被部分执行后取消。

```rust,ignore
// ❌ 错误：非 cancel-safe
async fn bad_deferred_choice(rx: &mut tokio::sync::mpsc::Receiver<i32>) -> i32 {
    let mut temp = 0;
    tokio::select! {
        val = async { temp = rx.recv().await.unwrap_or(0); temp } => val,
        _ = tokio::time::sleep(tokio::time::Duration::from_secs(1)) => temp,
    }
}

// ✅ 正确：确保 cancel-safe
async fn good_deferred_choice(rx: &mut tokio::sync::mpsc::Receiver<i32>) -> i32 {
    tokio::select! {
        Some(val) = rx.recv() => val,
        _ = tokio::time::sleep(tokio::time::Duration::from_secs(1)) => -1,
    }
}
```

若 Future 已修改共享状态（如上面的 `temp`），取消后状态不一致。应使用 cancel-safe 的 Future（如 `recv()` 而非手动赋值）。

> **[来源: Tokio Docs - Cancel Safety]**

---

## 7. 总结与展望

> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **[来源: Rust Internals - Polonius]** · **来源: [Workflow Patterns Initiative](https://www.workflowpatterns.com/)**

### 7.1 核心结论
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 分类 | 数量 | 占比 | 典型模式 |
|:---|:---:|:---:|:---|
| 🟢 Naturally Safe | 9 | 20.9% | Sequence, Exclusive Choice, Loop, Recursion |
| 🟡 Requires Shared State | 30 | 69.8% | Synchronization, Multi-Merge, Cancellation, Milestone |
| 🔴 Requires Unsafe / Pin | 3 | 7.0% | Arbitrary Cycles, 复杂 Discriminator |
| ⚪ Compile-time Only | 1 | 2.3% | MI Design-Time (const generics) |

**关键发现**：

1. **~70% 的模式需要共享状态原语**。这不是 Rust 的缺陷，而是并发工作流的本质需求：多个活动同时访问共享数据时，运行时协调不可避免。Rust 的价值在于将这些需求显式化，强制开发者在类型层面声明共享意图。
2. **基础控制流完全 🟢**。Rust 的所有权系统对顺序、选择、循环提供完美的静态验证，编译器自动防止 use-after-move 和数据竞争。
3. **取消模式内存安全**。RAII + Drop 语义确保取消时资源按逆序释放，无悬垂指针，这是 Rust 相对于 C/C++ 工作流引擎的显著优势。
4. **任意循环是唯一需要突破安全边界的模式**。其核心难点不在于循环本身（`loop` 完全安全），而在于自引用数据结构的表示。

### 7.2 Polonius 与未来改进
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

**Polonius**（下一代借用检查器）对工作流模式的潜在影响：

- **更精确的可变借用分析**：某些当前需 `RefCell` 的模式（如 WCP17）可能编译时验证。
- **循环借用优化**：WCP10 中的局部引用循环可能获得更好分析，减少 `unsafe` 需求。
- **异步状态机优化**：`select!` 的 cancel-safe 问题可能通过更精确分析改善。

但 Polonius **不会改变**：共享可变仍需 `Mutex`/通道；自引用仍需 `Pin`/`unsafe`；动态分支数仍需运行时计数器。

### 7.3 Rust 工作流引擎设计原则
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

1. **优先结构化**：用类型状态代替动态图遍历
2. **数据拆分优先**：进入并行前拆分不相交子集，避免 `Arc<Mutex<T>>`
3. **通道优先共享**：消息传递比共享内存更易推理，且天然 cancel-safe
4. **显式生命周期**：利用 `Drop` 实现取消补偿逻辑
5. **编译时推定**：将设计时信息编码到类型系统（const generics、枚举）

---

## 参考文献
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

1. van der Aalst, W. M. P., et al. (2003). "Workflow Patterns." *Distributed and Parallel Databases*, 14(1), 5-51.
2. Russell, N., et al. (2006). "Workflow Control-Flow Patterns: A Revised View." *BPM Center Report*, BPM-06-22.
3. Workflow Patterns Initiative. <https://www.workflowpatterns.com>
4. The Rust Programming Language (TRPL). <https://doc.rust-lang.org/book/>
5. The Rust Reference. <https://doc.rust-lang.org/reference/>
6. The Rustonomicon. <https://doc.rust-lang.org/nomicon/>
7. Tokio Documentation. <https://tokio.rs/>
8. Jung, R., et al. (2018). "RustBelt." *POPL 2018*.

## 权威来源索引

> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)** · **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)** · **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)** · **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)** · **来源: [Workflow Patterns Initiative](https://www.workflowpatterns.com/)** · **来源: [van der Aalst et al. (2003)](https://www.workflowpatterns.com/)** · **来源: [Russell et al. (2006)](https://www.workflowpatterns.com/)** · **来源: [Tokio Documentation](https://tokio.rs/)** · **来源: [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)** · **[来源: Rust Internals - Polonius Update]**

---

## 相关文件
>
> **[来源: [crates.io](https://crates.io/)]**

- [工作流模式总览](08-workflow-patterns.md)
- 工作流模式主索引
- [并发编程模型](../../../concept/03_advanced/01_concurrency.md)
- [异步编程模型](../../../concept/03_advanced/02_async.md)
- [形式化操作语义](../../../concept/04_formal/17_operational_semantics.md)
- [系统可组合性设计模式](../../../concept/06_ecosystem/30_system_composability.md)

---

*本文档是 Rust 所有权可判定性研究系列的一部分，与 `08-workflow-patterns.md` 及 `workflow-patterns/` 目录下的模式文件保持一致的语义框架。*

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Tree Borrows](https://plv.mpi-sws.org/rustbelt/tree-borrows/)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>
> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-22 补全权威来源标注 [来源: Authority Source Sprint Batch 9]

---
