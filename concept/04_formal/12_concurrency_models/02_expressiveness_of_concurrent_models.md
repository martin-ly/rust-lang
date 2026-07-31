> **内容分级**: [专家级]

# 并发模型表达能力比较（Expressiveness of Concurrent Models）

> **EN**: Expressiveness of Concurrent Models
> **Summary**: Comparing the expressive power of concurrent models via encodings, bisimulation, and Felleisen's expressiveness framework.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 从**编码、互模拟与 Felleisen 表达力框架**三个维度，比较共享内存、CSP、Actor、π 演算等并发模型的表达能力边界，并解释 Rust 的 `tokio::select!`、`async/await` 等原语在形式表达力坐标系中的位置。
> **前置概念**: [Async/Await](../../03_advanced/01_async/01_async.md) · [Models of Concurrency](01_models_of_concurrency.md) · [Process Calculi for Rust](../07_concurrency_semantics/01_process_calculi_for_rust.md) · [Actor Semantics](../07_concurrency_semantics/03_actor_semantics.md) · [Algorithm Equivalence](../08_algorithm_semantics/05_algorithm_equivalence.md)
> **后置概念**: [Distributed Systems Semantics](../09_system_semantics/04_distributed_systems_semantics.md) · [Reactive Systems Semantics](../09_system_semantics/05_reactive_systems_semantics.md) · [Five Models Definition Matrix](../../05_comparative/00_paradigms/04_five_models_definition_matrix.md)

---

> **来源**:
> [Felleisen, *On the Expressive Power of Programming Languages*, ESOP / LNCS 1990/1991](https://doi.org/10.1007/3-540-52592-0_60) ·
> [Sangiorgi & Walker, *The π-Calculus: A Theory of Mobile Processes*, Cambridge UP 2001](https://doi.org/10.1017/CBO9780511777683) ·
> [van Glabbeek, *The Linear Time – Branching Time Spectrum*, CONCUR 1990 / LNCS 458](https://doi.org/10.1007/BFb0030039) ·
> [Milner, *Communication and Concurrency*, Prentice Hall 1989](https://doi.org/10.5555/28251) ·
> [Herlihy & Shavit, *The Art of Multiprocessor Programming*, Morgan Kaufmann 2011](https://www.sciencedirect.com/book/9780123973375/the-art-of-multiprocessor-programming) ·
> [std::sync::mpsc — Rust 标准库文档](https://doc.rust-lang.org/std/sync/mpsc/) ·
> [Rust Reference — async blocks and closures](https://doc.rust-lang.org/reference/expressions/block-expr.html#async-blocks)
>
> ⚠️ **声明**: 本页讨论的是**形式模型之间的表达能力关系**，不是 Rust 编译器实现细节。「不可表达」指在 Felleisen 框架下需要改变语言语义或运行时观察集，而非单纯的"代码写起来麻烦"。

---

## 📑 目录

- [并发模型表达能力比较（Expressiveness of Concurrent Models）](#并发模型表达能力比较expressiveness-of-concurrent-models)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 表达能力的三把尺子](#11-表达能力的三把尺子)
    - [1.2 模型互编码：Actor → π 与 CSP → Actor](#12-模型互编码actor--π-与-csp--actor)
    - [1.3 互模拟：强、弱与观察等价](#13-互模拟强弱与观察等价)
    - [1.4 编码中必然丢失的语义](#14-编码中必然丢失的语义)
    - [1.5 Felleisen 表达力框架](#15-felleisen-表达力框架)
    - [1.6 Herlihy \& Shavit 并发进展条件](#16-herlihy--shavit-并发进展条件)
  - [二、Rust 实例：`tokio::select!` 与状态机](#二rust-实例tokioselect-与状态机)
  - [三、反例与边界](#三反例与边界)
    - [反例："Actor 与 π 演算表达能力相同"](#反例actor-与-π-演算表达能力相同)
    - [反例："只要加锁，共享内存就能模拟任意消息传递"](#反例只要加锁共享内存就能模拟任意消息传递)
    - [边界：公平性与故障模型不可编码保持](#边界公平性与故障模型不可编码保持)
    - [反例：Rust 类型系统对跨模型表达的编译期拦截](#反例rust-类型系统对跨模型表达的编译期拦截)
  - [四、定理链与相关概念](#四定理链与相关概念)
  - [五、认知路径](#五认知路径)
  - [International Authority References（国际权威来源）](#international-authority-references国际权威来源)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：编码与表达能力](#测验-1编码与表达能力)
    - [测验 2：强互模拟与弱互模拟](#测验-2强互模拟与弱互模拟)
    - [测验 3：`tokio::select!` 的表达力](#测验-3tokioselect-的表达力)
    - [测验 4：Actor 与 π 演算](#测验-4actor-与-π-演算)
    - [测验 5：共享内存模拟消息传递的边界](#测验-5共享内存模拟消息传递的边界)
  - [🧭 思维导图（Mindmap）](#-思维导图mindmap)

---

## 一、核心概念

### 1.1 表达能力的三把尺子

比较两个并发模型 "A 比 B 更具表达力" 之前，必须先固定**比较标准**。形式语义中常用三把尺子（共享内存并发模型的工程语义与线性化理论由 Herlihy & Shavit, 2011 系统总结；进程代数中函数式计算与并发进程的对应关系则由 Milner, 1992 的 *Functions as Processes* 奠定）：

```text
1. 编码能力（Encodability）
   是否存在一个编译（编码）函数 ⟦·⟧，把模型 A 的任意进程 P 翻译成模型 B 的进程 ⟦P⟧，
   使得 A 中可观察的行为在 B 中保持（通常要求某种形式等价）。

2. 互模拟等价（Bisimulation）
   两个系统能否被环境无限期地混淆；强互模拟要求步数一一对应，弱互模拟允许忽略内部 τ 步。

3. Felleisen 表达力（Expressiveness Framework）
   语言 L₂ 比 L₁ 更具表达力，当且仅当：
   (a) 存在一个从 L₁ 到 L₂ 的*局部*翻译（不改变程序其余部分的语义）；
   (b) 存在 L₂ 程序，其在 L₁ 中*没有*行为等价的对应物（即 L₂ 能区分原 L₁ 程序无法区分的观察）。
```

> **关键区分**: 编码只要求"能翻译"；Felleisen 进一步要求"翻译是模块化的"且"新增了真实区分能力"。后者更贴近工程问题：把 `select!` 从 Rust 语言中拿掉，能否用纯库完全替代？

---

### 1.2 模型互编码：Actor → π 与 CSP → Actor

**Actor → π 演算**是教科书中经典的**保行为编码**（Sangiorgi & Walker 2001, §15）：

```text
actor 地址 a        ⟼  π 演算中的通道名 a
邮箱中的消息 m      ⟼  在途消息 ⟨a, m⟩，表示为在通道 a 上发送的消息包
行为 become b'      ⟼  递归进程定义 μX. 处理输入后重新展开为 X'
创建新 actor        ⟼  (νx) 新建私有通道名 x 并通知调度器
```

π 演算只有"通道"没有"进程名"，因此 actor 的**地址**被编码为一条通道：其他进程向该通道发送消息即相当于向 actor 发送。调度器（mail system）用一个中心进程或分布式规则把消息派送给对应的行为体。

**CSP → Actor** 的编码则**不对称**（更多限制）：

```text
CSP 通道 c          ⟼  一个"通道 actor" C，持有消息队列
进程 P 的输入 c?x   ⟼  P 向 C 发送 request，C 回复消息包
进程 P 的输出 c!v   ⟼  P 向 C 发送 v
外部选择 P [] Q     ⟼  P 与 Q 同时向多个通道 actor 发请求，取先到达者
```

这里的问题在于 CSP 的**会合（rendezvous）**要求发送与接收同步发生；Actor 模型是**异步邮箱**，消息发送后立即返回。要用 Actor 模拟一次 CSP 会合，必须引入 request-response（两次异步消息）加锁确认，这会改变故障语义：如果接收 actor 在确认前崩溃，发送方对"消息是否已被接收"的观测与 CSP 不同。

> **类型化协议的额外约束**：上述编码只保证语法可译；若引入 session types（Honda 1993; Gay & Hole 2005; Wadler 2012），通道两端的类型必须互为对偶，某些看似可行的编码会因破坏线性使用或对偶性而被类型系统拒绝。这相当于在表达能力比较中再增加一条「类型安全保持」的尺子。

---

### 1.3 互模拟：强、弱与观察等价

互模拟回答"两个并发系统何时可互换"。设迁移系统状态为 `S`，动作标签为 `Act`（含内部动作 `τ`）：

```text
强互模拟（Strong Bisimulation）:
  R 是强互模拟 ⟺ 若 (s, t) ∈ R，且 s ─α→ s'，则存在 t' 使 t ─α→ t' 且 (s', t') ∈ R（反之亦然）。
  强互模拟等价 ~ 要求内部 τ 步也一一对应。

弱互模拟（Weak/Observational Bisimulation）:
  只要求*外部可见动作*匹配，τ 步可以任意插入或省略。
  弱互模拟等价 ≈ 是工程上更常用的"行为相同"。
```

在 Rust 语境中，

```rust
use std::sync::{Arc, Mutex};

fn main() {
    // 实现 A：显式锁
    let data = Arc::new(Mutex::new(0));
    let d1 = Arc::clone(&data);
    std::thread::spawn(move || { *d1.lock().unwrap() += 1; });
    *data.lock().unwrap() += 1;

    // 实现 B：通过 mpsc 串行化
    let (tx, rx) = std::sync::mpsc::channel::<i32>();
    std::thread::spawn(move || { tx.send(1).unwrap(); });
    let mut sum = 0;
    if let Ok(v) = rx.recv() { sum += v; }
    sum += 1;
}
```

如果观察集 `O` 只看"最终某个计数器是否增加了 2"，两个实现**可能**弱互模拟等价；但如果 `O` 包含"哪个线程先完成增量"或"是否发生锁竞争"，则不等价。互模拟不是实现本身的属性，而是**实现 + 观察集 + 等价关系**的三元关系。

---

### 1.4 编码中必然丢失的语义

即使存在从模型 A 到模型 B 的编码，以下语义性质通常**不能保持**：

| 性质 | 说明 | 例子 |
|:---|:---|:---|
| **公平性（Fairness）** | A 的调度假设消息最终会被处理 | Actor → π 编码若采用异步调度器，可能引入无限延迟 |
| **分布/位置（Distribution）** | A 中节点故障独立 | 编码到共享内存模型后，所有"节点"在同一个地址空间，故障不再独立 |
| **故障模型（Failure Model）** | A 中进程崩溃可观测 | CSP 经典语义没有崩溃；Rust 的 `SendError` 是一等可观测值 |
| **消息顺序（Message Order）** | A 中同一通道严格 FIFO | Actor 模型在途消息是多重集，编码后顺序必须由实现额外保证 |
| **同步/异步边界** | CSP 会合是原子握手 | 用异步消息 + 锁模拟时，握手被拆分为多步，原子性丢失 |

> **工程推论**: 当有人说"X 模型能表达 Y 模型"时，必须追问**保留了哪些观察集**；否则会把理论等价误解为工程可互换。

---

### 1.5 Felleisen 表达力框架

Felleisen（1991）提出：**比较两种语言/原语的表达力，要看"新增原语是否让语言能区分更多程序行为"**。形式化地，语言 `L'` 比 `L` 更具表达力，当且仅当：

```text
1. 存在从 L 到 L' 的局部翻译（local translation）⟦·⟧；
2. 存在 L' 程序 C' 与上下文 C[·]，使得：
     C[C'] 在 L' 中的行为无法被任何 L 程序在 L 的上下文中复现。
```

"局部"是关键：翻译只替换一个子表达式，不改变程序其余部分的控制结构。这正好对应工程问题——`tokio::select!` 是不是一个**纯宏**就能实现？如果不是，它就在 Felleisen 意义上增加了表达力。

> **Algebraic effects 作为表达力的另一条轴**：Plotkin & Pretnar (2009) 把效应操作的签名与解释器分离；Dolan et al. (2017) 进一步用 effect handlers 统一实现 async/await、异常、状态等语义。在 Felleisen 框架下，algebraic effects 通常比固定语义的 `async/await` 更具表达力，因为前者允许通过不同 handler 局部重解释同一套效应操作。

---

### 1.6 Herlihy & Shavit 并发进展条件

Herlihy & Shavit (2011) 从**共享内存并发对象**的角度给出另一组表达力/正确性分层——**进展条件（progress conditions）**：

```text
1. wait-free（无等待）
   每个线程都能在有限步内完成操作，无论其他线程是否被挂起、延迟或崩溃。

2. lock-free（无锁）
   系统整体持续进展：至少有一个线程能在有限步内完成操作。
   允许个别线程饥饿（starvation），但不允许全局死锁。

3. obstruction-free（无阻碍）
   如果线程在一段时间内单独运行（无其他线程竞争），则能在有限步内完成操作。
   允许活锁（livelock），只要最终能遇到无争用窗口。

4. blocking（基于锁）
   依赖互斥锁；若持有锁的线程被挂起，其他线程可能无限等待。
```

**与模型编码的关系**：wait-free/lock-free/obstruction-free 不是"能不能编码"的问题，而是"编码后是否保持**进展保证**"的问题。一个 wait-free 算法如果被人用锁重新实现，即使功能等价，也丢失了 wait-free 的进展语义。

**Rust 生态映射**：

| 进展条件 | Rust 生态代表 | 说明 |
|---|---|---|
| wait-free | `crossbeam::epoch`（部分路径）、无锁数据结构 | 最难实现，通常只用于核心原子操作 |
| lock-free | `crossbeam::queue`、`parking_lot::Mutex` 的某些算法 | 系统整体进展，但个别线程可能饥饿 |
| obstruction-free | 某些 STM（Software Transactional Memory）设计 | 本库未大规模使用 |
| blocking | `std::sync::Mutex`、`std::sync::RwLock` | 最常用，但依赖调度公平性 |

> **关键区分**：`parking_lot::Mutex` 在实现上可能使用自旋 + 阻塞，从外部契约看仍是 blocking；`crossbeam::queue` 的 `push`/`pop` 提供 lock-free 保证。选型时必须区分"实现没用锁"与"接口承诺 lock-free"。

**判定依据**：进展条件是**系统语义**层面的保证，不能仅通过功能测试验证；需要形式化论证（线性化 + 进展证明）或权威文档声明。

---

## 二、Rust 实例：`tokio::select!` 与状态机

`tokio::select!` 等待多个异步操作中的**第一个就绪者**，并执行对应分支。它看起来像宏，但无法仅通过普通过程宏在不改变 Rust 语义的情况下实现：

```rust,ignore
// tokio::select! 的工程形态（需 tokio 依赖）
use tokio::select;

async fn demo(rx: &mut tokio::sync::mpsc::Receiver<i32>, timer: &mut tokio::time::Interval) {
    select! {
        Some(v) = rx.recv() => println!("channel: {}", v),
        _ = timer.tick()    => println!("timeout"),
    }
}
```

为什么纯库宏不够？因为 `select!` 需要：

1. **同时轮询多个 Future**：每次 `poll` 必须按某种策略检查所有分支；
2. **在分支返回前保存其他分支的中间状态**：如果分支 A 返回 `Pending`，分支 B 已部分推进的状态不能丢失；
3. **在编译期生成一个枚举状态机**：这是 `async/await` 的核心机制，由编译器把异步函数转换为 `Future` 状态机。

```rust,ignore
// 一个"手写"的近似 select! 会迅速陷入状态爆炸：
enum Select2State<A, B> {
    Start { a: A, b: B },
    ADone { b: B },       // A 已完成，等待 B
    BDone { a: A },       // B 已完成，等待 A
    Done,
}

// 每增加一个分支，枚举状态数翻倍；对泛型、生命周期、Pin 的处理必须由编译器完成。
```

因此，`tokio::select!` 在 Felleisen 意义上**增加了表达力**：它依赖 Rust 编译器提供的 `async/await` 状态机转换。没有这一语言级机制，相同的可观察行为（"等待多 Future 先完成者"）无法通过纯过程宏局部实现而不引入显式手动状态机枚举。

> 注意：`select!` 在 Rust 中**不是没有它就写不出来**——任何熟练开发者都可以手写状态机——而是"无法在保持原上下文结构不变的前提下，用一个局部宏调用替换"。这正是 Felleisen "局部翻译"条件的意义。

---

## 三、反例与边界

### 反例："Actor 与 π 演算表达能力相同"

这个命题在**纯语法编码**意义下**成立**：存在从 Actor 到 π 演算的合理编码，也存在反向编码（通过命名通道 + 调度器）。但在**工程语义**意义下**不成立**，因为：

```text
❌ 错误推论: "既然能互相编码，Actor 和 π 演算在 Rust 中可以互换。"

正确表述:
  • Actor 模型有内置的*命名进程*和*异步、无保证顺序*的邮箱语义；
  • π 演算有*命名通道*和*移动性*（通道作为一等值传递）；
  • 互相编码后，Actor 的"单个 actor 崩溃不影响其他 actor"故障隔离语义
    在 π 演算编码中需要额外引入 failure detector / 监督树才能复现；
  • π 演算中通道作用域的*词法限制* (νx) 在 Actor 编码中需要显式撤销/传递能力管理。
```

因此，"表达能力相同"只在忽略**故障模型、分布位置、调度公平性**的抽象层面成立；一旦把这些纳入观察集，两者立刻可区分。

---

### 反例："只要加锁，共享内存就能模拟任意消息传递"

这个命题在**单地址空间、无故障**假设下可以成立，但在真实 Rust 程序中**边界明显**：

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    // 用共享内存 + 锁模拟"消息传递计数器"
    let counter = Arc::new(Mutex::new(0));
    let c = Arc::clone(&counter);
    thread::spawn(move || {
        let mut guard = c.lock().unwrap();
        *guard += 1;
        // 如果这里 panic，锁被 poison，共享状态语义与"消息已发送但未处理"不同
    });
    *counter.lock().unwrap() += 1;
}
```

当线程在持有锁时 panic，Rust 的 `Mutex` 会被**poison**——后续 `lock()` 返回 `PoisonError`。消息传递模型没有"锁 poison"这一概念；对应现象是"消息在途或处理者崩溃"，其观测方式（`RecvError`、`SendError`）完全不同。因此，共享内存编码**改变了故障观察集**。

---

### 边界：公平性与故障模型不可编码保持

| 原模型性质 | 编码后通常丢失 | 为什么重要 |
|:---|:---|:---|
| Actor 公平性：每条消息最终处理 | 在 π 编码中，调度器可能永远推迟某条消息 | 活性（liveness）证明失效 |
| CSP 同步会合 | 在 Actor 编码中拆分为 request-response | 原子性、故障原子性改变 |
| π 演算通道限制 `(νx)` | 在共享内存编码中，指针可任意泄漏 | 能力控制从类型/作用域退化为运行时约定 |
| Rust 线程 panic 传播 | 在经典进程代数中没有对应 | 失败模型是 Rust 独有的观测维度 |

> **边界总结**: 模型间编码保持的是**语法结构**和**某种弱行为等价**；公平性、分布、故障、消息顺序等"系统级语义"几乎必然需要在目标模型中重新建模。

### 反例：Rust 类型系统对跨模型表达的编译期拦截

Rust 的所有权、生命周期与 trait 系统会在编译期拒绝某些在形式模型中"语法可行"的程序。下列 `compile_fail` 示例说明表达力比较不能只看抽象语法，还要看类型系统是否允许相应实现落地。

**`Send`/`Sync` 边界违反（E0277）**：`Rc<T>` 不是 `Send`，不能跨线程移动；形式模型中"复制引用"在 Rust 中不可表达。

```rust,compile_fail,E0277
use std::rc::Rc;
use std::thread;

fn main() {
    let data = Rc::new(42);
    thread::spawn(move || {
        println!("{}", *data);
    });
}
```

**`async` 块捕获局部引用逃逸作用域（E0373）**：返回的 `Future` 不能持有对局部变量的引用。

```rust,compile_fail,E0373
fn make_future() -> impl std::future::Future<Output = ()> {
    let s = String::from("captured");
    async {
        println!("{}", s);
    }
}

fn main() {}
```

**π 演算通道移动性触发生命周期错误（E0597）**：把局部名字的引用作为消息传递，接收端在发送端作用域结束后仍使用该引用。

```rust,compile_fail,E0597
use std::sync::mpsc;

fn main() {
    let (tx, rx) = mpsc::channel::<&str>();
    let received: &str;
    {
        let local = String::from("mobility");
        tx.send(&local).unwrap();
        received = rx.recv().unwrap();
    }
    println!("{}", received);
}
```

**数据竞争被借用检查器拦截（E0499）**：同一作用域内不能同时存在两个可变借用。

```rust,compile_fail,E0499
fn main() {
    let mut data = 0;
    let r1 = &mut data;
    let r2 = &mut data;

    std::thread::scope(|s| {
        s.spawn(|| { *r1 += 1; });
        s.spawn(|| { *r2 += 1; });
    });
}
```

**通道类型协议错配（E0308）**：`Sender<i32>` 不接受 `String`，对应 session types 中的对偶类型不匹配。

```rust,compile_fail,E0308
use std::sync::mpsc;

fn main() {
    let (tx, _rx) = mpsc::channel::<i32>();
    tx.send("hello".to_string()).unwrap();
}
```

---

## 四、定理链与相关概念

| 编号 | 命题 | 前提 | 结论 |
|:---|:---|:---|:---|
| T-ECM-01 | Actor 可编码入 π 演算 | Sangiorgi & Walker 的地址-as-通道编码 | Actor 计算模型的行为可由 π 演算模拟（在忽略故障模型时） |
| T-ECM-02 | CSP 会合不可由异步 Actor 直接保持 | CSP 会合是原子握手；Actor send 是非阻塞返回 | CSP → Actor 编码必须引入额外同步协议，改变故障语义 |
| T-ECM-03 | 强互模拟 ⟹ 弱互模拟 | 弱互模拟定义更宽松 | 若两系统强互模拟，则必然弱互模拟；反之不成立 |
| T-ECM-04 | `tokio::select!` 非纯库可表达 | 需要编译器生成 Future 状态机 + 同时保存多分支中间状态 | 在 Felleisen 框架下，`select!` 增加 Rust async 表达力 |
| T-ECM-05 | 编码不保公平性/故障模型 | 公平性与故障是目标模型未定义的额外假设 | 跨模型等价声明必须显式限定观察集 |
| T-ECM-06 | wait-free ⟹ lock-free ⟹ obstruction-free | Herlihy & Shavit 进展条件层次 | 功能等价不保持进展条件；选型需区分接口契约与实现细节 |

**相关概念**:

- [Models of Concurrency](01_models_of_concurrency.md) —— 并发模型谱系的形式骨架
- [Process Calculi for Rust](../07_concurrency_semantics/01_process_calculi_for_rust.md) —— CSP/CCS/π 演算与 Rust 原语的对应
- [Actor Semantics](../07_concurrency_semantics/03_actor_semantics.md) —— Actor 三公理、监督树与 Rust 映射
- [Algorithm Equivalence](../08_algorithm_semantics/05_algorithm_equivalence.md) —— 观察等价、精化序与等价判据
- [Distributed Systems Semantics](../09_system_semantics/04_distributed_systems_semantics.md) —— 分布式、故障模型与一致性
- [Five Models Definition Matrix](../../05_comparative/00_paradigms/04_five_models_definition_matrix.md) —— 同步/并发/并行/异步/分布式五范式一页式导航

---

## 五、认知路径

> **认知路径**: 模型谱系 ⟹ 编码能力 ⟹ 互模拟等价 ⟹ 编码丢失的语义 ⟹ Felleisen 框架 ⟹ Herlihy & Shavit 进展条件 ⟹ Rust `select!` 实例 ⟹ 反例边界。

学习顺序建议：先读 [Models of Concurrency](01_models_of_concurrency.md) 建立各模型的形式骨架，再读本页理解它们之间的表达力关系；随后通过 [Process Calculi for Rust](../07_concurrency_semantics/01_process_calculi_for_rust.md) 与 [Actor Semantics](../07_concurrency_semantics/03_actor_semantics.md) 把理论落回 Rust 原语；最后在 [Five Models Definition Matrix](../../05_comparative/00_paradigms/04_five_models_definition_matrix.md) 中把五范式坐标补齐。

**核心推理链**: 编码存在 ⟹ 行为等价成立（在限定观察集下）⟹ 但公平性/故障/分布/顺序会丢失 ⟹ 工程选型时不能只看"能不能模拟"。

---

## International Authority References（国际权威来源）

- Felleisen, M. *On the Expressive Power of Programming Languages*. ESOP 1990 / LNCS 432, 1990, 351–375. [DOI](https://doi.org/10.1007/3-540-52592-0_60)（期刊版本：Science of Computer Programming 17(1–3), 1991, 35–75）
- Sangiorgi, D., Walker, D. *The π-Calculus: A Theory of Mobile Processes*. Cambridge University Press, 2001. [DOI](https://doi.org/10.1017/CBO9780511777683)
- van Glabbeek, R. J. *The Linear Time – Branching Time Spectrum*. CONCUR 1990 / LNCS 458, 1990, 278–297. [DOI](https://doi.org/10.1007/BFb0030039)
- Milner, R. *Communication and Concurrency*. Prentice Hall, 1989. [DOI](https://doi.org/10.5555/28251)
- Milner, R., Parrow, J., Walker, D. *A Calculus of Mobile Processes*. Information and Computation 100(1), 1992. [DOI](https://doi.org/10.1016/0890-5401(92)90008-4)
- Milner, R. *Communicating and Mobile Systems: the π-Calculus*. Cambridge University Press, 1999.
- Hoare, C. A. R. *Communicating Sequential Processes*. Communications of the ACM 21(8), 1978, 666–677. [DOI](https://doi.org/10.1145/359576.359585)
- Hoare, C. A. R. *Communicating Sequential Processes*. Prentice Hall, 1985.
- Hewitt, C. *Actor Model of Computation: Scalable Robust Information Systems*. arXiv:1008.1459, 2010. [arXiv](https://arxiv.org/abs/1008.1459)
- Honda, K. "Types for Dyadic Interaction." *CONCUR 1993*, LNCS 715, 1993, 509–523. [DOI](https://doi.org/10.1007/3-540-57208-2_35)
- Gay, S. J., Hole, M. "Subtyping for Session Types in the Pi Calculus." *Acta Informatica* 42(2–3), 2005, 191–225. [DOI](https://doi.org/10.1007/s00236-005-0177-z)
- Wadler, P. "Propositions as Sessions." *ICFP 2012*, 2012, 273–286. [DOI](https://doi.org/10.1145/2364527.2364568)
- Plotkin, G. D., Pretnar, M. "Handlers of Algebraic Effects." *ESOP 2009*, LNCS 5502, 2009, 80–94. [DOI](https://doi.org/10.1007/978-3-642-00590-9_7)
- Dolan, S., Eliopoulos, S., Hillerström, D., Madhavapeddy, A., Sivaramakrishnan, K. C., White, L. "Concurrent System Programming with Effect Handlers." *TFP 2017*, LNCS 10788, 2017, 98–117. [DOI](https://doi.org/10.1007/978-3-319-89719-6_6)
- Herlihy, M., Shavit, N. *The Art of Multiprocessor Programming*. Morgan Kaufmann, 2011. [ScienceDirect](https://www.sciencedirect.com/book/9780123973375/the-art-of-multiprocessor-programming)
- [std::sync::mpsc — Rust 标准库文档](https://doc.rust-lang.org/std/sync/mpsc/) —— Rust 通道语义与故障契约的官方来源
- [Rust Reference — async blocks and closures](https://doc.rust-lang.org/reference/expressions/block-expr.html#async-blocks) —— `async/await` 状态机转换的语言级说明
- [tokio::select! tutorial](https://tokio.rs/tokio/tutorial/select) —— `select!` 的工程用法（非官方 Rust，但为 tokio 生态权威文档）
- [RustBelt: securing the foundations of the Rust programming language](https://plv.mpi-sws.org/rustbelt/) —— MPI-SWS 对 Rust 所有权与并发原语的形式化基础
- [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/) —— Rust 官方异步编程书的权威参考
- [docs.rs: tokio::select!](https://docs.rs/tokio/latest/tokio/macro.select.html) —— tokio `select!` 宏的 API 文档与行为契约
- [Async await is stable](https://blog.rust-lang.org/2019/11/07/Async-await-stable.html) —— Rust 官方博客宣布 `async/await` 稳定的语言级说明

> **相关文件**: [同层：Models of Concurrency](01_models_of_concurrency.md) · [同层 07：Process Calculi](../07_concurrency_semantics/01_process_calculi_for_rust.md) · [同层 07：Actor Semantics](../07_concurrency_semantics/03_actor_semantics.md) · [同层 08：Algorithm Equivalence](../08_algorithm_semantics/05_algorithm_equivalence.md)
>
> **文档版本**: 1.0 ｜ **最后更新**: 2026-07-28 ｜ **状态**: ✅ 新建权威页（Rust 1.97 对齐）

---

## 嵌入式测验（Embedded Quiz）

### 测验 1：编码与表达能力

"存在从模型 A 到模型 B 的编码"意味着：

- A. A 和 B 在所有观察集下行为等价
- B. A 的任意进程可以翻译成 B 的进程，并在某种限定观察集下保持行为
- C. B 一定比 A 更具 Felleisen 表达力

<details>
<summary>✅ 答案</summary>

**B. A 的任意进程可以翻译成 B 的进程，并在某种限定观察集下保持行为**。

编码只保证在特定等价关系/观察集下行为保持；公平性、故障模型、消息顺序等系统级语义通常会丢失。A 过于绝对；C 混淆了"可编码"与"Felleisen 表达力增加"，后者还要求局部翻译和新增区分能力。

</details>

---

### 测验 2：强互模拟与弱互模拟

若两个 Rust 异步服务在所有外部可见请求/响应序列上不可区分，但内部 `poll` 次数不同，则它们至少满足：

- A. 强互模拟
- B. 弱互模拟
- C. 两者都不满足

<details>
<summary>✅ 答案</summary>

**B. 弱互模拟**。

弱互模拟忽略内部 τ 步（如状态机内部的额外 `poll`），只要求外部可见动作匹配。强互模拟要求步数一一对应，因此内部 `poll` 次数不同会打破强互模拟。

</details>

---

### 测验 3：`tokio::select!` 的表达力

`tokio::select!` 无法仅用一个普通过程宏在 Rust 中完全替代，主要原因是：

- A. tokio 的 API 是私有的
- B. 它需要编译器把异步函数转换为 Future 状态机，以同时保存多个分支的中间状态
- C. `select!` 使用的语法 Rust 解析器不支持

<details>
<summary>✅ 答案</summary>

**B. 它需要编译器把异步函数转换为 Future 状态机，以同时保存多个分支的中间状态**。

`select!` 依赖 `async/await` 状态机转换；手写等价代码需要显式维护枚举状态。A 和 C 都不是本质原因——tokio API 是公开的，Rust 解析器也能处理宏语法。

</details>

---

### 测验 4：Actor 与 π 演算

"Actor 与 π 演算表达能力相同"在哪种意义下最合理？

- A. 在包含故障模型和分布位置的工程语义下
- B. 在忽略故障模型、公平性和消息顺序的纯语法编码层面
- C. 在 Rust 运行时实现层面

<details>
<summary>✅ 答案</summary>

**B. 在忽略故障模型、公平性和消息顺序的纯语法编码层面**。

Actor → π 的经典编码只保证结构可译；一旦纳入故障模型、分布位置或公平性，两者立刻可区分。Rust 运行时实现同时包含线程、通道、actor 框架等，无法直接对应单一形式模型。

</details>

---

### 测验 5：共享内存模拟消息传递的边界

用 `Arc<Mutex<T>>` 模拟跨线程消息传递时，以下哪项是共享内存模型**不直接提供**、而消息传递模型拥有的语义？

- A. 对 `T` 的独占访问
- B. 发送方在接收方崩溃时得到显式 `SendError`
- C. 通过锁保护数据的能力

<details>
<summary>✅ 答案</summary>

**B. 发送方在接收方崩溃时得到显式 `SendError`**。

`Arc<Mutex<T>>` 中线程崩溃会导致锁 poison，但发送方不会收到类似 `SendError` 的显式反馈；消息传递模型则把"对端消失"作为一等可观测错误。A 和 C 都是共享内存模型能提供的。

</details>

---

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((并发模型表达能力比较))
    核心概念
      表达能力三把尺子
        编码能力
        互模拟等价
        Felleisen 框架
      Herlihy & Shavit 进展条件
        wait-free
        lock-free
        obstruction-free
      模型互编码
        Actor → π
        CSP → Actor 的限制
      互模拟
        强互模拟
        弱互模拟
      编码丢失的语义
        公平性
        分布位置
        故障模型
        消息顺序
    Rust 实例
      tokio::select!
      async/await 状态机
      非纯库可表达
    反例与边界
      Actor ≈ π 的限定条件
      共享内存模拟消息传递的故障语义差异
      公平性不可编码保持
    相关概念
      Models of Concurrency
      Process Calculi
      Actor Semantics
      Algorithm Equivalence
```

> **认知功能**: 本 mindmap 从本页章节结构提炼，一级分支对应核心主题，叶子节点为关键子概念，可作为本页的快速导航与复习索引。
