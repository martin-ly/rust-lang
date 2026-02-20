# 执行模型边界分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📊 目录

- [执行模型边界分析](#执行模型边界分析)
  - [📊 目录](#-目录)
  - [五模型 × 三维边界](#五模型--三维边界)
  - [形式化定义](#形式化定义)
  - [执行确定性形式化](#执行确定性形式化)
  - [Rust 1.93 执行模型相关变更](#rust-193-执行模型相关变更)
  - [静态判定 vs 运行时验证](#静态判定-vs-运行时验证)
  - [确定性判定决策树](#确定性判定决策树)
  - [并发 vs 并行判定](#并发-vs-并行判定)
  - [并发选型决策树（Actor、channel、async、Mutex）](#并发选型决策树actorchannelasyncmutex)
  - [决策树：选择执行模型](#决策树选择执行模型)
  - [执行模型与设计模式映射](#执行模型与设计模式映射)
  - [边界证明思路](#边界证明思路)
  - [常见组合](#常见组合)
  - [与形式化基础衔接](#与形式化基础衔接)
    - [相关思维表征](#相关思维表征)

---

## 五模型 × 三维边界

| 模型 | 安全 | 支持 | 表达 |
| :--- | :--- | :--- | :--- |
| 同步 | 纯 Safe | 原生 | 等价 |
| 异步 | 纯 Safe | 库 | 等价 |
| 并发 | 纯 Safe | 原生 | 等价 |
| 并行 | 纯 Safe | 库/原生 | 等价 |
| 分布式 | Safe/unsafe | 库 | 近似 |

---

## 形式化定义

**Def 1.1（执行模型边界）**:

设 $M$ 为执行模型（同步/异步/并发/并行/分布式），$B_s$ 为安全边界，$B_p$ 为支持边界，$B_e$ 为表达边界。则：

- $B_s(M) \in \{\mathrm{Safe}, \mathrm{Unsafe}, \mathrm{Inexpressible}\}$
- $B_p(M) \in \{\mathrm{Native}, \mathrm{Library}, \mathrm{FFI}\}$
- $B_e(M) \in \{\mathrm{Equivalent}, \mathrm{Approximate}, \mathrm{Inexpressible}\}$

**Axiom EB1**：同步为默认模型；其余模型为同步的扩展或组合。

**Axiom EB2**：异步与并发可组合（async + 多任务）；并行与分布式可组合（多节点并行）。

**定理 EB-T1（五模型安全边界）**：同步、异步、并发、并行均为纯 Safe；分布式在 FFI 场景需 unsafe，可封装为 Safe。

*证明*：由 [01_synchronous](01_synchronous.md) SY-T2、[02_async](02_async.md) AS-T1、[03_concurrent](03_concurrent.md) CC-T1、[04_parallel](04_parallel.md) PL-T1、[05_distributed](05_distributed.md) DI-T1；各模型形式化文档已给出与 ownership/borrow/type_system 的衔接。

**定理 EB-T2（边界一致性）**：$B_s$、$B_p$、$B_e$ 与 [05_boundary_system](../05_boundary_system/) 三维矩阵一致。

*证明*：Def 1.1 中 $B_s$、$B_p$、$B_e$ 取值与 safe_unsafe_matrix、supported_unsupported_matrix、expressive_inexpressive_matrix 定义一致。

**引理 EB-EX-L1**：五模型互斥覆盖常见执行需求；对任意需求「单机/多机 × I/O/CPU × 并发/顺序」，存在唯一或组合模型。

*证明*：由决策树穷尽分支；同步、异步、并发、并行、分布式对应不同需求组合。∎

**推论 EB-EX-C1**：若需求为「单机 + I/O 并发」，则选异步；若为「单机 + CPU 并行」，则选并行；由 Axiom EB1、EB2。

**引理 EB-EX-L2（组合模型边界）**：异步 + 并发、并行 + 同步等组合模型的 $B_s$、$B_p$、$B_e$ 取各子模型的最严约束。

*证明*：由 Axiom EB2；组合时若任一子模型需 unsafe，则组合需 unsafe；支持取 max（Native < Lib < FFI）；表达取 min（Equivalent > Approximate > Inexpressible）。∎

**推论 EB-EX-C2**：五模型与 [05_boundary_system](../05_boundary_system/) 三维矩阵一致；执行模型选型可复用安全/支持/表达决策树。

---

## 执行确定性形式化

**Def EB-DET1（执行确定性）**：

设 $M$ 为执行模型。**执行确定性** $\mathit{Det}(M) \in \{\mathrm{Sequential}, \mathrm{Interleaved}, \mathrm{Parallel}, \mathrm{Distributed}\}$ 定义如下：

- **Sequential**：单线程顺序执行；执行顺序完全确定；同步模型
- **Interleaved**：多任务交错执行；调度非确定，但无数据竞争；异步、并发（消息传递）
- **Parallel**：多核同时执行；任务间可能同时运行；并行（rayon、join）
- **Distributed**：跨节点；网络延迟与故障非确定；分布式

**Axiom EB-DET1**：$\mathit{Det}(\mathrm{Sync}) = \mathrm{Sequential}$；$\mathit{Det}(\mathrm{Async}) = \mathit{Det}(\mathrm{Concurrent}) = \mathrm{Interleaved}$；$\mathit{Det}(\mathrm{Parallel}) = \mathrm{Parallel}$；$\mathit{Det}(\mathrm{Distributed}) = \mathrm{Distributed}$。

**定理 EB-DET-T1（确定性蕴涵数据竞争自由）**：若 $M$ 为 Sync、Async、Concurrent 或 Parallel，且程序满足 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) 定理 T1（数据竞争自由）及 Send/Sync 约束，则执行无数据竞争；执行顺序的非确定性不导致 UB。

*证明*：由 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) T1；Send/Sync 保证跨线程传递安全；ownership/borrow 保证无别名违规；Interleaved/Parallel 的调度非确定性仅影响执行顺序，不影响内存安全。∎

**推论 EB-DET-C1（控制确定性判定）**：对于「需保证执行顺序」的需求，选 Sync；对于「可接受非确定调度」的 I/O 并发，选 Async；对于「需 CPU 并行」的需求，选 Parallel；由 Def EB-DET1 与决策树。

---

## Rust 1.93 执行模型相关变更

以下 Rust 1.93 变更影响执行模型与并发/并行设计；详见 [07_rust_1.93_full_changelog](../../../06_toolchain/07_rust_1.93_full_changelog.md)、[05_rust_1.93_vs_1.92_comparison](../../../06_toolchain/05_rust_1.93_vs_1.92_comparison.md)。

| 变更 | 影响 | 说明 |
| :--- | :--- | :--- |
| **全局分配器 thread_local** | 并发/异步 | 1.93 允许全局分配器使用 `thread_local!` 和 `std::thread::current()` 而无重入担忧；影响自定义分配器与 async 运行时的组合 |
| **asm_cfg** | 底层/并行 | `#[cfg]` 可应用于 `asm!` 块内单行；条件汇编与平台特定并行代码（如 SIMD）的交互更灵活 |
| **musl 1.2.5** | 分布式/网络 | 静态 musl 构建的 DNS 解析可靠性提升；影响分布式系统中 musl 目标 |

---

## 静态判定 vs 运行时验证

**Def EB-VER1（确定性判定可验证性）**：设 $M$ 为执行模型。**静态判定**：编译期可完全确定（`cargo check`、clippy）；**运行时验证**：需实际执行或额外工具（Miri、集成测试、模糊测试）才能判定。

| 情形 | 判定方式 | 说明 |
| :--- | :--- | :--- |
| **Sync、单线程** | 静态 | ownership、borrow、type_system 完全可静态检查 |
| **Async、Send 边界** | 静态 | Future 的 Send 约束、跨 await 点检查；编译器可判定 |
| **Concurrent、std::thread** | 静态 | Send/Sync 约束在 spawn 点检查；无数据竞争可静态保证 |
| **Parallel、rayon** | 静态 | join/scope 的闭包需 Send；编译器可判定 |
| **死锁** | 运行时 | 锁顺序、循环等待无法静态判定；需 Miri、测试 |
| **分布式、网络故障** | 运行时 | 超时、重试、一致性需集成测试、契约验证 |

**决策分支**：需确定性保证？→ 静态可判定（Sync/Async/Concurrent/Parallel 满足 Send/Sync）→ 选上述模型；需死锁自由？→ 运行时验证；需分布式一致性？→ 契约 + 集成测试。

---

## 确定性判定决策树

```text
需求：执行顺序是否必须确定？
├── 是（顺序敏感）→ 同步（Sync）
│   └── 单线程；Determinism = Sequential
└── 否（可接受非确定）
    ├── 需求：跨节点？
    │   └── 是 → 分布式（Distributed）
    │       └── 网络延迟、故障非确定
    └── 否（单节点）
        ├── 需求：I/O 并发？
        │   └── 是 → 异步（Async）
        │       └── Interleaved；调度非确定，无数据竞争
        ├── 需求：CPU 并行？
        │   └── 是 → 并行（Parallel）
        │       └── Parallel；多核同时，任务完成顺序非确定
        └── 否则 → 并发（Concurrent）
            └── Interleaved；消息传递或锁保护
```

---

## 并发 vs 并行判定

| 维度 | 并发 (Concurrent) | 并行 (Parallel) |
| :--- | :--- | :--- |
| **定义** | 多任务可交错执行；不必同时运行 | 多任务可同时运行；利用多核 |
| **执行** | 单核可模拟；调度器交错 | 多核/多 CPU 同时执行 |
| **确定性** | Interleaved；调度非确定 | Parallel；完成顺序非确定 |
| **典型** | std::thread + mpsc、tokio 多任务 | rayon、join、std::thread 多核 |
| **选型** | I/O 等待、事件驱动 | CPU 密集、数据并行 |

**判定树**：需要 I/O 并发（等待网络/磁盘）→ 选 Async/Concurrent；需要 CPU 并行（计算密集）→ 选 Parallel。

---

## 并发选型决策树（Actor、channel、async、Mutex）

**用途**：在已选定「并发」模型后，进一步选择 Actor、channel、async、Mutex 等具体机制；与 [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) CHAN-T1、MUTEX-T1 形式化衔接。

```text
并发场景细分
├── 需 I/O 并发（网络、磁盘、定时器）？
│   └── 是 → async/await（tokio、async-std）
│       └── 形式化：async_state_machine T6.1–T6.3；Send 跨 await
├── 需共享可变状态？
│   ├── 是、且临界区短 → Mutex/RwLock
│   │   └── 形式化：MUTEX-T1；任一时刻至多一个 &mut T
│   └── 是、且临界区长 → 考虑 channel 解耦，避免持锁过久
├── 需消息传递、无共享可变？
│   ├── 一对一、多生产者单消费者 → mpsc
│   │   └── 形式化：CHAN-T1；消息传递无共享可变
│   ├── 一对多广播 → broadcast
│   └── 多 Actor、每 Actor 独立状态 → Actor（actix、bastion）
│       └── 形式化：每 Actor 独占状态；消息传递；与 CHAN-T1 一致
└── 需 CPU 并行 → rayon、join（见上文并行判定）
```

| 机制 | 适用场景 | 形式化边界 | crate |
| :--- | :--- | :--- | :--- |
| **async** | I/O 并发、高连接数 | T6.1–T6.3、Send 约束 | tokio、async-std |
| **channel (mpsc)** | 生产者-消费者、任务分发 | CHAN-T1 | std::sync::mpsc |
| **Mutex** | 共享可变、短临界区 | MUTEX-T1 | std::sync::Mutex |
| **Actor** | 独立状态、消息驱动 | 每 Actor 独占；消息即 channel | actix、bastion |

**选型原则**：优先 channel 解耦，避免共享可变；若必须共享则 Mutex；I/O 密集用 async。

---

## 决策树：选择执行模型

```text
需要跨节点通信？
├── 是 → 分布式（tonic、actix、surge）
└── 否 → 单节点
    ├── 需要并发执行？
    │   ├── 否 → 同步
    │   └── 是 → 需要 I/O 并发？
    │       ├── 是 → 异步（tokio、async-std）
    │       └── 否 → 需要 CPU 并行？
    │           ├── 是 → 并行（rayon、std::thread）
    │           └── 否 → 并发（std::thread、mpsc）
    └── （仅顺序执行）→ 同步
```

---

## 执行模型与设计模式映射

| 执行模型 | 相关设计模式 | 说明 |
| :--- | :--- | :--- |
| 同步 | 全部 23 | 默认顺序执行 |
| 异步 | Observer（channel）、Command（Future）、State | Future 即可恢复的 Command |
| 并发 | Singleton（OnceLock）、Observer（mpsc）、Mediator | 共享状态需 Send/Sync |
| 并行 | Strategy、Template Method、Iterator | 数据并行、任务并行 |
| 分布式 | Proxy、Gateway、DTO、Remote Facade、Actor | 跨进程/跨网络 |

---

## 边界证明思路

| 模型 | 安全证明要点 | 表达证明要点 |
| :--- | :--- | :--- |
| 同步 | 无共享可变；单线程所有权 | 顺序语义与 GoF 一致 |
| 异步 | Future 不共享可变；Pin 保证自引用安全 | async/await 等价于 Promise |
| 并发 | Send/Sync 静态保证；无数据竞争 | 强于 OOP（编译期检查） |
| 并行 | rayon 任务无共享可变；join 安全 | 数据并行、任务并行等价 |
| 分布式 | 序列化类型安全；FFI 需 unsafe 封装 | 无内置 RPC；库近似 |

---

## 常见组合

| 组合 | 说明 | 示例 |
| :--- | :--- | :--- |
| 异步 + 并发 | async 多任务 | tokio::spawn |
| 并行 + 同步 | 并行块内顺序 | rayon + 单线程段 |
| 分布式 + 异步 | RPC 异步 | tonic + async |
| 并发 +  Observer | 多线程事件 | mpsc + spawn |

---

## 与形式化基础衔接

| 模型 | 引用定理 | 文档 |
| :--- | :--- | :--- |
| 同步 | ownership T2/T3、borrow T1、type_system T1–T3 | [ownership_model](../../formal_methods/ownership_model.md)、[type_system_foundations](../../type_theory/type_system_foundations.md) |
| 异步 | async T6.1–T6.3（状态一致性、并发安全、进度保证）、pin T1–T3、Send 边界 | [async_state_machine](../../formal_methods/async_state_machine.md)、[pin_self_referential](../../formal_methods/pin_self_referential.md) |
| 并发 | borrow T1（数据竞争自由）、Send/Sync 语义、EB-DET-T1、CHAN-T1、MUTEX-T1 | [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md)、[async_state_machine](../../formal_methods/async_state_machine.md) |
| 并行 | 同上 + rayon 不变式、EB-DET-T1、SPAWN-T1 | [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md)、[async_state_machine](../../formal_methods/async_state_machine.md) |
| 分布式 | 序列化类型安全、FFI 契约 | [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](../../SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) |

**确定性形式化**：Def EB-DET1、定理 EB-DET-T1 与 [FORMAL_PROOF_SYSTEM_GUIDE](../../FORMAL_PROOF_SYSTEM_GUIDE.md) Send/Sync、borrow T1 衔接；静态 vs 运行时验证见 § [静态判定 vs 运行时验证](#静态判定-vs-运行时验证)；确定性判定决策树见上文。

---

### 相关思维表征

| 类型 | 位置 |
| :--- | :--- |
| 多维矩阵 | [README §执行模型多维对比矩阵](README.md#执行模型多维对比矩阵) |
| 决策树 | 本文 § 并发选型决策树、§ 决策树：选择执行模型；[DECISION_GRAPH_NETWORK](../../../04_thinking/DECISION_GRAPH_NETWORK.md) |

*依据*：[HIERARCHICAL_MAPPING_AND_SUMMARY](../../../HIERARCHICAL_MAPPING_AND_SUMMARY.md) § 文档↔思维表征。
