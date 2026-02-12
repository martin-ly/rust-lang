# 执行模型边界分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)

---

## 五模型 × 三维边界

| 模型 | 安全 | 支持 | 表达 |
|------|------|------|------|
| 同步 | 纯 Safe | 原生 | 等价 |
| 异步 | 纯 Safe | 库 | 等价 |
| 并发 | 纯 Safe | 原生 | 等价 |
| 并行 | 纯 Safe | 库/原生 | 等价 |
| 分布式 | Safe/unsafe | 库 | 近似 |

---

## 形式化定义

**Def 1.1（执行模型边界）**

设 $M$ 为执行模型（同步/异步/并发/并行/分布式），$B_s$ 为安全边界，$B_p$ 为支持边界，$B_e$ 为表达边界。则：

- $B_s(M) \in \{\mathrm{Safe}, \mathrm{Unsafe}, \mathrm{Inexpressible}\}$
- $B_p(M) \in \{\mathrm{Native}, \mathrm{Library}, \mathrm{FFI}\}$
- $B_e(M) \in \{\mathrm{Equivalent}, \mathrm{Approximate}, \mathrm{Inexpressible}\}$

**Axiom EB1**：同步为默认模型；其余模型为同步的扩展或组合。

**Axiom EB2**：异步与并发可组合（async + 多任务）；并行与分布式可组合（多节点并行）。

**定理 EB-T1（五模型安全边界）**：同步、异步、并发、并行均为纯 Safe；分布式在 FFI 场景需 unsafe，可封装为 Safe。

*证明*：由 [01_synchronous](01_synchronous.md) SY-T2、[02_async](02_async.md) AS-T1、[03_concurrent](03_concurrent.md)、[04_parallel](04_parallel.md)、[05_distributed](05_distributed.md)；各模型形式化文档已给出与 ownership/borrow/type_system 的衔接。

**定理 EB-T2（边界一致性）**：$B_s$、$B_p$、$B_e$ 与 [05_boundary_system](../05_boundary_system/) 三维矩阵一致。

*证明*：Def 1.1 中 $B_s$、$B_p$、$B_e$ 取值与 safe_unsafe_matrix、supported_unsupported_matrix、expressive_inexpressive_matrix 定义一致。

**引理 EB-EX-L1**：五模型互斥覆盖常见执行需求；对任意需求「单机/多机 × I/O/CPU × 并发/顺序」，存在唯一或组合模型。

*证明*：由决策树穷尽分支；同步、异步、并发、并行、分布式对应不同需求组合。∎

**推论 EB-EX-C1**：若需求为「单机 + I/O 并发」，则选异步；若为「单机 + CPU 并行」，则选并行；由 Axiom EB1、EB2。

**引理 EB-EX-L2（组合模型边界）**：异步 + 并发、并行 + 同步等组合模型的 $B_s$、$B_p$、$B_e$ 取各子模型的最严约束。

*证明*：由 Axiom EB2；组合时若任一子模型需 unsafe，则组合需 unsafe；支持取 max（Native < Lib < FFI）；表达取 min（Equivalent > Approximate > Inexpressible）。∎

**推论 EB-EX-C2**：五模型与 [05_boundary_system](../05_boundary_system/) 三维矩阵一致；执行模型选型可复用安全/支持/表达决策树。

---

## 决策树：选择执行模型

```
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
|----------|--------------|------|
| 同步 | 全部 23 | 默认顺序执行 |
| 异步 | Observer（channel）、Command（Future）、State | Future 即可恢复的 Command |
| 并发 | Singleton（OnceLock）、Observer（mpsc）、Mediator | 共享状态需 Send/Sync |
| 并行 | Strategy、Template Method、Iterator | 数据并行、任务并行 |
| 分布式 | Proxy、Gateway、DTO、Remote Facade、Actor | 跨进程/跨网络 |

---

## 边界证明思路

| 模型 | 安全证明要点 | 表达证明要点 |
|------|--------------|--------------|
| 同步 | 无共享可变；单线程所有权 | 顺序语义与 GoF 一致 |
| 异步 | Future 不共享可变；Pin 保证自引用安全 | async/await 等价于 Promise |
| 并发 | Send/Sync 静态保证；无数据竞争 | 强于 OOP（编译期检查） |
| 并行 | rayon 任务无共享可变；join 安全 | 数据并行、任务并行等价 |
| 分布式 | 序列化类型安全；FFI 需 unsafe 封装 | 无内置 RPC；库近似 |

---

## 常见组合

| 组合 | 说明 | 示例 |
|------|------|------|
| 异步 + 并发 | async 多任务 | tokio::spawn |
| 并行 + 同步 | 并行块内顺序 | rayon + 单线程段 |
| 分布式 + 异步 | RPC 异步 | tonic + async |
| 并发 +  Observer | 多线程事件 | mpsc + spawn |

---

## 与形式化基础衔接

| 模型 | 引用定理 | 文档 |
|------|----------|------|
| 同步 | ownership T2/T3、borrow T1、type_system T1–T3 | [ownership_model](../../formal_methods/ownership_model.md)、[type_system_foundations](../../type_theory/type_system_foundations.md) |
| 异步 | async T6.1–T6.3、pin T1–T3 | [async_state_machine](../../formal_methods/async_state_machine.md)、[pin_self_referential](../../formal_methods/pin_self_referential.md) |
| 并发 | borrow T1、Send/Sync 语义 | [borrow_checker_proof](../../formal_methods/borrow_checker_proof.md) |
| 并行 | 同上 + rayon 不变式 | 同上 |
| 分布式 | 序列化类型安全、FFI 契约 | [SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](../../SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md) |
