# Send/Sync 形式化

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024) ✅
> **状态**: ✅ 已完成 (100%)
> **并表**: [README §formal_methods 六篇并表](README.md#formal_methods-六篇并表) 第 6 行（Send/Sync）

---

## 📊 目录

- [Send/Sync 形式化](#sendsync-形式化)
  - [📊 目录](#-目录)
  - [🎯 研究目标](#-研究目标)
    - [核心问题](#核心问题)
    - [预期成果](#预期成果)
  - [📚 理论基础](#-理论基础)
  - [🔬 形式化定义](#-形式化定义)
  - [定理与引理](#定理与引理)
  - [⚠️ 反例](#️-反例)
  - [🌳 公理-定理证明树](#-公理-定理证明树)
  - [🔗 与 spawn/Future/Arc 衔接](#-与-spawnfuturearc-衔接)
    - [相关思维表征](#相关思维表征)
  - [📖 参考文献](#-参考文献)

---

## 🎯 研究目标

对 Rust 的 **Send** 与 **Sync** 做独立形式化：给出概念定义、属性关系、解释论证与形式证明，并与其他形式化文档（ownership、borrow、async、pin）衔接。

### 核心问题

1. **Send/Sync 的形式化定义**：如何用数学语言精确描述「可安全跨线程转移」与「可安全跨线程共享引用」？
2. **属性关系**：$T : \text{Sync} \Leftrightarrow \&T : \text{Send}$ 如何形式化并用于证明？
3. **与并发原语衔接**：thread::spawn、Future、Arc、通道、Mutex 如何依赖 Send/Sync？

### 预期成果

- Send/Sync 的 Def 与定理（SEND1、SYNC1、SEND-T1、SYNC-T1、SYNC-L1）
- 反例索引（Rc !Send、Cell !Sync、非 Send 闭包 spawn）
- 与 [async_state_machine](async_state_machine.md)、[borrow_checker_proof](borrow_checker_proof.md)、[ownership_model](ownership_model.md) 的双向链接

---

## 📚 理论基础

- **Send**：类型可以**安全地跨线程转移所有权**。若值从线程 $t_1$ 转移到 $t_2$，则 $t_1$ 不再访问该值，且 $t_2$ 的访问满足单线程内存与借用规则。
- **Sync**：类型可以**安全地跨线程共享引用**。即多线程同时持有 `&T` 时，不产生数据竞争（无共享可变或由同步原语保护）。
- **关系**：$T : \text{Sync} \Leftrightarrow \&T : \text{Send}$（Rust 标准库定义）；即「可共享引用」等价于「引用类型可跨线程传递」。
- **可判定性**：Send/Sync 由**编译期**类型检查判定；违反则编译错误。

**与 Rc/Arc/Cell 的关系**：见 [ownership_model](ownership_model.md) Def RC1/ARC1/CELL1。`Rc: !Send`（非原子计数）；`Arc: Send + Sync` 当 $T: \text{Send} + \text{Sync}$；`Cell: !Sync`（内部可变无同步）。

---

## 🔬 形式化定义

**Def SEND1（Send）**：类型 $\tau$ 满足 **Send** 当且仅当：将 $\tau$ 的值从线程 $t_1$ 转移到线程 $t_2$ 后，$t_1$ 不再持有或访问该值，且 $t_2$ 上的使用满足单线程内存安全与 [borrow_checker_proof](borrow_checker_proof.md) 借用规则。形式化谓词：

$$\text{Send}(\tau) \leftrightarrow \forall v:\tau,\, t_1,\, t_2.\ \text{SafeTransfer}(v, t_1, t_2)$$

其中 $\text{SafeTransfer}(v, t_1, t_2)$ 表示：$v$ 在 $t_1$ 上创建或持有，转移至 $t_2$ 后，$t_1$ 不再访问 $v$，且 $t_2$ 上对 $v$ 的访问满足内存安全与借用规则。

**Def SYNC1（Sync）**：类型 $\tau$ 满足 **Sync** 当且仅当：多线程共享不可变引用 $\& \tau$ 时，无数据竞争。形式化谓词：

$$\text{Sync}(\tau) \leftrightarrow \forall t.\ \text{SafeShare}(\& \tau, t)$$

其中 $\text{SafeShare}(\& \tau, t)$ 表示：在任意线程 $t$ 上持有 $\& \tau$ 时，与其他线程对同一 $\tau$ 的访问不构成数据竞争（无并发写或未同步的读写）。

**等价形式（Rust 标准）**：

$$\text{Sync}(\tau) \leftrightarrow \text{Send}(\& \tau)$$

---

## 定理与引理

**引理 SYNC-L1（Sync 与 Send 等价）**：$T : \text{Sync} \Leftrightarrow \&T : \text{Send}$。

*证明*：由 Rust 标准库定义；多线程共享 `&T` 等价于将 `&T` 作为值跨线程传递，故 Sync 与 &T: Send 等价。∎

**定理 SEND-T1（跨线程转移安全）**：若 $T : \text{Send}$，则将 $v:T$ 从线程 $t_1$ 转移至 $t_2$ 后，程序在 [borrow_checker_proof](borrow_checker_proof.md) 与 [ownership_model](ownership_model.md) 意义下保持内存安全与数据竞争自由。

*证明*：由 Def SEND1，转移后 $t_1$ 不再访问 $v$，故无跨线程别名；$t_2$ 上单线程使用满足 ownership/borrow 规则。与 [borrow_checker_proof](borrow_checker_proof.md) 定理 T1 数据竞争自由一致。∎

**定理 SYNC-T1（跨线程共享引用安全）**：若 $T : \text{Sync}$，则多线程同时持有 $\&T$ 不引入数据竞争。

*证明*：由 Def SYNC1 与 SYNC-L1；$\&T : \text{Send}$ 保证引用可跨线程传递，且不可变引用允许多读者、无写，故无数据竞争。与 [async_state_machine](async_state_machine.md) 定理 6.2 中 Sync 约束一致。∎

**定理 SEND-SYNC-T1（spawn 数据竞争自由）**：若闭包类型 $F$ 满足 $F : \text{Send} + \text{'static}$，则 `thread::spawn(|| body)` 与 [async_state_machine](async_state_machine.md) Def SPAWN1、定理 SPAWN-T1 一致，跨线程无数据竞争。

*证明*：SPAWN1 要求闭包 `Send + 'static`；由 SEND-T1，捕获的 $T$ 转移至新线程后原线程不再访问，故满足数据竞争自由。∎

---

## ⚠️ 反例

| 反例 | 违反 | 结果 | 形式化对应 |
| :--- | :--- | :--- | :--- |
| `Rc<T>` 跨线程传递 | Send | 编译错误；若用 unsafe 则多线程持 Rc 导致计数竞态 | Def SEND1；[ownership_model](ownership_model.md) Def RC1 |
| `Cell<T>` 多线程共享 `&Cell<T>` | Sync | 编译错误；内部可变无同步，共享即数据竞争 | Def SYNC1；[ownership_model](ownership_model.md) Def CELL1 |
| 非 Send 闭包传入 `thread::spawn` | Send | 编译错误 | SPAWN1；[async_state_machine](async_state_machine.md) |
| 非 Send Future 在多线程运行时 poll | Send | 编译错误或 UB | [async_state_machine](async_state_machine.md) 定理 6.2 |
| `&T` 跨线程但 `T: !Sync` | Sync | 编译错误 | SYNC-L1 |

---

## 🌳 公理-定理证明树

```text
Def SEND1, SYNC1
├── SYNC-L1: T: Sync ⇔ &T: Send
├── SEND-T1: Send ⇒ 跨线程转移安全（与 borrow T1 一致）
├── SYNC-T1: Sync ⇒ 跨线程共享 &T 无数据竞争
└── SEND-SYNC-T1: spawn(Send + 'static) ⇒ 数据竞争自由（与 SPAWN-T1 一致）
    前提: [async_state_machine](async_state_machine.md) Def SPAWN1
```

---

## 🔗 与 spawn/Future/Arc 衔接

- **thread::spawn**：[async_state_machine](async_state_machine.md) Def SPAWN1、定理 SPAWN-T1。闭包需 `Send + 'static`；由 SEND-T1 保证转移后数据竞争自由。
- **Future 并发**：[async_state_machine](async_state_machine.md) 定理 6.2。多 Future 并发 poll 时，若各 Future 为 Send/Sync，则并发执行数据竞争自由；Send/Sync 语义与本篇 Def SEND1/SYNC1 一致。
- **Arc**：[ownership_model](ownership_model.md) Def ARC1。`Arc<T>: Send + Sync` 当 $T: \text{Send} + \text{Sync}$；跨线程共享 Arc 依赖 Sync。
- **通道 / Mutex**：[borrow_checker_proof](borrow_checker_proof.md) Def CHAN1、MUTEX1，定理 CHAN-T1、MUTEX-T1。发送端类型需 Send；与 SEND-T1 一致。

---

### 相关思维表征

| 类型 | 位置 |
| :--- | :--- |
| 思维导图 | [MIND_MAP_COLLECTION](../../04_thinking/MIND_MAP_COLLECTION.md) §5、C06；安全可判定机制节点 |
| 概念多维矩阵 | [README §六篇并表](README.md#formal_methods-六篇并表) 第 6 行；[SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN](SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN.md) §3.1 |
| 决策树 | [DESIGN_MECHANISM_RATIONALE](../DESIGN_MECHANISM_RATIONALE.md) § Send/Sync；[06_boundary_analysis](../software_design_theory/03_execution_models/06_boundary_analysis.md) 并发选型 |
| 推理证明树 | [PROOF_INDEX](../PROOF_INDEX.md)；本篇 § 公理-定理证明树 |

*依据*：[HIERARCHICAL_MAPPING_AND_SUMMARY](../HIERARCHICAL_MAPPING_AND_SUMMARY.md) § 文档↔思维表征。

---

## 📖 参考文献

- [Ferrocene FLS Ch. 17.1 Send and Sync](https://spec.ferrocene.dev/concurrency.html#send-and-sync)
- [RustBelt Meets Relaxed Memory POPL 2020](https://plv.mpi-sws.org/rustbelt/rbrlx/) — Arc、Send/Sync 与松弛内存
- [async_state_machine](async_state_machine.md) — Future 与 Send/Sync 约束、定理 6.2
- [DESIGN_MECHANISM_RATIONALE](../DESIGN_MECHANISM_RATIONALE.md) § Send/Sync — 设计理由与决策树

---

**维护者**: Rust Formal Methods Research Group
**最后更新**: 2026-02-14
**状态**: ✅ 已完成 (100%)
