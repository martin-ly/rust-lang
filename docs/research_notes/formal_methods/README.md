# 🔬 形式化方法研究 {#-形式化方法研究}

> **创建日期**: 2025-01-27
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **docs 全结构**: [DOCS_STRUCTURE_OVERVIEW](../../DOCS_STRUCTURE_OVERVIEW.md) § 2.7 formal_methods

---

## ✅ 完备性声明 {#-完备性声明}

**本目录形式化论证已 100% 完成**。详见 [00_completeness_gaps](00_completeness_gaps.md)：

- **内存与所有权**：Box、Rc/Arc、Cell/RefCell、MaybeUninit、Deref/Drop、repr、const &mut static（Phase 1–6）
- **并发与异步**：通道、Mutex/RwLock、原子操作、thread::spawn（Phase 2、4、6）
- **FFI 与 unsafe**：裸指针、union、transmute、extern、C variadic（Phase 3、4、6）
- **控制流**：match、for、? 操作符（Phase 5、6）

**已完成**：所有权规则 1–8、借用规则、生命周期、Pin、async 状态机核心定理；Phase 1–6 全部形式化。✅ **100% 完成**。

---

## 控制流形式化

**Axiom A-CF1（控制流归约保持）**：若 $e$ 为控制流表达式（`if`/`loop`/`match`/`for`/`?`），$e \to e'$ 为一步归约，则 $\Gamma \vdash e : \tau \land e \to e' \Rightarrow \Gamma \vdash e' : \tau$。即控制流归约保持类型与所有权。

**与子文档衔接**：

- [borrow_checker_proof](borrow_checker_proof.md) Def MATCH1/FOR1/QUERY1、定理 MATCH-T1/FOR-T1/QUERY-T1
- [type_system_foundations](../type_theory/type_system_foundations.md) 定理 T2（保持性）、T3（类型安全）

---

## 📊 目录 {#-目录}

- [🔬 形式化方法研究 {#-形式化方法研究}](#-形式化方法研究--形式化方法研究)
  - [✅ 完备性声明 {#-完备性声明}](#-完备性声明--完备性声明)
  - [控制流形式化](#控制流形式化)
  - [📊 目录 {#-目录}](#-目录--目录)
  - [🎯 研究目标 {#-研究目标}](#-研究目标--研究目标)
  - [📚 研究主题 {#-研究主题}](#-研究主题--研究主题)
    - [1. 所有权模型形式化](#1-所有权模型形式化)
    - [2. 借用检查器证明](#2-借用检查器证明)
    - [3. 异步状态机形式化](#3-异步状态机形式化)
    - [4. 生命周期形式化](#4-生命周期形式化)
    - [5. Pin 和自引用类型形式化](#5-pin-和自引用类型形式化)
    - [6. Send/Sync 形式化](#6-sendsync-形式化)
    - [7. Actor 模型形式化 ⭐ 新增](#7-actor-模型形式化--新增)
  - [formal\_methods 六篇并表](#formal_methods-六篇并表)
  - [形式化论证汇总](#形式化论证汇总)
  - [公理-定理形式化索引](#公理-定理形式化索引)
  - [📝 研究笔记 {#-研究笔记}](#-研究笔记--研究笔记)
    - [已完成 ✅ {#已完成-}](#已完成--已完成-)
  - [🔗 相关资源 {#-相关资源}](#-相关资源--相关资源)
    - [核心文档](#核心文档)
    - [代码实现](#代码实现)
    - [学术资源](#学术资源)
  - [国际权威对标（Authoritative References）](#国际权威对标authoritative-references)
    - [权威来源对照表](#权威来源对照表)
    - [权威论文与规范（含链接）](#权威论文与规范含链接)
    - [与本目录的对应说明](#与本目录的对应说明)
    - [权威来源快速链接](#权威来源快速链接)
    - [Ferrocene FLS 章节与本目录对应](#ferrocene-fls-章节与本目录对应)
    - [国际权威奖项与认可](#国际权威奖项与认可)
  - [📖 研究方法 {#-研究方法}](#-研究方法--研究方法)
    - [形式化工具](#形式化工具)
    - [形式化方法](#形式化方法)
    - [证明策略](#证明策略)
  - [🚀 快速开始 {#-快速开始}](#-快速开始--快速开始)
    - [创建新的研究笔记](#创建新的研究笔记)
    - [研究流程](#研究流程)

---

## 🎯 研究目标 {#-研究目标}

本目录专注于 Rust 核心机制的形式化建模与证明，包括：

1. **所有权系统**：形式化定义所有权规则，证明内存安全
2. **借用检查器**：形式化借用规则，证明数据竞争自由
3. **异步系统**：形式化 Future/Poll 状态机，证明并发安全
4. **生命周期**：形式化生命周期语义，证明引用有效性

---

## 📚 研究主题 {#-研究主题}

### 1. 所有权模型形式化

**研究问题**:

- 如何形式化定义 Rust 的所有权规则？
- 如何证明所有权系统保证内存安全？
- 所有权转移的语义如何形式化表示？

**相关笔记**: [ownership_model.md](./ownership_model.md)

**状态**: ✅ 已完成 (100%)

---

### 2. 借用检查器证明

**研究问题**:

- 借用检查器的算法如何形式化？
- 如何证明借用检查器保证数据竞争自由？
- 借用规则与所有权规则的关系如何形式化？

**相关笔记**: [borrow_checker_proof.md](./borrow_checker_proof.md)

**状态**: ✅ 已完成 (100%)

---

### 3. 异步状态机形式化

**研究问题**:

- Future/Poll 状态机如何形式化描述？
- 如何证明异步执行的安全性？
- async/await 的语义如何形式化表示？

**相关笔记**: [async_state_machine.md](./async_state_machine.md)

**状态**: ✅ 已完成 (100%)

---

### 4. 生命周期形式化

**研究问题**:

- 生命周期的语义如何形式化定义？
- 如何证明生命周期系统保证引用有效性？
- 生命周期推断算法如何形式化？

**相关笔记**: [lifetime_formalization.md](./lifetime_formalization.md)

**状态**: ✅ 已完成 (100%)

---

### 5. Pin 和自引用类型形式化

**研究问题**:

- Pin 类型如何形式化定义？
- 如何证明自引用类型的安全性？
- Pin 如何保证内存位置的稳定性？

**相关笔记**: [pin_self_referential.md](./pin_self_referential.md)

**状态**: ✅ 已完成 (100%)

---

### 6. Send/Sync 形式化

**研究问题**:

- Send/Sync 的形式化定义与属性关系？
- 与 thread::spawn、Future、Arc 的衔接？
- 反例（Rc !Send、Cell !Sync）与数据竞争自由？

**相关笔记**: [send_sync_formalization.md](./send_sync_formalization.md)

**状态**: ✅ 已完成 (100%)

---

### 7. Actor 模型形式化 ⭐ 新增

**研究问题**:

- Actor 模型的形式化语义如何定义？
- 如何证明 Actor 系统的数据竞争自由？
- Ask/Tell 模式的形式化规范是什么？
- 监督树如何保证故障隔离？

**相关笔记**: [ACTOR_MODEL_DEEP_DIVE](../../rust-ownership-decidability/actor-specialty/ACTOR_MODEL_DEEP_DIVE.md)

**包含内容**:

- Actor 形式化定义: `Actor := (State, Behavior, Mailbox)`
- 操作语义与转换规则
- **定理 ACTOR-ISOLATION**: 无共享状态 ⇒ 无数据竞争
- **定理 ACTOR-DEADLOCK-FREEDOM**: 条件下死锁自由
- **定理 ACTOR-FAULT-ISOLATION**: 故障隔离保证
- 5+ 反例分析: 循环Ask、共享状态、Actor泄漏等
- 完整聊天系统案例研究

**状态**: ✅ 已完成 (1400+ 行，10+ 定理，15+ 代码)

---

## formal_methods 六篇并表

下表为本目录六篇核心文档的**概念×公理×定理×证明方法×反例**并表；用于跨篇对比与 [HIERARCHICAL_MAPPING_AND_SUMMARY](../HIERARCHICAL_MAPPING_AND_SUMMARY.md) 衔接。各子文档内可注明「本概念在 README §formal_methods 六篇并表 第 x 行」。

| 概念 | 公理/定义 | 定理 | 证明方法 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| **所有权** | 规则 1–3, Def 1.1–1.5 | T2 唯一性, T3 内存安全 | 结构归纳、反证 | [ownership_model](ownership_model.md) 使用已移动值、双重释放 |
| **借用** | 规则 5–8 | T1 数据竞争自由, T2 | 规则归纳 | [borrow_checker_proof](borrow_checker_proof.md) 双重可变借用 |
| **生命周期** | Axiom LF1–LF2, Def 1.4, $\ell \subseteq \text{lft}$ | LF-T1–T3 引用有效性 | 三步骤、约束求解 | [lifetime_formalization](lifetime_formalization.md) 返回局部引用、存储短生命周期 |
| **异步** | Def 4.1–5.2（Future、Poll、Ready/Pending） | T6.1 状态一致, T6.2 并发安全, T6.3 进度 | 归纳+案例分析 | [async_state_machine](async_state_machine.md) 非 Send 跨线程、移动未 Pin |
| **Pin** | Def 1.1–2.2（位置稳定、自引用） | T1–T3 Pin 保证/自引用/投影 | 类型系统、位置稳定 | [pin_self_referential](pin_self_referential.md) 移动未 Pin 自引用 |
| **Send/Sync** | Def SEND1, SYNC1；SYNC-L1 $T:\text{Sync} \Leftrightarrow \&T:\text{Send}$ | SEND-T1, SYNC-T1, SEND-SYNC-T1 | 与 borrow/async 衔接 | [send_sync_formalization](send_sync_formalization.md) Rc !Send、Cell !Sync、非 Send spawn |
| **Actor模型** | Actor := (State, Behavior, Mailbox) | ACTOR-ISOLATION, ACTOR-NO-DATA-RACE, ACTOR-FAULT-ISOLATION | 结构归纳、Actor演算 | [ACTOR_MODEL_DEEP_DIVE](../../rust-ownership-decidability/actor-specialty/ACTOR_MODEL_DEEP_DIVE.md) 循环Ask、共享状态、Actor泄漏 |

*控制流*：A-CF1 见本 README「控制流形式化」；变量 Def 1.4/1.5 见 ownership_model。

---

## 形式化论证汇总

**Def FM1（形式化方法覆盖）**：设 $\mathcal{M}$ 为形式化方法族，$\mathcal{M} = \{\text{ownership},\, \text{borrow},\, \text{lifetime},\, \text{async},\, \text{pin},\, \text{send\_sync}\}$。每 $m \in \mathcal{M}$ 有 Def、Axiom、Theorem 及证明。

**Axiom FM1**：形式化方法族 $\mathcal{M}$ 覆盖 Rust 内存安全、并发安全、引用有效性的核心机制；各机制定理可组合。

**定理 FM-T1（形式化完备性）**：若程序 $P$ 满足 $\mathcal{M}$ 中全部定理，则 $P$ 满足内存安全、数据竞争自由、引用有效性。

*证明*：由 ownership T2/T3、borrow T1、lifetime T2、async T6.2、pin T1–T3、send_sync SEND-T1/SYNC-T1；各定理分别保证不同性质，组合无冲突。∎

**引理 FM-L1（族内定理无循环依赖）**：$\mathcal{M}$ 中 ownership、borrow、lifetime、async、pin、send_sync 的定理依赖链无环；ownership 为 borrow 上游；async 与 spawn 依赖 Send/Sync；send_sync 与 borrow/async 衔接。

*证明*：由各文档定义；ownership 规则 1–3 为 borrow 规则 5–8 前提；lifetime 与 borrow 关联；async 依赖 Pin 与 Send/Sync；send_sync 独立成篇且被 async/spawn/Arc 引用；依赖图无环。∎

**推论 FM-C1**：若 $P$ 违反 $\mathcal{M}$ 中任一定理，则 $P$ 非 Safe 或非良型；反例见 [FORMAL_PROOF_SYSTEM_GUIDE](../FORMAL_PROOF_SYSTEM_GUIDE.md) 反例索引。

*证明*：由 FM-T1 逆否；违反 ⇒ 不满足全部定理 ⇒ 非 Safe 或非良型。∎

---

## 公理-定理形式化索引

| 文档 | 核心公理/定理 | 证明要点 |
| :--- | :--- | :--- |
| [00_completeness_gaps](./00_completeness_gaps.md) | Def FMG1、定理 FMG-T1 | 完备性缺口声明 |
| [ownership_model](./ownership_model.md) | 所有权规则 1–8、T2/T3、RC/ARC/CELL/REFCELL/BOX、MAYBEUNINIT/ATOMIC/UNION/TRANSMUTE、DROP/DEREF/REPR/CONST_MUT_STATIC | 唯一性、RAII、Rc/Arc、Cell/RefCell、MaybeUninit、atomic、union、transmute、Drop/Deref、repr、const &mut static |
| [borrow_checker_proof](./borrow_checker_proof.md) | 借用规则、T1、CHAN/MUTEX/RAW、UNSAFE、MATCH/FOR、EXTERN/CVARIADIC/QUERY | 互斥借用、通道、Mutex、裸指针、unsafe 契约、match/for/?、extern、C variadic |
| [lifetime_formalization](./lifetime_formalization.md) | outlives、T2 引用有效性 | 区域类型、NLL |
| [async_state_machine](./async_state_machine.md) | T6.1–T6.3 状态一致性、并发安全、进度 | Future 状态机、Pin |
| [pin_self_referential](./pin_self_referential.md) | Pin 不变式、T1–T3 自引用安全 | 堆/栈区分、!Unpin |
| [send_sync_formalization](./send_sync_formalization.md) | Def SEND1/SYNC1、SEND-T1/SYNC-T1、SYNC-L1 | 跨线程转移/共享、与 spawn/Future/Arc 衔接 |
| [ACTOR_MODEL_DEEP_DIVE](../../rust-ownership-decidability/actor-specialty/ACTOR_MODEL_DEEP_DIVE.md) | Actor形式语义、10+定理、15+代码示例 | Actor隔离定理、死锁自由、故障隔离、反例分析 |

本索引与 [FORMAL_PROOF_SYSTEM_GUIDE](../FORMAL_PROOF_SYSTEM_GUIDE.md)、[PROOF_INDEX](../PROOF_INDEX.md)、[RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](../RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) 衔接。

---

## 📝 研究笔记 {#-研究笔记}

### 已完成 ✅ {#已完成-}

- [x] [完备性缺口](./00_completeness_gaps.md) - 缺口声明与路线图
- [x] [所有权模型形式化](./ownership_model.md) - 100%；含 RC/ARC/CELL/REFCELL/BOX 扩展
- [x] [借用检查器证明](./borrow_checker_proof.md) - 100%；含 CHAN/MUTEX/RAW 扩展
- [x] [异步状态机形式化](./async_state_machine.md) - 100%
- [x] [生命周期形式化](./lifetime_formalization.md) - 100%
- [x] [Pin 和自引用类型形式化](./pin_self_referential.md) - 100%
- [x] [Send/Sync 形式化](./send_sync_formalization.md) - 100%；Def SEND1/SYNC1、SEND-T1/SYNC-T1、与 spawn/Future/Arc 衔接

---

## 🔗 相关资源 {#-相关资源}

### 核心文档

- [形式化论证系统梳理指南](../FORMAL_PROOF_SYSTEM_GUIDE.md) - 论证缺口分析、反例索引、公理-定理证明树
- [形式化工程系统 - 理论基础](../../rust-formal-engineering-system/01_theoretical_foundations/)
- [所有权与借用文档](../../../crates/c01_ownership_borrow_scope/docs/README.md)
- [异步语义理论](../../../../crates/c06_async/src/async_semantics_theory.rs)

### 代码实现

- [所有权实现](../../../crates/c01_ownership_borrow_scope/src/)
- [借用检查器实现](../../../crates/c01_ownership_borrow_scope/src/)
- [异步系统实现](../../../crates/c06_async/src/)

### 学术资源

- [RustBelt 项目](https://plv.mpi-sws.org/rustbelt/) — MPI-SWS 形式化 Rust 研究；Ralf Jung 博士论文获 **ACM SIGPLAN John C. Reynolds Doctoral Dissertation Award**
- [RustBelt POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) — 首个 Rust 安全形式化证明
- [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) — 别名模型；Miri 实现
- [Tree Borrows PLDI 2025](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html) — Stacked Borrows 演进（**Distinguished Paper Award**）；[ACM PDF](https://dl.acm.org/doi/pdf/10.1145/3735592)、[Iris PDF](https://iris-project.org/pdfs/2025-pldi-treeborrows.pdf)、[源码](https://gitlab.mpi-sws.org/iris/simuliris/-/tree/master/theories/tree_borrows)
- [Ferrocene FLS](https://spec.ferrocene.dev/) — Rust 1.93 形式化规范；[Rust 官方采纳 2025](https://blog.rust-lang.org/2025/03/26/adopting-the-fls/)

---

## 国际权威对标（Authoritative References）

本目录形式化论证对标下述国际权威来源；Def/定理与学术论文、官方规范、形式化工具对应关系如下。

### 权威来源对照表

| 本目录 Def/定理 | 国际权威来源 | 对应关系 |
| :--- | :--- | :--- |
| ownership 规则 1–8、T2/T3 | [RustBelt POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) | Iris 分离逻辑、unsafe 安全抽象 |
| borrow 规则、T1 数据竞争自由 | [RustBelt POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)、[Stacked Borrows POPL 2020](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) | 别名模型、&mut 唯一性 |
| RAW1、裸指针 | [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)、[Tree Borrows PLDI 2025](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html) | 解引用非空、对齐、有效；Tree Borrows 为 Stacked Borrows 演进（Distinguished Paper Award；Rocq 形式化证明） |
| CHAN/MUTEX、relaxed memory | [RustBelt Meets Relaxed Memory POPL 2020](https://plv.mpi-sws.org/rustbelt/rbrlx/) | Arc 数据竞争、同步 ghost state |
| lifetime outlives、NLL | [RustBelt](https://plv.mpi-sws.org/rustbelt/)、[Polonius](https://rust-lang.github.io/polonius/) | 区域类型、NLL；Polonius 为 datalog 形式化 borrow 分析 |
| Pin T1–T3 | [Rust RFC 2349](https://rust-lang.github.io/rfcs/2349-pin.html)、[async 规范](https://doc.rust-lang.org/std/future/trait.Future.html) | 自引用、!Unpin |
| 形式化工具 | [Prusti](https://prusti.org/)、[Kani](https://model-checking.github.io/kani/)、[Miri](https://github.com/rust-lang/miri)、[Iris (Coq)](https://iris-project.org/) | Miri 实现 Stacked Borrows |

### 权威论文与规范（含链接）

| 来源 | 类型 | 链接 | 说明 |
| :--- | :--- | :--- | :--- |
| **RustBelt** | 论文 POPL 2018 | [plv.mpi-sws.org/rustbelt/popl18](https://plv.mpi-sws.org/rustbelt/popl18/) | 首个 Rust 安全形式化证明；Iris + Coq |
| **Stacked Borrows** | 论文 POPL 2020 | [plv.mpi-sws.org/rustbelt/stacked-borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) | 别名模型；UB 定义；Miri 实现 |
| **RustBelt Meets Relaxed Memory** | 论文 POPL 2020 | [plv.mpi-sws.org/rustbelt/rbrlx](https://plv.mpi-sws.org/rustbelt/rbrlx/) | relaxed memory、Arc 数据竞争 |
| **Rust Reference** | 官方规范 | [doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/) | 语法、语义、UB 列表 |
| **Rustonomicon** | 官方文档 | [doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/) | unsafe、内存布局、UB |
| **Ferrocene FLS** | 形式化规范 | [spec.ferrocene.dev](https://spec.ferrocene.dev/) | Rust 1.93 形式化规范；[Rust 官方采纳 2025](https://blog.rust-lang.org/2025/03/26/adopting-the-fls/) |
| **Tree Borrows** | 论文 PLDI 2025（Distinguished Paper Award） | [ETH 项目页](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)、[Iris PDF](https://iris-project.org/pdfs/2025-pldi-treeborrows.pdf)、[Ralf 博客](https://www.ralfj.de/blog/2025/07/07/tree-borrows-paper.html) | Stacked Borrows 演进；树结构；30k crates 测试 54% 更少拒绝；Rocq 形式化证明 |
| **Polonius** | 形式化 borrow 分析 | [rust-lang.github.io/polonius](https://rust-lang.github.io/polonius/) | datalog 形式化；NLL 后继；`-Zpolonius` |
| **Prusti** | 验证工具 | [prusti.org](https://prusti.org/) | 基于 Viper 的 deductive verification |
| **Kani** | 验证工具 | [model-checking.github.io/kani](https://model-checking.github.io/kani/) | 模型检查、UB 验证 |

### 与本目录的对应说明

- **Rust Reference** 明确声明「Rust 的 unsafe 语义尚无形式化模型」；本目录提供 Def/定理级形式化框架，与 RustBelt/Stacked Borrows 学术成果对齐。
- **Ferrocene FLS** 覆盖 Rust 1.93 的语法与 legality；2025 年 Rust 官方采纳；本目录侧重**语义与安全性质**（ownership、borrow、并发），二者互补。
- **Tree Borrows** 为 Stacked Borrows 演进（PLDI 2025 Distinguished Paper Award）；树结构替代栈；30k crates 测试 54% 更少拒绝；Rocq 形式化证明；本目录 borrowing 规则与二者对应。
- **Polonius** 为 Rust 编译器 borrow 分析的形式化（datalog）；与本目录 lifetime、borrow 语义对应。
- **Prusti/Kani/Miri** 为可执行验证工具；Miri 实现 Stacked Borrows；本目录 Def/定理可作为其 specification 的理论基础。

### 权威来源快速链接

| 来源 | 链接 | 用途 |
| :--- | :--- | :--- |
| **releases.rs 1.93.0** | [releases.rs/docs/1.93.0](https://releases.rs/docs/1.93.0/) | 完整变更清单 |
| **Rust 1.93 发布说明** | [blog.rust-lang.org/2026/01/22/Rust-1.93.0](https://blog.rust-lang.org/2026/01/22/Rust-1.93.0/) | 语言特性权威公告 |
| **Ferrocene FLS** | [spec.ferrocene.dev](https://spec.ferrocene.dev/) | Rust 1.93 形式化规范 |

**版本说明**：Ferrocene FLS 覆盖 **Rust 2021 Edition** 与 rustc 1.93.0。本项目文档使用 **Edition 2024**；Edition 2024 新增语法与语义尚未纳入 FLS 正式章节，形式化引用以 FLS 当前覆盖范围为准。

### Ferrocene FLS 章节与本目录对应

Rust 官方采纳（2025 年 3 月）的 [Ferrocene FLS](https://spec.ferrocene.dev/) 覆盖 Rust 1.93 语法与 legality；本目录侧重**语义与安全性质**，二者互补：

| FLS 章节 | 直接链接 | 本目录对应 |
| :--- | :--- | :--- |
| [Ch. 5 Patterns](https://spec.ferrocene.dev/patterns.html) | 5.1 [Refutability](https://spec.ferrocene.dev/patterns.html#refutability)、5.13 [Pattern Matching](https://spec.ferrocene.dev/patterns.html#pattern-matching) | [02_reference/quick_reference/control_flow_functions_cheatsheet.md](../../02_reference/quick_reference/control_flow_functions_cheatsheet.md) |
| [Ch. 15 Ownership and Destruction](https://spec.ferrocene.dev/ownership-and-deconstruction.html) | 15.1 [Ownership](https://spec.ferrocene.dev/ownership-and-deconstruction.html#ownership)、15.4 [Borrowing](https://spec.ferrocene.dev/ownership-and-deconstruction.html#borrowing)、15.6–15.9 [Destruction](https://spec.ferrocene.dev/ownership-and-deconstruction.html#destruction) | [ownership_model](ownership_model.md)、[borrow_checker_proof](borrow_checker_proof.md) Def OW1、规则 1–8、DROP1 |
| [Ch. 16 Exceptions and Errors](https://spec.ferrocene.dev/exceptions-and-errors.html) | 16.1 [Panic](https://spec.ferrocene.dev/exceptions-and-errors.html#panic)、16.2 [Abort](https://spec.ferrocene.dev/exceptions-and-errors.html#abort) | [02_reference/quick_reference/error_handling_cheatsheet.md](../../02_reference/quick_reference/error_handling_cheatsheet.md)、[EDGE_CASES_AND_SPECIAL_CASES](../../02_reference/EDGE_CASES_AND_SPECIAL_CASES.md) |
| [Ch. 17 Concurrency](https://spec.ferrocene.dev/concurrency.html) | 17.1 [Send/Sync](https://spec.ferrocene.dev/concurrency.html#send-and-sync)、17.2 [Atomics](https://spec.ferrocene.dev/concurrency.html#atomics)、17.3 [Async](https://spec.ferrocene.dev/concurrency.html#asynchronous-computation) | CHAN-T1、MUTEX-T1、ATOMIC1、SPAWN-T1 |
| [Ch. 19 Unsafety](https://spec.ferrocene.dev/unsafety.html) | 完整章节 | UNSAFE1、RAW1、EXTERN1 |
| [Ch. 21 FFI](https://spec.ferrocene.dev/ffi.html) | 21.2–21.4 External blocks/functions/statics | EXTERN1、CVARIADIC1 |
| [Appendix C Undefined Behavior](https://spec.ferrocene.dev/undefined-behavior.html) | 完整列表 | RAW1、UNION1、TRANSMUTE1、MAYBEUNINIT1 前置条件 |

### 国际权威奖项与认可

- **ACM SIGPLAN John C. Reynolds Doctoral Dissertation Award**：Ralf Jung 博士论文（RustBelt 等）获此奖项；见 [Ralf Jung 研究主页](https://research.ralfj.de/thesis.html)。
- **PLDI 2025 Distinguished Paper Award**：Tree Borrows 获此奖项；见 [ETH 项目页](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)。

---

## 📖 研究方法 {#-研究方法}

### 形式化工具

- **Coq**: 交互式定理证明器
- **Lean**: 现代定理证明器
- **Isabelle/HOL**: 高阶逻辑证明助手
- **TLA+**: 时序逻辑规范语言

### 形式化方法

1. **操作语义**: 定义程序执行的行为
2. **类型系统**: 定义类型规则和类型检查
3. **霍尔逻辑**: 证明程序正确性
4. **模型检查**: 验证系统属性

### 证明策略

- **结构归纳**: 证明递归结构的性质
- **规则归纳**: 证明类型规则的性质
- **进展性定理**: 证明良型程序不会卡住
- **保持性定理**: 证明类型在求值后保持

---

## 🚀 快速开始 {#-快速开始}

### 创建新的研究笔记

1. 复制模板文件（如 `ownership_model.md`）
2. 填写研究问题和目标
3. 添加形式化定义和证明
4. 提供代码示例和验证
5. 更新本 README 的链接

### 研究流程

1. **问题定义**: 明确要形式化的机制
2. **文献调研**: 查阅相关论文和文档
3. **形式化建模**: 使用数学/逻辑语言定义
4. **证明验证**: 使用工具或手工证明
5. **文档编写**: 记录研究过程和结果

---

**维护团队**: Rust Formal Methods Research Group
**最后更新**: 2026-02-12
**状态**: ✅ **100% 完成**；Phase 1–6 全部补全，见 [00_completeness_gaps](00_completeness_gaps.md)。**意见与可持续推进**（Send/Sync 独立形式化、安全可判定机制全面梳理、完备特性对比、思维表征四类绑定）：[SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN](SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN.md)。**完备性检查表**（六篇×六维）：[FORMAL_METHODS_COMPLETENESS_CHECKLIST](FORMAL_METHODS_COMPLETENESS_CHECKLIST.md)。
