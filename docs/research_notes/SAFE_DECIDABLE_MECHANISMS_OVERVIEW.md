# 安全可判定机制总览

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 总览完成
> **用途**: 全面梳理 Rust 中「安全且编译期可判定」的机制，每项含概念定义、属性关系、解释论证、形式证明引用、反例；与 [formal_methods](formal_methods/README.md)、[type_theory](type_theory/) 双向链接
> **上位**: [SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN](formal_methods/SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN.md)、[HIERARCHICAL_MAPPING_AND_SUMMARY](HIERARCHICAL_MAPPING_AND_SUMMARY.md)

---

## 一、何为“安全的可判定的机制”

- **安全**：在 Safe Rust 下，违反机制会导致编译错误或类型系统拒绝，从而避免内存安全/数据竞争等 UB。
- **可判定**：是否满足该机制可由**编译期**算法判定（类型系统 + 固定规则），无需运行时或人工证明。

**例外**：RefCell 的借用为**运行时**可判定（违反则 panic）；死锁、进度为**不可判定**（需额外方法）。

---

## 二、机制清单与形式化对应总表

| 机制 | 可判定性 | 形式化文档 | Def/定理 | 反例 |
| :--- | :--- | :--- | :--- | :--- |
| 所有权 | 静态 | [ownership_model](formal_methods/ownership_model.md) | 规则 1–3, T2, T3 | 使用已移动值、双重释放 |
| 借用 | 静态 | [borrow_checker_proof](formal_methods/borrow_checker_proof.md) | 规则 5–8, T1 | 双重可变借用、悬垂引用 |
| 生命周期 | 静态 | [lifetime_formalization](formal_methods/lifetime_formalization.md) | LF1–LF2, LF-T1–T3 | 返回局部引用、存短命引用 |
| Send | 静态 | [send_sync_formalization](formal_methods/send_sync_formalization.md) | SEND1, SEND-T1 | Rc 跨线程、!Send 闭包 spawn |
| Sync | 静态 | [send_sync_formalization](formal_methods/send_sync_formalization.md) | SYNC1, SYNC-L1, SYNC-T1 | Cell 跨线程共享、Rc &T 跨线程 |
| Pin/Unpin | 静态 | [pin_self_referential](formal_methods/pin_self_referential.md) | Def 1.1–2.2, T1–T3 | 未 Pin 自引用、栈上 !Unpin |
| Future/async | 静态（边界） | [async_state_machine](formal_methods/async_state_machine.md) | Def 4.1–5.2, T6.1–T6.3 | 非 Send 跨 await、未 Pin 移动 |
| 类型系统 | 静态 | [type_system_foundations](type_theory/type_system_foundations.md) | 进展/保持, T1–T3 | 类型错误 |
| match 穷尽 | 静态 | [borrow_checker_proof](formal_methods/borrow_checker_proof.md) | MATCH1, MATCH-T1 | 非穷尽 match |
| for / ? | 静态 | [borrow_checker_proof](formal_methods/borrow_checker_proof.md) | FOR1/QUERY1, FOR-T1/QUERY-T1 | 迭代中修改、非 Result ? |
| 通道/Mutex | 静态（接口） | [borrow_checker_proof](formal_methods/borrow_checker_proof.md) | CHAN1/MUTEX1, CHAN-T1/MUTEX-T1 | 发送非 Send |
| thread::spawn | 静态 | [async_state_machine](formal_methods/async_state_machine.md) | SPAWN1, SPAWN-T1 | 非 Send 闭包 spawn |
| RefCell 借用 | 运行时 | [ownership_model](formal_methods/ownership_model.md) | REFCELL1, REFCELL-T1 | 双重可变借用 panic |

---

## 三、各机制分节（概念定义·属性关系·解释论证·形式证明·反例）

### 3.1 所有权

- **概念定义**：唯一所有者、移动语义、Copy/Clone 区分；形式化见 [ownership_model](formal_methods/ownership_model.md) 规则 1–3、Def 1.1–1.5。
- **属性关系**：为借用的前提；borrow 规则 5–8 在单所有者下定义。
- **解释论证**：无 GC 内存安全；设计理由见 [DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md)。
- **形式证明**：定理 T2 唯一性、T3 内存安全；[PROOF_INDEX](PROOF_INDEX.md)。
- **反例**：使用已移动值、双重释放；[FORMAL_PROOF_SYSTEM_GUIDE](FORMAL_PROOF_SYSTEM_GUIDE.md) 反例索引。

### 3.2 借用

- **概念定义**：&T/&mut T、可变独占、不可变可多；[borrow_checker_proof](formal_methods/borrow_checker_proof.md) 规则 5–8。
- **属性关系**：依赖所有权；与生命周期协同；跨线程时需 Send/Sync。
- **解释论证**：数据竞争自由；与 RustBelt/Stacked Borrows 对应。
- **形式证明**：定理 T1 数据竞争自由；[PROOF_INDEX](PROOF_INDEX.md)。
- **反例**：双重可变借用、悬垂引用。

### 3.3 生命周期

- **概念定义**：outlives、区域、NLL；[lifetime_formalization](formal_methods/lifetime_formalization.md) Axiom LF1–LF2、Def 1.4。
- **属性关系**：$\ell \subseteq \text{lft}$；与借用、型变组合。
- **解释论证**：引用有效性；Polonius/区域类型。
- **形式证明**：LF-T1–T3 引用有效性。
- **反例**：返回局部引用、存储短生命周期引用。

### 3.4 Send

- **概念定义**：可安全跨线程**转移所有权**；[send_sync_formalization](formal_methods/send_sync_formalization.md) Def SEND1。
- **属性关系**：$T : \text{Sync} \Leftrightarrow \&T : \text{Send}$（SYNC-L1）；spawn 闭包需 Send；Future 跨 await 需 Send。
- **解释论证**：跨线程无共享可变；FLS Ch. 17.1。
- **形式证明**：SEND-T1、SEND-SYNC-T1；与 borrow T1、SPAWN-T1 一致。
- **反例**：Rc 跨线程、非 Send 闭包 spawn。

### 3.5 Sync

- **概念定义**：可安全跨线程**共享引用** &T；[send_sync_formalization](formal_methods/send_sync_formalization.md) Def SYNC1。
- **属性关系**：Sync ⇔ &T: Send；多线程共享 &T 时需 T: Sync。
- **解释论证**：共享不可变引用无数据竞争；FLS Ch. 17.1。
- **形式证明**：SYNC-T1；与 async 定理 6.2 一致。
- **反例**：Cell 跨线程共享、Rc &T 跨线程。

### 3.6 Pin/Unpin

- **概念定义**：位置稳定、自引用、!Unpin 堆固定；[pin_self_referential](formal_methods/pin_self_referential.md) Def 1.1–2.2。
- **属性关系**：Future 自引用依赖 Pin；栈固定需 Unpin、堆固定任意。
- **解释论证**：自引用移动→悬垂；RFC 2349。
- **形式证明**：T1–T3 Pin 保证/自引用/投影。
- **反例**：未 Pin 自引用、栈上 !Unpin。

### 3.7 Future/async

- **概念定义**：Poll、Ready/Pending、async 状态机；[async_state_machine](formal_methods/async_state_machine.md) Def 4.1–5.2。
- **属性关系**：依赖 Pin；跨 await 需 Send；并发 poll 需 Send+Sync。
- **解释论证**：I/O 并发、无数据竞争；FLS Ch. 17.3。
- **形式证明**：T6.1–T6.3 状态一致、并发安全、进度。
- **反例**：非 Send 跨 await、未 Pin 移动 Future。

### 3.8 类型系统

- **概念定义**：类型规则、进展性、保持性；[type_system_foundations](type_theory/type_system_foundations.md)。
- **属性关系**：为所有机制的类型检查基础。
- **解释论证**：良型程序不卡住、归约保持类型。
- **形式证明**：T1 进展、T2 保持、T3 类型安全。
- **反例**：类型错误、不可达代码。

### 3.9 match / for / ?

- **概念定义**：穷尽匹配、IntoIterator、Result 早期返回；[borrow_checker_proof](formal_methods/borrow_checker_proof.md) Def MATCH1/FOR1/QUERY1。
- **属性关系**：控制流与借用协同；A-CF1 见 [formal_methods README](formal_methods/README.md)。
- **形式证明**：MATCH-T1、FOR-T1、QUERY-T1。
- **反例**：非穷尽 match、迭代中修改集合、非 Result 类型 ?。

### 3.10 通道 / Mutex / thread::spawn

- **概念定义**：CHAN1、MUTEX1、SPAWN1；见 [borrow_checker_proof](formal_methods/borrow_checker_proof.md)、[async_state_machine](formal_methods/async_state_machine.md)。
- **属性关系**：发送类型需 Send；spawn 闭包需 Send + 'static。
- **形式证明**：CHAN-T1、MUTEX-T1、SPAWN-T1。
- **反例**：发送非 Send、非 Send 闭包 spawn。

### 3.11 RefCell 借用（运行时可判定）

- **概念定义**：运行时借用栈；[ownership_model](formal_methods/ownership_model.md) Def REFCELL1。
- **属性关系**：与编译期借用规则同构；违反时 panic。
- **形式证明**：REFCELL-T1。
- **反例**：双重可变借用导致 panic。

---

## 四、思维表征入口

| 类型 | 入口 |
| :--- | :--- |
| 思维导图 | [MIND_MAP_COLLECTION](../04_thinking/MIND_MAP_COLLECTION.md)；安全可判定机制节点 → 本总览 §二、§三 |
| 概念多维矩阵 | [formal_methods README §六篇并表](formal_methods/README.md#formal_methods-六篇并表)；[SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN](formal_methods/SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN.md) §3.1 |
| 决策树 | [06_boundary_analysis](software_design_theory/03_execution_models/06_boundary_analysis.md)；[DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md) § Send/Sync |
| 推理证明树 | [PROOF_INDEX](PROOF_INDEX.md)；[PROOF_GRAPH_NETWORK](../04_thinking/PROOF_GRAPH_NETWORK.md) |

---

## 六、并发与异步族、Trait 族 四维对比表（完备特性对比子集）

在 [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) 基础上，为「并发与异步族」「Trait 与多态族」增加**可判定性、安全边界、形式化文档、思维表征**四维，便于与 formal_methods 对照。

### 6.1 并发与异步族

| 特性 | 可判定性 | 安全边界 | 形式化 Def/定理 | 思维表征入口 |
| :--- | :--- | :--- | :--- | :--- |
| 线程 | 静态 | Safe 并发 | SPAWN1, SPAWN-T1 | [async_state_machine](formal_methods/async_state_machine.md)、[send_sync_formalization](formal_methods/send_sync_formalization.md)、06_boundary_analysis |
| Future | 静态（边界） | Safe 异步 | Def 4.1–5.2, T6.1–T6.3 | async_state_machine、六篇并表、PROOF_INDEX |
| async/await | 静态（边界） | Safe 异步 | 同上 + Send 跨 await | 同上、DESIGN_MECHANISM |
| Pin | 静态 | Safe 自引用 | Def 1.1–2.2, T1–T3 | [pin_self_referential](formal_methods/pin_self_referential.md)、六篇并表 |
| Send/Sync | 静态 | Safe 并发 | SEND1/SYNC1, SEND-T1/SYNC-T1 | [send_sync_formalization](formal_methods/send_sync_formalization.md)、六篇并表、DESIGN_MECHANISM |
| 通道 | 静态（接口） | Safe 并发 | CHAN1, CHAN-T1 | borrow_checker_proof、06_boundary |
| Mutex/RwLock | 静态（接口） | Safe 并发 | MUTEX1, MUTEX-T1 | borrow_checker_proof、06_boundary |
| 原子操作 | 静态（接口） | Safe 并发 | ATOMIC1, ATOMIC-T1 | ownership_model |

### 6.2 Trait 与多态族

| 特性 | 可判定性 | 安全边界 | 形式化 Def/定理 | 思维表征入口 |
| :--- | :--- | :--- | :--- | :--- |
| Trait | 静态 | Safe 核心 | trait_system_formalization COH1/COH2 | type_theory、PROOF_INDEX |
| 泛型 | 静态 | Safe 核心 | 单态化、类型规则 | type_system_foundations |
| 关联类型 / GATs | 静态 | Safe 核心 | advanced_types AT-L1 | type_theory |
| Trait 对象 | 静态 | Safe 核心 | 对象安全 T1–T3 | trait_system_formalization |
| **Send/Sync** | **静态** | **Safe 并发** | **SEND1/SYNC1, SEND-T1/SYNC-T1** | **send_sync_formalization、六篇并表** |
| Unpin | 静态 | Safe 自引用 | Def 2.2, pin T1–T3 | pin_self_referential |
| blanket impl | 静态 | Safe 核心 | coherence | trait_system_formalization |
| Trait 继承 | 静态 | Safe 核心 | - | trait_system |

*说明*：92 项全量四维表见 [SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN](formal_methods/SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN.md) §3.2；本表为并发与 Trait 族子集。

---

## 七、相关文档

- [formal_methods README](formal_methods/README.md) — 六篇并表、公理-定理索引
- [SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN](formal_methods/SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN.md) — 意见与建议、阶段 A–E 计划
- [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) — 92 项特性与形式化映射
- [FORMAL_PROOF_SYSTEM_GUIDE](FORMAL_PROOF_SYSTEM_GUIDE.md) — 反例索引

---

**维护者**: Rust Formal Methods Research Group
**最后更新**: 2026-02-14
