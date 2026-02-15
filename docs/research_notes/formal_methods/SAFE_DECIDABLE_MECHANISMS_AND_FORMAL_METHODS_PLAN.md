# formal_methods 意见与建议、安全可判定机制梳理与可持续推进计划

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **用途**: 针对 formal_methods 目录的批判性意见、Sync/Send/async 等机制缺口、安全可判定机制全面梳理建议、完备 Rust 特性对比表、思维表征结合建议及后续可持续推进计划
> **状态**: ✅ **阶段 A–D 已完成 100%**（Send/Sync 专篇、安全可判定总览、并发+Trait 四维表、思维表征绑定）
> **上位**: [formal_methods README](README.md)、[00_completeness_gaps](00_completeness_gaps.md)、[HIERARCHICAL_MAPPING_AND_SUMMARY](../HIERARCHICAL_MAPPING_AND_SUMMARY.md)

---

## 一、对 formal_methods 的意见与建议

### 1.1 现状简述

- **已有**：所有权、借用、生命周期、Pin、异步（Future/Poll 状态机）、**Send/Sync** 六篇独立形式化文档；控制流、通道、Mutex、thread::spawn、裸指针、unsafe 等以 Def/定理形式分散在 ownership_model、borrow_checker_proof、async_state_machine 中；[六篇并表](README.md#formal_methods-六篇并表) 与 [00_completeness_gaps](00_completeness_gaps.md) 声明 Phase 1–6 已完备。**Send/Sync 已独立成篇**：[send_sync_formalization](send_sync_formalization.md)。
- **缺口与观感（已通过阶段 A–D 补全）**：
  1. ~~Sync、Send、async 未作为“机制”独立成篇~~ → **已补**：Send/Sync 专篇 [send_sync_formalization](send_sync_formalization.md)；async 仍由 async_state_machine 覆盖。
  2. ~~“安全的可判定的机制”未做统一梳理~~ → **已补**：[SAFE_DECIDABLE_MECHANISMS_OVERVIEW](../SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md) 每机制一节 + 并发/Trait 族四维表。
  3. ~~思维表征与 formal_methods 结合不足~~ → **已补**：HIERARCHICAL_MAPPING 机制↔思维表征、六篇并表、各篇「相关思维表征」统一四类；原 README 五篇并表已扩展为六篇并表，并含：
     - 以**安全可判定机制**为纲的**思维导图**（概念层次 + 机制间依赖）；
     - **概念多维矩阵**（机制 × 可判定性 × 安全边界 × 形式化文档 × 典型反例）；
     - **决策树**（何时依赖 Send/Sync/async、何时用 ownership/borrow/lifetime）；
     - **推理证明树**在「机制 ↔ Def/Axiom/定理」层面的统一索引（与 PROOF_INDEX 互补的“按机制查证明”视图）。

### 1.2 具体建议

| 建议 | 优先级 | 说明 |
| :--- | :--- | :--- |
| **新增 Send/Sync 形式化专篇** | P0 | 独立文档：概念定义（SafeTransfer/SafeShare）、属性关系（T: Sync ⇔ &T: Send）、与 thread::spawn/Future/Arc 的衔接、形式化 Def/Axiom/定理、反例（Rc !Send、Cell !Sync）；与 async_state_machine、borrow_checker_proof、ownership_model 双向链接。 |
| **安全可判定机制总览文档** | P0 | 单文档列出所有“安全且编译期可判定”的机制，每项含：概念定义、属性关系、解释论证、形式证明引用、反例；并注明对应思维表征（思维导图、矩阵、决策树、证明树）位置。 |
| **完备 Rust 特性全部特征对比表** | P1 | 在现有 [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](../RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) 基础上，增加维度：可判定性（静态/运行时/不可判定）、安全边界（Safe/Unsafe 边界）、形式化文档、思维表征入口；必要时拆出「核心机制子表」含 Send/Sync/async。 |
| **思维表征四类与 formal_methods 绑定** | P1 | 在 HIERARCHICAL_MAPPING 或本目录 README 中明确：思维导图、概念多维矩阵、决策树图、推理证明树图各自对应哪些 formal_methods 文档/小节；各篇形式化文档末尾「相关思维表征」表统一包含四类入口。 |
| **async 机制单篇可选** | P2 | 若需“async 语法与运行时模型”与“Future 状态机”分离，可增「async 机制形式化」篇，侧重 async fn、.await、Send 边界、与 Pin 的接口；与 async_state_machine 分工（状态机 vs 语言机制）。 |

---

## 二、安全的可判定的机制：全面梳理建议

### 2.1 何为“安全的可判定的机制”

- **安全**：在 Safe Rust 下，违反机制会导致编译错误或类型系统拒绝，从而避免内存安全/数据竞争等 UB。
- **可判定**：是否满足该机制可由**编译期**算法判定（或由类型系统 + 固定规则在编译期检查），无需运行时或人工证明。

示例：所有权、借用、生命周期、Send、Sync、Unpin（及 async 的 Send 边界）、match 穷尽、for/IntoIterator、? 的 Result 类型等，均为**静态可判定**；RefCell 的借用为**运行时**可判定（panic）；死锁、进度则为**不可判定**（需额外方法或规范）。

### 2.2 建议的“安全可判定机制”清单与形式化对应

下表为**全面梳理**的推荐范围；每项应具备：概念定义、属性关系、解释论证、形式证明引用、反例；并与思维表征四类挂钩。

| 机制 | 可判定性 | 概念定义要点 | 属性关系 | 形式化文档 | 反例 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| 所有权 | 静态 | 唯一所有者、移动、Copy/Clone | 规则 1–3 → T2/T3 | [ownership_model](ownership_model.md) | 使用已移动值、双重释放 |
| 借用 | 静态 | &T/&mut T、互斥可变、不可变可多 | 规则 5–8 → T1 | [borrow_checker_proof](borrow_checker_proof.md) | 双重可变借用、悬垂引用 |
| 生命周期 | 静态 | outlives、区域、NLL | $\ell \subseteq \text{lft}$ → LF-T1–T3 | [lifetime_formalization](lifetime_formalization.md) | 返回局部引用、存短命引用 |
| **Send** | **静态** | **跨线程转移所有权安全** | **T: Sync ⇔ &T: Send** | **[send_sync_formalization](send_sync_formalization.md)** | **Rc 跨线程、!Send 闭包 spawn** |
| **Sync** | **静态** | **跨线程共享引用安全** | **见上** | **同上** | **Cell 跨线程共享、Rc &T 跨线程** |
| Pin/Unpin | 静态 | 位置稳定、自引用、!Unpin 堆固定 | Def 1.1–2.2 → T1–T3 | [pin_self_referential](pin_self_referential.md) | 未 Pin 自引用、栈上 !Unpin |
| Future/async | 静态（边界） | Poll、Ready/Pending、Send 跨 await | Def 4.1–5.2 → T6.1–T6.3 | [async_state_machine](async_state_machine.md) | 非 Send 跨 await、未 Pin 移动 |
| 类型系统 | 静态 | 进展性、保持性、类型安全 | typing rules → T1–T3 | [type_system_foundations](../type_theory/type_system_foundations.md) | 类型错误、不可达代码 |
| match 穷尽 | 静态 | 模式覆盖所有变体 | Def MATCH1 → MATCH-T1 | [borrow_checker_proof](borrow_checker_proof.md) | 非穷尽 match |
| for/? | 静态 | IntoIterator、Result 类型 | FOR1/QUERY1 → FOR-T1/QUERY-T1 | [borrow_checker_proof](borrow_checker_proof.md) | 迭代中修改、非 Result ? |
| 通道/Mutex | 静态（接口） | 消息传递、锁保护；Send 约束 | CHAN1/MUTEX1 → CHAN-T1/MUTEX-T1 | [borrow_checker_proof](borrow_checker_proof.md) | 发送非 Send、锁外访问 |
| thread::spawn | 静态 | F: Send + 'static | SPAWN1 → SPAWN-T1 | [async_state_machine](async_state_machine.md) | 非 Send 闭包 spawn |
| RefCell 借用 | 运行时 | 运行时借用栈、panic | REFCELL1 → REFCELL-T1 | [ownership_model](ownership_model.md) | 双重可变借用 panic |

**说明**：Send/Sync 已通过阶段 A 独立成篇 [send_sync_formalization](send_sync_formalization.md)，与上表一致。

### 2.3 与“概念定义–属性关系–解释论证–形式证明”的对应

- **概念定义**：每机制在对应形式化文档中有 Def 或等价形式化描述（Send/Sync 需补）。
- **属性关系**：如 Send 与 Sync 的等价关系、与 ownership/borrow 的依赖（spawn 依赖 Send；Future 并发依赖 Send+Sync）。
- **解释论证**：设计动机、为何编译期可判定、与 FLS/RustBelt 等权威来源的对应（见 README 国际权威对标）。
- **形式证明**：定理编号与证明思路指向具体文档与小节；反例集中见 [FORMAL_PROOF_SYSTEM_GUIDE](../FORMAL_PROOF_SYSTEM_GUIDE.md) 反例索引。

---

## 三、完备的 Rust 特性全部特征对比

下表在 [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](../RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) 92 项基础上，增加**可判定性、安全边界、形式化文档、思维表征**四维，形成「全部特征对比」视图；核心机制（含 Send/Sync/async）单独成块便于与 formal_methods 对照。

### 3.1 核心安全可判定机制对比（子表）

| 特性 | 可判定性 | 安全边界 | 形式化 Def/定理 | 思维导图 | 矩阵 | 决策树 | 证明树 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| 所有权 | 静态 | Safe 核心 | 规则 1–3, T2, T3 | 支柱 1 | 六篇并表 | 选型/边界 | PROOF_INDEX |
| 借用 | 静态 | Safe 核心 | 规则 5–8, T1 | 支柱 1 | 六篇并表 | 06_boundary | PROOF_INDEX |
| 生命周期 | 静态 | Safe 核心 | LF1–LF2, LF-T1–T3 | 支柱 1 | 六篇并表 | - | PROOF_INDEX |
| **Send** | **静态** | **Safe 并发** | **[send_sync_formalization](send_sync_formalization.md)** SEND1, SEND-T1 | 支柱 1 / C06 | 六篇并表 | DESIGN_MECHANISM §Send/Sync | PROOF_INDEX |
| **Sync** | **静态** | **Safe 并发** | **同上** SYNC1, SYNC-L1, SYNC-T1 | 同上 | 六篇并表 | 同上 | 同上 |
| Pin/Unpin | 静态 | Safe 自引用 | Def 1.1–2.2, T1–T3 | 支柱 1 | 六篇并表 | DESIGN_MECHANISM | PROOF_INDEX |
| Future/async | 静态（边界） | Safe 异步 | Def 4.1–5.2, T6.1–T6.3 | 支柱 1 | 六篇并表 | 06_boundary_analysis | PROOF_INDEX |
| 类型系统 | 静态 | Safe 核心 | 进展/保持, T1–T3 | type_theory | - | - | PROOF_INDEX |
| match/for/? | 静态 | Safe 控制流 | MATCH1/FOR1/QUERY1 | - | - | - | borrow_checker |
| 通道/Mutex/spawn | 静态（接口） | Safe 并发 | CHAN1/MUTEX1/SPAWN1 | 03_execution | 执行模型矩阵 | 06_boundary | PROOF_INDEX |

### 3.2 全 92 项特性维度说明（与 RUST_193 一致 + 四维）

- **可判定性**：静态 / 运行时 / 不可判定（或 N/A）。
- **安全边界**：Safe 核心 / Safe 并发 / Safe 异步 / Unsafe 边界 / 仅规范（无形式化）。
- **形式化文档**：formal_methods 或 type_theory 中的文档名 + Def/定理编号；无则「-」。
- **思维表征**：思维导图（04_thinking/MIND_MAP_COLLECTION 等）、概念多维矩阵（六篇并表、执行模型矩阵等）、决策树（06_boundary_analysis、DESIGN_MECHANISM）、推理证明树（PROOF_INDEX、PROOF_GRAPH_NETWORK）。

完整 92 项逐项表可在后续迭代中从 [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](../RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) 自动生成或手填扩展；本小节仅给出**核心安全可判定机制子表**作为“完备对比”的模板与首期交付。

---

## 四、思维表征与 formal_methods 结合建议

### 4.1 四类思维表征与文档绑定

| 类型 | 当前入口 | 与 formal_methods 的绑定建议 |
| :--- | :--- | :--- |
| **思维导图** | [MIND_MAP_COLLECTION](../04_thinking/MIND_MAP_COLLECTION.md) | 增加「安全可判定机制」节点：ownership → borrow → lifetime → Send/Sync → Pin → async；每节点链到对应 formal_methods 文档。 |
| **概念多维矩阵** | [README §六篇并表](README.md#formal_methods-六篇并表)、[执行模型矩阵](../software_design_theory/03_execution_models/README.md#执行模型多维对比矩阵)、[SAFE_DECIDABLE_MECHANISMS_OVERVIEW](../SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md) §6 | 安全可判定机制 × 可判定性 × 安全边界 × 形式化文档（§3.1）；六篇并表含 Send/Sync 专篇。 |
| **决策树** | [06_boundary_analysis](../software_design_theory/03_execution_models/06_boundary_analysis.md)、[DESIGN_MECHANISM_RATIONALE §Send/Sync](../DESIGN_MECHANISM_RATIONALE.md) | 需跨线程 → Send/Sync；需 async → Send 跨 await、Pin；与 formal_methods Def/定理编号并排引用。 |
| **推理证明树** | [PROOF_INDEX](../PROOF_INDEX.md)、[PROOF_GRAPH_NETWORK](../04_thinking/PROOF_GRAPH_NETWORK.md) | Send/Sync → [send_sync_formalization](send_sync_formalization.md)、async T6.2、SPAWN-T1、CHAN-T1；ownership/borrow/lifetime 保持现有。 |

### 4.2 各篇形式化文档内「相关思维表征」块

- 已存在「相关思维表征」的篇：ownership_model、borrow_checker_proof、lifetime_formalization、async_state_machine、pin_self_referential、06_boundary_analysis 等。
- **建议**：统一包含四类（思维导图、矩阵、决策树、证明树）；若某类暂无专门页面，可写「见 HIERARCHICAL_MAPPING § 文档↔思维表征」或本计划文档 §4.1。
- **Send/Sync 专篇**：已建 [send_sync_formalization](send_sync_formalization.md)，其「相关思维表征」表含四类，并链回本计划与 README。

---

## 五、后续可持续推进计划与安排

### 5.1 阶段划分

| 阶段 | 目标 | 产出 | 优先级 | 状态 |
| :--- | :--- | :--- | :--- | :--- |
| **阶段 A** | Send/Sync 形式化专篇 | 新文档 `send_sync_formalization.md`：Def SEND1/SYNC1、定理 SEND-T1/SYNC-T1、与 spawn/Future/Arc 衔接、反例；README 六篇并表 | P0 | ✅ 已完成 |
| **阶段 B** | 安全可判定机制总览 | 单文档 [SAFE_DECIDABLE_MECHANISMS_OVERVIEW](../SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md)：每机制一节（概念定义、属性关系、解释论证、形式证明、反例）；与 formal_methods/type_theory 双向链接 | P0 | ✅ 已完成 |
| **阶段 C** | 完备特性对比表扩展 | 并发与异步族、Trait 族四维表已入 [SAFE_DECIDABLE_MECHANISMS_OVERVIEW](../SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md) §6；92 项全量可选后续迭代 | P1 | ✅ 已完成（并发+Trait 族） |
| **阶段 D** | 思维表征四类绑定 | MIND_MAP 增安全可判定机制节点；README 或 HIERARCHICAL_MAPPING 增「机制↔思维表征」表；各篇「相关思维表征」统一四类 | P1 | ✅ 见 §4 与总览/各篇块 |
| **阶段 E** | async 机制单篇（可选） | 若需拆分，新增 async 机制形式化（async fn、.await、Send 边界）；与 async_state_machine 分工明确 | P2 | ⏸ 可选，不实施不影响 100% |

### 5.2 依赖与顺序

- 阶段 A（Send/Sync 专篇）与阶段 B（安全可判定总览）可并行启动；B 可引用 A 的 Def/定理。
- 阶段 C 依赖 RUST_193 现有 92 项，可在 A/B 之后做。
- 阶段 D 可与 A/B 同步：先做 README/HIERARCHICAL_MAPPING 的「机制↔思维表征」表，再补 MIND_MAP 节点与各篇四类块。
- 阶段 E 视资源与需求决定是否开篇。

### 5.3 维护约定

- 新增形式化文档时：同步更新 README、00_completeness_gaps、六篇并表、HIERARCHICAL_MAPPING、PROOF_INDEX、本计划文档 §2.2/§3.1。
- 思维表征入口变更时：更新 HIERARCHICAL_MAPPING § 文档↔思维表征、本计划 §4.1。

---

## 六、与现有文档的衔接

| 文档 | 与本计划的关系 |
| :--- | :--- |
| [formal_methods README](README.md) | 本计划为 README 的「意见与可持续推进」扩展；README 可增加「参见 [SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN](SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN.md)」。 |
| [00_completeness_gaps](00_completeness_gaps.md) | Send/Sync 独立形式化已补全；§8 后续可持续推进已标阶段 A–D 完成，链到本计划与总览。 |
| [HIERARCHICAL_MAPPING_AND_SUMMARY](../HIERARCHICAL_MAPPING_AND_SUMMARY.md) | 阶段 D 中增加「安全可判定机制↔思维表征」表或节。 |
| [FORMAL_METHODS_COMPLETENESS_CHECKLIST](FORMAL_METHODS_COMPLETENESS_CHECKLIST.md) | 六篇×六维完备性检查表（概念定义、属性关系、解释论证、形式证明、反例、思维表征四类）；与总览互为自检。 |
| [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](../RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) | §3 完备对比表与该文档 92 项一致；可互为「总览」与「详表」。 |
| [DESIGN_MECHANISM_RATIONALE](../DESIGN_MECHANISM_RATIONALE.md) | Send/Sync 设计理由已存在；形式化 Def/定理由阶段 A 专篇承担，DESIGN_MECHANISM 链到专篇。 |

---

**维护者**: Rust Formal Methods Research Group
**最后更新**: 2026-02-14
