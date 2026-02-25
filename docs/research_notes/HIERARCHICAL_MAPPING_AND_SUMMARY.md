# research_notes 层次化梳理与映射总结

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 映射完成
> **用途**: 按三大支柱的文档树、概念族↔文档↔Def/Axiom/定理映射、文档↔思维表征映射；支撑层次化检索与双向追溯
> **上位文档**: [00_COMPREHENSIVE_SUMMARY](./00_COMPREHENSIVE_SUMMARY.md)、[RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN](../archive/process_reports/2026_02/RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md)

---

## 📊 目录 {#-目录}

- [research\_notes 层次化梳理与映射总结](#research_notes-层次化梳理与映射总结)
  - [📊 目录 {#-目录}](#-目录--目录)
  - [一、按三大支柱的文档树](#一按三大支柱的文档树)
  - [二、概念族 ↔ 文档 ↔ Def/Axiom/定理 映射表](#二概念族--文档--defaxiom定理-映射表)
    - [2.1 支柱 1（公理判定）](#21-支柱-1公理判定)
    - [2.2 支柱 2（语言表达力）](#22-支柱-2语言表达力)
    - [2.3 支柱 3（组件组合）](#23-支柱-3组件组合)
  - [三、文档 ↔ 思维表征 映射表](#三文档--思维表征-映射表)
    - [3.1 按文档 → 思维表征](#31-按文档--思维表征)
    - [3.2 按思维表征 → 文档（入口）](#32-按思维表征--文档入口)
  - [四、文档依赖关系（简表）](#四文档依赖关系简表)
  - [五、使用说明](#五使用说明)

---

## 一、按三大支柱的文档树

```text
research_notes/
│
├── 【支柱 1：公理判定系统】
│   ├── formal_methods/
│   │   ├── README.md
│   │   ├── 00_completeness_gaps.md
│   │   ├── ownership_model.md          ← 所有权 规则1-3, T2, T3
│   │   ├── borrow_checker_proof.md     ← 借用 规则5-8, T1, T2
│   │   ├── lifetime_formalization.md   ← 生命周期 LF-T1–T3
│   │   ├── async_state_machine.md      ← 异步 Def4.1-5.2, T6.1–T6.3
│   │   └── pin_self_referential.md     ← Pin Def1.1-2.2, T1–T3
│   ├── type_theory/
│   │   ├── README.md
│   │   ├── 00_completeness_gaps.md
│   │   ├── type_system_foundations.md  ← 类型 进展/保持, T1–T3
│   │   ├── variance_theory.md          ← 型变 Def1.1-3.1, T1–T4
│   │   ├── trait_system_formalization.md
│   │   ├── lifetime_formalization.md
│   │   ├── advanced_types.md
│   │   └── construction_capability.md
│   ├── FORMAL_FULL_MODEL_OVERVIEW.md   ← 统一形式系统、公理列表、定理DAG
│   ├── FORMAL_LANGUAGE_AND_PROOFS.md
│   ├── CORE_THEOREMS_FULL_PROOFS.md
│   ├── PROOF_INDEX.md
│   └── coq_skeleton/
│
├── 【支柱 2：语言表达力】
│   └── software_design_theory/
│       ├── 00_MASTER_INDEX.md
│       ├── 01_design_patterns_formal/   ← 23 模式 Def/Axiom/定理
│       ├── 02_workflow_safe_complete_models/  ← 23 安全 / 43 完全
│       ├── 03_execution_models/         ← 01_sync～05_distributed, 06_boundary_analysis
│       ├── 04_compositional_engineering/  ← CE-T1–T3, CE-MAT1
│       ├── 05_boundary_system/
│       └── LANGUAGE_SEMANTICS_EXPRESSIVENESS.md（交叉）
│
├── 【支柱 3：组件组合法则】
│   └── software_design_theory/04_compositional_engineering/
│       ├── README.md
│       ├── 01_formal_composition.md
│       ├── 02_effectiveness_proofs.md
│       └── 03_integration_theory.md
│
└── 【交叉层：论证与框架】
    ├── 00_COMPREHENSIVE_SUMMARY.md
    ├── ARGUMENTATION_CHAIN_AND_FLOW.md
    ├── HIERARCHICAL_MAPPING_AND_SUMMARY.md  ← 本文件
    ├── RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md
    ├── THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md
    ├── COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md
    ├── UNIFIED_SYSTEMATIC_FRAMEWORK.md
    ├── FORMAL_PROOF_SYSTEM_GUIDE.md
    └── ARGUMENTATION_GAP_INDEX.md
```

---

## 二、概念族 ↔ 文档 ↔ Def/Axiom/定理 映射表

### 2.1 支柱 1（公理判定）

| 概念族 | 主文档 | Def/Axiom | 定理/推论 | 备注 |
| :--- | :--- | :--- | :--- | :--- |
| 所有权 | [ownership_model](formal_methods/ownership_model.md) | 规则 1–3, Def 1.1–1.5 | T2 唯一性, T3 内存安全 | 变量绑定/遮蔽 Def 1.4/1.5 |
| 借用 | [borrow_checker_proof](formal_methods/borrow_checker_proof.md) | 规则 5–8 | T1 数据竞争自由, T2 | |
| 生命周期 | [lifetime_formalization](formal_methods/lifetime_formalization.md) | Axiom LF1–LF2, Def 1.4 | LF-T1–T3 引用有效性 | |
| 类型系统 | [type_system_foundations](type_theory/type_system_foundations.md) | typing rules, 进展/保持 | T1 进展, T2 保持, T3 类型安全 | |
| 型变 | [variance_theory](type_theory/variance_theory.md) | Def 1.1–3.1 | T1–T4 协变/逆变/不变/函数 | |
| Trait | [trait_system_formalization](type_theory/trait_system_formalization.md) | Axiom COH1/COH2 | COH-T1, 对象安全 T1–T3 | |
| 异步 | [async_state_machine](formal_methods/async_state_machine.md) | Def 4.1–5.2 | T6.1 状态一致, T6.2 并发安全, T6.3 进度 | |
| Pin | [pin_self_referential](formal_methods/pin_self_referential.md) | Def 1.1–2.2 | T1–T3 Pin 保证/自引用/投影 | |
| Send/Sync | [send_sync_formalization](formal_methods/send_sync_formalization.md) | Def SEND1/SYNC1、SYNC-L1 | SEND-T1、SYNC-T1、SEND-SYNC-T1 | 与 spawn/Future/Arc 衔接 |
| 控制流 | [formal_methods/README](formal_methods/README.md) | A-CF1 | 与 T-TY3 衔接 | |

### 2.2 支柱 2（语言表达力）

| 概念族 | 主文档 | Def/Axiom | 定理/推论 | 备注 |
| :--- | :--- | :--- | :--- | :--- |
| 设计模式 23 | [01_design_patterns_formal](software_design_theory/01_design_patterns_formal/) | 各模式 Def, Axiom | 各模式 B-T1、AF-T1 等 | 见 00_MASTER_INDEX |
| 23 安全 / 43 完全 | [02_workflow_safe_complete_models](software_design_theory/02_workflow_safe_complete_models/) | 安全/完全模型定义 | 语义边界 SB1–SB3 | |
| 执行模型 | [03_execution_models](software_design_theory/03_execution_models/) | 01–05 Def, 06 EB-DET1 | EB-DET-T1, 并发选型决策树 | |
| 表达边界 | [04_expressiveness_boundary](software_design_theory/02_workflow_safe_complete_models/04_expressiveness_boundary.md) | 等价/近似/不可表达 | EB-Meta, EB-L1, EB-C1/C2 | |
| 边界系统 | [05_boundary_system](software_design_theory/05_boundary_system/) | Def 1.1–1.2, B1–B3 | SBM-T1/T2, SUM-T1/T2, EIM-T1/T2 | |

### 2.3 支柱 3（组件组合）

| 概念族 | 主文档 | Def/Axiom | 定理/推论 | 备注 |
| :--- | :--- | :--- | :--- | :--- |
| 组合有效性 | [04_compositional_engineering](software_design_theory/04_compositional_engineering/README.md) | Def CE1, Axiom CE1 | CE-T1–T3, CE-MAT1, CE-MAT-T1 | 依赖 ownership T3, borrow T1, type T3 |

---

## 三、文档 ↔ 思维表征 映射表

以下为 research_notes 文档与思维表征（思维导图、多维矩阵、证明树、决策树）的对应关系；思维表征主文档位于 [04_thinking](../04_thinking/)。

### 3.1 按文档 → 思维表征

| research_notes 文档 | 思维导图 | 多维矩阵 | 证明树 | 决策树 |
| :--- | :--- | :--- | :--- | :--- |
| ownership_model | [MIND_MAP_COLLECTION](../04_thinking/MIND_MAP_COLLECTION.md) §2, C01 | [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md) §1 | 文档内「公理-定理证明树」、[PROOF_GRAPH_NETWORK](../04_thinking/PROOF_GRAPH_NETWORK.md) | [DECISION_GRAPH_NETWORK](../04_thinking/DECISION_GRAPH_NETWORK.md) §1 |
| borrow_checker_proof | 同上 | 同上 | 同上 | 同上 |
| lifetime_formalization | - | MULTI_MATRIX §形式化 | [THINKING_REPRESENTATION_METHODS](../04_thinking/THINKING_REPRESENTATION_METHODS.md) §4.5 | - |
| type_system_foundations | MIND_MAP §3, C02 | MULTI_MATRIX §2 | type_theory | DECISION §2 |
| variance_theory | - | MULTI_MATRIX §形式化 | variance_theory 文档内 | - |
| async_state_machine | MIND_MAP §5, C06 | MULTI_MATRIX §3,5 | async_state_machine 文档内 | DECISION §4 |
| pin_self_referential | - | 六篇并表 | 文档内 | DESIGN_MECHANISM |
| send_sync_formalization | MIND_MAP §5, C06 | [README §六篇并表](formal_methods/README.md#formal_methods-六篇并表) | 文档内、PROOF_INDEX | DESIGN_MECHANISM §Send/Sync、06_boundary_analysis |
| 01_design_patterns_formal | software_design_theory | [04_boundary_matrix](software_design_theory/01_design_patterns_formal/04_boundary_matrix.md)、[README §23 模式多维对比矩阵](software_design_theory/01_design_patterns_formal/README.md#23-模式多维对比矩阵) | 各模式「证明思路」 | 03_semantic_boundary_map 需求→模式 |
| 06_boundary_analysis | - | [03_execution_models README §执行模型多维对比矩阵](software_design_theory/03_execution_models/README.md#执行模型多维对比矩阵) | async §6.2 | 文档内并发选型决策树 |
| 04_compositional_engineering | - | UNIFIED_SYSTEMATIC_FRAMEWORK 组合相关 | CE-T1–T3 证明思路 | 组合决策树、L1–L4 |
| 安全可判定机制总览 | MIND_MAP、本表 | [SAFE_DECIDABLE_MECHANISMS_OVERVIEW](SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md) §二、§六 | PROOF_INDEX、各篇证明树 | 06_boundary、DESIGN_MECHANISM |
| ownership_model / borrow / lifetime / async / pin / send_sync | MIND_MAP、各文档「相关思维表征」 | [formal_methods/README §六篇并表](formal_methods/README.md#formal_methods-六篇并表) | 各文档内证明树、PROOF_INDEX | 06_boundary、DESIGN_MECHANISM |

### 3.2 按思维表征 → 文档（入口）

| 思维表征文档 | 覆盖领域 | 对应 research_notes 入口 |
| :--- | :--- | :--- |
| [MIND_MAP_COLLECTION](../04_thinking/MIND_MAP_COLLECTION.md) | 所有权、类型、并发、异步、C01–C08 | formal_methods、type_theory、COMPREHENSIVE_SYSTEMATIC_OVERVIEW § 按研究领域索引 |
| [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX.md) | 所有权、类型、并发、形式化理论 | FORMAL_PROOF_SYSTEM_GUIDE 概念-公理-定理映射、COMPREHENSIVE_SYSTEMATIC_OVERVIEW § 形式化理论概念对比矩阵 |
| [PROOF_GRAPH_NETWORK](../04_thinking/PROOF_GRAPH_NETWORK.md) | MaybeUninit、借用、生命周期、联合体、迭代器 | PROOF_INDEX、各 formal_methods/type_theory 文档 |
| [DECISION_GRAPH_NETWORK](../04_thinking/DECISION_GRAPH_NETWORK.md) | 所有权、类型、异步、性能、安全 | 06_boundary_analysis、DESIGN_MECHANISM_RATIONALE、03_semantic_boundary_map |
| [THINKING_REPRESENTATION_METHODS](../04_thinking/THINKING_REPRESENTATION_METHODS.md) | 1.93 特性、证明树、决策树 | RUST_193、各模块证明树/决策树小节 |
| [SAFE_DECIDABLE_MECHANISMS_OVERVIEW](SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md) | 安全可判定机制、四类思维表征入口 | §四 思维表征入口、§六 并发+Trait 族四维表；formal_methods 六篇、06_boundary、DESIGN_MECHANISM |

*更细的「按研究领域索引」见 [COMPREHENSIVE_SYSTEMATIC_OVERVIEW](COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md) § 思维表征方式全索引。*

---

## 四、文档依赖关系（简表）

| 文档 A | 依赖/引用 | 文档 B |
| :--- | :--- | :--- |
| 04_compositional_engineering | 引用定理 | ownership_model (T3), borrow_checker_proof (T1), type_system_foundations (T3) |
| 01_design_patterns_formal 各模式 | 引用 | ownership_model, borrow_checker_proof, safe_unsafe_matrix |
| FORMAL_FULL_MODEL_OVERVIEW | 汇总 | formal_methods 各篇、type_theory 各篇 |
| CORE_THEOREMS_FULL_PROOFS | 证明引用 | ownership_model, borrow_checker_proof, type_system_foundations |
| 06_boundary_analysis | 衔接 | 04_expressiveness_boundary, formal_methods |

*完整论证依赖见 [ARGUMENTATION_CHAIN_AND_FLOW](ARGUMENTATION_CHAIN_AND_FLOW.md) § 文档间论证关系。*

---

## 五、使用说明

- **按支柱/层级查文档**：用 § 一 文档树。
- **按概念查定义与定理**：用 § 二 概念族↔文档↔Def/Axiom/定理。
- **从文档查思维表征**：用 § 3.1；**从思维表征反查文档**：用 § 3.2。
- **改文档时查影响**：用 § 四 与 ARGUMENTATION_CHAIN_AND_FLOW。

本文件为 [RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN](../archive/process_reports/2026_02/RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md) 阶段 1 交付物；阶段 2–3 将补全 23 模式矩阵、执行模型矩阵、思维表征-文档双向标注等。

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
