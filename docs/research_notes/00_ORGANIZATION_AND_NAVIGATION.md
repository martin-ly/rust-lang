# research_notes 组织架构与导航

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 统一组织架构说明、按目标导航、三大支柱映射；解决「文档多、入口杂、难定位」问题
> **原则**: 单入口、按目标、支柱映射、层次清晰

---

## 一、从这里开始（单入口）

**首次使用？** 按你的目标选一条路径：

| 我的目标 | 入口 | 预计时间 |
| :--- | :--- | :--- |
| **我想理解 Rust 形式化证明** | [FORMAL_FULL_MODEL_OVERVIEW](./FORMAL_FULL_MODEL_OVERVIEW.md) → [CORE_THEOREMS_FULL_PROOFS](./CORE_THEOREMS_FULL_PROOFS.md) | 30min |
| **我想查某个概念的证明/定义** | [QUICK_FIND](./QUICK_FIND.md)（按关键词） | 2min |
| **我想选设计模式/并发模型** | [software_design_theory/00_MASTER_INDEX](./software_design_theory/00_MASTER_INDEX.md) → 03_semantic_boundary_map、06_boundary_analysis | 15min |
| **我想理解权威对齐体系** | [AUTHORITATIVE_ALIGNMENT_GUIDE](./AUTHORITATIVE_ALIGNMENT_GUIDE.md) | 10min |
| **三大支柱** | [AUTHORITATIVE_ALIGNMENT_GUIDE](./AUTHORITATIVE_ALIGNMENT_GUIDE.md)（原 RESEARCH_PILLARS_AND_SUSTAINABLE_PLAN 已归档） | 10min |
| **我想看完整总结与论证脉络** | [00_COMPREHENSIVE_SUMMARY](./00_COMPREHENSIVE_SUMMARY.md) → [ARGUMENTATION_CHAIN_AND_FLOW](./ARGUMENTATION_CHAIN_AND_FLOW.md) | 15min |
| **我想看批判性意见与改进计划** | [RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN](../archive/process_reports/2026_02/RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md) | 15min |
| **我想看格式统一与 Rust 1.93 对齐计划** | [FORMAT_AND_CONTENT_ALIGNMENT_PLAN](../archive/process_reports/2026_02/FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md) (归档) | 10min |
| **我想看目录缺失与内容深化计划** | [00_COMPREHENSIVE_SUMMARY](./00_COMPREHENSIVE_SUMMARY.md) | 10min |
| **我想查层次化映射（文档树/概念↔定理/文档↔思维表征）** | [HIERARCHICAL_MAPPING_AND_SUMMARY](./HIERARCHICAL_MAPPING_AND_SUMMARY.md) | 5min |
| **我想看 research_notes 全面梳理（结构、归档、维护）** | [RESEARCH_NOTES_ORGANIZATION](./RESEARCH_NOTES_ORGANIZATION.md) | 5min |
| **我想查 Send/Sync 或安全可判定机制** | [send_sync_formalization](./formal_methods/send_sync_formalization.md) → [SAFE_DECIDABLE_MECHANISMS_OVERVIEW](./SAFE_DECIDABLE_MECHANISMS_OVERVIEW.md) | 5min |
| **我想查 formal_methods 完备性（六篇×六维）** | [FORMAL_METHODS_COMPLETENESS_CHECKLIST](./formal_methods/FORMAL_METHODS_COMPLETENESS_CHECKLIST.md) | 2min |
| **我想贡献/维护** | [CONTRIBUTING](./CONTRIBUTING.md) → [QUALITY_CHECKLIST](./QUALITY_CHECKLIST.md) | 5min |

---

## 二、按三大支柱组织（核心架构）

本目录围绕 [AUTHORITATIVE_ALIGNMENT_GUIDE](./AUTHORITATIVE_ALIGNMENT_GUIDE.md) 所述的三大支柱组织，现推荐参考 [AUTHORITATIVE_ALIGNMENT_GUIDE](./AUTHORITATIVE_ALIGNMENT_GUIDE.md)：

```text
支柱 1：公理判定系统（形式系统）
├── formal_methods/          ← 所有权、借用、生命周期、异步、Pin、Send/Sync（六篇并表）
├── type_theory/             ← 类型系统、Trait、型变、高级类型
├── FORMAL_FULL_MODEL_OVERVIEW
├── FORMAL_LANGUAGE_AND_PROOFS
├── CORE_THEOREMS_FULL_PROOFS
└── coq_skeleton/

支柱 2：语言表达力
├── software_design_theory/  ← 设计模式、23/43、执行模型、边界
├── LANGUAGE_SEMANTICS_EXPRESSIVENESS
└── 02_workflow / 04_expressiveness_boundary

支柱 3：组件组合法则
├── 04_compositional_engineering  ← CE-T1–T3、组合反例→错误码
└── 06_boundary_analysis          ← 并发选型决策树
```

**交叉层**：experiments/（实验验证）、practical_applications、BEST_PRACTICES

---

## 三、目录层级（简化视图）

```text
research_notes/
├── 00_ORGANIZATION_AND_NAVIGATION.md  ← 本文件（组织架构与导航）
├── README.md                           ← 主入口、研究方向、规范
├── INDEX.md                            ← 完整索引（按领域、主题）
├── QUICK_FIND.md                       ← 按关键词/领域/目标快速查找
│
├── 【支柱 1 形式化】
│   ├── formal_methods/                 ← 所有权、借用、异步、Pin、Send/Sync（六篇并表）
│   ├── type_theory/                    ← 类型、Trait、型变
│   ├── FORMAL_FULL_MODEL_OVERVIEW.md   ← 统一形式系统入口
│   ├── FORMAL_LANGUAGE_AND_PROOFS.md   ← 推理规则、操作语义
│   ├── CORE_THEOREMS_FULL_PROOFS.md    ← T-OW2/T-BR1/T-TY3 证明
│   ├── PROOF_INDEX.md                  ← 105+ 证明索引
│   └── coq_skeleton/                   ← Coq 骨架
│
├── 【支柱 2+3 设计与组合】
│   └── software_design_theory/         ← 设计模式、23/43、执行模型、组合、边界
│
├── 【实验与综合】
│   ├── experiments/                    ← 性能、内存、并发、宏
│   ├── practical_applications.md
│   └── research_methodology.md
│
└── 【导航/框架/指南】（按需查阅）
    ├── 00_COMPREHENSIVE_SUMMARY.md      ← 完整总结综合、知识地图、论证总览
    ├── ARGUMENTATION_CHAIN_AND_FLOW.md  ← 论证思路、论证脉络关系、文档依赖
    ├── [AUTHORITATIVE_ALIGNMENT_GUIDE](./AUTHORITATIVE_ALIGNMENT_GUIDE.md) - 权威对齐指南、技术决策参考
    ├── CLASSIFICATION.md                ← 按角色/层次/主题分类
    ├── RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md  ← 批判性分析、层次化/矩阵/思维表征缺口、可持续改进计划
    ├── HIERARCHICAL_MAPPING_AND_SUMMARY.md                      ← 文档树、概念↔文档↔Def/定理、文档↔思维表征映射
    ├── ARGUMENTATION_GAP_INDEX.md
    ├── CONTRIBUTING.md、QUALITY_CHECKLIST.md
    └── 其他运维/参考文档
```

---

## 四、文档角色速查

| 角色 | 文档 | 何时用 |
| :--- | :--- | :--- |
| **入口** | README、本文件 | 首次进入、不知道从哪开始 |
| **查找** | QUICK_FIND、INDEX | 按关键词/主题定位 |
| **证明** | PROOF_INDEX、CORE_THEOREMS、FORMAL_LANGUAGE_AND_PROOFS | 查定理、公理、证明 |
| **选型** | software_design_theory、06_boundary_analysis、04_expressiveness_boundary | 选模式、选并发模型 |
| **完整总结** | 00_COMPREHENSIVE_SUMMARY、ARGUMENTATION_CHAIN_AND_FLOW | 全貌、论证思路与脉络 |
| **框架** | AUTHORITATIVE_ALIGNMENT_GUIDE、FORMAL_FULL_MODEL、CLASSIFICATION | 理解整体架构 |
| **贡献** | CONTRIBUTING、QUALITY_CHECKLIST、BEST_PRACTICES | 编写/维护内容 |

---

## 五、常见困惑与解答

| 困惑 | 解答 |
| :--- | :--- |
| 文档太多，不知道看哪个 | 用本文件 § 一「从这里开始」按目标选路径 |
| README 和 INDEX 有什么区别 | README=主入口+规范；INDEX=完整列表+多维度分类 |
| QUICK_FIND 和 QUICK_REFERENCE 有什么区别 | QUICK_FIND=按关键词/领域/目标；QUICK_REFERENCE=按主题快速参考；二者可合并使用 |
| 三大支柱和 formal_methods/type_theory 什么关系 | 支柱 1 = formal_methods + type_theory；支柱 2+3 = software_design_theory |
| 想查「组合反例→错误码」 | [04_compositional_engineering](software_design_theory/04_compositional_engineering/README.md#组合反例编译错误映射ce-t1t2t3) |
| 想查「并发选型 Actor/channel/async」 | [06_boundary_analysis](software_design_theory/03_execution_models/06_boundary_analysis.md) |

---

## 六、权威来源与版本约定

本目录文档与 Rust 1.93 完全对齐，引用以下权威来源时统一采用下列版本说明：

| 来源 | 版本约定 | 用途 |
| :--- | :--- | :--- |
| **releases.rs** | [1.93.0](https://releases.rs/docs/1.93.0/) | 语言/库变更完整清单 |
| **Rust 发布说明** | [Rust 1.93.0](https://blog.rust-lang.org/2026/01/22/Rust-1.93.0/) | 官方特性公告 |
| **Ferrocene FLS** | [spec.ferrocene.dev](https://spec.ferrocene.dev/)；当前覆盖 **Rust 2021 + rustc 1.93** | 形式化规范引用 |
| **本项目** | **Rust 1.93.1+ (Edition 2024)** | 所有 research_notes 元信息与示例默认版本 |

新文档引用 FLS 或 releases 时可直接引用本小节；详见 [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) § 权威来源对齐。

---

## 七、与顶层 docs 的衔接

| docs 入口 | research_notes 对应 |
| :--- | :--- |
| docs/00_MASTER_INDEX § 03 理论与形式化 | research_notes/、PROOF_INDEX、FORMAL_LANGUAGE_AND_PROOFS |
| docs/01_learning 研究者路径 | RESEARCH_PILLARS、FORMAL_FULL_MODEL、CORE_THEOREMS |
| docs/07_project TASK_INDEX | RESEARCH_PILLARS 阶段任务、AENEAS_INTEGRATION_PLAN |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-26
