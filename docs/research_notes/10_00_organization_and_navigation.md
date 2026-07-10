# research_notes 组织架构与导航 {#research_notes-组织架构与导航}

> **EN**: 00 Organization And Navigation
> **Summary**: research_notes 组织架构与导航 00 Organization And Navigation. (stub/archive redirect)
>
> **概念族**: 元/导航/索引
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **创建日期**: 2026-02-14
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成权威国际化来源对齐升级
> **用途**: 统一组织架构说明、按目标导航、三大支柱映射；解决「文档多、入口杂、难定位」问题
> **原则**: 单入口、按目标、支柱映射、层次清晰

---

## 📑 目录 {#目录}

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [research\_notes 组织架构与导航 {#research\_notes-组织架构与导航}](#research_notes-组织架构与导航-research_notes-组织架构与导航)
  - [📑 目录 {#目录}](#-目录-目录)
  - [一、从这里开始（单入口） {#一从这里开始单入口}](#一从这里开始单入口-一从这里开始单入口)
  - [二、按三大支柱组织（核心架构） {#二按三大支柱组织核心架构}](#二按三大支柱组织核心架构-二按三大支柱组织核心架构)
  - [三、目录层级（简化视图） {#三目录层级简化视图}](#三目录层级简化视图-三目录层级简化视图)
  - [四、文档角色速查 {#四文档角色速查}](#四文档角色速查-四文档角色速查)
  - [五、常见困惑与解答 {#五常见困惑与解答}](#五常见困惑与解答-五常见困惑与解答)
  - [六、权威来源与版本约定 {#六权威来源与版本约定}](#六权威来源与版本约定-六权威来源与版本约定)
  - [七、与顶层 docs 的衔接 {#七与顶层-docs-的衔接}](#七与顶层-docs-的衔接-七与顶层-docs-的衔接)
  - [🆕 Rust 1.97.0+ / Edition 2024 权威国际化升级说明 {#rust-1960-edition-2024-权威国际化升级说明}](#-rust-1961--edition-2024-权威国际化升级说明-rust-1960-edition-2024-权威国际化升级说明)
    - [升级要点 {#升级要点}](#升级要点-升级要点)
      - [权威来源对齐 {#权威来源对齐}](#权威来源对齐-权威来源对齐)
      - [形式化来源对照 {#形式化来源对照}](#形式化来源对照-形式化来源对照)
      - [版本与生态更新 {#版本与生态更新}](#版本与生态更新-版本与生态更新)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 一、从这里开始（单入口） {#一从这里开始单入口}
>
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Reference](https://doc.rust-lang.org/reference/), [Cargo Book](https://doc.rust-lang.org/cargo/), [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)

**首次使用？** 按你的目标选一条路径：

| 我的目标 | 入口 | 预计时间 |
| :--- | :--- | :--- |
| **我想理解 Rust 形式化证明** | [FORMAL_FULL_MODEL_OVERVIEW](10_formal_full_model_overview.md) → [CORE_THEOREMS_FULL_PROOFS](10_core_theorems_full_proofs.md) | 30min |
| **我想查某个概念的证明/定义** | [QUICK_FIND](10_quick_find.md)（按关键词） | 2min |
| **我想选设计模式/并发模型** | [software_design_theory/00_MASTER_INDEX](software_design_theory/10_00_master_index.md) → 03_semantic_boundary_map、06_boundary_analysis | 15min |
| **我想理解权威对齐体系** | [AUTHORITATIVE_ALIGNMENT_GUIDE](10_authoritative_alignment_guide.md) | 10min |
| **三大支柱** | [AUTHORITATIVE_ALIGNMENT_GUIDE](10_authoritative_alignment_guide.md)（原 RESEARCH_PILLARS_AND_SUSTAINABLE_PLAN 已归档） | 10min |
| **我想看完整总结与论证脉络** | [00_COMPREHENSIVE_SUMMARY](10_00_comprehensive_summary.md) → [ARGUMENTATION_CHAIN_AND_FLOW](10_argumentation_chain_and_flow.md) | 15min |
| **我想看批判性意见与改进计划** | RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN | 15min |
| **我想看格式统一与 Rust 1.93 对齐计划** | FORMAT_AND_CONTENT_ALIGNMENT_PLAN (归档) | 10min |
| **我想看目录缺失与内容深化计划** | [00_COMPREHENSIVE_SUMMARY](10_00_comprehensive_summary.md) | 10min |
| **我想查层次化映射（文档树/概念↔定理/文档↔思维表征）** | [HIERARCHICAL_MAPPING_AND_SUMMARY](10_hierarchical_mapping_and_summary.md) | 5min |
| **我想看 research_notes 全面梳理（结构、归档、维护）** | [RESEARCH_NOTES_ORGANIZATION](10_research_notes_organization.md) | 5min |
| **我想查 Send/Sync 或安全可判定机制** | [send_sync_formalization](formal_methods/10_send_sync_formalization.md) → [SAFE_DECIDABLE_MECHANISMS_OVERVIEW](10_safe_decidable_mechanisms_overview.md) | 5min |
| **我想查 formal_methods 完备性（六篇×六维）** | [FORMAL_METHODS_COMPLETENESS_CHECKLIST](formal_methods/10_formal_methods_completeness_checklist.md) | 2min |
| **我想贡献/维护** | [CONTRIBUTING](10_contributing.md) → [QUALITY_CHECKLIST](10_quality_checklist.md) | 5min |

---

## 二、按三大支柱组织（核心架构） {#二按三大支柱组织核心架构}
>
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Reference](https://doc.rust-lang.org/reference/), [Cargo Book](https://doc.rust-lang.org/cargo/), [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)

本目录围绕 [AUTHORITATIVE_ALIGNMENT_GUIDE](10_authoritative_alignment_guide.md) 所述的三大支柱组织，现推荐参考 [AUTHORITATIVE_ALIGNMENT_GUIDE](10_authoritative_alignment_guide.md)：

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

## 三、目录层级（简化视图） {#三目录层级简化视图}
>
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Reference](https://doc.rust-lang.org/reference/), [Cargo Book](https://doc.rust-lang.org/cargo/), [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)

```text
research_notes/
├── 10_00_organization_and_navigation.md  ← 本文件（组织架构与导航）
├── README.md                           ← 主入口、研究方向、规范
├── INDEX.md                            ← 完整索引（按领域、主题）
├── 10_quick_find.md                       ← 按关键词/领域/目标快速查找
│
├── 【支柱 1 形式化】
│   ├── formal_methods/                 ← 所有权、借用、异步、Pin、Send/Sync（六篇并表）
│   ├── type_theory/                    ← 类型、Trait、型变
│   ├── 10_formal_full_model_overview.md   ← 统一形式系统入口
│   ├── FORMAL_LANGUAGE_AND_PROOFS.md   ← 推理规则、操作语义
│   ├── 10_core_theorems_full_proofs.md    ← T-OW2/T-BR1/T-TY3 证明
│   ├── 10_proof_index.md                  ← 105+ 证明索引
│   └── coq_skeleton/                   ← Coq 骨架
│
├── 【支柱 2+3 设计与组合】
│   └── software_design_theory/         ← 设计模式、23/43、执行模型、组合、边界
│
├── 【实验与综合】
│   ├── experiments/                    ← 性能、内存、并发、宏
│   ├── 10_practical_applications.md
│   └── 10_research_methodology.md
│
└── 【导航/框架/指南】（按需查阅）
    ├── 10_00_comprehensive_summary.md      ← 完整总结综合、知识地图、论证总览
    ├── ARGUMENTATION_CHAIN_AND_FLOW.md  ← 论证思路、论证脉络关系、文档依赖
    ├── [AUTHORITATIVE_ALIGNMENT_GUIDE](10_authoritative_alignment_guide.md) - 权威对齐指南、技术决策参考
    ├── 10_classification.md                ← 按角色/层次/主题分类
    ├── RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md  ← 批判性分析、层次化/矩阵/思维表征缺口、可持续改进计划
    ├── 10_hierarchical_mapping_and_summary.md                      ← 文档树、概念↔文档↔Def/定理、文档↔思维表征映射
    ├── ARGUMENTATION_GAP_INDEX.md
    ├── 10_contributing.md、10_quality_checklist.md
    └── 其他运维/参考文档
```

---

## 四、文档角色速查 {#四文档角色速查}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

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

## 五、常见困惑与解答 {#五常见困惑与解答}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 困惑 | 解答 |
| :--- | :--- |
| 文档太多，不知道看哪个 | 用本文件 § 一「从这里开始」按目标选路径 |
| README 和 INDEX 有什么区别 | README=主入口+规范；INDEX=完整列表+多维度分类 |
| QUICK_FIND 和 QUICK_REFERENCE 有什么区别 | QUICK_FIND=按关键词/领域/目标；QUICK_REFERENCE=按主题快速参考；二者可合并使用 |
| 三大支柱和 formal_methods/type_theory 什么关系 | 支柱 1 = formal_methods + type_theory；支柱 2+3 = software_design_theory |
| 想查「组合反例→错误码」 | [04_compositional_engineering](software_design_theory/04_compositional_engineering/README.md#组合反例编译错误映射ce-t1t2t3) |
| 想查「并发选型 Actor/channel/async」 | [06_boundary_analysis](software_design_theory/03_execution_models/06_boundary_analysis.md) |

---

## 六、权威来源与版本约定 {#六权威来源与版本约定}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

本目录文档已与 **Rust 1.97.0+ (Edition 2024)** 对齐，引用（Reference）以下权威来源时统一采用下列版本说明：

| 来源 | 版本约定 | 用途 |
| :--- | :--- | :--- |
| **releases.rs** | [1.96.0](https://releases.rs/docs/1.96.0/) | 语言/库变更完整清单 |
| **Rust 发布说明** | [Rust Blog](https://blog.rust-lang.org/) | 官方特性公告 |
| **Rust Edition Guide** | [Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) | 版本差异与迁移 |
| **Ferrocene FLS** | [spec.ferrocene.dev](https://spec.ferrocene.dev/) | 形式化规范引用（以 Ferrocene 官方发布基线为准） |
| **本项目** | **Rust 1.97.0+ (Edition 2024)** | 所有 research_notes 元信息与示例默认版本 |

新文档引用 FLS 或 releases 时可直接引用本小节；详见 [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](10_rust_193_language_features_comprehensive_analysis.md) § 权威来源对齐。

---

## 七、与顶层 docs 的衔接 {#七与顶层-docs-的衔接}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

| docs 入口 | research_notes 对应 |
| :--- | :--- |
| docs/00_MASTER_INDEX § 03 理论与形式化 | research_notes/、PROOF_INDEX、FORMAL_LANGUAGE_AND_PROOFS |
| docs/01_learning 研究者路径 | RESEARCH_PILLARS、FORMAL_FULL_MODEL、CORE_THEOREMS |
| docs/07_project TASK_INDEX | RESEARCH_PILLARS 阶段任务、AENEAS_INTEGRATION_PLAN |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-26

---

## 🆕 Rust 1.97.0+ / Edition 2024 权威国际化升级说明 {#rust-1960-edition-2024-权威国际化升级说明}
>
> **来源**: [Rust Edition Guide - Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html)
> **来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/)
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
> **适用版本**: Rust 1.97.0+ (Edition 2024)
> **更新日期**: 2026-06-29

### 升级要点 {#升级要点}

> **来源**: [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/)

本文档已完成权威国际化来源对齐升级：将泛化的 "Rust Official Docs" 替换为官方具体章节/模块（Module）/API 链接，并补充 P1 形式化来源对照。

#### 权威来源对齐 {#权威来源对齐}

| 来源类型 | 具体链接 | 用途 |
| :--- | :--- | :--- |
| **The Rust Programming Language** | [所有权（Ownership）](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)、[借用（Borrowing）](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html)、[生命周期（Lifetimes）](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)、[Trait](https://doc.rust-lang.org/book/ch10-02-traits.html)、[并发](https://doc.rust-lang.org/book/ch16-00-concurrency.html)、[异步（Async）](https://doc.rust-lang.org/book/ch17-00-async-await.html)、[Unsafe Rust](https://doc.rust-lang.org/book/ch19-01-unsafe-rust.html) | 概念教学与场景解释 |
| **Rust Reference** | [引言](https://doc.rust-lang.org/reference/introduction.html)、[变量与所有权（Ownership）](https://doc.rust-lang.org/reference/variables.html)、[类型](https://doc.rust-lang.org/reference/types.html)、[Trait 项](https://doc.rust-lang.org/reference/items/traits.html)、[async 函数](https://doc.rust-lang.org/reference/items/functions.html#async-functions)、[Unsafe 块](https://doc.rust-lang.org/reference/unsafe-blocks.html) | 语言规范与精确语义 |
| **Cargo Book** | [Cargo Book](https://doc.rust-lang.org/cargo/)、[Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html)、[依赖](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html)、[Targets](https://doc.rust-lang.org/cargo/reference/cargo-targets.html) | 构建、包与项目管理 |
| **Rust Standard Library** | [std](https://doc.rust-lang.org/std/)、[Vec](https://doc.rust-lang.org/std/vec/struct.Vec.html)、[HashMap](https://doc.rust-lang.org/std/collections/struct.HashMap.html)、[Result](https://doc.rust-lang.org/std/result/enum.Result.html)、[Future](https://doc.rust-lang.org/std/future/trait.Future.html)、[Pin](https://doc.rust-lang.org/std/pin/struct.Pin.html)、[thread](https://doc.rust-lang.org/std/thread/)、[sync](https://doc.rust-lang.org/std/sync/) | API/模块（Module）级别参考 |
| **Rust Edition Guide** | [Edition Guide](https://doc.rust-lang.org/edition-guide/)、[Rust 2024](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) | 版本差异与迁移 |

#### 形式化来源对照 {#形式化来源对照}

> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/) / [Aeneas](https://aeneas-verification.github.io/) / [Ferrocene FLS](https://spec.ferrocene.dev/)

| 形式化主题 | RustBelt | Aeneas | Ferrocene FLS |
| :--- | :--- | :--- | :--- |
| 所有权唯一性/内存安全（Memory Safety） | ✓ 核心模型 | ✓ 可验证提取 | ✓ 规范 § 所有权 |
| 借用（Borrowing）/数据竞争自由 | ✓ 生命周期逻辑 | ✓ 借用检查验证 | ✓ 规范 § 借用 |
| 类型系统（Type System）/Trait | ✓ Iris 语义 | ✓ 类型系统提取 | ✓ 规范 § 类型 |
| 异步（Async）/Pin | ✓ 扩展模型 | 部分支持 | ✓ 规范 § 表达式 |

#### 版本与生态更新 {#版本与生态更新}

- 所有概念、示例与最佳实践统一对齐 **Rust 1.97.0+ (Edition 2024)**。
- 生态引用已更新：async-std → Tokio / smol；wasm32-wasi → wasm32-wasip1 / wasm32-wasip2（详见 [10_application_trees.md](10_application_trees.md)）。
- 后续版本跟踪请参见 [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/rust-2024/index.html) 与 [Rust Reference](https://doc.rust-lang.org/reference/)。

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-06-29 (Rust 1.97.0+ / Edition 2024 权威国际化升级)

---

> **权威来源**: [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Reference](https://doc.rust-lang.org/reference/), [Cargo Book](https://doc.rust-lang.org/cargo/), [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Edition Guide](https://doc.rust-lang.org/edition-guide/), [RustBelt](https://plv.mpi-sws.org/rustbelt/), [Aeneas](https://aeneas-verification.github.io/), [Ferrocene FLS](https://spec.ferrocene.dev/)
>
> **权威来源对齐变更日志**: 2026-06-29 完成 Batch 9：将泛化 Rust Official Docs 替换为具体章节/API/模块链接，并补充 P1 形式化来源对照 [Authority Source Sprint Batch 9](../../concept/00_meta/02_sources/international_authority_index.md)

**文档版本**: 1.2
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-06-29
**状态**: ✅ 已完成权威国际化来源对齐升级

---

## 相关概念 {#相关概念}
>
> **[来源: [crates.io](https://crates.io/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **形式化来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/) — Rust 语义与形式化安全性证明
> **形式化来源**: [Aeneas](https://aeneas-verification.github.io/) — Rust 程序到 Lean 的验证前端
> **形式化来源**: [Ferrocene FLS](https://spec.ferrocene.dev/) — Rust 语言形式化规范

---
