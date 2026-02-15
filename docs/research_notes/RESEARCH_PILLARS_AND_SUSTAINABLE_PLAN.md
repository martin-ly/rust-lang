# Rust 研究三大支柱与可持续推进计划

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **用途**: 按用户表述重新梳理任务体系，围绕「公理判定系统」「语言表达力」「组件组合」三大支柱，结合国际权威对标，输出批判性意见与层次推进方案
> **上位文档**: [INDEX](./INDEX.md)、[AUTHORITATIVE_ALIGNMENT_CRITICAL_EVALUATION_2026_02](../07_project/AUTHORITATIVE_ALIGNMENT_CRITICAL_EVALUATION_2026_02.md)

---

## 一、三大支柱总览

| 支柱 | 核心问题 | 确定性判定目标 | 本项目对应 |
| :--- | :--- | :--- | :--- |
| **支柱 1：公理判定系统** | 类型、控制流、变量等全面形式化推理与证明 | 确定性的形式化判定 | formal_methods、type_theory、PROOF_INDEX、CORE_THEOREMS_FULL_PROOFS |
| **支柱 2：语言表达力** | 设计模式、并发/并行/分布式、工作流设计模式 | 表达力的确定性判定与有效设计判定 | software_design_theory、LANGUAGE_SEMANTICS_EXPRESSIVENESS、02_workflow、04_expressiveness_boundary |
| **支柱 3：组件组合法则** | 结合 1、2 的组件组合、构建复合的有效可判定法则 | 组合有效性、构建能力确定性 | 04_compositional_engineering、CE-T1–T3、CE-MAT1 |

---

## 二、支柱 1：公理判定系统（形式系统）

### 2.1 范围与目标

**形式系统范围**：类型系统、控制流、变量（所有权/借用/生命周期）、异步、Pin 等。

**确定性判定目标**：

- 公理→引理→定理的**形式化推理链**可追溯
- 每项定理有**确定性的判定**（编译时/静态/机器可检查）
- 与 Rust Reference、RustBelt、Aeneas 等国际权威**对齐**

### 2.2 当前覆盖与缺口

| 领域 | 已覆盖 | 缺口 | 国际对标 |
| :--- | :--- | :--- | :--- |
| **所有权** | ownership_model、T-OW2/T-OW3、coq_skeleton | L3 机器证明 Admitted | RustBelt、RustSEM |
| **借用** | borrow_checker_proof、T-BR1 | L3 骨架已创建（BORROW_DATARACE_FREE.v） | RustBelt |
| **类型** | type_system_foundations、T-TY3 | 进展性/保持性完整证明 | RustBelt、Aeneas |
| **生命周期** | lifetime_formalization、LF-T1–T3 | 与借用规则显式衔接 | RustBelt（间接） |
| **控制流** | formal_methods README A-CF1 | 与 T-TY3 衔接 | - |
| **变量** | ownership_model Def 1.4/1.5 变量绑定与遮蔽 | 模式匹配形式化可扩展 | - |
| **异步/Pin** | async_state_machine、pin_self_referential | 无国际直接对标 | - |

### 2.3 批判性意见

| 维度 | 现状 | 建议 |
| :--- | :--- | :--- |
| **公理编号** | PROOF_INDEX 有 A/L/T/C 规范；FORMAL_FULL_MODEL_OVERVIEW 有统一编号；A-CF1、A-BIND1、A-SHADOW1 已补全 | 持续同步 |
| **机器可检查** | T-OW2/T-BR1/T-TY3 骨架已创建（证明 Admitted 待补全） | Aeneas/coq-of-rust 对接；见 [AENEAS_INTEGRATION_PLAN](./AENEAS_INTEGRATION_PLAN.md) |
| **国际对标** | RustBelt、Aeneas、RustSEM 已索引 | 季度更新 [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](./INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) |

---

## 三、支柱 2：语言表达力

### 3.1 范围与目标

**表达力范围**：

- **设计模式**：GoF 23、扩展 43（Repository、Service Layer、DTO、Event Sourcing 等）
- **并发/并行/分布式**：Actor、Reactor、CSP、消息传递、Tokio、Arc/Mutex
- **工作流**：23 安全 vs 43 完全、语义边界图、表达边界

**确定性判定目标**：

- 何者**可表达**、何者**不可表达**、**边界**在哪
- 设计选型的**有效判定**（等价/近似/不可表达）
- 与 OOP、函数式、并发范式的**对比论证**

### 3.2 当前覆盖与缺口

| 领域 | 已覆盖 | 缺口 | 国际对标 |
| :--- | :--- | :--- | :--- |
| **设计模式** | 23 安全、43 完全、02_workflow、04_expressiveness_boundary | 已补全 | Fowler EAA、DDD |
| **并发模式** | formal_methods Phase 4、C05/C06、CHAN-T1、MUTEX-T1；06_boundary_analysis 并发选型决策树 | 已补全 | Go CSP、Erlang Actor |
| **工作流** | 02_workflow_safe_complete_models、03_semantic_boundary_map；工作流引擎表达力（状态机/补偿/Temporal） | 已补全 | - |
| **表达边界** | LANGUAGE_SEMANTICS_EXPRESSIVENESS、04_expressiveness_boundary；分布式模式（Event Sourcing/Saga/CQRS） | 可进一步细化 | - |

### 3.3 批判性意见

| 维度 | 现状 | 建议 |
| :--- | :--- | :--- |
| **等价/近似表** | 04_expressiveness_boundary 有等价/近似/不可表达；分布式模式（Event Sourcing/Saga/CQRS）已补全 | 持续细化 |
| **设计判定** | 03_semantic_boundary_map 按需求反向查模式；06_boundary_analysis 并发选型决策树已补全 | 持续细化 |
| **工作流** | 02_workflow 有 23/43 模型；工作流引擎表达力（状态机/补偿/Temporal）已补全 | 持续细化 |

---

## 四、支柱 3：组件组合法则

### 4.1 范围与目标

**组合范围**：模块、crate、trait、泛型、跨进程、分布式架构。

**确定性判定目标**：

- **组合有效性**：CE-T1（内存安全）、CE-T2（数据竞争自由）、CE-T3（类型安全）
- **构建能力确定性**：CE-MAT1（L1–L4 成熟度）、CE-MAT-T1（静态 vs 运行时判定）
- **组合法则**：无循环依赖、pub 边界、trait 约束传递

### 4.2 当前覆盖与缺口

| 领域 | 已覆盖 | 缺口 | 国际对标 |
| :--- | :--- | :--- | :--- |
| **形式组合** | 01_formal_composition、02_effectiveness_proofs、03_integration_theory | 跨 crate 语义版本形式化 | Cargo、semver |
| **成熟度层级** | CE-MAT1（L1–L4）、CE-MAT-T1、验证手段表 | L4 分布式事务、一致性形式化 | - |
| **模式组合** | Builder+Factory、Repository+Service+DTO、选型决策树 | 更多多模式组合案例 | - |

### 4.3 批判性意见

| 维度 | 现状 | 建议 |
| :--- | :--- | :--- |
| **与支柱 1 衔接** | CE-T1–T3 引用 ownership、borrow、type | 显式建立「公理→组合定理」推导链 |
| **与支柱 2 衔接** | 43 模式映射到 L1–L4 | 表达力边界与组合有效性的联合判定树 |
| **构建法则** | 无循环依赖、pub 边界已形式化 | 补充「组合反例→编译错误」映射表 |

---

## 五、国际权威对标与批判性意见

### 5.1 对标矩阵（三大支柱 × 权威源）

| 权威源 | 支柱 1 公理 | 支柱 2 表达力 | 支柱 3 组合 |
| :--- | :--- | :--- | :--- |
| **Rust Reference** | 类型、生命周期规范 | - | 模块、crate |
| **RustBelt** | 所有权、借用、MIR 级 | - | - |
| **RustSEM (K-Framework)** | 内存级 OBS、可执行语义 | - | - |
| **Aeneas / coq-of-rust** | Safe Rust → 证明助手 | - | - |
| **Fowler EAA / DDD** | - | Repository、Service Layer、DTO | 分层架构 |
| **The Rust Book** | 所有权、类型、trait | 并发、异步 | - |
| **Comprehensive Rust** | - | 并发、嵌入式 | - |

### 5.2 批判性意见汇总

| 支柱 | 优势 | 不足 | 建议 |
| :--- | :--- | :--- |------|
| **支柱 1** | 公理编号规范、L2 完整证明、coq_skeleton | 控制流/变量独立形式化缺失；L3 仅 T-OW2 | 补控制流公理；推进 Aeneas 对接 |
| **支柱 2** | 23/43 模型、表达边界、语义边界图 | 并发/分布式选型形式化不足；工作流引擎缺 | 并发选型决策树；工作流表达力考察 |
| **支柱 3** | CE-T1–T3、CE-MAT1、L1–L4 验证手段 | 与支柱 1/2 的显式推导链可加强 | 公理→组合定理 DAG；表达力×组合联合判定 |

### 5.3 全网权威内容对齐清单

| 类别 | 权威源 | 对齐状态 | 行动 |
| :--- | :--- | :--- | :--- |
| **形式化** | RustBelt、RustSEM、Aeneas、coq-of-rust | 已索引；Aeneas 对接计划已制定 | 季度更新 INTERNATIONAL_FORMAL_VERIFICATION_INDEX |
| **学习路径** | rust-lang.org/learn、Book、RBE、Rustlings | 已对标 AUTHORITATIVE_ALIGNMENT | 持续同步 |
| **设计模式** | Fowler EAA、GoF | 23/43 已覆盖 | 补充分布式模式形式化 |
| **并发** | Tokio、async-std、Go CSP、Erlang | 部分覆盖 | 并发选型决策树 |

---

## 六、可持续推进计划（层次推进）

### 6.1 阶段 1：巩固与衔接（1–2 个月）

| 任务 | 支柱 | 交付物 | 优先级 | 状态 |
| :--- | :--- | :--- | :--- | :--- |
| 控制流公理小节 | 1 | formal_methods README 新增「控制流形式化」A-CF1；与 T-TY3 衔接 | P2 | ✅ 2026-02-14 |
| 变量遮蔽形式化 | 1 | ownership_model Def 1.4/1.5 变量绑定与遮蔽 | P3 | ✅ 2026-02-14 |
| 公理→组合定理 DAG | 1+3 | FORMAL_FULL_MODEL_OVERVIEW 显式标注 ownership/borrow/type → CE-T1–T3 | P2 | ✅ 2026-02-14 |
| 表达力×组合联合判定树 | 2+3 | 04_compositional_engineering 新增联合决策树 | P2 | ✅ 2026-02-14 |

### 6.2 阶段 2：扩展与对标（2–4 个月）

| 任务 | 支柱 | 交付物 | 优先级 | 状态 |
| :--- | :--- | :--- | :--- | :--- |
| 并发选型决策树 | 2 | 何时 Actor、channel、async、Mutex；形式化边界 | P2 | ✅ 2026-02-14 |
| 分布式模式形式化 | 2 | Event Sourcing、Saga、CQRS 与 Rust 表达力；等价/近似表扩展 | P2 | ✅ 2026-02-14 |
| 工作流引擎表达力 | 2 | 状态机、补偿、Temporal 式工作流与 Rust | P3 | ✅ 2026-02-14 |
| Aeneas/coq-of-rust 对接 | 1 | 至少 1 个示例翻译验证；PROOF_INDEX 标注 L3 | P2 | 📋 骨架就绪（aeneas_first.rs、计划更新） |
| T-BR1/T-TY3 Coq 骨架 | 1 | coq_skeleton 扩展；见 COQ_ISABELLE_PROOF_SCAFFOLDING | P3 | ✅ 2026-02-14 |

### 6.3 阶段 3：深化与国际化（季度–年度）

| 任务 | 支柱 | 交付物 | 优先级 | 状态 |
| :--- | :--- | :--- | :--- | :--- |
| 季度国际对标更新 | 1 | INTERNATIONAL_FORMAL_VERIFICATION_INDEX 补充新论文/工具 | 持续 | 待季度 |
| 组合反例→编译错误映射 | 3 | 违反 CE-T1–T3 的典型错误码与修复 | P3 | ✅ 2026-02-14 |
| 三大支柱总览文档 | 全 | 本文档持续更新；与 INDEX、RESEARCH_ROADMAP 同步 | 持续 |
| 英文版核心文档 | 全 | CORE_THEOREMS、FORMAL_FULL_MODEL 英文摘要 | P3 | ✅ 2026-02-14 |

### 6.4 持续机制

| 机制 | 触发 | 执行 |
| :--- | :--- | :--- |
| **版本发布** | Rust 稳定版 | RUST_RELEASE_TRACKING_CHECKLIST |
| **季度审查** | 每季度 | 三大支柱缺口复核；国际对标更新 |
| **链接检查** | 定期 | scripts/check_links.ps1 |

---

## 七、与现有文档的衔接

**组织架构**：研究笔记按三大支柱组织；首次使用见 [00_ORGANIZATION_AND_NAVIGATION](./00_ORGANIZATION_AND_NAVIGATION.md)。**完整总结与论证脉络**见 [00_COMPREHENSIVE_SUMMARY](./00_COMPREHENSIVE_SUMMARY.md)、[ARGUMENTATION_CHAIN_AND_FLOW](./ARGUMENTATION_CHAIN_AND_FLOW.md)。

| 本文档 | 现有文档 |
| :--- | :--- |
| 完整总结/论证脉络 | [00_COMPREHENSIVE_SUMMARY](./00_COMPREHENSIVE_SUMMARY.md)、[ARGUMENTATION_CHAIN_AND_FLOW](./ARGUMENTATION_CHAIN_AND_FLOW.md) |
| 批判性分析与改进计划 | [RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN](./RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md)（概念/属性/论证/矩阵/层次化/思维表征缺口与四阶段推进） |
| 支柱 1 | [FORMAL_FULL_MODEL_OVERVIEW](./FORMAL_FULL_MODEL_OVERVIEW.md)、[FORMAL_LANGUAGE_AND_PROOFS](./FORMAL_LANGUAGE_AND_PROOFS.md)、[CORE_THEOREMS_FULL_PROOFS](./CORE_THEOREMS_FULL_PROOFS.md)、[PROOF_INDEX](./PROOF_INDEX.md)、[formal_methods](./formal_methods/README.md)、[type_theory](./type_theory/README.md) |
| 支柱 2 | [LANGUAGE_SEMANTICS_EXPRESSIVENESS](./LANGUAGE_SEMANTICS_EXPRESSIVENESS.md)、[software_design_theory](./software_design_theory/README.md)、[02_workflow_safe_complete_models](./software_design_theory/02_workflow_safe_complete_models/README.md)、[04_expressiveness_boundary](./software_design_theory/02_workflow_safe_complete_models/04_expressiveness_boundary.md)、[06_boundary_analysis](./software_design_theory/03_execution_models/06_boundary_analysis.md) |
| 支柱 3 | [04_compositional_engineering](./software_design_theory/04_compositional_engineering/README.md)（含 CE-T1–T3、组合反例→错误码映射）、[03_integration_theory](./software_design_theory/04_compositional_engineering/03_integration_theory.md) |
| 国际对标 | [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](./INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md)、[AUTHORITATIVE_ALIGNMENT_CRITICAL_EVALUATION_2026_02](../07_project/AUTHORITATIVE_ALIGNMENT_CRITICAL_EVALUATION_2026_02.md) |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
