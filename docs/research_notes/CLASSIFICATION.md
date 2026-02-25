# 研究笔记分类体系

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 宗旨

为 research_notes 提供多维度分类与扩展路线，便于按角色、层次、主题快速定位文档。

---

## 一、按文档角色分类

| 角色 | 文档 | 用途 |
| :--- | :--- | :--- |
| **导航** | [README](README.md)、[00_ORGANIZATION_AND_NAVIGATION](00_ORGANIZATION_AND_NAVIGATION.md)、[INDEX](INDEX.md)、[QUICK_REFERENCE](QUICK_REFERENCE.md)、[QUICK_FIND](QUICK_FIND.md) | 入口、按目标导航、索引、快速查找 |
| **总结与论证脉络** | [00_COMPREHENSIVE_SUMMARY](00_COMPREHENSIVE_SUMMARY.md)、[ARGUMENTATION_CHAIN_AND_FLOW](ARGUMENTATION_CHAIN_AND_FLOW.md) | 完整总结综合、知识地图、论证思路与脉络关系 |
| **证明索引** | [PROOF_INDEX](PROOF_INDEX.md)、[ARGUMENTATION_GAP_INDEX](ARGUMENTATION_GAP_INDEX.md) | 公理-定理映射、缺口追踪 |
| **框架** | [COMPREHENSIVE_SYSTEMATIC_OVERVIEW](COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md)、[UNIFIED_SYSTEMATIC_FRAMEWORK](UNIFIED_SYSTEMATIC_FRAMEWORK.md)、[THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE](THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md) | 全局一致性、概念族谱、理论/论证架构 |
| **分析** | [LANGUAGE_SEMANTICS_EXPRESSIVENESS](LANGUAGE_SEMANTICS_EXPRESSIVENESS.md)、[DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md)、[SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md)、[RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) | 语义、设计理由、安全边界、92 特性 |
| **指南** | [FORMAL_PROOF_SYSTEM_GUIDE](FORMAL_PROOF_SYSTEM_GUIDE.md)、[FORMAL_VERIFICATION_GUIDE](FORMAL_VERIFICATION_GUIDE.md)、[BEST_PRACTICES](BEST_PRACTICES.md)、[CONTENT_ENHANCEMENT](CONTENT_ENHANCEMENT.md)、[WRITING_GUIDE](WRITING_GUIDE.md) | 论证规范、验证流程、实质内容自检 |
| **运维** | [CONTRIBUTING](CONTRIBUTING.md)、[MAINTENANCE_GUIDE](MAINTENANCE_GUIDE.md)、[CHANGELOG](CHANGELOG.md)、[STATISTICS](STATISTICS.md)、[QUALITY_CHECKLIST](QUALITY_CHECKLIST.md) | 贡献、维护、统计、质量 |
| **参考** | [GLOSSARY](GLOSSARY.md)、[RESOURCES](RESOURCES.md)、[FAQ](FAQ.md)、[EXAMPLE](EXAMPLE.md)、[GETTING_STARTED](GETTING_STARTED.md) | 术语、资源、示例、入门 |
| **规划** | [RESEARCH_ROADMAP](RESEARCH_ROADMAP.md)、[TASK_CHECKLIST](TASK_CHECKLIST.md)、[PROGRESS_TRACKING](PROGRESS_TRACKING.md)、[TASK_ORCHESTRATION_AND_EXECUTION_PLAN](../archive/process_reports/2026_02/TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md) | 路线图、任务、进展 |
| **内容** | formal_methods/、type_theory/、software_design_theory/、experiments/、practical_applications、research_methodology | 核心研究笔记 |

---

## 二、按知识层次分类

| 层次 | 内容 | 文档 |
| :--- | :--- | :--- |
| **理论基础** | 形式化定义、公理、定理 | formal_methods/、type_theory/ |
| **应用层** | 设计模式、Rust Idioms、反模式、边界 | software_design_theory/ |
| **工程层** | 组合、执行模型、43 完全 | 04_compositional_engineering、03_execution_models、02_complete_43 |
| **实验层** | 基准测试、内存分析、性能 | experiments/ |
| **综合层** | 实际案例、方法论 | practical_applications、research_methodology |

---

## 三、按主题域分类

| 主题域 | 子域 | 文档 |
| :--- | :--- | :--- |
| **内存与所有权** | 所有权、借用、智能指针、RAII | ownership_model、borrow_checker_proof、06_rust_idioms |
| **类型系统** | 类型基础、Trait、型变、高级类型 | type_theory/ |
| **生命周期** | 区域、outlives、NLL | formal_methods/lifetime、type_theory/lifetime |
| **并发与异步** | Future、Pin、Send/Sync、执行模型 | async_state_machine、pin_self_referential、03_execution_models |
| **安全与 unsafe** | 边界、契约、UB、安全抽象 | SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS、05_boundary_system、07_anti_patterns |
| **设计模式与工程** | GoF 23、43 完全、组合、边界 | 01_design_patterns_formal、02_workflow、04_compositional_engineering |
| **实验与性能** | 基准、内存、编译、并发、宏 | experiments/ |
| **版本与特性** | Rust 1.93、92、91 更新 | RUST_193_*、RUST_192_*、RUST_191_* |

---

## 四、按研究领域分类（扩展）

| 领域 | 文档数 | 子目录/文档 |
| :--- | :--- | :--- |
| **形式化方法** | 6 | 00_completeness_gaps、ownership、borrow、async、lifetime、pin |
| **类型理论** | 6 | 00_completeness_gaps、type_system、trait、lifetime、advanced、variance |
| **软件设计理论** | 7 模块 | 01_design_patterns、02_workflow、03_execution、04_compositional、05_boundary、06_idioms、07_anti_patterns |
| **实验研究** | 5 | performance、memory、compiler、concurrency、macro |
| **综合** | 2 | practical_applications、research_methodology |

---

## 五、扩展路线

### 5.1 内容扩展

| 方向 | 当前 | 可扩展 |
| :--- | :--- | :--- |
| **设计模式** | GoF 23 + 扩展 20（43 完全） | Actor、CSP、事件溯源 |
| **执行模型** | 同步/异步/并发/并行/分布式 | 更多运行时（rayon、actix） |
| **Rust 版本** | 1.93 为主 | 1.94+ 增量更新 |
| **国际权威** | RustBelt、Stacked Borrows、Tree Borrows、FLS | 新论文、规范 |

### 5.2 分类扩展

| 方向 | 当前 | 可扩展 |
| :--- | :--- | :--- |
| **按受众** | 研究者、贡献者 | 教学路径、工程路径 |
| **按难度** | 无 | L1–L4 层次标注 |
| **按依赖** | 分散 | 依赖图、学习顺序 |

### 5.3 索引扩展

| 方向 | 当前 | 可扩展 |
| :--- | :--- | :--- |
| **反例索引** | FORMAL_PROOF_SYSTEM_GUIDE | 反例按主题域分类 |
| **决策树索引** | 分散 | 决策树总索引 |
| **证明链索引** | PROOF_INDEX | 证明依赖图 |

---

## 六、快速查找指引

| 我想… | 入口 |
| :--- | :--- |
| **首次使用、按目标选路径** | [00_ORGANIZATION_AND_NAVIGATION](00_ORGANIZATION_AND_NAVIGATION.md) |
| 快速定位文档 | [QUICK_REFERENCE](QUICK_REFERENCE.md)、[QUICK_FIND](QUICK_FIND.md) |
| 理解文档角色 | 本表 § 一 |
| 按主题查 | [INDEX § 按主题分类](INDEX.md#-按主题分类) |
| 查证明与缺口 | [PROOF_INDEX](PROOF_INDEX.md)、[ARGUMENTATION_GAP_INDEX](ARGUMENTATION_GAP_INDEX.md) |
| 查设计理由 | [DESIGN_MECHANISM_RATIONALE](DESIGN_MECHANISM_RATIONALE.md) |
| 查 Rust 1.93 特性 | [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) |
| 查设计模式与反模式 | [software_design_theory](software_design_theory/README.md)、[07_anti_patterns](software_design_theory/07_anti_patterns.md) |

---

## 引用

- [INDEX](INDEX.md) — 完整索引
- [README](README.md) — 主入口
- [ARGUMENTATION_GAP_INDEX](ARGUMENTATION_GAP_INDEX.md) — 论证缺口
