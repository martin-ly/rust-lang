# research_notes 全面梳理

> **创建日期**: 2026-02-26
> **最后更新**: 2026-02-28
> **Rust 版本**: 1.93.1+ (Edition 2024)
> **状态**: ✅ 梳理完成
> **用途**: 统一说明 research_notes 实际结构、归档约定、入口与索引关系，便于维护与查找

---

## 一、梳理目标

1. **结构透明**：实际目录与文件清单与 README/INDEX 一致
2. **归档清晰**：已归档项（Aeneas、coq-of-rust、coq_skeleton）入口统一指向 archive
3. **版本统一**：全目录元数据默认 Rust 1.93.1+ (Edition 2024)
4. **单入口**：首次使用从 [00_ORGANIZATION_AND_NAVIGATION](./00_ORGANIZATION_AND_NAVIGATION.md) 或 [README](./README.md) 进入

---

## 二、实际目录结构（当前）

```text
research_notes/
├── 00_ORGANIZATION_AND_NAVIGATION.md   # 按目标导航（推荐首读）
├── 00_COMPREHENSIVE_SUMMARY.md         # 完整总结、知识地图、论证总览
├── README.md                           # 主入口、研究方向、规范
├── INDEX.md                            # 完整索引（按领域/主题）
├── QUICK_FIND.md                       # 按关键词/领域/目标查找
├── QUICK_REFERENCE.md                  # 按主题快速参考
│
├── formal_methods/                     # 形式化方法（六篇核心 + 思维表征与矩阵）
│   ├── README.md
│   ├── 00_completeness_gaps.md
│   ├── ownership_model.md
│   ├── borrow_checker_proof.md
│   ├── lifetime_formalization.md
│   ├── async_state_machine.md
│   ├── pin_self_referential.md
│   ├── send_sync_formalization.md
│   ├── AXIOMATIC_SEMANTICS.md
│   ├── FORMAL_METHODS_COMPLETENESS_CHECKLIST.md
│   ├── SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN.md
│   ├── # 思维导图 / 矩阵 / 决策树（选列）
│   ├── OWNERSHIP_CONCEPT_MINDMAP.md, VARIANCE_CONCEPT_MINDMAP.md
│   ├── ASYNC_CONCEPT_MINDMAP.md, WORKFLOW_CONCEPT_MINDMAP.md, DISTRIBUTED_CONCEPT_MINDMAP.md
│   ├── TYPE_SYSTEM_CONCEPT_MINDMAP.md, MEMORY_MODEL_MINDMAP.md, ERROR_HANDLING_MINDMAP.md
│   ├── CONCEPT_AXIOM_THEOREM_MATRIX.md, PROOF_COMPLETION_MATRIX.md, VERIFICATION_TOOLS_MATRIX.md
│   ├── DESIGN_PATTERN_SELECTION_DECISION_TREE.md, WORKFLOW_ENGINE_DECISION_TREE.md
│   └── …（其余见 formal_methods/README 与 INDEX）
│
├── type_theory/                        # 类型理论
│   ├── README.md, 00_completeness_gaps.md
│   ├── type_system_foundations.md, trait_system_formalization.md
│   ├── lifetime_formalization.md, advanced_types.md, variance_theory.md
│   └── construction_capability.md
│
├── software_design_theory/             # 设计模式、工作流、执行模型、组合、边界
│   ├── 00_MASTER_INDEX.md
│   ├── 01_design_patterns_formal/      # GoF 23
│   ├── 02_workflow_safe_complete_models/
│   ├── 03_execution_models/
│   ├── 04_compositional_engineering/
│   ├── 05_boundary_system/
│   ├── 06_rust_idioms.md, 07_anti_patterns.md
│   └── COMPREHENSIVE_ARGUMENTATION_GAP_ANALYSIS_AND_PLAN.md 等
│
├── experiments/                        # 实验研究
│   ├── README.md
│   ├── performance_benchmarks.md, memory_analysis.md
│   ├── compiler_optimizations.md, concurrency_performance.md
│   └── macro_expansion_performance.md
│
├── coq_skeleton/                       # ⚠️ 重定向：内容已迁至 archive/deprecated/coq_skeleton/
│   └── README.md                       # 仅保留重定向说明
│
├── # 根目录核心文档（选列）
├── FORMAL_FULL_MODEL_OVERVIEW.md, CORE_THEOREMS_FULL_PROOFS.md, PROOF_INDEX.md
├── FORMAL_LANGUAGE_AND_PROOFS.md, AUTHORITATIVE_ALIGNMENT_GUIDE.md
├── HIERARCHICAL_MAPPING_AND_SUMMARY.md, ARGUMENTATION_CHAIN_AND_FLOW.md
├── RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md, RUST_193_COUNTEREXAMPLES_INDEX.md
├── practical_applications.md, research_methodology.md
├── CONTRIBUTING.md, QUALITY_CHECKLIST.md, TEMPLATE.md, CHANGELOG.md
└── …（其余见 INDEX.md）
```

---

## 三、归档约定

以下内容**已归档**，本目录内仅保留重定向或索引说明：

| 原位置 | 归档位置 | 说明 |
| :--- | :--- | :--- |
| AENEAS_INTEGRATION_PLAN.md | [archive/deprecated/AENEAS_INTEGRATION_PLAN.md](../archive/deprecated/AENEAS_INTEGRATION_PLAN.md) | Aeneas 对接计划 |
| COQ_OF_RUST_INTEGRATION_PLAN.md | [archive/deprecated/COQ_OF_RUST_INTEGRATION_PLAN.md](../archive/deprecated/COQ_OF_RUST_INTEGRATION_PLAN.md) | coq-of-rust 对接计划 |
| COQ_ISABELLE_PROOF_SCAFFOLDING.md | [archive/deprecated/](../archive/deprecated/) | Coq/Isabelle 骨架说明 |
| coq_skeleton/（.v 等） | [archive/deprecated/coq_skeleton/](../archive/deprecated/coq_skeleton/) | Coq 证明骨架；本目录仅保留 [coq_skeleton/README.md](./coq_skeleton/README.md) 重定向 |

**引用建议**：新文档中提及 Aeneas、coq-of-rust、Coq 骨架时，链接至上述 `archive/deprecated/` 路径；INDEX/README 中已统一标注「已归档」。

---

## 四、入口与索引关系

| 文档 | 角色 | 何时用 |
| :--- | :--- | :--- |
| [00_ORGANIZATION_AND_NAVIGATION](./00_ORGANIZATION_AND_NAVIGATION.md) | 按目标选路径、三大支柱、层级 | 首次使用、不知道从哪看 |
| [README](./README.md) | 主入口、研究方向、规范、目录树 | 总览、规范 |
| [INDEX](./INDEX.md) | 完整列表、按领域/主题/证明 | 查具体文档、证明索引 |
| [QUICK_FIND](./QUICK_FIND.md) | 关键词/领域/目标 | 快速定位 |
| [QUICK_REFERENCE](./QUICK_REFERENCE.md) | 按主题快速参考 | 按主题查 |
| [HIERARCHICAL_MAPPING_AND_SUMMARY](./HIERARCHICAL_MAPPING_AND_SUMMARY.md) | 文档树、概念↔定理、文档↔思维表征 | 层次化检索、双向追溯 |
| 本文件 | 结构梳理、归档约定、版本 | 维护与一致性检查 |

---

## 五、版本与元数据约定

- **默认版本**：所有 research_notes 下文档元数据统一为 **Rust 1.93.1+ (Edition 2024)**（历史归档保留原版本）。
- **权威引用**：releases.rs [1.93.0](https://releases.rs/docs/1.93.0/)、
- [Rust 1.93.1 公告](https://blog.rust-lang.org/2026/02/12/Rust-1.93.1/)；
- 详见 [00_ORGANIZATION_AND_NAVIGATION § 六](./00_ORGANIZATION_AND_NAVIGATION.md#六权威来源与版本约定)。

---

## 六、formal_methods 文件清单（概览）

除六篇核心（ownership、borrow、lifetime、async、pin、send_sync）外，本目录还包含：

- **完备性与计划**：00_completeness_gaps、FORMAL_METHODS_COMPLETENESS_CHECKLIST、SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN
- **语义与基础**：AXIOMATIC_SEMANTICS、OPERATIONAL_SEMANTICS、SEPARATION_LOGIC、LOGICAL_FOUNDATIONS
- **思维导图**：*_CONCEPT_MINDMAP（OWNERSHIP、VARIANCE、ASYNC、WORKFLOW、DISTRIBUTED、TYPE_SYSTEM、MEMORY_MODEL、ERROR_HANDLING、UNSAFE、GENERICS_TRAITS、DESIGN_PATTERN、CONCURRENCY、LIFETIME、MACRO_SYSTEM）
- **矩阵**：CONCEPT_AXIOM_THEOREM_MATRIX、PROOF_COMPLETION_MATRIX、VERIFICATION_TOOLS_MATRIX、DESIGN_PATTERNS_MATRIX、
  DISTRIBUTED_PATTERNS_MATRIX、WORKFLOW_ENGINES_MATRIX、CONCURRENCY_SAFETY_MATRIX、FIVE_DIMENSIONAL_CONCEPT_MATRIX、
  PARADIGM_COMPARISON_MATRIX、RISK_ASSESSMENT_MATRIX、LEARNING_PROGRESSION_MATRIX、IMPLEMENTATION_PROGRESS_MATRIX 等
- **决策树**：*_DECISION_TREE（DESIGN_PATTERN_SELECTION、WORKFLOW_ENGINE、DISTRIBUTED_ARCHITECTURE、ASYNC_RUNTIME、ERROR_TYPE_SELECTION、OWNERSHIP_TRANSFER、TESTING_STRATEGY、ERROR_HANDLING、SERIALIZATION、VERIFICATION_TOOLS）
- **其他**：APPLICATION_TREES、PROOF_TECHNIQUES_MINDMAP、PROOF_STRATEGIES、FORMAL_FOUNDATIONS_INDEX、CASE_STUDIES 等

完整列表以 `formal_methods/` 下实际文件为准；详见 [formal_methods/README](./formal_methods/README.md)。

---

## 七、维护检查清单

- [ ] 新增文档时：在 INDEX.md 对应分类下添加条目；若为 formal_methods，在 formal_methods/README 或本文件 § 六 补充
- [ ] 归档文档时：在 README、INDEX 中将链接改为 archive 路径，并在本文件 § 三 补充
- [ ] 版本升级时：批量更新元数据「Rust 版本」及 00_ORGANIZATION § 六 的权威链接
- [ ] 季度核对：README 目录树、INDEX 核心文档列表、HIERARCHICAL_MAPPING 文档树与本文件 § 二 一致

---

## 八、100% 完成检查项（2026-02-28）

- [x] 实际目录与 README/INDEX 一致，入口统一 00_ORGANIZATION 与 README
- [x] 归档项（Aeneas、coq-of-rust、Coq 骨架、COQ_ISABELLE）全部指向 archive/deprecated，根目录仅保留重定向
- [x] 全目录元数据版本统一为 Rust 1.93.1+ (Edition 2024)
- [x] 核心导航与索引（README、INDEX、QUICK_FIND、00_ORGANIZATION）最后更新与状态一致（2026-02-28）
- [x] 状态/页脚「Rust 1.93.0 更新完成」已统一为「Rust 1.93.1+ 更新完成」
- [x] formal_methods 下版本元数据已统一为 1.93.1+
- [x] AUTHORITATIVE_ALIGNMENT_GUIDE 版本检查项为 1.93.1+

**完成标准**：上述项全部勾选即视为 research_notes 当前轮次 100% 完成；后续版本升级或归档变更时刷新本清单。

---

**维护者**: Rust 文档推进团队
