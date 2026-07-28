# Canonical Boundary Patrol Report

**EN**: docs/content vs concept/ Canonical Boundary Overlap Risk Report
**Summary**: 基于 `scripts/check_canonical_boundary.py` 对 `docs/`、`content/` 与 `concept/` 的相似度扫描，识别可能违反 AGENTS.md §2 canonical 规则的高风险重复内容。

> **Rust 版本**: 1.97.1 (Edition 2024)
> **生成时间**: 2026-07-28
> **扫描参数**: threshold=0.60, min-concept-words=50
> **脚本**: `scripts/check_canonical_boundary.py`

---

## 一、扫描结果摘要

| 指标 | 数值 |
|---|---|
| 已扫描 `concept/` 页 | 527（跳过 13 个短页） |
| 已扫描 `docs/` 页 | 457 |
| 已扫描 `content/` 页 | 56 |
| 相似度 ≥ 0.60 的配对 | 1190 |
| 报告列出的 Top 对 | 20 |
| 完整 JSON | [`CANONICAL_BOUNDARY_PATROL_2026_07_28.json`](./CANONICAL_BOUNDARY_PATROL_2026_07_28.json) |

## 二、结论与建议

本次扫描的 1190 对高风险重叠主要集中在两类**合法摘要/研究笔记**路径：

1. `docs/03_reference/quick_reference/` —— 速查卡（cheatsheet），按 AGENTS.md §2 允许作为摘要存在；
2. `docs/12_research_notes/` —— 研究笔记，用于记录形式化推导与项目专属分析。

因此，**不触发任何自动修复**；本报告作为月度巡逻产物，供维护者人工复核是否存在超出摘要/笔记范畴的完整概念重复。

建议后续处理：

- 对 Top 20 中的每一对确认其外部文件是否仅保留摘要/链接/决策树；若存在完整概念正文，则迁移到 `concept/` 权威页并 stub 化外部文件。
- 下月再次运行 `python scripts/check_canonical_boundary.py --top 20 --json reports/CANONICAL_BOUNDARY_PATROL_YYYY_MM_DD.json` 观察趋势。

## 三、Top 20 高风险配对

[canonical-boundary] concept=527 (skipped 13 short) docs=457 content=56 threshold=0.6

[canonical-boundary] ⚠️ Found 1190 pairs with similarity >= 0.6
--------------------------------------------------------------------------------

1. similarity=0.878
   external: docs\03_reference\quick_reference\25_testing_cheatsheet.md — 🧪 Rust 测试速查卡 {#rust-测试速查卡}
   concept:  concept\06_ecosystem\09_testing_and_quality\01_testing_strategies.md — Rust 测试策略：从单元测试到属性验证
2. similarity=0.873
   external: docs\12_research_notes\05_type_theory\05_type_system_foundations.md — 类型系统基础 {#类型系统基础}
   concept:  concept\04_formal\00_type_theory\01_type_theory.md — Type Theory（类型论基础）
3. similarity=0.851
   external: docs\12_research_notes\05_type_theory\04_trait_system_formalization.md — Trait 系统形式化 {#trait-系统形式化}
   concept:  concept\02_intermediate\00_traits\01_traits.md — Trait 系统
4. similarity=0.851
   external: docs\03_reference\quick_reference\25_testing_cheatsheet.md — 🧪 Rust 测试速查卡 {#rust-测试速查卡}
   concept:  concept\01_foundation\10_testing_basics\01_testing_basics.md — 测试基础：从单元测试到集成测试
5. similarity=0.845
   external: docs\03_reference\quick_reference\25_testing_cheatsheet.md — 🧪 Rust 测试速查卡 {#rust-测试速查卡}
   concept:  concept\06_ecosystem\09_testing_and_quality\03_testing.md — 测试生态：单元测试、集成测试与验证策略
6. similarity=0.833
   external: docs\12_research_notes\02_formal_methods\13_testing_strategy_decision_tree.md — Rust 测试策略决策树 {#rust-测试策略决策树}
   concept:  concept\06_ecosystem\09_testing_and_quality\01_testing_strategies.md — Rust 测试策略：从单元测试到属性验证
7. similarity=0.826
   external: docs\12_research_notes\05_type_theory\01_advanced_types.md — 高级类型特性 {#高级类型特性}
   concept:  concept\04_formal\00_type_theory\01_type_theory.md — Type Theory（类型论基础）
8. similarity=0.825
   external: docs\03_reference\quick_reference\27_type_system.md — 🔷 Rust 类型系统速查卡 {#rust-类型系统速查卡}
   concept:  concept\04_formal\00_type_theory\01_type_theory.md — Type Theory（类型论基础）
9. similarity=0.822
   external: docs\12_research_notes\05_type_theory\01_advanced_types.md — 高级类型特性 {#高级类型特性}
   concept:  concept\04_formal\00_type_theory\10_dependent_refinement_types.md — 依赖类型与细化类型（Dependent Types and Refinement Types）
10. similarity=0.821
   external: docs\12_research_notes\02_formal_methods\13_testing_strategy_decision_tree.md — Rust 测试策略决策树 {#rust-测试策略决策树}
   concept:  concept\06_ecosystem\09_testing_and_quality\03_testing.md — 测试生态：单元测试、集成测试与验证策略
11. similarity=0.820
   external: docs\12_research_notes\05_type_theory\05_type_system_foundations.md — 类型系统基础 {#类型系统基础}
   concept:  concept\01_foundation\02_type_system\01_type_system.md — 类型系统基础
12. similarity=0.819
   external: docs\12_research_notes\02_formal_methods\13_testing_strategy_decision_tree.md — Rust 测试策略决策树 {#rust-测试策略决策树}
   concept:  concept\01_foundation\10_testing_basics\01_testing_basics.md — 测试基础：从单元测试到集成测试
13. similarity=0.807
   external: docs\12_research_notes\05_type_theory\05_type_system_foundations.md — 类型系统基础 {#类型系统基础}
   concept:  concept\04_formal\00_type_theory\10_dependent_refinement_types.md — 依赖类型与细化类型（Dependent Types and Refinement Types）
14. similarity=0.804
   external: docs\12_research_notes\02_formal_methods\03_borrow_checker_proof.md — 借用检查器证明 {#借用检查器证明}
   concept:  concept\01_foundation\01_ownership_borrow_lifetime\02_borrowing.md — 借用
15. similarity=0.802
   external: docs\12_research_notes\05_type_theory\05_type_system_foundations.md — 类型系统基础 {#类型系统基础}
   concept:  concept\04_formal\00_type_theory\09_type_system_reference.md — 类型系统参考（Type System Reference）
16. similarity=0.799
   external: docs\12_research_notes\05_type_theory\01_advanced_types.md — 高级类型特性 {#高级类型特性}
   concept:  concept\02_intermediate\01_generics\01_generics.md — 泛型系统
17. similarity=0.793
   external: docs\06_research\09_rust_for_linux_2026.md — Rust for Linux：2026 年全景与工程实践 {#rust-for-linux2026-年全景与工程实践}
   concept:  concept\07_future\04_research_and_experimental\04_rust_for_linux.md — Rust for Linux ：操作系统内核中的内存安全
18. similarity=0.791
   external: docs\03_reference\quick_reference\25_testing_cheatsheet.md — 🧪 Rust 测试速查卡 {#rust-测试速查卡}
   concept:  concept\06_ecosystem\00_toolchain\13_compiler_testing.md — rustc 编译器测试体系
19. similarity=0.789
   external: docs\12_research_notes\02_formal_methods\09_ownership_model.md — 所有权模型形式化 {#所有权模型形式化}
   concept:  concept\01_foundation\01_ownership_borrow_lifetime\01_ownership.md — 所有权
20. similarity=0.786
   external: docs\12_research_notes\08_software_design_theory\02_workflow\01_workflow_state_machine.md — 工作流状态机模式形式化定义 {#工作流状态机模式形式化定义}
   concept:  concept\03_advanced\01_async\15_state_machine_semantics.md — 状态机语义与工作流模型

... and 1170 more pairs
