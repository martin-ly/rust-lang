# 链接有效性检查报告

## 100% 验收说明（2026-02-26）

**归档排除**：`docs/archive/` 目录内损坏链接不纳入 100% 验收统计。验收目标为**非 archive 核心路径**损坏链接 ≤ 50。完整全量检查需运行 `npx markdown-link-check docs/**/*.md` 并排除 archive 后统计。

---

## 链接修复进度（2026-02-26）

### 第一批（research_notes 高影响）

| 文件 | 修复内容 | 状态 |
| :--- | :--- | :--- |
| research_notes/BEST_PRACTICES.md | ownership_model、borrow_checker_proof → formal_methods/ | ✅ |
| research_notes/CODE_DOC_FORMAL_MAPPING.md | 01_core_concepts → 02_reference/quick_reference | ✅ |
| research_notes/CODE_DOC_FORMAL_MAPPING.md | concurrency_model → send_sync_formalization | ✅ |
| research_notes/CODE_DOC_FORMAL_MAPPING.md | async_formalization → async_state_machine | ✅ |
| research_notes/COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | MIND_MAP_COLLECTION → 04_thinking/ | ✅ |
| research_notes/LANGUAGE_SEMANTICS_EXPRESSIVENESS.md | MULTI_DIMENSIONAL_CONCEPT_MATRIX → 04_thinking/ | ✅ |

### 第二批（rust-formal-engineering-system 路径修正，2026-02-26）

| 文件/目录 | 修复内容 | 状态 |
| :--- | :--- | :--- |
| rfes/02_practical_applications/memory, performance | ../../../../research_notes/ → ../../../research_notes/ | ✅ |
| rfes/02_programming_paradigms/01_sync, 02_async, 09_actor | 同上 | ✅ |
| rfes/03_design_patterns/04_concurrent | 同上 | ✅ |
| rfes/05_software_engineering/07_testing | 同上；type_system_formalization → type_theory/type_system_foundations | ✅ |
| rfes/06_toolchain_ecosystem/* | 同上；quick_reference → 02_reference/quick_reference | ✅ |
| rfes/09_research_agenda/04_research_methods | ../../../../../ → ../../../ | ✅ |
| rfes/README, 00_master_index, 10_quality_assurance | THINKING_REPRESENTATION、MULTI_DIMENSIONAL、TESTING_COVERAGE 路径 | ✅ |

### 第三批（research_notes/README）

| 文件 | 修复内容 | 状态 |
| :--- | :--- | :--- |
| research_notes/README.md | quick_reference → 02_reference/quick_reference；研究议程→04_research_methods | ✅ |

### 第四批（2026-02-26 追加）

| 文件 | 修复内容 | 状态 |
| :--- | :--- | :--- |
| 01_learning/LEARNING_PATH_PLANNING.md | ../../rust-formal-engineering-system → ../rust-formal-engineering-system | ✅ |
| research_notes/PROOF_INDEX.md | ../software_design_theory → ./software_design_theory | ✅ |
| rust-formal-engineering-system/03_design_patterns/README.md | ../../../research_notes → ../../research_notes | ✅ |
| research_notes/BEST_PRACTICES.md | 错误示例路径 /docs/research_notes/ → wrong/absolute/path/ | ✅ |
| 04_thinking/APPLICATIONS_ANALYSIS_VIEW.md | #no_std → #no_std-与嵌入式支持（锚点） | ✅ |

### 第五批（2026-02-26 追加）

| 文件 | 修复内容 | 状态 |
| :--- | :--- | :--- |
| research_notes/CODE_DOC_FORMAL_MAPPING.md | EDGE_CASES → ../02_reference/EDGE_CASES_AND_SPECIAL_CASES.md；async_formalization → async_state_machine | ✅ |
| research_notes/00_COMPREHENSIVE_SUMMARY.md | RESEARCH_NOTES_CRITICAL、FORMAT_AND_CONTENT → archive/process_reports/2026_02/ | ✅ |
| research_notes/00_ORGANIZATION_AND_NAVIGATION.md | RESEARCH_NOTES_CRITICAL → archive/process_reports/2026_02/ | ✅ |
| research_notes/ARGUMENTATION_GAP_INDEX.md | RESEARCH_NOTES_CRITICAL → archive/process_reports/2026_02/ | ✅ |
| research_notes/CLASSIFICATION.md | TASK_ORCHESTRATION_AND_EXECUTION_PLAN → archive/process_reports/2026_02/ | ✅ |
| research_notes/INDEX.md | RESEARCH_NOTES_CRITICAL、FORMAT_AND_CONTENT → archive/process_reports/2026_02/ | ✅ |
| research_notes/HIERARCHICAL_MAPPING_AND_SUMMARY.md | RESEARCH_NOTES_CRITICAL → archive/process_reports/2026_02/ | ✅ |
| research_notes/CONTENT_ENHANCEMENT.md | RESEARCH_NOTES_CRITICAL → archive/process_reports/2026_02/ | ✅ |
| research_notes/CONTRIBUTING.md | FORMAT_AND_CONTENT_ALIGNMENT_PLAN → archive/process_reports/2026_02/ | ✅ |

### 第六批（2026-02-26 设计模式矩阵）

| 文件 | 修复内容 | 状态 |
| :--- | :--- | :--- |
| software_design_theory/.../DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 8.1 内部链接 rust_design_patterns/ownership/typestate/zero_cost → 05_guides、formal_methods、06_rust_idioms、generics_cheatsheet | ✅ |
| software_design_theory/.../DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 23 个 examples/xxx.rs(#) → 各模式 01_creational/、02_structural/、03_behavioral/ .md | ✅ |
| software_design_theory/.../DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 附录 deState 笔误 → State | ✅ |
| software_design_theory/.../04_boundary_matrix.md | 04_compositional_engineering/README.md → ../04_compositional_engineering/README.md | ✅ |

### 第七批（2026-02-26 收尾）

| 文件 | 修复内容 | 状态 |
| :--- | :--- | :--- |
| research_notes/AUTHORITATIVE_ALIGNMENT_GUIDE.md | 差异标记模板占位符 (链接) → https://doc.rust-lang.org/book/ | ✅ |

### 第八批（2026-02-26 路径规范化）

| 文件 | 修复内容 | 状态 |
| :--- | :--- | :--- |
| research_notes/CODE_DOC_FORMAL_MAPPING.md | ../research_notes/formal_methods → ./formal_methods；../research_notes/type_theory → ./type_theory | ✅ |

### 第九批（2026-02-26 rust-formal-engineering-system 路径）

| 文件 | 修复内容 | 状态 |
| :--- | :--- | :--- |
| research_notes/QUICK_REFERENCE.md | ../../rust-formal-engineering-system → ../rust-formal-engineering-system | ✅ |
| research_notes/SYSTEM_SUMMARY.md | 同上 | ✅ |
| research_notes/SYSTEM_INTEGRATION.md | 同上 | ✅ |
| research_notes/EXAMPLE.md | 同上 | ✅ |
| research_notes/research_methodology.md | 同上 | ✅ |
| research_notes/type_theory/*.md | ../../../rust-formal-engineering-system → ../../rust-formal-engineering-system（variance_theory、lifetime_formalization、trait_system_formalization、type_system_foundations） | ✅ |
| research_notes/formal_methods/lifetime_formalization.md | 同上 | ✅ |

### 第十批（2026-02-26 software_design_theory 内部路径）

| 文件 | 修复内容 | 状态 |
| :--- | :--- | :--- |
| software_design_theory/02_workflow_safe_complete_models/02_complete_43_catalog.md | ../../04_compositional_engineering、05_boundary_system、06_rust_idioms、01_design_patterns_formal → ../ | ✅ |
| software_design_theory/02_workflow_safe_complete_models/03_semantic_boundary_map.md | ../../01_design_patterns_formal、03_execution_models → ../ | ✅ |
| software_design_theory/02_workflow_safe_complete_models/04_expressiveness_boundary.md | ../../03_execution_models、04_compositional_engineering → ../ | ✅ |

### 第十一批（2026-02-26 补充修复）

| 文件 | 修复内容 | 状态 |
| :--- | :--- | :--- |
| research_notes/research_methodology.md | 00_index.md → README.md（09_research_agenda/04_research_methods 路径） | ✅ |
| research_notes/PROOF_INDEX.md | ../experiments → ./experiments | ✅ |

### 第十二批（2026-02-26 持续推进）

| 文件 | 修复内容 | 状态 |
| :--- | :--- | :--- |
| research_notes/practical_applications.md | ../formal_methods/async_state_machine → ./formal_methods/async_state_machine | ✅ |
| research_notes/INDEX.md | COMPREHENSIVE_REVIEW_REPORT_2026_02 → archive/process_reports/2026_02/ | ✅ |

> **说明**：上述修复已应用。2026-02-26 对 QUICK_REFERENCE、SYSTEM_SUMMARY、02_complete_43_catalog 等抽样验证：`../rust-formal-engineering-system`、`../04_compositional_engineering` 等路径均通过。完整全量检查需运行 `npx markdown-link-check docs/**/*.md` 以更新统计；剩余损坏多为锚点编码（Phase 4 低优先级）及 archive 历史文档。

---

## 统计

| 类别 | 数量 |
| :--- | :--- |
| 总链接数 | 14408 |
| 有效链接 | 12762 |
| 损坏链接 | 655 |
| 外部链接 | 967 |
| 仅锚点链接 | 7054 |

## 损坏链接清单（按问题类型分组）

### 文件不存在 (357个)

| 源文件 | 链接文本 | 链接路径 | 问题 |
| :--- | :--- | :--- | :--- |
| docs\LINK_REPAIR_COMPLETION_REPORT.md | 归档路径 | `../archive/process_reports/2026_02/` | 文件不存在: archive\process_reports\2026_02 |
| docs\01_learning\LEARNING_PATH_PLANNING.md | 形式化工程系统 | `../rust-formal-engineering-system/` | ✅ 已修复 |
| docs\archive\process_reports\LINK_FIX_PLAN_2026_02.md | PROJECT_CRITICAL_EVALUATION_REPORT_2026_02.md | `./PROJECT_CRITICAL_EVALUATION_REPORT_2026_02.md` | 文件不存在: docs\archive\process_reports\PROJECT_CRITICAL_EVALUATION_REPORT_2026_02.md |
| docs\archive\process_reports\2026_02\project\ONE_PAGE_SUMMARY_TEMPLATE.md | {}_cheatsheet | `../../../../02_reference/quick_reference/{}_cheatsheet.md` | 文件不存在: docs\02_reference\quick_reference\{}_cheatsheet.md |
| docs\archive\reports\RUST_1.91_FEATURES_COMPREHENSIVE.md | Rust 1.91 vs 1.90 对比文档 | `./toolchain/04_rust_1.91_vs_1.90_comparison.md` | 文件不存在: docs\archive\reports\toolchain\04_rust_1.91_vs_1.90_comparison.md |
| docs\archive\reports\formal_system_reports\DOCUMENTATION_ENHANCEMENT_REPORT_2025_09_27.md | README.md | `./README.md` | 文件不存在: docs\archive\reports\formal_system_reports\README.md |
| docs\archive\reports\formal_system_reports\RUST_1_91_QUICK_REFERENCE.md | `01_theoretical_foundations/02_memory_safety/03_dangling_pointer_warnings_rust_1_91.md` | `./01_theoretical_foundations/02_memory_safety/03_dangling_pointer_warnings_rust_1_91.md` | 文件不存在: docs\archive\reports\formal_system_reports\01_theoretical_foundations\02_memory_safety\03_dangling_pointer_warnings_rust_1_91.md |
| docs\archive\reports\formal_system_reports\RUST_1_91_QUICK_REFERENCE.md | `01_theoretical_foundations/01_type_system/core_theory/08_pattern_matching_improvements_rust_1_91.md` | `./01_theoretical_foundations/01_type_system/core_theory/08_pattern_matching_improvements_rust_1_91.md` | 文件不存在: docs\archive\reports\formal_system_reports\01_theoretical_foundations\01_type_system\core_theory\08_pattern_matching_improvements_rust_1_91.md |
| docs\archive\reports\formal_system_reports\RUST_1_91_QUICK_REFERENCE.md | `06_toolchain_ecosystem/01_compiler/03_arm_windows_tier1_support_rust_1_91.md` | `./06_toolchain_ecosystem/01_compiler/03_arm_windows_tier1_support_rust_1_91.md` | 文件不存在: docs\archive\reports\formal_system_reports\06_toolchain_ecosystem\01_compiler\03_arm_windows_tier1_support_rust_1_91.md |
| docs\archive\reports\formal_system_reports\RUST_1_91_QUICK_REFERENCE.md | Rust 1.91.0 更新日志 | `./RUST_1_91_CHANGELOG.md` | 文件不存在: docs\archive\reports\formal_system_reports\RUST_1_91_CHANGELOG.md |
| docs\archive\reports\formal_system_reports\RUST_1_91_QUICK_REFERENCE.md | Rust 1.91 更新总结 | `./RUST_1_91_UPDATE_SUMMARY.md` | 文件不存在: docs\archive\reports\formal_system_reports\RUST_1_91_UPDATE_SUMMARY.md |
| docs\archive\reports\formal_system_reports\RUST_1_91_QUICK_REFERENCE.md | 悬空指针警告机制 | `./01_theoretical_foundations/02_memory_safety/03_dangling_pointer_warnings_rust_1_91.md` | 文件不存在: docs\archive\reports\formal_system_reports\01_theoretical_foundations\02_memory_safety\03_dangling_pointer_warnings_rust_1_91.md |
| docs\archive\reports\formal_system_reports\RUST_1_91_QUICK_REFERENCE.md | 模式匹配改进 | `./01_theoretical_foundations/01_type_system/core_theory/08_pattern_matching_improvements_rust_1_91.md` | 文件不存在: docs\archive\reports\formal_system_reports\01_theoretical_foundations\01_type_system\core_theory\08_pattern_matching_improvements_rust_1_91.md |
| docs\archive\reports\formal_system_reports\RUST_1_91_QUICK_REFERENCE.md | ARM Windows Tier 1 支持 | `./06_toolchain_ecosystem/01_compiler/03_arm_windows_tier1_support_rust_1_91.md` | 文件不存在: docs\archive\reports\formal_system_reports\06_toolchain_ecosystem\01_compiler\03_arm_windows_tier1_support_rust_1_91.md |
| docs\archive\root_completion_reports\COMPLETION_SUMMARY_2025_12_25.md | PROGRESS_TRACKING.md | `./PROGRESS_TRACKING.md` | 文件不存在: docs\archive\root_completion_reports\PROGRESS_TRACKING.md |
| docs\archive\root_completion_reports\COMPREHENSIVE_PROGRESS_REPORT_2025_12_25.md | PROGRESS_TRACKING.md | `./PROGRESS_TRACKING.md` | 文件不存在: docs\archive\root_completion_reports\PROGRESS_TRACKING.md |
| docs\archive\root_completion_reports\FINAL_100_PERCENT_COMPLETION_REPORT_2026_01_27.md | run_workspace_tests.ps1 | `scripts/run_workspace_tests.ps1` | 文件不存在: docs\archive\root_completion_reports\scripts\run_workspace_tests.ps1 |
| docs\archive\root_completion_reports\FINAL_COMPLETION_STATUS_2025_12_25.md | PROGRESS_TRACKING.md | `./PROGRESS_TRACKING.md` | 文件不存在: docs\archive\root_completion_reports\PROGRESS_TRACKING.md |
| docs\archive\root_completion_reports\ULTIMATE_COMPLETION_REPORT_2025_12_25.md | PROGRESS_TRACKING.md | `./PROGRESS_TRACKING.md` | 文件不存在: docs\archive\root_completion_reports\PROGRESS_TRACKING.md |
| docs\archive\spell_check\SPELL_CHECK_FINAL_COMPLETION.md | 快速指南 | `./QUICK_START_SPELL_CHECK.md` | 文件不存在: docs\archive\spell_check\QUICK_START_SPELL_CHECK.md |
| docs\archive\spell_check\SPELL_CHECK_SETUP_SUMMARY.md | 快速启动指南 | `./QUICK_START_SPELL_CHECK.md` | 文件不存在: docs\archive\spell_check\QUICK_START_SPELL_CHECK.md |
| docs\archive\spell_check\SPELL_CHECK_SETUP_SUMMARY.md | VS Code 配置 | `./.vscode/settings.json` | 文件不存在: docs\archive\spell_check\.vscode\settings.json |
| docs\archive\spell_check\SPELL_CHECK_SETUP_SUMMARY.md | cSpell 配置 | `./cspell.json` | 文件不存在: docs\archive\spell_check\cspell.json |
| docs\archive\spell_check\SPELL_CHECK_SETUP_SUMMARY.md | 推荐扩展 | `./.vscode/extensions.json` | 文件不存在: docs\archive\spell_check\.vscode\extensions.json |
| docs\archive\spell_check\SPELL_CHECK_SETUP_SUMMARY.md | 快速启动指南 | `./QUICK_START_SPELL_CHECK.md` | 文件不存在: docs\archive\spell_check\QUICK_START_SPELL_CHECK.md |
| docs\archive\spell_check\SPELL_CHECK_SUPPLEMENT_REPORT.md | 快速启动指南 | `./QUICK_START_SPELL_CHECK.md` | 文件不存在: docs\archive\spell_check\QUICK_START_SPELL_CHECK.md |
| docs\archive\temp\FORMAL_AND_PRACTICAL_NAVIGATION.md | 并发模型形式化理论 | `../../rust-formal-engineering-system/01_theoretical_foundations/04_concurrency_models/` | 文件不存在: docs\rust-formal-engineering-system\01_theoretical_foundations\04_concurrency_models |
| docs\archive\temp\FORMAL_AND_PRACTICAL_NAVIGATION.md | Reactor 模式实现 | `../../../../crates/c06_async/src/reactor/` | 文件不存在: E:\_src\crates\c06_async\src\reactor |
| docs\archive\temp\FORMAL_AND_PRACTICAL_NAVIGATION.md | 宏系统形式化理论 | `../../rust-formal-engineering-system/01_theoretical_foundations/08_macro_system/` | 文件不存在: docs\rust-formal-engineering-system\01_theoretical_foundations\08_macro_system |
| docs\archive\temp\FORMAL_AND_PRACTICAL_NAVIGATION.md | 泛型系统形式化理论 | `../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/generics/` | 文件不存在: docs\rust-formal-engineering-system\01_theoretical_foundations\01_type_system\generics |
| docs\archive\temp\FORMAL_AND_PRACTICAL_NAVIGATION.md | 完整度报告 | `../../rust-formal-engineering-system/COMPLETION_STATUS_REAL_2025_10_30.md` | 文件不存在: docs\rust-formal-engineering-system\COMPLETION_STATUS_REAL_2025_10_30.md |
| docs\archive\temp\QUICK_REFERENCE.md | 完整学习路径 | `./README.md#学习路径推荐` | 文件不存在: docs\archive\temp\README.md |
| docs\archive\temp\QUICK_REFERENCE.md | 学习检查清单 | `./LEARNING_CHECKLIST.md` | 文件不存在: docs\archive\temp\LEARNING_CHECKLIST.md |
| docs\archive\temp\QUICK_REFERENCE.md | 贡献指南 | `./CONTRIBUTING.md` | 文件不存在: docs\archive\temp\CONTRIBUTING.md |
| docs\archive\temp\QUICK_START_SPELL_CHECK.md | SPELL_CHECK_CONFIGURATION.md | `./SPELL_CHECK_CONFIGURATION.md` | 文件不存在: docs\archive\temp\SPELL_CHECK_CONFIGURATION.md |
| docs\archive\temp\REFERENCE_VALIDITY_MODEL_ALIGNMENT.md | 🛡️ 资源安全理论 | `./01_theory/04_memory_safety_theory.md` | 文件不存在: docs\archive\temp\01_theory\04_memory_safety_theory.md |
| docs\archive\temp\REFERENCE_VALIDITY_MODEL_ALIGNMENT.md | 🛡️ 资源安全保证 | `./04_safety/01_memory_safety.md` | 文件不存在: docs\archive\temp\04_safety\01_memory_safety.md |
| docs\archive\temp\swap\RUST_190_FAQ.md | 主报告 | `RUST_190_CONTENT_ALIGNMENT_REPORT_2025_10_26.md` | 文件不存在: docs\archive\temp\swap\RUST_190_CONTENT_ALIGNMENT_REPORT_2025_10_26.md |
| docs\archive\temp\swap\RUST_190_FAQ.md | Phase 2 完成报告 | `RUST_190_PHASE2_完成报告_2025_10_26.md` | 文件不存在: docs\archive\temp\swap\RUST_190_PHASE2_完成报告_2025_10_26.md |
| docs\archive\temp\swap\RUST_190_FAQ.md | 完整会话总结 | `RUST_190_完整会话总结_2025_10_26.md` | 文件不存在: docs\archive\temp\swap\RUST_190_完整会话总结_2025_10_26.md |
| docs\archive\temp\swap\RUST_190_FAQ.md | 主报告 | `RUST_190_CONTENT_ALIGNMENT_REPORT_2025_10_26.md` | 文件不存在: docs\archive\temp\swap\RUST_190_CONTENT_ALIGNMENT_REPORT_2025_10_26.md |
| docs\archive\temp\swap\RUST_190_GLOSSARY.md | 主报告 | `RUST_190_CONTENT_ALIGNMENT_REPORT_2025_10_26.md` | 文件不存在: docs\archive\temp\swap\RUST_190_CONTENT_ALIGNMENT_REPORT_2025_10_26.md |
| docs\archive\temp\swap\RUST_190_GLOSSARY.md | 完整会话总结 | `RUST_190_完整会话总结_2025_10_26.md` | 文件不存在: docs\archive\temp\swap\RUST_190_完整会话总结_2025_10_26.md |
| docs\archive\temp\swap\RUST_190_QUICK_NAVIGATION.md | RUST*190*完整会话总结\_2025_10_26.md | `RUST_190_完整会话总结_2025_10_26.md` | 文件不存在: docs\archive\temp\swap\RUST_190_完整会话总结_2025_10_26.md |
| docs\archive\temp\swap\RUST_190_QUICK_NAVIGATION.md | 完整会话总结 | `RUST_190_完整会话总结_2025_10_26.md` | 文件不存在: docs\archive\temp\swap\RUST_190_完整会话总结_2025_10_26.md |
| docs\archive\temp\swap\RUST_190_QUICK_NAVIGATION.md | 主报告 | `RUST_190_CONTENT_ALIGNMENT_REPORT_2025_10_26.md` | 文件不存在: docs\archive\temp\swap\RUST_190_CONTENT_ALIGNMENT_REPORT_2025_10_26.md |
| docs\archive\temp\swap\RUST_190_QUICK_NAVIGATION.md | RUST_190_DOCUMENTATION_INDEX.md | `RUST_190_DOCUMENTATION_INDEX.md` | 文件不存在: docs\archive\temp\swap\RUST_190_DOCUMENTATION_INDEX.md |
| docs\archive\temp\swap\RUST_190_QUICK_NAVIGATION.md | 完整索引 | `RUST_190_DOCUMENTATION_INDEX.md` | 文件不存在: docs\archive\temp\swap\RUST_190_DOCUMENTATION_INDEX.md |
| docs\archive\version_reports\RUST_192_THINKING_REPRESENTATION_COMPLETION.md | DECISION_GRAPH_NETWORK.md | `./DECISION_GRAPH_NETWORK.md` | 文件不存在: docs\archive\version_reports\DECISION_GRAPH_NETWORK.md |
| docs\archive\version_reports\RUST_192_THINKING_REPRESENTATION_COMPLETION.md | PROOF_GRAPH_NETWORK.md | `./PROOF_GRAPH_NETWORK.md` | 文件不存在: docs\archive\version_reports\PROOF_GRAPH_NETWORK.md |
| docs\research_notes\00_COMPREHENSIVE_SUMMARY.md | RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN | `./RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md` | 文件不存在: docs\research_notes\RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md |
| docs\research_notes\00_COMPREHENSIVE_SUMMARY.md | FORMAT_AND_CONTENT_ALIGNMENT_PLAN | `FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md` | 文件不存在: docs\research_notes\FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md |
| docs\research_notes\00_ORGANIZATION_AND_NAVIGATION.md | RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN | `./RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md` | 文件不存在: docs\research_notes\RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md |
| docs\research_notes\ARGUMENTATION_GAP_INDEX.md | RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN | `RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md` | 文件不存在: docs\research_notes\RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md |
| docs\research_notes\BEST_PRACTICES.md | 研究路线图 | `/docs/research_notes/RESEARCH_ROADMAP.md` | 文件不存在: docs\docs\research_notes\RESEARCH_ROADMAP.md |
| docs\research_notes\BEST_PRACTICES.md | 所有权模型形式化 | `./ownership_model.md` | 文件不存在: docs\research_notes\ownership_model.md |
| docs\research_notes\BEST_PRACTICES.md | 借用检查器证明 | `./borrow_checker_proof.md` | 文件不存在: docs\research_notes\borrow_checker_proof.md |
| docs\research_notes\CLASSIFICATION.md | TASK_ORCHESTRATION_AND_EXECUTION_PLAN | `TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md` | 文件不存在: docs\research_notes\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 所有权 | `../01_core_concepts/C01_ownership_borrowing.md` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 所有权 | `../01_core_concepts/C01_ownership_borrowing.md#移动语义` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 函数参数 | `../01_core_concepts/C01_ownership_borrowing.md#函数参数` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 借用 | `../01_core_concepts/C01_ownership_borrowing.md#引用与借用` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 生命周期 | `../01_core_concepts/C01_ownership_borrowing.md#生命周期` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 结构体生命周期 | `../01_core_concepts/C01_ownership_borrowing.md#生命周期标注` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 生命周期省略 | `../01_core_concepts/C01_ownership_borrowing.md#生命周期省略规则` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C04 泛型 | `../01_core_concepts/C04_generics_traits.md` | 文件不存在: docs\01_core_concepts\C04_generics_traits.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C04 泛型结构体 | `../01_core_concepts/C04_generics_traits.md#泛型结构体` | 文件不存在: docs\01_core_concepts\C04_generics_traits.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C04 Trait Bound | `../01_core_concepts/C04_generics_traits.md#trait-bound` | 文件不存在: docs\01_core_concepts\C04_generics_traits.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C04 Trait 定义 | `../01_core_concepts/C04_generics_traits.md#定义-trait` | 文件不存在: docs\01_core_concepts\C04_generics_traits.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C04 Trait 实现 | `../01_core_concepts/C04_generics_traits.md#实现-trait` | 文件不存在: docs\01_core_concepts\C04_generics_traits.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C05 线程 | `../01_core_concepts/C05_thread_synchronization.md#创建线程` | 文件不存在: docs\01_core_concepts\C05_thread_synchronization.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C05 Arc + Mutex | `../01_core_concepts/C05_thread_synchronization.md#共享状态并发` | 文件不存在: docs\01_core_concepts\C05_thread_synchronization.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C05 消息传递 | `../01_core_concepts/C05_thread_synchronization.md#消息传递` | 文件不存在: docs\01_core_concepts\C05_thread_synchronization.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C06 异步 | `../01_core_concepts/C06_async_await.md#async-函数` | 文件不存在: docs\01_core_concepts\C06_async_await.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C06 任务调度 | `../01_core_concepts/C06_async_await.md#任务调度` | 文件不存在: docs\01_core_concepts\C06_async_await.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C02 Vec | `../01_core_concepts/C02_type_system.md#vec` | 文件不存在: docs\01_core_concepts\C02_type_system.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C02 HashMap | `../01_core_concepts/C02_type_system.md#hashmap` | 文件不存在: docs\01_core_concepts\C02_type_system.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C02 String | `../01_core_concepts/C02_type_system.md#string` | 文件不存在: docs\01_core_concepts\C02_type_system.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C07 I/O | `../01_core_concepts/C07_io_operations.md#读取文件` | 文件不存在: docs\01_core_concepts\C07_io_operations.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C07 进程 | `../01_core_concepts/C07_process_management.md#运行外部命令` | 文件不存在: docs\01_core_concepts\C07_process_management.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 C-T1 - Arc 安全 | `../research_notes/formal_methods/concurrency_model.md#定理-c-t1-arc-安全` | 文件不存在: docs\research_notes\formal_methods\concurrency_model.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 C-T2 - Mutex 互斥 | `../research_notes/formal_methods/concurrency_model.md#定理-c-t2-mutex-互斥` | 文件不存在: docs\research_notes\formal_methods\concurrency_model.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 C-T3 - 读写锁 | `../research_notes/formal_methods/concurrency_model.md#定理-c-t3-读写锁` | 文件不存在: docs\research_notes\formal_methods\concurrency_model.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定义 - Send | `../research_notes/formal_methods/concurrency_model.md#定义-send` | 文件不存在: docs\research_notes\formal_methods\concurrency_model.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定义 - Sync | `../research_notes/formal_methods/concurrency_model.md#定义-sync` | 文件不存在: docs\research_notes\formal_methods\concurrency_model.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定义 - 异步函数 | `../research_notes/formal_methods/async_formalization.md#定义-异步函数` | 文件不存在: docs\research_notes\formal_methods\async_formalization.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 A-T1 - Await 正确性 | `../research_notes/formal_methods/async_formalization.md#定理-a-t1-await-正确性` | 文件不存在: docs\research_notes\formal_methods\async_formalization.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 A-T2 - Pin 安全性 | `../research_notes/formal_methods/async_formalization.md#定理-a-t2-pin-安全性` | 文件不存在: docs\research_notes\formal_methods\async_formalization.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | EDGE_CASES | `./EDGE_CASES_AND_SPECIAL_CASES.md` | 文件不存在: docs\research_notes\EDGE_CASES_AND_SPECIAL_CASES.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 借用 | `../01_core_concepts/C01_ownership_borrowing.md` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 借用检查器 | `../01_core_concepts/C01_ownership_borrowing.md` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 所有权 | `../01_core_concepts/C01_ownership_borrowing.md` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 借用 | `../01_core_concepts/C01_ownership_borrowing.md` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 生命周期 | `../01_core_concepts/C01_ownership_borrowing.md` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C06 异步 | `../01_core_concepts/C06_async_await.md` | 文件不存在: docs\01_core_concepts\C06_async_await.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C04 Trait | `../01_core_concepts/C04_generics_traits.md` | 文件不存在: docs\01_core_concepts\C04_generics_traits.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C02 类型推断 | `../01_core_concepts/C02_type_system.md` | 文件不存在: docs\01_core_concepts\C02_type_system.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C04 泛型 | `../01_core_concepts/C04_generics_traits.md` | 文件不存在: docs\01_core_concepts\C04_generics_traits.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C04 泛型 | `../01_core_concepts/C04_generics_traits.md` | 文件不存在: docs\01_core_concepts\C04_generics_traits.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C05 线程 | `../01_core_concepts/C05_thread_synchronization.md` | 文件不存在: docs\01_core_concepts\C05_thread_synchronization.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C01 所有权与借用 | `../01_core_concepts/C01_ownership_borrowing.md` | 文件不存在: docs\01_core_concepts\C01_ownership_borrowing.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C02 类型系统 | `../01_core_concepts/C02_type_system.md` | 文件不存在: docs\01_core_concepts\C02_type_system.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | C04 泛型与 Trait | `../01_core_concepts/C04_generics_traits.md` | 文件不存在: docs\01_core_concepts\C04_generics_traits.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | concurrency_model.md | `./formal_methods/concurrency_model.md` | 文件不存在: docs\research_notes\formal_methods\concurrency_model.md |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | async_formalization.md | `./formal_methods/async_formalization.md` | 文件不存在: docs\research_notes\formal_methods\async_formalization.md |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | 知识结构框架 | `../KNOWLEDGE_STRUCTURE_FRAMEWORK.md` | 文件不存在: docs\KNOWLEDGE_STRUCTURE_FRAMEWORK.md |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | MIND_MAP_COLLECTION | `../MIND_MAP_COLLECTION.md` | 文件不存在: docs\MIND_MAP_COLLECTION.md |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | MULTI_DIMENSIONAL_CONCEPT_MATRIX | `../MULTI_DIMENSIONAL_CONCEPT_MATRIX.md` | 文件不存在: docs\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | MULTI_DIMENSIONAL_CONCEPT_MATRIX | `../MULTI_DIMENSIONAL_CONCEPT_MATRIX.md` | 文件不存在: docs\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | KNOWLEDGE_STRUCTURE_FRAMEWORK | `../KNOWLEDGE_STRUCTURE_FRAMEWORK.md` | 文件不存在: docs\KNOWLEDGE_STRUCTURE_FRAMEWORK.md |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | MULTI_DIMENSIONAL_CONCEPT_MATRIX | `../MULTI_DIMENSIONAL_CONCEPT_MATRIX.md` | 文件不存在: docs\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | MIND_MAP_COLLECTION | `../MIND_MAP_COLLECTION.md` | 文件不存在: docs\MIND_MAP_COLLECTION.md |
| docs\research_notes\CONTENT_ENHANCEMENT.md | RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN | `RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md` | 文件不存在: docs\research_notes\RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md |
| docs\research_notes\CONTENT_ENHANCEMENT.md | RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN | `RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md` | 文件不存在: docs\research_notes\RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md |
| docs\research_notes\CONTENT_ENHANCEMENT.md | xx | `path/to/doc.md` | 文件不存在: docs\research_notes\path\to\doc.md |
| docs\research_notes\CONTENT_ENHANCEMENT.md | 所有权实现 | `../../../crates/c01_ownership_borrow_scope/src/` | 文件不存在: E:\_src\crates\c01_ownership_borrow_scope\src |
| docs\research_notes\CONTENT_ENHANCEMENT.md | 所有权文档 | `../../../crates/c01_ownership_borrow_scope/docs/` | 文件不存在: E:\_src\crates\c01_ownership_borrow_scope\docs |
| docs\research_notes\CONTRIBUTING.md | FORMAT_AND_CONTENT_ALIGNMENT_PLAN | `FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md` | 文件不存在: docs\research_notes\FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md |
| docs\research_notes\EXAMPLE.md | 所有权系统实现 | `../../rust-formal-engineering-system/01_theoretical_foundations/02_ownership_system/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\02_ownership_system |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN | `./RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md` | 文件不存在: docs\research_notes\RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN | `RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md` | 文件不存在: docs\research_notes\RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md |
| docs\research_notes\INDEX.md | RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md | `./RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md` | 文件不存在: docs\research_notes\RESEARCH_NOTES_CRITICAL_ANALYSIS_AND_IMPROVEMENT_PLAN.md |
| docs\research_notes\INDEX.md | FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md | `./FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md` | 文件不存在: docs\research_notes\FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md |
| docs\research_notes\INDEX.md | COMPREHENSIVE_REVIEW_REPORT_2026_02.md | `./COMPREHENSIVE_REVIEW_REPORT_2026_02.md` | 文件不存在: docs\research_notes\COMPREHENSIVE_REVIEW_REPORT_2026_02.md |
| docs\research_notes\LANGUAGE_SEMANTICS_EXPRESSIVENESS.md | MULTI_DIMENSIONAL_CONCEPT_MATRIX | `../MULTI_DIMENSIONAL_CONCEPT_MATRIX.md` | 文件不存在: docs\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md |
| docs\research_notes\practical_applications.md | async_state_machine | `../formal_methods/async_state_machine.md` | 文件不存在: docs\formal_methods\async_state_machine.md |
| docs\research_notes\PROOF_INDEX.md | 05_boundary_system | `../software_design_theory/05_boundary_system/` | 文件不存在: docs\software_design_theory\05_boundary_system |
| docs\research_notes\PROOF_INDEX.md | 04_boundary_matrix | `../software_design_theory/01_design_patterns_formal/04_boundary_matrix.md` | 文件不存在: docs\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md |
| docs\research_notes\PROOF_INDEX.md | 06_boundary_analysis | `../software_design_theory/03_execution_models/06_boundary_analysis.md` | 文件不存在: docs\software_design_theory\03_execution_models\06_boundary_analysis.md |
| docs\research_notes\PROOF_INDEX.md | safe_unsafe_matrix | `../software_design_theory/05_boundary_system/safe_unsafe_matrix.md` | 文件不存在: docs\software_design_theory\05_boundary_system\safe_unsafe_matrix.md |
| docs\research_notes\PROOF_INDEX.md | supported_unsupported_matrix | `../software_design_theory/05_boundary_system/supported_unsupported_matrix.md` | 文件不存在: docs\software_design_theory\05_boundary_system\supported_unsupported_matrix.md |
| docs\research_notes\PROOF_INDEX.md | expressive_inexpressive_matrix | `../software_design_theory/05_boundary_system/expressive_inexpressive_matrix.md` | 文件不存在: docs\software_design_theory\05_boundary_system\expressive_inexpressive_matrix.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../software_design_theory/01_design_patterns_formal/04_boundary_matrix.md` | 文件不存在: docs\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../software_design_theory/01_design_patterns_formal/04_boundary_matrix.md` | 文件不存在: docs\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../software_design_theory/01_design_patterns_formal/04_boundary_matrix.md` | 文件不存在: docs\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../software_design_theory/03_execution_models/06_boundary_analysis.md` | 文件不存在: docs\software_design_theory\03_execution_models\06_boundary_analysis.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../software_design_theory/03_execution_models/06_boundary_analysis.md` | 文件不存在: docs\software_design_theory\03_execution_models\06_boundary_analysis.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../software_design_theory/03_execution_models/06_boundary_analysis.md` | 文件不存在: docs\software_design_theory\03_execution_models\06_boundary_analysis.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../software_design_theory/03_execution_models/06_boundary_analysis.md` | 文件不存在: docs\software_design_theory\03_execution_models\06_boundary_analysis.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../software_design_theory/02_workflow_safe_complete_models/03_semantic_boundary_map.md` | 文件不存在: docs\software_design_theory\02_workflow_safe_complete_models\03_semantic_boundary_map.md |
| docs\research_notes\PROOF_INDEX.md | LANGUAGE_SEMANTICS_EXPRESSIVENESS | `../../LANGUAGE_SEMANTICS_EXPRESSIVENESS.md` | 文件不存在: LANGUAGE_SEMANTICS_EXPRESSIVENESS.md |
| docs\research_notes\PROOF_INDEX.md | experiments/README | `../experiments/README.md` | 文件不存在: docs\experiments\README.md |
| docs\research_notes\PROOF_INDEX.md | compiler_optimizations | `../experiments/compiler_optimizations.md` | 文件不存在: docs\experiments\compiler_optimizations.md |
| docs\research_notes\PROOF_INDEX.md | memory_analysis | `../experiments/memory_analysis.md` | 文件不存在: docs\experiments\memory_analysis.md |
| docs\research_notes\PROOF_INDEX.md | performance_benchmarks | `../experiments/performance_benchmarks.md` | 文件不存在: docs\experiments\performance_benchmarks.md |
| docs\research_notes\PROOF_INDEX.md | concurrency_performance | `../experiments/concurrency_performance.md` | 文件不存在: docs\experiments\concurrency_performance.md |
| docs\research_notes\PROOF_INDEX.md | macro_expansion_performance | `../experiments/macro_expansion_performance.md` | 文件不存在: docs\experiments\macro_expansion_performance.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/compiler_optimizations.md` | 文件不存在: docs\experiments\compiler_optimizations.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/memory_analysis.md` | 文件不存在: docs\experiments\memory_analysis.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/memory_analysis.md` | 文件不存在: docs\experiments\memory_analysis.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/performance_benchmarks.md` | 文件不存在: docs\experiments\performance_benchmarks.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/performance_benchmarks.md` | 文件不存在: docs\experiments\performance_benchmarks.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/concurrency_performance.md` | 文件不存在: docs\experiments\concurrency_performance.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/concurrency_performance.md` | 文件不存在: docs\experiments\concurrency_performance.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/macro_expansion_performance.md` | 文件不存在: docs\experiments\macro_expansion_performance.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/macro_expansion_performance.md` | 文件不存在: docs\experiments\macro_expansion_performance.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/compiler_optimizations.md` | 文件不存在: docs\experiments\compiler_optimizations.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/memory_analysis.md` | 文件不存在: docs\experiments\memory_analysis.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/performance_benchmarks.md` | 文件不存在: docs\experiments\performance_benchmarks.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/concurrency_performance.md` | 文件不存在: docs\experiments\concurrency_performance.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/macro_expansion_performance.md` | 文件不存在: docs\experiments\macro_expansion_performance.md |
| docs\research_notes\PROOF_INDEX.md | 证明位置 | `../experiments/compiler_optimizations.md` | 文件不存在: docs\experiments\compiler_optimizations.md |
| docs\research_notes\QUICK_REFERENCE.md | 形式化工程系统 | `../../rust-formal-engineering-system/README.md` | 文件不存在: rust-formal-engineering-system\README.md |
| docs\research_notes\README.md | 形式化工程系统 | `../../rust-formal-engineering-system/01_theoretical_foundations/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations |
| docs\research_notes\README.md | 形式化工程系统 - 类型系统 | `../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\01_type_system |
| docs\research_notes\README.md | 形式化工程系统 | `../../rust-formal-engineering-system/README.md` | 文件不存在: rust-formal-engineering-system\README.md |
| docs\research_notes\README.md | 研究议程 | `../../rust-formal-engineering-system/09_research_agenda/00_index.md` | 文件不存在: rust-formal-engineering-system\09_research_agenda\00_index.md |
| docs\research_notes\README.md | 个人索引 | `../archive/temp/MY_PERSONAL_INDEX.md` | 文件不存在: docs\archive\temp\MY_PERSONAL_INDEX.md |
| docs\research_notes\README.md | 类型系统速查卡 | `../../quick_reference/type_system.md` | 文件不存在: quick_reference\type_system.md |
| docs\research_notes\README.md | 所有权速查卡 | `../../quick_reference/ownership_cheatsheet.md` | 文件不存在: quick_reference\ownership_cheatsheet.md |
| docs\research_notes\README.md | 异步模式速查卡 | `../../quick_reference/async_patterns.md` | 文件不存在: quick_reference\async_patterns.md |
| docs\research_notes\research_methodology.md | 研究方法索引 | `../../rust-formal-engineering-system/09_research_agenda/04_research_methods/00_index.md` | 文件不存在: rust-formal-engineering-system\09_research_agenda\04_research_methods\00_index.md |
| docs\research_notes\research_methodology.md | 研究工具指南 | `../../rust-formal-engineering-system/09_research_agenda/04_research_methods/` | 文件不存在: rust-formal-engineering-system\09_research_agenda\04_research_methods |
| docs\research_notes\SYSTEM_INTEGRATION.md | 类型系统理论基础 | `../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/core_theory/01_basic_type_system.md` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\01_type_system\core_theory\01_basic_type_system.md |
| docs\research_notes\SYSTEM_INTEGRATION.md | Trait 系统理论 | `../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/core_theory/02_trait_system.md` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\01_type_system\core_theory\02_trait_system.md |
| docs\research_notes\SYSTEM_INTEGRATION.md | 类型系统高级理论 | `../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/advanced_theory/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\01_type_system\advanced_theory |
| docs\research_notes\SYSTEM_INTEGRATION.md | 所有权系统理论 | `../../rust-formal-engineering-system/01_theoretical_foundations/02_ownership_system/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\02_ownership_system |
| docs\research_notes\SYSTEM_INTEGRATION.md | 借用系统理论 | `../../rust-formal-engineering-system/01_theoretical_foundations/02_ownership_system/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\02_ownership_system |
| docs\research_notes\SYSTEM_INTEGRATION.md | 生命周期系统理论 | `../../rust-formal-engineering-system/01_theoretical_foundations/03_lifetime_system/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\03_lifetime_system |
| docs\research_notes\SYSTEM_INTEGRATION.md | 性能优化理论 | `../../rust-formal-engineering-system/02_practical_applications/performance/` | 文件不存在: rust-formal-engineering-system\02_practical_applications\performance |
| docs\research_notes\SYSTEM_INTEGRATION.md | 内存管理理论 | `../../rust-formal-engineering-system/02_practical_applications/memory/` | 文件不存在: rust-formal-engineering-system\02_practical_applications\memory |
| docs\research_notes\SYSTEM_INTEGRATION.md | 编译器理论 | `../../rust-formal-engineering-system/03_compiler_theory/` | 文件不存在: rust-formal-engineering-system\03_compiler_theory |
| docs\research_notes\SYSTEM_INTEGRATION.md | 类型系统理论基础 | `../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/core_theory/01_basic_type_system.md` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\01_type_system\core_theory\01_basic_type_system.md |
| docs\research_notes\SYSTEM_INTEGRATION.md | 类型系统理论 | `../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\01_type_system |
| docs\research_notes\SYSTEM_INTEGRATION.md | 所有权系统理论 | `../../rust-formal-engineering-system/01_theoretical_foundations/02_ownership_system/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\02_ownership_system |
| docs\research_notes\SYSTEM_INTEGRATION.md | 所有权系统理论 | `../../rust-formal-engineering-system/01_theoretical_foundations/02_ownership_system/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\02_ownership_system |
| docs\research_notes\SYSTEM_INTEGRATION.md | 性能优化理论 | `../../rust-formal-engineering-system/02_practical_applications/performance/` | 文件不存在: rust-formal-engineering-system\02_practical_applications\performance |
| docs\research_notes\SYSTEM_INTEGRATION.md | 性能优化理论 | `../../rust-formal-engineering-system/02_practical_applications/performance/` | 文件不存在: rust-formal-engineering-system\02_practical_applications\performance |
| docs\research_notes\SYSTEM_INTEGRATION.md | 形式化工程系统主页 | `../../rust-formal-engineering-system/README.md` | 文件不存在: rust-formal-engineering-system\README.md |
| docs\research_notes\SYSTEM_INTEGRATION.md | 理论基础 | `../../rust-formal-engineering-system/01_theoretical_foundations/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations |
| docs\research_notes\SYSTEM_INTEGRATION.md | 实际应用 | `../../rust-formal-engineering-system/02_practical_applications/` | 文件不存在: rust-formal-engineering-system\02_practical_applications |
| docs\research_notes\SYSTEM_SUMMARY.md | ../../rust-formal-engineering-system/README.md | `../../rust-formal-engineering-system/README.md` | 文件不存在: rust-formal-engineering-system\README.md |
| docs\research_notes\TEMPLATE.md | 相关代码位置 | `../../crates/xxx/src/` | 文件不存在: crates\xxx\src |
| docs\research_notes\TEMPLATE.md | 示例代码位置 | `../../crates/xxx/examples/` | 文件不存在: crates\xxx\examples |
| docs\research_notes\experiments\performance_benchmarks.md | 性能基准测试代码 | `../../../crates/cXX_performance_benchmarks/` | 文件不存在: crates\cXX_performance_benchmarks |
| docs\research_notes\formal_methods\DISTRIBUTED_CONCEPT_MINDMAP.md | CQRS 实现指南 | `../../../05_guides/DISTRIBUTED_SYSTEMS_GUIDE.md` | 文件不存在: 05_guides\DISTRIBUTED_SYSTEMS_GUIDE.md |
| docs\research_notes\formal_methods\lifetime_formalization.md | 形式化工程系统 - 生命周期 | `../../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\01_type_system |
| docs\research_notes\formal_methods\README.md | 异步语义理论 | `../../../../crates/c06_async/src/async_semantics_theory.rs` | 文件不存在: E:\_src\crates\c06_async\src\async_semantics_theory.rs |
| docs\research_notes\formal_methods\WORKFLOW_CONCEPT_MINDMAP.md | 工作流引擎指南 | `../../../05_guides/WORKFLOW_ENGINE_GUIDE.md` | 文件不存在: 05_guides\WORKFLOW_ENGINE_GUIDE.md |
| docs\research_notes\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md | CE-PAT1 | `../../04_compositional_engineering/02_effectiveness_proofs.md#定理-ce-pat1模式组合-ce-保持` | 文件不存在: docs\research_notes\04_compositional_engineering\02_effectiveness_proofs.md |
| docs\research_notes\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md | 03_integration_theory | `../../04_compositional_engineering/03_integration_theory.md` | 文件不存在: docs\research_notes\04_compositional_engineering\03_integration_theory.md |
| docs\research_notes\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md | 04_compositional_engineering | `04_compositional_engineering/README.md` | 文件不存在: docs\research_notes\software_design_theory\01_design_patterns_formal\04_compositional_engineering\README.md |
| docs\research_notes\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md | CE-PAT1 | `../../04_compositional_engineering/02_effectiveness_proofs.md#定理-ce-pat1模式组合-ce-保持` | 文件不存在: docs\research_notes\04_compositional_engineering\02_effectiveness_proofs.md |
| docs\research_notes\software_design_theory\01_design_patterns_formal\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | Rust 设计模式实践指南 | `../../rust_design_patterns.md` | 文件不存在: docs\research_notes\rust_design_patterns.md |
| docs\research_notes\software_design_theory\01_design_patterns_formal\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 所有权系统详解 | `../../ownership_deep_dive.md` | 文件不存在: docs\research_notes\ownership_deep_dive.md |
| docs\research_notes\software_design_theory\01_design_patterns_formal\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 类型状态模式指南 | `../../typestate_pattern.md` | 文件不存在: docs\research_notes\typestate_pattern.md |
| docs\research_notes\software_design_theory\01_design_patterns_formal\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 零成本抽象实践 | `../../zero_cost_abstractions.md` | 文件不存在: docs\research_notes\zero_cost_abstractions.md |
| docs\research_notes\software_design_theory\01_design_patterns_formal\README.md | 04_compositional_engineering 组合反例→错误映射 | `../../04_compositional_engineering/README.md#组合反例编译错误映射ce-t1t2t3` | 文件不存在: docs\research_notes\04_compositional_engineering\README.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | 03_integration_theory | `../../04_compositional_engineering/03_integration_theory.md` | 文件不存在: docs\research_notes\04_compositional_engineering\03_integration_theory.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | 02_effectiveness_proofs | `../../04_compositional_engineering/02_effectiveness_proofs.md` | 文件不存在: docs\research_notes\04_compositional_engineering\02_effectiveness_proofs.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | 05_boundary_system | `../../05_boundary_system/README.md` | 文件不存在: docs\research_notes\05_boundary_system\README.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | 06_rust_idioms | `../../06_rust_idioms.md` | 文件不存在: docs\research_notes\06_rust_idioms.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | singleton | `../../01_design_patterns_formal/01_creational/singleton.md` | 文件不存在: docs\research_notes\01_design_patterns_formal\01_creational\singleton.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | proxy | `../../01_design_patterns_formal/02_structural/proxy.md` | 文件不存在: docs\research_notes\01_design_patterns_formal\02_structural\proxy.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | strategy | `../../01_design_patterns_formal/03_behavioral/strategy.md` | 文件不存在: docs\research_notes\01_design_patterns_formal\03_behavioral\strategy.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | composite | `../../01_design_patterns_formal/02_structural/composite.md` | 文件不存在: docs\research_notes\01_design_patterns_formal\02_structural\composite.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\03_semantic_boundary_map.md | 01_design_patterns_formal §23 模式多维对比矩阵 | `../../01_design_patterns_formal/README.md#23-模式多维对比矩阵` | 文件不存在: docs\research_notes\01_design_patterns_formal\README.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\03_semantic_boundary_map.md | 执行模型边界 | `../../03_execution_models/06_boundary_analysis.md` | 文件不存在: docs\research_notes\03_execution_models\06_boundary_analysis.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\04_expressiveness_boundary.md | 06_boundary_analysis 并发选型 | `../../03_execution_models/06_boundary_analysis.md` | 文件不存在: docs\research_notes\03_execution_models\06_boundary_analysis.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\04_expressiveness_boundary.md | 04_compositional_engineering | `../../04_compositional_engineering/README.md` | 文件不存在: docs\research_notes\04_compositional_engineering\README.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\04_expressiveness_boundary.md | 05_distributed | `../../03_execution_models/05_distributed.md` | 文件不存在: docs\research_notes\03_execution_models\05_distributed.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\04_expressiveness_boundary.md | 05_distributed | `../../03_execution_models/05_distributed.md` | 文件不存在: docs\research_notes\03_execution_models\05_distributed.md |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\04_expressiveness_boundary.md | 04_compositional_engineering 表达力×组合联合判定树 | `../../04_compositional_engineering/README.md#表达力组合联合判定树支柱-23` | 文件不存在: docs\research_notes\04_compositional_engineering\README.md |
| docs\research_notes\software_design_theory\03_execution_models\03_concurrent.md | observer | `../../01_design_patterns_formal/03_behavioral/observer.md` | 文件不存在: docs\research_notes\01_design_patterns_formal\03_behavioral\observer.md |
| docs\research_notes\software_design_theory\03_execution_models\03_concurrent.md | flyweight | `../../01_design_patterns_formal/02_structural/flyweight.md` | 文件不存在: docs\research_notes\01_design_patterns_formal\02_structural\flyweight.md |
| docs\research_notes\software_design_theory\03_execution_models\04_parallel.md | iterator | `../../01_design_patterns_formal/03_behavioral/iterator.md` | 文件不存在: docs\research_notes\01_design_patterns_formal\03_behavioral\iterator.md |
| docs\research_notes\software_design_theory\03_execution_models\04_parallel.md | flyweight | `../../01_design_patterns_formal/02_structural/flyweight.md` | 文件不存在: docs\research_notes\01_design_patterns_formal\02_structural\flyweight.md |
| docs\research_notes\software_design_theory\03_execution_models\05_distributed.md | 02_complete_43_catalog | `../../02_workflow_safe_complete_models/02_complete_43_catalog.md` | 文件不存在: docs\research_notes\02_workflow_safe_complete_models\02_complete_43_catalog.md |
| docs\research_notes\software_design_theory\03_execution_models\05_distributed.md | 02_complete_43_catalog | `../../02_workflow_safe_complete_models/02_complete_43_catalog.md` | 文件不存在: docs\research_notes\02_workflow_safe_complete_models\02_complete_43_catalog.md |
| docs\research_notes\software_design_theory\03_execution_models\05_distributed.md | observer | `../../01_design_patterns_formal/03_behavioral/observer.md` | 文件不存在: docs\research_notes\01_design_patterns_formal\03_behavioral\observer.md |
| docs\research_notes\software_design_theory\03_execution_models\05_distributed.md | 02_effectiveness_proofs | `../../04_compositional_engineering/02_effectiveness_proofs.md` | 文件不存在: docs\research_notes\04_compositional_engineering\02_effectiveness_proofs.md |
| docs\research_notes\software_design_theory\03_execution_models\05_distributed.md | 04_expressiveness_boundary | `../../02_workflow_safe_complete_models/04_expressiveness_boundary.md` | 文件不存在: docs\research_notes\02_workflow_safe_complete_models\04_expressiveness_boundary.md |
| docs\research_notes\software_design_theory\05_boundary_system\README.md | borrow_checker_proof | `borrow_checker_proof.md` | 文件不存在: docs\research_notes\software_design_theory\05_boundary_system\borrow_checker_proof.md |
| docs\research_notes\type_theory\lifetime_formalization.md | 形式化工程系统 - 生命周期 | `../../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\01_type_system |
| docs\research_notes\type_theory\trait_system_formalization.md | m | `\text{data}, \text{args}` | 文件不存在: E:\text{data}, \text{args} |
| docs\research_notes\type_theory\trait_system_formalization.md | advanced_types | `../advanced_types.md` | 文件不存在: docs\research_notes\advanced_types.md |
| docs\research_notes\type_theory\trait_system_formalization.md | 形式化工程系统 - Trait | `../../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\01_type_system |
| docs\research_notes\type_theory\type_system_foundations.md | 形式化工程系统 - 类型系统 | `../../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\01_type_system |
| docs\research_notes\type_theory\variance_theory.md | 形式化工程系统 - 型变 | `../../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/06_variance.md` | 文件不存在: rust-formal-engineering-system\01_theoretical_foundations\01_type_system\06_variance.md |
| docs\rust-formal-engineering-system\00_master_index.md | docs/TESTING_COVERAGE_GUIDE.md | `../TESTING_COVERAGE_GUIDE.md` | 文件不存在: docs\TESTING_COVERAGE_GUIDE.md |
| docs\rust-formal-engineering-system\README.md | 思维表征方式 | `../THINKING_REPRESENTATION_METHODS.md` | 文件不存在: docs\THINKING_REPRESENTATION_METHODS.md |
| docs\rust-formal-engineering-system\README.md | 多维概念矩阵 | `../MULTI_DIMENSIONAL_CONCEPT_MATRIX.md` | 文件不存在: docs\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md |
| docs\rust-formal-engineering-system\02_practical_applications\memory\README.md | memory_analysis.md | `../../../../research_notes/experiments/memory_analysis.md` | 文件不存在: research_notes\experiments\memory_analysis.md |
| docs\rust-formal-engineering-system\02_practical_applications\memory\README.md | ../../../../research_notes/experiments/memory_analysis.md | `../../../../research_notes/experiments/memory_analysis.md` | 文件不存在: research_notes\experiments\memory_analysis.md |
| docs\rust-formal-engineering-system\02_practical_applications\memory\README.md | ../../../../research_notes/experiments/compiler_optimizations.md | `../../../../research_notes/experiments/compiler_optimizations.md` | 文件不存在: research_notes\experiments\compiler_optimizations.md |
| docs\rust-formal-engineering-system\02_practical_applications\memory\README.md | ../../../../research_notes/formal_methods/ownership_model.md | `../../../../research_notes/formal_methods/ownership_model.md` | 文件不存在: research_notes\formal_methods\ownership_model.md |
| docs\rust-formal-engineering-system\02_practical_applications\memory\README.md | ../../../../research_notes/formal_methods/lifetime_formalization.md | `../../../../research_notes/formal_methods/lifetime_formalization.md` | 文件不存在: research_notes\formal_methods\lifetime_formalization.md |
| docs\rust-formal-engineering-system\02_practical_applications\memory\README.md | ../../../../research_notes/type_theory/type_system_foundations.md | `../../../../research_notes/type_theory/type_system_foundations.md` | 文件不存在: research_notes\type_theory\type_system_foundations.md |
| docs\rust-formal-engineering-system\02_practical_applications\memory\README.md | ../../../../research_notes/type_theory/lifetime_formalization.md | `../../../../research_notes/type_theory/lifetime_formalization.md` | 文件不存在: research_notes\type_theory\lifetime_formalization.md |
| docs\rust-formal-engineering-system\02_practical_applications\memory\README.md | ../../../../research_notes/type_theory/variance_theory.md | `../../../../research_notes/type_theory/variance_theory.md` | 文件不存在: research_notes\type_theory\variance_theory.md |
| docs\rust-formal-engineering-system\02_practical_applications\memory\README.md | ../../../../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md | `../../../../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md` | 文件不存在: research_notes\SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md |
| docs\rust-formal-engineering-system\02_practical_applications\memory\README.md | ../../../../crates/c04_memory/ | `../../../../crates/c04_memory/` | 文件不存在: crates\c04_memory |
| docs\rust-formal-engineering-system\02_practical_applications\performance\README.md | performance_benchmarks.md | `../../../../research_notes/experiments/performance_benchmarks.md` | 文件不存在: research_notes\experiments\performance_benchmarks.md |
| docs\rust-formal-engineering-system\02_practical_applications\performance\README.md | ../../../../research_notes/experiments/performance_benchmarks.md | `../../../../research_notes/experiments/performance_benchmarks.md` | 文件不存在: research_notes\experiments\performance_benchmarks.md |
| docs\rust-formal-engineering-system\02_practical_applications\performance\README.md | ../../../../research_notes/experiments/compiler_optimizations.md | `../../../../research_notes/experiments/compiler_optimizations.md` | 文件不存在: research_notes\experiments\compiler_optimizations.md |
| docs\rust-formal-engineering-system\02_practical_applications\performance\README.md | ../../../../research_notes/experiments/concurrency_performance.md | `../../../../research_notes/experiments/concurrency_performance.md` | 文件不存在: research_notes\experiments\concurrency_performance.md |
| docs\rust-formal-engineering-system\02_practical_applications\performance\README.md | ../../../../research_notes/formal_methods/send_sync_formalization.md | `../../../../research_notes/formal_methods/send_sync_formalization.md` | 文件不存在: research_notes\formal_methods\send_sync_formalization.md |
| docs\rust-formal-engineering-system\02_practical_applications\performance\README.md | ../../../../crates/c11_advanced/ | `../../../../crates/c11_advanced/` | 文件不存在: crates\c11_advanced |
| docs\rust-formal-engineering-system\02_programming_paradigms\11_benchmark_minimal_guide.md | ../05_guides/PERFORMANCE_TUNING_GUIDE.md | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\rust-formal-engineering-system\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\11_benchmark_minimal_guide.md | ../05_guides/PERFORMANCE_TUNING_GUIDE.md | `../05_guides/PERFORMANCE_TUNING_GUIDE.md` | 文件不存在: docs\rust-formal-engineering-system\05_guides\PERFORMANCE_TUNING_GUIDE.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\01_synchronous\README.md | ../../../../research_notes/software_design_theory/03_execution_models/01_synchronous.md | `../../../../research_notes/software_design_theory/03_execution_models/01_synchronous.md` | 文件不存在: research_notes\software_design_theory\03_execution_models\01_synchronous.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\01_synchronous\README.md | ../../../../research_notes/software_design_theory/03_execution_models/03_concurrent.md | `../../../../research_notes/software_design_theory/03_execution_models/03_concurrent.md` | 文件不存在: research_notes\software_design_theory\03_execution_models\03_concurrent.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\01_synchronous\README.md | ../../../../research_notes/software_design_theory/03_execution_models/04_parallel.md | `../../../../research_notes/software_design_theory/03_execution_models/04_parallel.md` | 文件不存在: research_notes\software_design_theory\03_execution_models\04_parallel.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\01_synchronous\README.md | ../../../../research_notes/formal_methods/send_sync_formalization.md | `../../../../research_notes/formal_methods/send_sync_formalization.md` | 文件不存在: research_notes\formal_methods\send_sync_formalization.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\01_synchronous\README.md | ../../../../research_notes/formal_methods/ownership_model.md | `../../../../research_notes/formal_methods/ownership_model.md` | 文件不存在: research_notes\formal_methods\ownership_model.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\01_synchronous\README.md | ../../../../research_notes/experiments/concurrency_performance.md | `../../../../research_notes/experiments/concurrency_performance.md` | 文件不存在: research_notes\experiments\concurrency_performance.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\02_async\README.md | ../../../../research_notes/software_design_theory/03_execution_models/02_async.md | `../../../../research_notes/software_design_theory/03_execution_models/02_async.md` | 文件不存在: research_notes\software_design_theory\03_execution_models\02_async.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\02_async\README.md | ../../../../research_notes/software_design_theory/03_execution_models/03_concurrent.md | `../../../../research_notes/software_design_theory/03_execution_models/03_concurrent.md` | 文件不存在: research_notes\software_design_theory\03_execution_models\03_concurrent.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\02_async\README.md | ../../../../research_notes/formal_methods/async_state_machine.md | `../../../../research_notes/formal_methods/async_state_machine.md` | 文件不存在: research_notes\formal_methods\async_state_machine.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\02_async\README.md | ../../../../research_notes/formal_methods/pin_self_referential.md | `../../../../research_notes/formal_methods/pin_self_referential.md` | 文件不存在: research_notes\formal_methods\pin_self_referential.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\02_async\README.md | ../../../../research_notes/formal_methods/send_sync_formalization.md | `../../../../research_notes/formal_methods/send_sync_formalization.md` | 文件不存在: research_notes\formal_methods\send_sync_formalization.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\02_async\README.md | ../../../../research_notes/experiments/concurrency_performance.md | `../../../../research_notes/experiments/concurrency_performance.md` | 文件不存在: research_notes\experiments\concurrency_performance.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\09_actor_model\README.md | ../../../../research_notes/software_design_theory/03_execution_models/05_distributed.md | `../../../../research_notes/software_design_theory/03_execution_models/05_distributed.md` | 文件不存在: research_notes\software_design_theory\03_execution_models\05_distributed.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\09_actor_model\README.md | ../../../../research_notes/software_design_theory/04_compositional_engineering/README.md | `../../../../research_notes/software_design_theory/04_compositional_engineering/README.md` | 文件不存在: research_notes\software_design_theory\04_compositional_engineering\README.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\09_actor_model\README.md | ../../../../research_notes/formal_methods/send_sync_formalization.md | `../../../../research_notes/formal_methods/send_sync_formalization.md` | 文件不存在: research_notes\formal_methods\send_sync_formalization.md |
| docs\rust-formal-engineering-system\02_programming_paradigms\09_actor_model\README.md | ../../../../research_notes/formal_methods/ownership_model.md | `../../../../research_notes/formal_methods/ownership_model.md` | 文件不存在: research_notes\formal_methods\ownership_model.md |
| docs\rust-formal-engineering-system\03_compiler_theory\README.md | 01_compiler_features.md | `../06_toolchain/01_compiler_features.md` | 文件不存在: docs\rust-formal-engineering-system\06_toolchain\01_compiler_features.md |
| docs\rust-formal-engineering-system\03_compiler_theory\README.md | ../06_toolchain/01_compiler_features.md | `../06_toolchain/01_compiler_features.md` | 文件不存在: docs\rust-formal-engineering-system\06_toolchain\01_compiler_features.md |
| docs\rust-formal-engineering-system\03_compiler_theory\README.md | ../../crates/c11_advanced/ | `../../crates/c11_advanced/` | 文件不存在: docs\crates\c11_advanced |
| docs\rust-formal-engineering-system\03_compiler_theory\README.md | ../../crates/c12_macros/ | `../../crates/c12_macros/` | 文件不存在: docs\crates\c12_macros |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | ../../../research_notes/software_design_theory/01_design_patterns_formal/README.md | `../../../research_notes/software_design_theory/01_design_patterns_formal/README.md` | 文件不存在: research_notes\software_design_theory\01_design_patterns_formal\README.md |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | ../../../research_notes/software_design_theory/06_rust_idioms.md | `../../../research_notes/software_design_theory/06_rust_idioms.md` | 文件不存在: research_notes\software_design_theory\06_rust_idioms.md |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | ../../../research_notes/software_design_theory/07_anti_patterns.md | `../../../research_notes/software_design_theory/07_anti_patterns.md` | 文件不存在: research_notes\software_design_theory\07_anti_patterns.md |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | ../../../research_notes/software_design_theory/01_design_patterns_formal/01_creational/abstract_factory.md | `../../../research_notes/software_design_theory/01_design_patterns_formal/01_creational/abstract_factory.md` | 文件不存在: research_notes\software_design_theory\01_design_patterns_formal\01_creational\abstract_factory.md |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | ../../../research_notes/software_design_theory/01_design_patterns_formal/01_creational/builder.md | `../../../research_notes/software_design_theory/01_design_patterns_formal/01_creational/builder.md` | 文件不存在: research_notes\software_design_theory\01_design_patterns_formal\01_creational\builder.md |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | ../../../research_notes/software_design_theory/01_design_patterns_formal/01_creational/factory_method.md | `../../../research_notes/software_design_theory/01_design_patterns_formal/01_creational/factory_method.md` | 文件不存在: research_notes\software_design_theory\01_design_patterns_formal\01_creational\factory_method.md |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | ../../../research_notes/software_design_theory/01_design_patterns_formal/02_structural/adapter.md | `../../../research_notes/software_design_theory/01_design_patterns_formal/02_structural/adapter.md` | 文件不存在: research_notes\software_design_theory\01_design_patterns_formal\02_structural\adapter.md |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | ../../../research_notes/software_design_theory/01_design_patterns_formal/02_structural/decorator.md | `../../../research_notes/software_design_theory/01_design_patterns_formal/02_structural/decorator.md` | 文件不存在: research_notes\software_design_theory\01_design_patterns_formal\02_structural\decorator.md |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | ../../../research_notes/software_design_theory/01_design_patterns_formal/02_structural/facade.md | `../../../research_notes/software_design_theory/01_design_patterns_formal/02_structural/facade.md` | 文件不存在: research_notes\software_design_theory\01_design_patterns_formal\02_structural\facade.md |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | ../../../research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/observer.md | `../../../research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/observer.md` | 文件不存在: research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\observer.md |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | ../../../research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/strategy.md | `../../../research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/strategy.md` | 文件不存在: research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\strategy.md |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | ../../../research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/state.md | `../../../research_notes/software_design_theory/01_design_patterns_formal/03_behavioral/state.md` | 文件不存在: research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\state.md |
| docs\rust-formal-engineering-system\03_design_patterns\04_concurrent\README.md | ../../../../research_notes/software_design_theory/03_execution_models/03_concurrent.md | `../../../../research_notes/software_design_theory/03_execution_models/03_concurrent.md` | 文件不存在: research_notes\software_design_theory\03_execution_models\03_concurrent.md |
| docs\rust-formal-engineering-system\03_design_patterns\04_concurrent\README.md | ../../../../research_notes/software_design_theory/03_execution_models/04_parallel.md | `../../../../research_notes/software_design_theory/03_execution_models/04_parallel.md` | 文件不存在: research_notes\software_design_theory\03_execution_models\04_parallel.md |
| docs\rust-formal-engineering-system\03_design_patterns\04_concurrent\README.md | ../../../../research_notes/software_design_theory/01_design_patterns_formal/04_boundary_matrix.md | `../../../../research_notes/software_design_theory/01_design_patterns_formal/04_boundary_matrix.md` | 文件不存在: research_notes\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md |
| docs\rust-formal-engineering-system\03_design_patterns\04_concurrent\README.md | ../../../../research_notes/formal_methods/send_sync_formalization.md | `../../../../research_notes/formal_methods/send_sync_formalization.md` | 文件不存在: research_notes\formal_methods\send_sync_formalization.md |
| docs\rust-formal-engineering-system\03_design_patterns\04_concurrent\README.md | ../../../../research_notes/formal_methods/ownership_model.md | `../../../../research_notes/formal_methods/ownership_model.md` | 文件不存在: research_notes\formal_methods\ownership_model.md |
| docs\rust-formal-engineering-system\03_design_patterns\04_concurrent\README.md | ../../../../research_notes/experiments/concurrency_performance.md | `../../../../research_notes/experiments/concurrency_performance.md` | 文件不存在: research_notes\experiments\concurrency_performance.md |
| docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md | testing_cheatsheet.md | `../../../quick_reference/testing_cheatsheet.md` | 文件不存在: docs\quick_reference\testing_cheatsheet.md |
| docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md | ../../../../research_notes/formal_methods/README.md | `../../../../research_notes/formal_methods/README.md` | 文件不存在: research_notes\formal_methods\README.md |
| docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md | ../../../../research_notes/formal_methods/type_system_formalization.md | `../../../../research_notes/formal_methods/type_system_formalization.md` | 文件不存在: research_notes\formal_methods\type_system_formalization.md |
| docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md | ../../../../research_notes/formal_methods/ownership_model.md | `../../../../research_notes/formal_methods/ownership_model.md` | 文件不存在: research_notes\formal_methods\ownership_model.md |
| docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md | ../../../../research_notes/PROOF_INDEX.md | `../../../../research_notes/PROOF_INDEX.md` | 文件不存在: research_notes\PROOF_INDEX.md |
| docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md | ../../../quick_reference/testing_cheatsheet.md | `../../../quick_reference/testing_cheatsheet.md` | 文件不存在: docs\quick_reference\testing_cheatsheet.md |
| docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md | ../../../TESTING_COVERAGE_GUIDE.md | `../../../TESTING_COVERAGE_GUIDE.md` | 文件不存在: docs\TESTING_COVERAGE_GUIDE.md |
| docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md | ../../../../research_notes/QUALITY_CHECKLIST.md | `../../../../research_notes/QUALITY_CHECKLIST.md` | 文件不存在: research_notes\QUALITY_CHECKLIST.md |
| docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md | ../../../../research_notes/TOOLS_GUIDE.md | `../../../../research_notes/TOOLS_GUIDE.md` | 文件不存在: research_notes\TOOLS_GUIDE.md |
| docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md | ../../../../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md | `../../../../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md` | 文件不存在: research_notes\SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md |
| docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md | 返回软件工程索引 | `../README.md` | 文件不存在: docs\rust-formal-engineering-system\05_software_engineering\README.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\README.md | ../../research_notes/formal_methods/type_system_formalization.md | `../../research_notes/formal_methods/type_system_formalization.md` | 文件不存在: docs\research_notes\formal_methods\type_system_formalization.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\01_compiler\README.md | ../../../../research_notes/formal_methods/README.md | `../../../../research_notes/formal_methods/README.md` | 文件不存在: research_notes\formal_methods\README.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\01_compiler\README.md | ../../../../research_notes/formal_methods/type_system_formalization.md | `../../../../research_notes/formal_methods/type_system_formalization.md` | 文件不存在: research_notes\formal_methods\type_system_formalization.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\01_compiler\README.md | ../../../../research_notes/formal_methods/ownership_model.md | `../../../../research_notes/formal_methods/ownership_model.md` | 文件不存在: research_notes\formal_methods\ownership_model.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\01_compiler\README.md | ../../../../research_notes/formal_methods/lifetime_formalization.md | `../../../../research_notes/formal_methods/lifetime_formalization.md` | 文件不存在: research_notes\formal_methods\lifetime_formalization.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\01_compiler\README.md | ../../../../research_notes/formal_methods/borrow_checker_proof.md | `../../../../research_notes/formal_methods/borrow_checker_proof.md` | 文件不存在: research_notes\formal_methods\borrow_checker_proof.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\01_compiler\README.md | ../../../../research_notes/PROOF_INDEX.md | `../../../../research_notes/PROOF_INDEX.md` | 文件不存在: research_notes\PROOF_INDEX.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\01_compiler\README.md | ../../../../research_notes/experiments/compiler_optimizations.md | `../../../../research_notes/experiments/compiler_optimizations.md` | 文件不存在: research_notes\experiments\compiler_optimizations.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\01_compiler\README.md | ../../../../research_notes/research_methodology.md | `../../../../research_notes/research_methodology.md` | 文件不存在: research_notes\research_methodology.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\01_compiler\README.md | ../../../../research_notes/TOOLS_GUIDE.md | `../../../../research_notes/TOOLS_GUIDE.md` | 文件不存在: research_notes\TOOLS_GUIDE.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\01_compiler\README.md | ../../../../research_notes/BEST_PRACTICES.md | `../../../../research_notes/BEST_PRACTICES.md` | 文件不存在: research_notes\BEST_PRACTICES.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\02_package_manager\README.md | ../../../../research_notes/formal_methods/README.md | `../../../../research_notes/formal_methods/README.md` | 文件不存在: research_notes\formal_methods\README.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\02_package_manager\README.md | ../../../../research_notes/formal_methods/type_system_formalization.md | `../../../../research_notes/formal_methods/type_system_formalization.md` | 文件不存在: research_notes\formal_methods\type_system_formalization.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\02_package_manager\README.md | ../../../../research_notes/formal_methods/send_sync_formalization.md | `../../../../research_notes/formal_methods/send_sync_formalization.md` | 文件不存在: research_notes\formal_methods\send_sync_formalization.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\02_package_manager\README.md | ../../../../research_notes/PROOF_INDEX.md | `../../../../research_notes/PROOF_INDEX.md` | 文件不存在: research_notes\PROOF_INDEX.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\02_package_manager\README.md | ../../../../research_notes/research_methodology.md | `../../../../research_notes/research_methodology.md` | 文件不存在: research_notes\research_methodology.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\02_package_manager\README.md | ../../../../research_notes/BEST_PRACTICES.md | `../../../../research_notes/BEST_PRACTICES.md` | 文件不存在: research_notes\BEST_PRACTICES.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\02_package_manager\README.md | ../../../../research_notes/TOOLS_GUIDE.md | `../../../../research_notes/TOOLS_GUIDE.md` | 文件不存在: research_notes\TOOLS_GUIDE.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\02_package_manager\README.md | ../../../../research_notes/QUALITY_CHECKLIST.md | `../../../../research_notes/QUALITY_CHECKLIST.md` | 文件不存在: research_notes\QUALITY_CHECKLIST.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\03_build_tools\README.md | ../../../../research_notes/formal_methods/README.md | `../../../../research_notes/formal_methods/README.md` | 文件不存在: research_notes\formal_methods\README.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\03_build_tools\README.md | ../../../../research_notes/formal_methods/type_system_formalization.md | `../../../../research_notes/formal_methods/type_system_formalization.md` | 文件不存在: research_notes\formal_methods\type_system_formalization.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\03_build_tools\README.md | ../../../../research_notes/formal_methods/borrow_checker_proof.md | `../../../../research_notes/formal_methods/borrow_checker_proof.md` | 文件不存在: research_notes\formal_methods\borrow_checker_proof.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\03_build_tools\README.md | ../../../../research_notes/PROOF_INDEX.md | `../../../../research_notes/PROOF_INDEX.md` | 文件不存在: research_notes\PROOF_INDEX.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\03_build_tools\README.md | ../../../../research_notes/research_methodology.md | `../../../../research_notes/research_methodology.md` | 文件不存在: research_notes\research_methodology.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\03_build_tools\README.md | ../../../../research_notes/TOOLS_GUIDE.md | `../../../../research_notes/TOOLS_GUIDE.md` | 文件不存在: research_notes\TOOLS_GUIDE.md |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\03_build_tools\README.md | ../../../../research_notes/BEST_PRACTICES.md | `../../../../research_notes/BEST_PRACTICES.md` | 文件不存在: research_notes\BEST_PRACTICES.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | research_methodology.md | `../../../../research_notes/research_methodology.md` | 文件不存在: research_notes\research_methodology.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/formal_methods/README.md | `../../../../../research_notes/formal_methods/README.md` | 文件不存在: E:\_src\research_notes\formal_methods\README.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/FORMAL_VERIFICATION_GUIDE.md | `../../../../../research_notes/FORMAL_VERIFICATION_GUIDE.md` | 文件不存在: E:\_src\research_notes\FORMAL_VERIFICATION_GUIDE.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md | `../../../../../research_notes/FORMAL_PROOF_SYSTEM_GUIDE.md` | 文件不存在: E:\_src\research_notes\FORMAL_PROOF_SYSTEM_GUIDE.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/formal_methods/ownership_model.md | `../../../../../research_notes/formal_methods/ownership_model.md` | 文件不存在: E:\_src\research_notes\formal_methods\ownership_model.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/formal_methods/type_system_formalization.md | `../../../../../research_notes/formal_methods/type_system_formalization.md` | 文件不存在: E:\_src\research_notes\formal_methods\type_system_formalization.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/formal_methods/lifetime_formalization.md | `../../../../../research_notes/formal_methods/lifetime_formalization.md` | 文件不存在: E:\_src\research_notes\formal_methods\lifetime_formalization.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/formal_methods/borrow_checker_proof.md | `../../../../../research_notes/formal_methods/borrow_checker_proof.md` | 文件不存在: E:\_src\research_notes\formal_methods\borrow_checker_proof.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/PROOF_INDEX.md | `../../../../../research_notes/PROOF_INDEX.md` | 文件不存在: E:\_src\research_notes\PROOF_INDEX.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/research_methodology.md | `../../../../../research_notes/research_methodology.md` | 文件不存在: E:\_src\research_notes\research_methodology.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/TOOLS_GUIDE.md | `../../../../../research_notes/TOOLS_GUIDE.md` | 文件不存在: E:\_src\research_notes\TOOLS_GUIDE.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/PROOF_INDEX.md | `../../../../../research_notes/PROOF_INDEX.md` | 文件不存在: E:\_src\research_notes\PROOF_INDEX.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/RESEARCH_ROADMAP.md | `../../../../../research_notes/RESEARCH_ROADMAP.md` | 文件不存在: E:\_src\research_notes\RESEARCH_ROADMAP.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/CORE_THEOREMS_FULL_PROOFS.md | `../../../../../research_notes/CORE_THEOREMS_FULL_PROOFS.md` | 文件不存在: E:\_src\research_notes\CORE_THEOREMS_FULL_PROOFS.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md | `../../../../../research_notes/FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md` | 文件不存在: E:\_src\research_notes\FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/BEST_PRACTICES.md | `../../../../../research_notes/BEST_PRACTICES.md` | 文件不存在: E:\_src\research_notes\BEST_PRACTICES.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | ../../../../../research_notes/QUALITY_CHECKLIST.md | `../../../../../research_notes/QUALITY_CHECKLIST.md` | 文件不存在: E:\_src\research_notes\QUALITY_CHECKLIST.md |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | 返回研究议程索引 | `../README.md` | 文件不存在: docs\rust-formal-engineering-system\09_research_agenda\README.md |
| docs\rust-formal-engineering-system\10_quality_assurance\README.md | TESTING_COVERAGE_GUIDE | `../TESTING_COVERAGE_GUIDE.md` | 文件不存在: docs\rust-formal-engineering-system\TESTING_COVERAGE_GUIDE.md |
| docs\rust-formal-engineering-system\10_quality_assurance\README.md | **TESTING_COVERAGE_GUIDE.md** | `../TESTING_COVERAGE_GUIDE.md` | 文件不存在: docs\rust-formal-engineering-system\TESTING_COVERAGE_GUIDE.md |
| docs\rust-formal-engineering-system\10_quality_assurance\README.md | ../TESTING_COVERAGE_GUIDE.md | `../TESTING_COVERAGE_GUIDE.md` | 文件不存在: docs\rust-formal-engineering-system\TESTING_COVERAGE_GUIDE.md |
| docs\rust-formal-engineering-system\10_quality_assurance\README.md | ../../research_notes/formal_methods/type_system_formalization.md | `../../research_notes/formal_methods/type_system_formalization.md` | 文件不存在: docs\research_notes\formal_methods\type_system_formalization.md |

### 锚点不存在 (298个)

| 源文件 | 链接文本 | 链接路径 | 问题 |
| :--- | :--- | :--- | :--- |
| docs\LINK_REPAIR_STRATEGY.md | 目录 | `#-目录` | 同文件锚点不存在: #-目录 |
| docs\LINK_REPAIR_STRATEGY.md | 目录 | `#目录` | 同文件锚点不存在: #目录 |
| docs\02_reference\EDGE_CASES_AND_SPECIAL_CASES.md | 空 HashMap / BTreeMap | `#空-hashmap--btreemap` | 同文件锚点不存在: #空-hashmap--btreemap |
| docs\02_reference\EDGE_CASES_AND_SPECIAL_CASES.md | 零个线程 / 空任务列表 | `#零个线程--空任务列表` | 同文件锚点不存在: #零个线程--空任务列表 |
| docs\02_reference\EDGE_CASES_AND_SPECIAL_CASES.md | unsafe 边界 {#unsafe-边界-1} | `#unsafe-边界-unsafe-边界-1` | 同文件锚点不存在: #unsafe-边界-unsafe-边界-1 |
| docs\02_reference\EDGE_CASES_AND_SPECIAL_CASES.md | ownership_model | `../research_notes/formal_methods/ownership_model.md#示例-8-复杂所有权场景---结构体字段移动` | 锚点不存在: #示例-8-复杂所有权场景---结构体字段移动 |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 1.5 Rust 1.93.0 标准库行为变更 ⚠️ {#15-rust-1930-标准库行为变更-️} | `#15-rust-1930-标准库行为变更-️-15-rust-1930-标准库行为变更-️` | 同文件锚点不存在: #15-rust-1930-标准库行为变更-️-15-rust-1930-标准库行为变更-️ |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 2.1.2 Vec {#212-vec} | `#212-vec-212-vec` | 同文件锚点不存在: #212-vec-212-vec |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 2.1.3 VecDeque {#213-vecdeque} | `#213-vecdeque-213-vecdeque` | 同文件锚点不存在: #213-vecdeque-213-vecdeque |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 2.2.1 Arc {#221-arc} | `#221-arc-221-arc` | 同文件锚点不存在: #221-arc-221-arc |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 2.2.2 Mutex {#222-mutex} | `#222-mutex-222-mutex` | 同文件锚点不存在: #222-mutex-222-mutex |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 2.2.3 RwLock {#223-rwlock} | `#223-rwlock-223-rwlock` | 同文件锚点不存在: #223-rwlock-223-rwlock |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 2.4.2 JoinHandle {#242-joinhandle} | `#242-joinhandle-242-joinhandle` | 同文件锚点不存在: #242-joinhandle-242-joinhandle |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 2.7.2 Option {#272-option} | `#272-option-272-option` | 同文件锚点不存在: #272-option-272-option |
| docs\02_reference\quick_reference\ai_ml_cheatsheet.md | 反例 4: 内存泄漏 - 循环引用张量缓存 | `#反例-4-内存泄漏---循环引用张量缓存` | 同文件锚点不存在: #反例-4-内存泄漏---循环引用张量缓存 |
| docs\02_reference\quick_reference\ai_ml_cheatsheet.md | 反例 5: 边界情况 - 空张量操作 | `#反例-5-边界情况---空张量操作` | 同文件锚点不存在: #反例-5-边界情况---空张量操作 |
| docs\02_reference\quick_reference\algorithms_cheatsheet.md | 示例 3: 动态规划 - 最长公共子序列 | `#示例-3-动态规划---最长公共子序列` | 同文件锚点不存在: #示例-3-动态规划---最长公共子序列 |
| docs\02_reference\quick_reference\ANTI_PATTERN_TEMPLATE.md | 十四、完整示例：场景 → 反模式 → 正确写法 | `#十四完整示例场景--反模式--正确写法` | 同文件锚点不存在: #十四完整示例场景--反模式--正确写法 |
| docs\02_reference\quick_reference\async_patterns.md | 🏗️ 运行时对比 {#️-运行时对比} | `#️-运行时对比-️-运行时对比` | 同文件锚点不存在: #️-运行时对比-️-运行时对比 |
| docs\02_reference\quick_reference\async_patterns.md | 模式 1: Arc + Mutex | `#模式-1-arc--mutex` | 同文件锚点不存在: #模式-1-arc--mutex |
| docs\02_reference\quick_reference\async_patterns.md | 模式 2: Arc + RwLock（读多写少） | `#模式-2-arc--rwlock读多写少` | 同文件锚点不存在: #模式-2-arc--rwlock读多写少 |
| docs\02_reference\quick_reference\async_patterns.md | ⚠️ 常见陷阱 {#️-常见陷阱} | `#️-常见陷阱-️-常见陷阱` | 同文件锚点不存在: #️-常见陷阱-️-常见陷阱 |
| docs\02_reference\quick_reference\async_patterns.md | ⚠️ 边界情况 {#️-边界情况} | `#️-边界情况-️-边界情况` | 同文件锚点不存在: #️-边界情况-️-边界情况 |
| docs\02_reference\quick_reference\cargo_cheatsheet.md | ⚙️ 配置文件 {#️-配置文件} | `#️-配置文件-️-配置文件` | 同文件锚点不存在: #️-配置文件-️-配置文件 |
| docs\02_reference\quick_reference\cargo_cheatsheet.md | 🛠️ 常用工具 {#️-常用工具} | `#️-常用工具-️-常用工具` | 同文件锚点不存在: #️-常用工具-️-常用工具 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 🗺️ HashMap（哈希映射） {#️-hashmap哈希映射} | `#️-hashmap哈希映射-️-hashmap哈希映射` | 同文件锚点不存在: #️-hashmap哈希映射-️-hashmap哈希映射 |
| docs\02_reference\quick_reference\collections_iterators_cheatsheet.md | 🍽️ 迭代器消费者 | `#️-迭代器消费者` | 同文件锚点不存在: #️-迭代器消费者 |
| docs\02_reference\quick_reference\control_flow_functions_cheatsheet.md | ⚠️ 边界情况 {#️-边界情况} | `#️-边界情况-️-边界情况` | 同文件锚点不存在: #️-边界情况-️-边界情况 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | ⚠️ Rust 错误处理速查卡 {#️-rust-错误处理速查卡} | `#️-rust-错误处理速查卡-️-rust-错误处理速查卡` | 同文件锚点不存在: #️-rust-错误处理速查卡-️-rust-错误处理速查卡 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 模式 3: ? 操作符 | `#模式-3--操作符` | 同文件锚点不存在: #模式-3--操作符 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | anyhow - 灵活的错误处理 | `#anyhow---灵活的错误处理` | 同文件锚点不存在: #anyhow---灵活的错误处理 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | thiserror - 自定义错误类型 | `#thiserror---自定义错误类型` | 同文件锚点不存在: #thiserror---自定义错误类型 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | ⚠️ 边界情况 {#️-边界情况} | `#️-边界情况-️-边界情况` | 同文件锚点不存在: #️-边界情况-️-边界情况 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 边界 2:  panic 恢复 | `#边界-2--panic-恢复` | 同文件锚点不存在: #边界-2--panic-恢复 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | ⚠️ 边界情况 {#️-边界情况} | `#️-边界情况-️-边界情况` | 同文件锚点不存在: #️-边界情况-️-边界情况 |
| docs\02_reference\quick_reference\generics_cheatsheet.md | 生命周期速查卡 | `./type_system.md#生命周期` | 锚点不存在: #生命周期 |
| docs\02_reference\quick_reference\modules_cheatsheet.md | 🛤️ 路径系统 {#️-路径系统} | `#️-路径系统-️-路径系统` | 同文件锚点不存在: #️-路径系统-️-路径系统 |
| docs\02_reference\quick_reference\modules_cheatsheet.md | 单文件模块 {#文件模块-1} | `#单文件模块-文件模块-1` | 同文件锚点不存在: #单文件模块-文件模块-1 |
| docs\02_reference\quick_reference\modules_cheatsheet.md | ⚠️ 边界情况 {#️-边界情况} | `#️-边界情况-️-边界情况` | 同文件锚点不存在: #️-边界情况-️-边界情况 |
| docs\02_reference\quick_reference\network_programming_cheatsheet.md | HTTP 客户端 {#http-客户端-1} | `#http-客户端-http-客户端-1` | 同文件锚点不存在: #http-客户端-http-客户端-1 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 🏗️ 智能指针速查 {#️-智能指针速查} | `#️-智能指针速查-️-智能指针速查` | 同文件锚点不存在: #️-智能指针速查-️-智能指针速查 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `Box<T>` - 堆分配 | `#boxt---堆分配` | 同文件锚点不存在: #boxt---堆分配 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `Rc<T>` - 引用计数（单线程） | `#rct---引用计数单线程` | 同文件锚点不存在: #rct---引用计数单线程 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `Arc<T>` - 原子引用计数（多线程） | `#arct---原子引用计数多线程` | 同文件锚点不存在: #arct---原子引用计数多线程 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `RefCell<T>` - 内部可变性（单线程） | `#refcellt---内部可变性单线程` | 同文件锚点不存在: #refcellt---内部可变性单线程 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | `Mutex<T>` - 互斥锁（多线程） | `#mutext---互斥锁多线程` | 同文件锚点不存在: #mutext---互斥锁多线程 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | ⚠️ 低效模式 {#️-低效模式} | `#️-低效模式-️-低效模式` | 同文件锚点不存在: #️-低效模式-️-低效模式 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | ⚠️ 边界情况 {#️-边界情况} | `#️-边界情况-️-边界情况` | 同文件锚点不存在: #️-边界情况-️-边界情况 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 生命周期速查卡 | `./type_system.md#生命周期` | 锚点不存在: #生命周期 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 借用检查器速查卡 | `./ownership_cheatsheet.md#借用规则` | 锚点不存在: #借用规则 |
| docs\02_reference\quick_reference\README.md | 15. 进程管理速查卡 ⭐ NEW | `#15-进程管理速查卡--new` | 同文件锚点不存在: #15-进程管理速查卡--new |
| docs\02_reference\quick_reference\README.md | 16. 网络编程速查卡 ⭐ NEW | `#16-网络编程速查卡--new` | 同文件锚点不存在: #16-网络编程速查卡--new |
| docs\02_reference\quick_reference\README.md | 17. 算法与数据结构速查卡 ⭐ NEW | `#17-算法与数据结构速查卡--new` | 同文件锚点不存在: #17-算法与数据结构速查卡--new |
| docs\02_reference\quick_reference\README.md | 18. 设计模式速查卡 ⭐ NEW | `#18-设计模式速查卡--new` | 同文件锚点不存在: #18-设计模式速查卡--new |
| docs\02_reference\quick_reference\README.md | 19. WASM 速查卡 ⭐ NEW | `#19-wasm-速查卡--new` | 同文件锚点不存在: #19-wasm-速查卡--new |
| docs\02_reference\quick_reference\README.md | 20. AI/ML 速查卡 ⭐ NEW | `#20-aiml-速查卡--new` | 同文件锚点不存在: #20-aiml-速查卡--new |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 📦 Box - 堆分配 {#-box---堆分配} | `#-box---堆分配--box---堆分配` | 同文件锚点不存在: #-box---堆分配--box---堆分配 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔗 Rc - 引用计数（单线程） {#-rc---引用计数单线程} | `#-rc---引用计数单线程--rc---引用计数单线程` | 同文件锚点不存在: #-rc---引用计数单线程--rc---引用计数单线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔗 Arc - 原子引用计数（多线程） {#-arc---原子引用计数多线程} | `#-arc---原子引用计数多线程--arc---原子引用计数多线程` | 同文件锚点不存在: #-arc---原子引用计数多线程--arc---原子引用计数多线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔓 RefCell - 内部可变性（单线程） {#-refcell---内部可变性单线程} | `#-refcell---内部可变性单线程--refcell---内部可变性单线程` | 同文件锚点不存在: #-refcell---内部可变性单线程--refcell---内部可变性单线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔒 Mutex - 互斥锁（多线程） {#-mutex---互斥锁多线程} | `#-mutex---互斥锁多线程--mutex---互斥锁多线程` | 同文件锚点不存在: #-mutex---互斥锁多线程--mutex---互斥锁多线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔓 RwLock - 读写锁（多线程） {#-rwlock---读写锁多线程} | `#-rwlock---读写锁多线程--rwlock---读写锁多线程` | 同文件锚点不存在: #-rwlock---读写锁多线程--rwlock---读写锁多线程 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 🔗 Weak - 弱引用 {#-weak---弱引用} | `#-weak---弱引用--weak---弱引用` | 同文件锚点不存在: #-weak---弱引用--weak---弱引用 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | Rc\<RefCell\> - 单线程内部可变性 | `#rcrefcell---单线程内部可变性` | 同文件锚点不存在: #rcrefcell---单线程内部可变性 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | Arc\<Mutex\> - 多线程共享可变数据 | `#arcmutex---多线程共享可变数据` | 同文件锚点不存在: #arcmutex---多线程共享可变数据 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | Arc\<RwLock\> - 多线程读写锁 | `#arcrwlock---多线程读写锁` | 同文件锚点不存在: #arcrwlock---多线程读写锁 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | Rc\<RefCell\<Vec\>\> - 共享可变向量 | `#rcrefcellvec---共享可变向量` | 同文件锚点不存在: #rcrefcellvec---共享可变向量 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | ✂️ 字符串操作 {#️-字符串操作} | `#️-字符串操作-️-字符串操作` | 同文件锚点不存在: #️-字符串操作-️-字符串操作 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | String ↔ \&str | `#string--str` | 同文件锚点不存在: #string--str |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | 🖨️ 格式化输出 {#️-格式化输出} | `#️-格式化输出-️-格式化输出` | 同文件锚点不存在: #️-格式化输出-️-格式化输出 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | 反例 4: format!  panic 导致的拒绝服务 | `#反例-4-format--panic-导致的拒绝服务` | 同文件锚点不存在: #反例-4-format--panic-导致的拒绝服务 |
| docs\02_reference\quick_reference\testing_cheatsheet.md | 🛠️ 测试工具和库 {#️-测试工具和库} | `#️-测试工具和库-️-测试工具和库` | 同文件锚点不存在: #️-测试工具和库-️-测试工具和库 |
| docs\02_reference\quick_reference\threads_concurrency_cheatsheet.md | 反例 2: 死锁 - 重复获取同一 Mutex | `#反例-2-死锁---重复获取同一-mutex` | 同文件锚点不存在: #反例-2-死锁---重复获取同一-mutex |
| docs\02_reference\quick_reference\type_system.md | 🏗️ Trait 系统 {#️-trait-系统} | `#️-trait-系统-️-trait-系统` | 同文件锚点不存在: #️-trait-系统-️-trait-系统 |
| docs\02_reference\quick_reference\type_system.md | 协变（Covariant）- \&T | `#协变covariant--t` | 同文件锚点不存在: #协变covariant--t |
| docs\02_reference\quick_reference\type_system.md | 逆变（Contravariant）- fn(T) | `#逆变contravariant--fnt` | 同文件锚点不存在: #逆变contravariant--fnt |
| docs\02_reference\quick_reference\type_system.md | 不变（Invariant）- \&mut T | `#不变invariant--mut-t` | 同文件锚点不存在: #不变invariant--mut-t |
| docs\02_reference\quick_reference\type_system.md | Debug \& Display | `#debug--display` | 同文件锚点不存在: #debug--display |
| docs\02_reference\quick_reference\type_system.md | Clone \& Copy | `#clone--copy` | 同文件锚点不存在: #clone--copy |
| docs\02_reference\quick_reference\type_system.md | PartialEq \& Eq | `#partialeq--eq` | 同文件锚点不存在: #partialeq--eq |
| docs\02_reference\quick_reference\type_system.md | PartialOrd \& Ord | `#partialord--ord` | 同文件锚点不存在: #partialord--ord |
| docs\02_reference\quick_reference\type_system.md | ⚠️ 边界情况 {#️-边界情况} | `#️-边界情况-️-边界情况` | 同文件锚点不存在: #️-边界情况-️-边界情况 |
| docs\04_thinking\APPLICATIONS_ANALYSIS_VIEW.md | supported_unsupported_matrix | `../research_notes/software_design_theory/05_boundary_system/supported_unsupported_matrix.md#no_std` | 锚点不存在: #no_std |
| docs\04_thinking\APPLICATIONS_ANALYSIS_VIEW.md | supported_unsupported | `../research_notes/software_design_theory/05_boundary_system/supported_unsupported_matrix.md#no_std` | 锚点不存在: #no_std |
| docs\04_thinking\DECISION_GRAPH_NETWORK.md | Rust 1.93.0 决策图网 / Decision Graph Network | `#rust-1930-决策图网--decision-graph-network` | 同文件锚点不存在: #rust-1930-决策图网--decision-graph-network |
| docs\04_thinking\MIND_MAP_COLLECTION.md | 🗺️ 核心概念思维导图 {#️-核心概念思维导图} | `#️-核心概念思维导图-️-核心概念思维导图` | 同文件锚点不存在: #️-核心概念思维导图-️-核心概念思维导图 |
| docs\04_thinking\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md | ⚠️ Rust 1.93 行为变更影响（性能矩阵补充） {#️-rust-193-行为变更影响性能矩阵补充} | `#️-rust-193-行为变更影响性能矩阵补充-️-rust-193-行为变更影响性能矩阵补充` | 同文件锚点不存在: #️-rust-193-行为变更影响性能矩阵补充-️-rust-193-行为变更影响性能矩阵补充 |
| docs\04_thinking\MULTI_DIMENSIONAL_CONCEPT_MATRIX.md | 🛡️ 安全性对比矩阵 {#️-安全性对比矩阵} | `#️-安全性对比矩阵-️-安全性对比矩阵` | 同文件锚点不存在: #️-安全性对比矩阵-️-安全性对比矩阵 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | Rust 1.93.0 证明图网 / Proof Graph Network | `#rust-1930-证明图网--proof-graph-network` | 同文件锚点不存在: #rust-1930-证明图网--proof-graph-network |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 🛡️ 内存安全证明树 {#️-内存安全证明树} | `#️-内存安全证明树-️-内存安全证明树` | 同文件锚点不存在: #️-内存安全证明树-️-内存安全证明树 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 组合1: MaybeUninit + 调用追踪 | `#组合1-maybeuninit--调用追踪` | 同文件锚点不存在: #组合1-maybeuninit--调用追踪 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 组合2: 关联类型多边界 + 自动特征 | `#组合2-关联类型多边界--自动特征` | 同文件锚点不存在: #组合2-关联类型多边界--自动特征 |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | Rust 1.93.0 思维表征方式文档 / Thinking Representation Methods Documentation | `#rust-1930-思维表征方式文档--thinking-representation-methods-documentation` | 同文件锚点不存在: #rust-1930-思维表征方式文档--thinking-representation-methods-documentation |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 🗺️ 1. 思维导图 (Mind Map) {#️-1-思维导图-mind-map} | `#️-1-思维导图-mind-map-️-1-思维导图-mind-map` | 同文件锚点不存在: #️-1-思维导图-mind-map-️-1-思维导图-mind-map |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 3.9.1 借用 ↔ 所有权转换树 | `#391-借用--所有权转换树` | 同文件锚点不存在: #391-借用--所有权转换树 |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 3.9.2 Option ↔ Result 转换树 | `#392-option--result-转换树` | 同文件锚点不存在: #392-option--result-转换树 |
| docs\05_guides\ASYNC_PROGRAMMING_USAGE_GUIDE.md | 🏗️ 异步编程模式（5+ 完整示例） | `#️-异步编程模式5-完整示例` | 同文件锚点不存在: #️-异步编程模式5-完整示例 |
| docs\05_guides\ASYNC_PROGRAMMING_USAGE_GUIDE.md | 问题 1: 阻塞运行时 {#阻塞运行时} | `#问题-1-阻塞运行时-阻塞运行时` | 同文件锚点不存在: #问题-1-阻塞运行时-阻塞运行时 |
| docs\05_guides\ASYNC_PROGRAMMING_USAGE_GUIDE.md | 问题 2: Future 必须 Send {#future-必须-send} | `#问题-2-future-必须-send-future-必须-send` | 同文件锚点不存在: #问题-2-future-必须-send-future-必须-send |
| docs\05_guides\CROSS_MODULE_INTEGRATION_EXAMPLES.md | 场景3: 嵌入式 + 云端协同 | `#场景3-嵌入式--云端协同` | 同文件锚点不存在: #场景3-嵌入式--云端协同 |
| docs\05_guides\FINAL_DOCUMENTATION_COMPLETION_GUIDE.md | 📚 文档完善最终指南 - 2026-01-27 {#-文档完善最终指南---2026-01-27} | `#-文档完善最终指南---2026-01-27--文档完善最终指南---2026-01-27` | 同文件锚点不存在: #-文档完善最终指南---2026-01-27--文档完善最终指南---2026-01-27 |
| docs\05_guides\FINAL_DOCUMENTATION_COMPLETION_GUIDE.md | 可选后续 | `#3-可选后续非阻塞-100` | 同文件锚点不存在: #3-可选后续非阻塞-100 |
| docs\05_guides\MACRO_SYSTEM_USAGE_GUIDE.md | ⚠️ 宏的常见陷阱与调试技巧 {#️-宏的常见陷阱与调试技巧} | `#️-宏的常见陷阱与调试技巧-️-宏的常见陷阱与调试技巧` | 同文件锚点不存在: #️-宏的常见陷阱与调试技巧-️-宏的常见陷阱与调试技巧 |
| docs\05_guides\UNSAFE_RUST_GUIDE.md | ⚠️ 未定义行为 (UB) 案例 {#️-未定义行为-ub-案例} | `#️-未定义行为-ub-案例-️-未定义行为-ub-案例` | 同文件锚点不存在: #️-未定义行为-ub-案例-️-未定义行为-ub-案例 |
| docs\05_guides\UNSAFE_RUST_GUIDE.md | 🛡️ 安全抽象原则 {#️-安全抽象原则} | `#️-安全抽象原则-️-安全抽象原则` | 同文件锚点不存在: #️-安全抽象原则-️-安全抽象原则 |
| docs\06_toolchain\02_cargo_workspace_guide.md | 11.1 大型多 crate 项目 - 完整配置 | `#111-大型多-crate-项目---完整配置` | 同文件锚点不存在: #111-大型多-crate-项目---完整配置 |
| docs\06_toolchain\02_cargo_workspace_guide.md | 11.2 微服务架构 - 完整示例 | `#112-微服务架构---完整示例` | 同文件锚点不存在: #112-微服务架构---完整示例 |
| docs\06_toolchain\04_rust_1.91_vs_1.90_comparison.md | 2) Cargo 原生支持 `cargo publish --workspace` | `#2-cargo-原生支持-cargo-publish---workspace` | 同文件锚点不存在: #2-cargo-原生支持-cargo-publish---workspace |
| docs\06_toolchain\06_rust_1.93_compatibility_notes.md | 1. ... 函数参数（可变参数） | `#1--函数参数可变参数` | 同文件锚点不存在: #1--函数参数可变参数 |
| docs\06_toolchain\07_rust_1.93_full_changelog.md | cargo tree --format 长格式 | `#cargo-tree---format-长格式` | 同文件锚点不存在: #cargo-tree---format-长格式 |
| docs\06_toolchain\07_rust_1.93_full_changelog.md | cargo clean --workspace | `#cargo-clean---workspace` | 同文件锚点不存在: #cargo-clean---workspace |
| docs\06_toolchain\11_rust_1.93_cargo_rustdoc_changes.md | cargo tree --format 长格式 | `#cargo-tree---format-长格式` | 同文件锚点不存在: #cargo-tree---format-长格式 |
| docs\06_toolchain\11_rust_1.93_cargo_rustdoc_changes.md | cargo clean --workspace | `#cargo-clean---workspace` | 同文件锚点不存在: #cargo-clean---workspace |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 🗺️ 文档网络总览 {#️-文档网络总览} | `#️-文档网络总览-️-文档网络总览` | 同文件锚点不存在: #️-文档网络总览-️-文档网络总览 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C01 - 所有权与借用 | `#c01---所有权与借用` | 同文件锚点不存在: #c01---所有权与借用 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C02 - 类型系统 | `#c02---类型系统` | 同文件锚点不存在: #c02---类型系统 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C03 - 控制流与函数 | `#c03---控制流与函数` | 同文件锚点不存在: #c03---控制流与函数 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C04 - 泛型编程 | `#c04---泛型编程` | 同文件锚点不存在: #c04---泛型编程 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C05 - 线程与并发 | `#c05---线程与并发` | 同文件锚点不存在: #c05---线程与并发 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C06 - 异步编程 | `#c06---异步编程` | 同文件锚点不存在: #c06---异步编程 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C07 - 进程管理 | `#c07---进程管理` | 同文件锚点不存在: #c07---进程管理 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C08 - 算法与数据结构 | `#c08---算法与数据结构` | 同文件锚点不存在: #c08---算法与数据结构 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C09 - 设计模式 | `#c09---设计模式` | 同文件锚点不存在: #c09---设计模式 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C10 - 网络编程 | `#c10---网络编程` | 同文件锚点不存在: #c10---网络编程 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C11 - 宏系统 | `#c11---宏系统` | 同文件锚点不存在: #c11---宏系统 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | C12 - WASM | `#c12---wasm` | 同文件锚点不存在: #c12---wasm |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 速查卡 ↔ 指南映射 | `#速查卡--指南映射` | 同文件锚点不存在: #速查卡--指南映射 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 速查卡 ↔ 研究笔记映射 | `#速查卡--研究笔记映射` | 同文件锚点不存在: #速查卡--研究笔记映射 |
| docs\07_project\KNOWLEDGE_STRUCTURE_FRAMEWORK.md | 🗺️ 思维表征方式 {#️-思维表征方式} | `#️-思维表征方式-️-思维表征方式` | 同文件锚点不存在: #️-思维表征方式-️-思维表征方式 |
| docs\07_project\MODULE_KNOWLEDGE_STRUCTURE_GUIDE.md | 🗺️ 思维表征方式补充 {#️-思维表征方式补充} | `#️-思维表征方式补充-️-思维表征方式补充` | 同文件锚点不存在: #️-思维表征方式补充-️-思维表征方式补充 |
| docs\07_project\PROJECT_ARCHITECTURE_GUIDE.md | 🏗️ 项目结构 {#️-项目结构} | `#️-项目结构-️-项目结构` | 同文件锚点不存在: #️-项目结构-️-项目结构 |
| docs\archive\process_reports\2026_02\DOCS_STRUCTURE_AND_FORMAT_AUDIT_REPORT.md | 链接文本 | `#锚点` | 同文件锚点不存在: #锚点 |
| docs\archive\process_reports\2026_02\DOCS_STRUCTURE_AND_FORMAT_AUDIT_REPORT.md | 子节 | `#子节锚点` | 同文件锚点不存在: #子节锚点 |
| docs\archive\process_reports\2026_02\FORMAT_FIX_COMPLETION_REPORT.md | 概述 | `#概述` | 同文件锚点不存在: #概述 |
| docs\archive\process_reports\2026_02\FORMAT_FIX_COMPLETION_REPORT.md | 详细内容 | `#详细内容` | 同文件锚点不存在: #详细内容 |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 📋 任务清单（历史记录 - 已全部完成 ✅） | `#-任务清单历史记录---已全部完成-` | 同文件锚点不存在: #-任务清单历史记录---已全部完成- |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 1. 所有权模型形式化 ✅ | `#1-所有权模型形式化-` | 同文件锚点不存在: #1-所有权模型形式化- |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 2. 借用检查器证明 ✅ | `#2-借用检查器证明-` | 同文件锚点不存在: #2-借用检查器证明- |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 3. 生命周期形式化 ✅ | `#3-生命周期形式化-` | 同文件锚点不存在: #3-生命周期形式化- |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 4. 类型系统基础 ✅ | `#4-类型系统基础-` | 同文件锚点不存在: #4-类型系统基础- |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 1. 异步状态机形式化 ✅ 完成度 100% | `#1-异步状态机形式化--完成度-100` | 同文件锚点不存在: #1-异步状态机形式化--完成度-100 |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 2. Trait 系统形式化 ✅ 完成度 100% | `#2-trait-系统形式化--完成度-100` | 同文件锚点不存在: #2-trait-系统形式化--完成度-100 |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 3. 性能基准测试 ✅ 完成度 100% | `#3-性能基准测试--完成度-100` | 同文件锚点不存在: #3-性能基准测试--完成度-100 |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 1. 高级类型特性 ✅ 完成度 100% | `#1-高级类型特性--完成度-100` | 同文件锚点不存在: #1-高级类型特性--完成度-100 |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 2. 宏展开性能分析 ✅ 完成度 100% | `#2-宏展开性能分析--完成度-100` | 同文件锚点不存在: #2-宏展开性能分析--完成度-100 |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 周7-8: 高级类型特性研究 ✅ | `#周7-8-高级类型特性研究-` | 同文件锚点不存在: #周7-8-高级类型特性研究- |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 周9-10: 宏展开性能分析 ✅ | `#周9-10-宏展开性能分析-` | 同文件锚点不存在: #周9-10-宏展开性能分析- |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 每日检查清单 ✅（历史记录 - 所有任务已完成） | `#每日检查清单-历史记录---所有任务已完成` | 同文件锚点不存在: #每日检查清单-历史记录---所有任务已完成 |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 每周回顾 ✅（历史记录 - 所有任务已完成） | `#每周回顾-历史记录---所有任务已完成` | 同文件锚点不存在: #每周回顾-历史记录---所有任务已完成 |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 每月总结 ✅（历史记录 - 所有任务已完成） | `#每月总结-历史记录---所有任务已完成` | 同文件锚点不存在: #每月总结-历史记录---所有任务已完成 |
| docs\archive\process_reports\2026_02\TOC_AND_CONTENT_DEEPENING_PLAN.md | 文档标题 | `#文档标题` | 同文件锚点不存在: #文档标题 |
| docs\archive\process_reports\2026_02\TOC_AND_CONTENT_DEEPENING_PLAN.md | 二、节二 | `#二节二` | 同文件锚点不存在: #二节二 |
| docs\archive\process_reports\2026_02\TOC_AND_CONTENT_DEEPENING_PLAN.md | 2.1 子节 | `#21-子节` | 同文件锚点不存在: #21-子节 |
| docs\archive\process_reports\2026_02\TOC_AND_CONTENT_DEEPENING_PLAN.md | 三、节三 | `#三节三` | 同文件锚点不存在: #三节三 |
| docs\archive\reports\RUST_1.91_FEATURES_COMPREHENSIVE.md | Rust 1.91 特性全面文档 | `#rust-191-特性全面文档` | 同文件锚点不存在: #rust-191-特性全面文档 |
| docs\archive\reports\formal_system_reports\DOCUMENTATION_ENHANCEMENT_REPORT_2025_09_27.md | Rust 形式化工程系统文档完善报告 | `#rust-形式化工程系统文档完善报告` | 同文件锚点不存在: #rust-形式化工程系统文档完善报告 |
| docs\archive\reports\formal_system_reports\FORMAL_PROOFS_2025_11_11.md | Rust 形式化论证集合 2025-11-11 | `#rust-形式化论证集合-2025-11-11` | 同文件锚点不存在: #rust-形式化论证集合-2025-11-11 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | Rust 形式化工程体系知识图谱 2025-11-11 | `#rust-形式化工程体系知识图谱-2025-11-11` | 同文件锚点不存在: #rust-形式化工程体系知识图谱-2025-11-11 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 理论基础 → 工具链生态 | `#理论基础--工具链生态` | 同文件锚点不存在: #理论基础--工具链生态 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 工具链生态 → 应用领域 | `#工具链生态--应用领域` | 同文件锚点不存在: #工具链生态--应用领域 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 应用领域 → 研究前沿 | `#应用领域--研究前沿` | 同文件锚点不存在: #应用领域--研究前沿 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 🗺️ 学习路径图谱 | `#️-学习路径图谱` | 同文件锚点不存在: #️-学习路径图谱 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 路径1：理论基础 → 实践应用 | `#路径1理论基础--实践应用` | 同文件锚点不存在: #路径1理论基础--实践应用 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 路径2：工具链 → 工程实践 | `#路径2工具链--工程实践` | 同文件锚点不存在: #路径2工具链--工程实践 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 路径3：研究前沿 → 创新应用 | `#路径3研究前沿--创新应用` | 同文件锚点不存在: #路径3研究前沿--创新应用 |
| docs\archive\root_completion_reports\COMPREHENSIVE_TASK_ORCHESTRATION_2025_12_25.md | 🎯 全面任务编排与推进计划 - 2025-12-25 | `#-全面任务编排与推进计划---2025-12-25` | 同文件锚点不存在: #-全面任务编排与推进计划---2025-12-25 |
| docs\archive\root_completion_reports\COMPREHENSIVE_TASK_ORCHESTRATION_2025_12_25.md | 🗺️ 思维导图：任务关系网络 | `#️-思维导图任务关系网络` | 同文件锚点不存在: #️-思维导图任务关系网络 |
| docs\archive\root_completion_reports\COMPREHENSIVE_TASK_ORCHESTRATION_2025_12_25.md | 第1周：高优先级研究任务启动 ✅ **已完成** | `#第1周高优先级研究任务启动--已完成` | 同文件锚点不存在: #第1周高优先级研究任务启动--已完成 |
| docs\archive\root_completion_reports\COMPREHENSIVE_TASK_ORCHESTRATION_2025_12_25.md | 第2周：高优先级研究任务深化 ✅ **部分提前完成** | `#第2周高优先级研究任务深化--部分提前完成` | 同文件锚点不存在: #第2周高优先级研究任务深化--部分提前完成 |
| docs\archive\root_completion_reports\COMPREHENSIVE_TASK_ORCHESTRATION_2025_12_25.md | ✅ 已完成任务清单 | `#-已完成任务清单-1` | 同文件锚点不存在: #-已完成任务清单-1 |
| docs\archive\root_completion_reports\COMPREHENSIVE_TASK_ORCHESTRATION_2025_12_25.md | 📊 完成度统计 | `#-完成度统计-1` | 同文件锚点不存在: #-完成度统计-1 |
| docs\archive\root_completion_reports\COMPREHENSIVE_TASK_ORCHESTRATION_2025_12_25.md | 🎯 超出预期 | `#-超出预期-1` | 同文件锚点不存在: #-超出预期-1 |
| docs\archive\temp\swap\RUST_190_FAQ.md | ❓ Rust 1.90 升级 FAQ | `#-rust-190-升级-faq` | 同文件锚点不存在: #-rust-190-升级-faq |
| docs\archive\temp\swap\RUST_190_FAQ.md | Q4.1: rust_189\_\*.rs 文件的作用是什么？ | `#q41-rust_189_rs-文件的作用是什么` | 同文件锚点不存在: #q41-rust_189_rs-文件的作用是什么 |
| docs\archive\temp\swap\RUST_190_FAQ.md | Q4.2: 是否需要删除 rust_189\_\*.rs 文件？ | `#q42-是否需要删除-rust_189_rs-文件` | 同文件锚点不存在: #q42-是否需要删除-rust_189_rs-文件 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | Rust 1.92.0 / 1.93.0 示例代码兼容性验证报告 | `#rust-1920--1930-示例代码兼容性验证报告` | 同文件锚点不存在: #rust-1920--1930-示例代码兼容性验证报告 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.2 C01 - 所有权和借用作用域 | `#22-c01---所有权和借用作用域` | 同文件锚点不存在: #22-c01---所有权和借用作用域 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.3 C02 - 类型系统 | `#23-c02---类型系统` | 同文件锚点不存在: #23-c02---类型系统 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.4 C03 - 控制流和函数 | `#24-c03---控制流和函数` | 同文件锚点不存在: #24-c03---控制流和函数 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.5 C04 - 泛型 | `#25-c04---泛型` | 同文件锚点不存在: #25-c04---泛型 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.6 C05 - 线程和并发 | `#26-c05---线程和并发` | 同文件锚点不存在: #26-c05---线程和并发 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.7 C06 - 异步编程 | `#27-c06---异步编程` | 同文件锚点不存在: #27-c06---异步编程 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.8 C07 - 进程管理 | `#28-c07---进程管理` | 同文件锚点不存在: #28-c07---进程管理 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.9 C08 - 算法 | `#29-c08---算法` | 同文件锚点不存在: #29-c08---算法 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.10 C09 - 设计模式 | `#210-c09---设计模式` | 同文件锚点不存在: #210-c09---设计模式 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.11 C10 - 网络编程 | `#211-c10---网络编程` | 同文件锚点不存在: #211-c10---网络编程 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.12 C11 - 宏系统 | `#212-c11---宏系统` | 同文件锚点不存在: #212-c11---宏系统 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 2.13 C12 - WebAssembly | `#213-c12---webassembly` | 同文件锚点不存在: #213-c12---webassembly |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | ⚠️ 需要更新的示例 | `#️-需要更新的示例` | 同文件锚点不存在: #️-需要更新的示例 |
| docs\archive\version_reports\RUST_192_FEATURES_ALIGNMENT.md | Rust 1.92.0 / 1.93.0 特性对齐文档 / Rust Features Alignment | `#rust-1920--1930-特性对齐文档--rust-features-alignment` | 同文件锚点不存在: #rust-1920--1930-特性对齐文档--rust-features-alignment |
| docs\archive\version_reports\RUST_192_FEATURES_ALIGNMENT.md | 5.1.1 展开表默认启用（Unwind Tables with `-Cpanic=abort`） | `#511-展开表默认启用unwind-tables-with--cpanicabort` | 同文件锚点不存在: #511-展开表默认启用unwind-tables-with--cpanicabort |
| docs\archive\version_reports\RUST_192_THINKING_REPRESENTATION_COMPREHENSIVE.md | Rust 1.92.0 思维表征方式综合文档 / Comprehensive Thinking Representation Methods | `#rust-1920-思维表征方式综合文档--comprehensive-thinking-representation-methods` | 同文件锚点不存在: #rust-1920-思维表征方式综合文档--comprehensive-thinking-representation-methods |
| docs\archive\version_reports\RUST_192_THINKING_REPRESENTATION_COMPREHENSIVE.md | 🗺️ 1. 思维导图 (Mind Map) | `#️-1-思维导图-mind-map` | 同文件锚点不存在: #️-1-思维导图-mind-map |
| docs\research_notes\AENEAS_INTEGRATION_PLAN.md | RustBelt | `./formal_methods/ownership_model.md#rustbelt` | 锚点不存在: #rustbelt |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 引理 1 - 资源释放 | `../research_notes/formal_methods/ownership_model.md#引理-1-资源释放` | 锚点不存在: #引理-1-资源释放 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 3 - Copy 语义 | `../research_notes/formal_methods/ownership_model.md#定理-3-copy-语义` | 锚点不存在: #定理-3-copy-语义 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 规则 1 - 借用规则 | `../research_notes/formal_methods/borrow_checker_proof.md#规则-1-借用规则` | 锚点不存在: #规则-1-借用规则 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 引理 2 - 切片有效性 | `../research_notes/formal_methods/borrow_checker_proof.md#引理-2-切片有效性` | 锚点不存在: #引理-2-切片有效性 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 规则 3 - 生命周期包含 | `../research_notes/formal_methods/lifetime_formalization.md#规则-3-生命周期包含` | 锚点不存在: #规则-3-生命周期包含 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 定理 LF-T1 - 生命周期传递 | `../research_notes/formal_methods/lifetime_formalization.md#定理-lf-t1-生命周期传递` | 锚点不存在: #定理-lf-t1-生命周期传递 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 0, infinity) \| [定义 - 静态生命周期 | `../research_notes/formal_methods/lifetime_formalization.md#定义-静态生命周期` | 锚点不存在: #定义-静态生命周期 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 类型规则 - Trait Bound | `../research_notes/type_theory/type_system_foundations.md#类型规则-trait-bound` | 锚点不存在: #类型规则-trait-bound |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 类型规则 - Trait 实现 | `../research_notes/type_theory/type_system_foundations.md#类型规则-trait-实现` | 锚点不存在: #类型规则-trait-实现 |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 类型规则 - Trait 对象 | `../research_notes/type_theory/type_system_foundations.md#类型规则-trait-对象` | 锚点不存在: #类型规则-trait-对象 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | 概念-公理-定理映射表 | `#-概念-公理-定理映射表` | 同文件锚点不存在: #-概念-公理-定理映射表 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | 论证要素规范 | `FORMAL_PROOF_SYSTEM_GUIDE.md#-论证要素规范` | 锚点不存在: #-论证要素规范 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | 反例索引 | `#️-反例索引` | 同文件锚点不存在: #️-反例索引 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | FORMAL_PROOF_SYSTEM_GUIDE | `FORMAL_PROOF_SYSTEM_GUIDE.md#️-反例索引` | 锚点不存在: #️-反例索引 |
| docs\research_notes\CONCEPT_RELATIONSHIP_NETWORK.md | L1 元概念 → 文档 | `#l1-元概念--文档` | 同文件锚点不存在: #l1-元概念--文档 |
| docs\research_notes\CONCEPT_RELATIONSHIP_NETWORK.md | L2 核心概念 → 文档 | `#l2-核心概念--文档` | 同文件锚点不存在: #l2-核心概念--文档 |
| docs\research_notes\CONCEPT_RELATIONSHIP_NETWORK.md | L3 具体概念 → 文档 | `#l3-具体概念--文档` | 同文件锚点不存在: #l3-具体概念--文档 |
| docs\research_notes\CONTENT_ENHANCEMENT.md | QUALITY_CHECKLIST | `QUALITY_CHECKLIST.md#概念定义-属性关系-解释论证-层次化` | 锚点不存在: #概念定义-属性关系-解释论证-层次化 |
| docs\research_notes\CORE_FEATURES_FULL_CHAIN.md | 13. ? 操作符 | `#13--操作符` | 同文件锚点不存在: #13--操作符 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | 🔗 跨文档映射网络 - 核心索引 | `#-跨文档映射网络---核心索引` | 同文件锚点不存在: #-跨文档映射网络---核心索引 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | formal\_methods ↔ 其他文档 | `#formal_methods--其他文档` | 同文件锚点不存在: #formal_methods--其他文档 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | type\_theory ↔ 其他文档 | `#type_theory--其他文档` | 同文件锚点不存在: #type_theory--其他文档 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | software\_design\_theory ↔ 其他文档 | `#software_design_theory--其他文档` | 同文件锚点不存在: #software_design_theory--其他文档 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | 速查卡 ↔ 指南/研究笔记 | `#速查卡--指南研究笔记` | 同文件锚点不存在: #速查卡--指南研究笔记 |
| docs\research_notes\FORMAL_VERIFICATION_GUIDE.md | 工具链扩展任务（Rust → 证明助手） | `#工具链扩展任务rust--证明助手` | 同文件锚点不存在: #工具链扩展任务rust--证明助手 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 二、概念族 ↔ 文档 ↔ Def/Axiom/定理 映射表 | `#二概念族--文档--defaxiom定理-映射表` | 同文件锚点不存在: #二概念族--文档--defaxiom定理-映射表 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 三、文档 ↔ 思维表征 映射表 | `#三文档--思维表征-映射表` | 同文件锚点不存在: #三文档--思维表征-映射表 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 3.1 按文档 → 思维表征 | `#31-按文档--思维表征` | 同文件锚点不存在: #31-按文档--思维表征 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 3.2 按思维表征 → 文档（入口） | `#32-按思维表征--文档入口` | 同文件锚点不存在: #32-按思维表征--文档入口 |
| docs\research_notes\PROOF_INDEX.md | borrow_checker_proof.md | `./formal_methods/borrow_checker_proof.md#定理-2-借用规则正确性` | 锚点不存在: #定理-2-借用规则正确性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-1-进展性` | 锚点不存在: #定理-1-进展性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-2-保持性` | 锚点不存在: #定理-2-保持性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-3-类型安全` | 锚点不存在: #定理-3-类型安全 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-4-类型推导正确性` | 锚点不存在: #定理-4-类型推导正确性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-5-类型推导算法正确性` | 锚点不存在: #定理-5-类型推导算法正确性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-3-类型安全` | 锚点不存在: #定理-3-类型安全 |
| docs\research_notes\PROOF_INDEX.md | borrow_checker_proof.md | `./formal_methods/borrow_checker_proof.md#定理-2-借用规则正确性` | 锚点不存在: #定理-2-借用规则正确性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-4-类型推导正确性` | 锚点不存在: #定理-4-类型推导正确性 |
| docs\research_notes\PROOF_INDEX.md | type_system_foundations.md | `./type_theory/type_system_foundations.md#定理-5-类型推导算法正确性` | 锚点不存在: #定理-5-类型推导算法正确性 |
| docs\research_notes\QUALITY_CHECKLIST.md | 证明目标 / 实验目标 | `#证明目标--实验目标` | 同文件锚点不存在: #证明目标--实验目标 |
| docs\research_notes\TEMPLATE.md | 🔬 形式化定义 / 实验设计 | `#-形式化定义--实验设计` | 同文件锚点不存在: #-形式化定义--实验设计 |
| docs\research_notes\TEMPLATE.md | ✅ 证明目标 / 实验目标 | `#-证明目标--实验目标` | 同文件锚点不存在: #-证明目标--实验目标 |
| docs\research_notes\TEMPLATE.md | 待证明的性质 / 待测试的场景 | `#待证明的性质--待测试的场景` | 同文件锚点不存在: #待证明的性质--待测试的场景 |
| docs\research_notes\TEMPLATE.md | 证明方法 / 测试方法 | `#证明方法--测试方法` | 同文件锚点不存在: #证明方法--测试方法 |
| docs\research_notes\WRITING_GUIDE.md | 文档标题 | `#文档标题` | 同文件锚点不存在: #文档标题 |
| docs\research_notes\WRITING_GUIDE.md | Rust 实现 | `#rust-实现` | 同文件锚点不存在: #rust-实现 |
| docs\research_notes\WRITING_GUIDE.md | 边界 | `#边界` | 同文件锚点不存在: #边界 |
| docs\research_notes\formal_methods\async_state_machine.md | 示例 5：并发场景 - 多个 Future 并发执行 | `#示例-5并发场景---多个-future-并发执行` | 同文件锚点不存在: #示例-5并发场景---多个-future-并发执行 |
| docs\research_notes\formal_methods\async_state_machine.md | 示例 6：状态转换 - Waker 使用 | `#示例-6状态转换---waker-使用` | 同文件锚点不存在: #示例-6状态转换---waker-使用 |
| docs\research_notes\formal_methods\ERROR_HANDLING_DECISION_TREE.md | 维度 1: 错误类型 - 可恢复 vs 不可恢复 | `#维度-1-错误类型---可恢复-vs-不可恢复` | 同文件锚点不存在: #维度-1-错误类型---可恢复-vs-不可恢复 |
| docs\research_notes\formal_methods\ERROR_HANDLING_DECISION_TREE.md | ❌ 反模式 3: 错误的 `?` 使用导致信息丢失 | `#-反模式-3-错误的--使用导致信息丢失` | 同文件锚点不存在: #-反模式-3-错误的--使用导致信息丢失 |
| docs\research_notes\formal_methods\ERROR_HANDLING_DECISION_TREE.md | 完整示例 3: anyhow + thiserror 混合使用 | `#完整示例-3-anyhow--thiserror-混合使用` | 同文件锚点不存在: #完整示例-3-anyhow--thiserror-混合使用 |
| docs\research_notes\formal_methods\ownership_model.md | 示例 8: 复杂所有权场景 - 结构体字段移动 | `#示例-8-复杂所有权场景---结构体字段移动` | 同文件锚点不存在: #示例-8-复杂所有权场景---结构体字段移动 |
| docs\research_notes\formal_methods\ownership_model.md | 示例 9: 错误示例 - 使用已移动的值 | `#示例-9-错误示例---使用已移动的值` | 同文件锚点不存在: #示例-9-错误示例---使用已移动的值 |
| docs\research_notes\formal_methods\send_sync_formalization.md | 🔬 形式化定义 | `#-形式化定义` | 同文件锚点不存在: #-形式化定义 |
| docs\research_notes\software_design_theory\07_anti_patterns.md | FORMAL_PROOF_SYSTEM_GUIDE | `../FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例` | 锚点不存在: #设计模式反例 |
| docs\research_notes\software_design_theory\07_anti_patterns.md | FORMAL_PROOF_SYSTEM_GUIDE | `../FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例` | 锚点不存在: #设计模式反例 |
| docs\research_notes\software_design_theory\README.md | 03_semantic_boundary_map 场景 7–9 | `02_workflow_safe_complete_models/03_semantic_boundary_map.md#场景化-safe-决策-3-例` | 锚点不存在: #场景化-safe-决策-3-例 |
| docs\research_notes\software_design_theory\README.md | FORMAL_PROOF_SYSTEM_GUIDE | `../FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例` | 锚点不存在: #设计模式反例 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\README.md | FORMAL_PROOF_SYSTEM_GUIDE | `../../FORMAL_PROOF_SYSTEM_GUIDE.md#设计模式反例` | 锚点不存在: #设计模式反例 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\abstract_factory.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\builder.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\factory_method.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\prototype.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\singleton.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\adapter.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\bridge.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\composite.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\decorator.md | 完整场景示例：HTTP 客户端装饰链（日志 + 重试） | `#完整场景示例http-客户端装饰链日志--重试` | 同文件锚点不存在: #完整场景示例http-客户端装饰链日志--重试 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\decorator.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\facade.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\flyweight.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\proxy.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\chain_of_responsibility.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\command.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\interpreter.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\iterator.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\mediator.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\memento.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\observer.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\state.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\strategy.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\template_method.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\visitor.md | GoF | `../README.md#与-gof-原书对应` | 锚点不存在: #与-gof-原书对应 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\03_semantic_boundary_map.md | 示例 5：领域逻辑 + 持久化 | `#示例-5领域逻辑--持久化` | 同文件锚点不存在: #示例-5领域逻辑--持久化 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\03_semantic_boundary_map.md | 场景 8：跨线程缓存（Flyweight + Arc） | `#场景-8跨线程缓存flyweight--arc` | 同文件锚点不存在: #场景-8跨线程缓存flyweight--arc |
| docs\research_notes\software_design_theory\03_execution_models\06_boundary_analysis.md | 五模型 × 三维边界 | `#五模型--三维边界` | 同文件锚点不存在: #五模型--三维边界 |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 场景 1：批处理流水线（同步 + 策略） | `#场景-1批处理流水线同步--策略` | 同文件锚点不存在: #场景-1批处理流水线同步--策略 |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 场景 2：高并发 Web 服务（异步 + Observer + 通道） | `#场景-2高并发-web-服务异步--observer--通道` | 同文件锚点不存在: #场景-2高并发-web-服务异步--observer--通道 |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 场景 3：图像处理（并行 + Iterator） | `#场景-3图像处理并行--iterator` | 同文件锚点不存在: #场景-3图像处理并行--iterator |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 场景 4：多服务编排（分布式 + Proxy + DTO） | `#场景-4多服务编排分布式--proxy--dto` | 同文件锚点不存在: #场景-4多服务编排分布式--proxy--dto |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 示例 1：批处理 + Strategy（同步） | `#示例-1批处理--strategy同步` | 同文件锚点不存在: #示例-1批处理--strategy同步 |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 示例 2：并发 + Observer（std::thread + mpsc） | `#示例-2并发--observerstdthread--mpsc` | 同文件锚点不存在: #示例-2并发--observerstdthread--mpsc |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 示例 3：并行 + Strategy（rayon，需 `cargo add rayon`） | `#示例-3并行--strategyrayon需-cargo-add-rayon` | 同文件锚点不存在: #示例-3并行--strategyrayon需-cargo-add-rayon |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 完整多模式组合链条：Builder + Factory + Repository | `#完整多模式组合链条builder--factory--repository` | 同文件锚点不存在: #完整多模式组合链条builder--factory--repository |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 链条 1：Builder + Factory + Repository | `#链条-1builder--factory--repository` | 同文件锚点不存在: #链条-1builder--factory--repository |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 链条 2：Decorator + Strategy + Observer（完整实现） | `#链条-2decorator--strategy--observer完整实现` | 同文件锚点不存在: #链条-2decorator--strategy--observer完整实现 |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 链条 3：Composite + Visitor + Iterator（完整实现） | `#链条-3composite--visitor--iterator完整实现` | 同文件锚点不存在: #链条-3composite--visitor--iterator完整实现 |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 链条 4：Chain of Responsibility + Command + Observer | `#链条-4chain-of-responsibility--command--observer` | 同文件锚点不存在: #链条-4chain-of-responsibility--command--observer |
| docs\research_notes\software_design_theory\04_compositional_engineering\README.md | 示例 1：Builder + Factory Method | `#示例-1builder--factory-method` | 同文件锚点不存在: #示例-1builder--factory-method |
| docs\research_notes\software_design_theory\04_compositional_engineering\README.md | 示例 2：Repository + Service Layer + DTO（完整链条） | `#示例-2repository--service-layer--dto完整链条` | 同文件锚点不存在: #示例-2repository--service-layer--dto完整链条 |
| docs\research_notes\type_theory\trait_system_formalization.md | Trait + 泛型 + GAT 组合与 Specialization | `#trait--泛型--gat-组合与-specialization` | 同文件锚点不存在: #trait--泛型--gat-组合与-specialization |
| docs\research_notes\type_theory\trait_system_formalization.md | 示例 8: 高级 Trait 特性 - 默认实现和关联函数 | `#示例-8-高级-trait-特性---默认实现和关联函数` | 同文件锚点不存在: #示例-8-高级-trait-特性---默认实现和关联函数 |
| docs\research_notes\type_theory\variance_theory.md | 组合法则：类型 + 生命周期 + 型变 | `#组合法则类型--生命周期--型变` | 同文件锚点不存在: #组合法则类型--生命周期--型变 |

## 修复建议

### 1. 文件不存在问题

- 检查链接路径是否正确
- 确认目标文件是否已被移动或删除
- 更新链接指向正确的文件位置

### 2. 锚点不存在问题

- 检查锚点ID是否与目标文件中的标题匹配
- GitHub风格锚点：将标题转换为小写，空格替换为连字符，移除标点
- 示例：`## Hello World!` -> `#hello-world`

### 3. 同文件锚点问题

- 检查文档中是否存在对应的标题
- 可能是文档结构已更改但目录未更新

## 源文件问题统计

| 源文件 | 损坏链接数 |
| :--- | :--- |
| docs\research_notes\CODE_DOC_FORMAL_MAPPING.md | 57 |
| docs\research_notes\PROOF_INDEX.md | 46 |
| docs\research_notes\SYSTEM_INTEGRATION.md | 18 |
| docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md | 18 |
| docs\07_project\DOCUMENTATION_CROSS_REFERENCE_GUIDE.md | 15 |
| docs\archive\process_reports\2026_02\TASK_ORCHESTRATION_AND_EXECUTION_PLAN.md | 15 |
| docs\archive\version_reports\RUST_192_EXAMPLE_COMPATIBILITY_REPORT.md | 14 |
| docs\rust-formal-engineering-system\03_design_patterns\README.md | 12 |
| docs\02_reference\quick_reference\smart_pointers_cheatsheet.md | 11 |
| docs\research_notes\COMPREHENSIVE_SYSTEMATIC_OVERVIEW.md | 11 |
| docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md | 11 |
| docs\02_reference\quick_reference\ownership_cheatsheet.md | 10 |
| docs\rust-formal-engineering-system\02_practical_applications\memory\README.md | 10 |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\01_compiler\README.md | 10 |
| docs\02_reference\quick_reference\type_system.md | 9 |
| docs\02_reference\STANDARD_LIBRARY_COMPREHENSIVE_ANALYSIS_2025_12_25.md | 8 |
| docs\archive\reports\formal_system_reports\KNOWLEDGE_GRAPH_2025_11_11.md | 8 |
| docs\archive\reports\formal_system_reports\RUST_1_91_QUICK_REFERENCE.md | 8 |
| docs\research_notes\README.md | 8 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md | 8 |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\02_package_manager\README.md | 8 |
| docs\archive\root_completion_reports\COMPREHENSIVE_TASK_ORCHESTRATION_2025_12_25.md | 7 |
| docs\archive\temp\swap\RUST_190_FAQ.md | 7 |
| docs\research_notes\software_design_theory\03_execution_models\README.md | 7 |
| docs\rust-formal-engineering-system\06_toolchain_ecosystem\03_build_tools\README.md | 7 |
| docs\02_reference\quick_reference\error_handling_cheatsheet.md | 6 |
| docs\02_reference\quick_reference\README.md | 6 |
| docs\research_notes\CONTENT_ENHANCEMENT.md | 6 |
| docs\research_notes\HIERARCHICAL_MAPPING_AND_SUMMARY.md | 6 |
| docs\research_notes\TEMPLATE.md | 6 |
| docs\rust-formal-engineering-system\02_practical_applications\performance\README.md | 6 |
| docs\rust-formal-engineering-system\02_programming_paradigms\01_synchronous\README.md | 6 |
| docs\rust-formal-engineering-system\02_programming_paradigms\02_async\README.md | 6 |
| docs\rust-formal-engineering-system\03_design_patterns\04_concurrent\README.md | 6 |
| docs\02_reference\quick_reference\async_patterns.md | 5 |
| docs\archive\spell_check\SPELL_CHECK_SETUP_SUMMARY.md | 5 |
| docs\archive\temp\FORMAL_AND_PRACTICAL_NAVIGATION.md | 5 |
| docs\archive\temp\swap\RUST_190_QUICK_NAVIGATION.md | 5 |
| docs\research_notes\CROSS_REFERENCE_INDEX.md | 5 |
| docs\research_notes\software_design_theory\02_workflow_safe_complete_models\04_expressiveness_boundary.md | 5 |
| docs\research_notes\software_design_theory\03_execution_models\05_distributed.md | 5 |
| docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md | 5 |
| docs\research_notes\type_theory\trait_system_formalization.md | 5 |
| docs\02_reference\EDGE_CASES_AND_SPECIAL_CASES.md | 4 |
| docs\02_reference\quick_reference\strings_formatting_cheatsheet.md | 4 |
| docs\04_thinking\PROOF_GRAPH_NETWORK.md | 4 |
| docs\04_thinking\THINKING_REPRESENTATION_METHODS.md | 4 |
| docs\archive\process_reports\2026_02\TOC_AND_CONTENT_DEEPENING_PLAN.md | 4 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md | 4 |
| docs\research_notes\software_design_theory\01_design_patterns_formal\DESIGN_PATTERNS_BOUNDARY_MATRIX.md | 4 |
| ... 还有 122 个文件 | |

**总计 172 个文件包含损坏链接**:
