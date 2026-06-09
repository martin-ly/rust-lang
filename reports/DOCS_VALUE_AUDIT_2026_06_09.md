# docs/ 目录价值审计报告

- **审计时间**: 2026-06-09
- **当前 Rust 版本**: 1.96.0
- **扫描文件数**: 1030

## 文件分类统计

| 分类 | 文件数 | 问题数 | 说明 |
|:---|:---:|:---:|:---|
| A (核心参考) | 47 | 31 | 速查表、学习路径、核心参考 |
| B (指南工具) | 126 | 65 | 指南、工具链、实践文档 |
| C (研究综述) | 857 | 1525 | 研究笔记、思考记录、大型专项 |

## 详细问题列表

### docs\00_master_index.md

- ⚠️ 损坏链接: [docs/02_reference/quick_reference/](02_reference/quick_reference/README.md)

### docs\00_meta\00_formal_content_master_index.md

- ⚠️ 损坏链接: [`00_rust_ownership_decidability_integration_plan.md`](./00_rust_ownership_decidability_integration_plan.md)
- ⚠️ 损坏链接: [`rust-ownership-decidability/README.md`](../rust-ownership-decidability/README.md)

### docs\00_meta\00_reorganization_complete.md

- ⚠️ 损坏链接: [重组记录](history/00_2026_reorganization.md)

### docs\00_meta\00_rust_feature_tracking_template.md

- ⚠️ 损坏链接: [矩阵模板](./00_template_matrix.md)

### docs\00_meta\00_template_concept_doc.md

- ⚠️ 损坏链接: [矩阵模板](./00_template_matrix.md)

### docs\00_meta\00_template_decision_tree.md

- ⚠️ 损坏链接: [矩阵模板](./00_template_matrix.md)

### docs\00_meta\analysis\00_rust_2026_project_goals_monthly_tracking.md

- ⚠️ 损坏链接: [2026-04 对称差分析报告](./00_rust_global_alignment_symmetric_difference_analysis_2026.md)
- ⚠️ 损坏链接: [2026-05 对称差分析报告](./00_rust_global_alignment_symmetric_difference_analysis_2026_05.md)

### docs\00_meta\history\00_2026_reorganization.md

- ⚠️ 损坏链接: [00_project_reorganization_plan.md](./00_project_reorganization_plan.md)

### docs\01_learning\01_google_rust_mapping.md

- ⚠️ 损坏链接: [01_traits.md](../concept/02_intermediate/01_traits.md)
- ⚠️ 损坏链接: [02_borrowing.md](../concept/01_foundation/02_borrowing.md)
- ⚠️ 损坏链接: [concept/01_foundation/01_ownership.md](../concept/01_foundation/01_ownership.md)
- ⚠️ 损坏链接: [concept/01_foundation/04_type_system.md](../concept/01_foundation/04_type_system.md)
- ⚠️ 损坏链接: [concept/01_foundation/10_error_handling_basics.md](../concept/01_foundation/10_error_handling_basics.md)
- ⚠️ 损坏链接: [concept/01_foundation/](../concept/01_foundation/)
- ⚠️ 损坏链接: [concept/02_intermediate/02_generics.md](../concept/02_intermediate/02_generics.md)

### docs\01_learning\01_official_resources_mapping.md

- ⚠️ 损坏链接: [MVP 学习路径](../LEARNING_MVP_PATH.md)
- ⚠️ 损坏链接: [concept/01_foundation/](../concept/01_foundation/)
- ⚠️ 损坏链接: [concept/03_advanced/02_async.md](../concept/03_advanced/02_async.md)
- ⚠️ 损坏链接: [concept/03_advanced/03_unsafe.md](../concept/03_advanced/03_unsafe.md)
- ⚠️ 损坏链接: [concept/](../concept/)
- ⚠️ 损坏链接: [docs/06_toolchain/03_rustdoc_advanced.md](06_toolchain/03_rustdoc_advanced.md)
- ⚠️ 损坏链接: [docs/06_toolchain/06_19_rust_1_96_features.md](06_toolchain/06_19_rust_1_96_features.md)
- ⚠️ 损坏链接: [docs/06_toolchain/](06_toolchain/)
- ⚠️ 损坏链接: [examples/](../examples/)

### docs\01_learning\quizzes\README.md

- ⚠️ 损坏链接: [concept/03_advanced/21_quiz_concurrency_async.md](../../concept/03_advanced/21_quiz_concurrency_async.md)
- ⚠️ 损坏链接: [concept/03_advanced/22_quiz_unsafe.md](../../concept/03_advanced/22_quiz_unsafe.md)
- ⚠️ 损坏链接: [concept/03_advanced/23_quiz_macros.md](../../concept/03_advanced/23_quiz_macros.md)

### docs\02_reference\02_cross_language_comparison.md

- ⚠️ 损坏链接: [T constraints.Ordered](a, b T)
- ⚠️ 损坏链接: [多维概念矩阵](../04_thinking/04_multi_dimensional_concept_matrix.md)

### docs\02_reference\02_rustnomicon_alignment.md

- ⚠️ 损坏链接: [02_reference 目录](./README.md)
- ⚠️ 损坏链接: [README](./README.md)

### docs\02_reference\02_standard_library_comprehensive_analysis_2025_12_25.md

- ⚠️ 损坏链接: [02_reference 目录](./README.md)

### docs\02_reference\ALIGNMENT_GUIDE.md

- ⚠️ 损坏链接: [02_reference 目录](./README.md)
- ⚠️ 损坏链接: [07_alignment_knowledge_critical_evaluation_2026_02.md](../07_project/07_alignment_knowledge_critical_evaluation_2026_02.md)
- ⚠️ 损坏链接: [RUST_RELEASE_TRACKING_CHECKLIST](../07_project/07_rust_release_tracking_checklist.md)

### docs\02_reference\quick_reference\02_pin_cheatsheet.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.68' → 建议更新为 1.96.0+

### docs\02_reference\quick_reference\02_rust_190_to_193_features_cheatsheet.md

- ⚠️ 旧版本声明: '**对应 Rust 版本**: 1.90.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **版本**: Rust 1.90.0' → 建议更新为 1.96.0+

### docs\02_reference\quick_reference\02_rust_195_features_cheatsheet.md

- ⚠️ 旧版本声明: '> **稳定版本**: Rust 1.95.0' → 建议更新为 1.96.0+

### docs\04_thinking\04_applications_analysis_view.md

- ⚠️ 损坏链接: [多维概念矩阵](./04_multi_dimensional_concept_matrix.md)

### docs\04_thinking\04_mind_map_collection.md

- ⚠️ 损坏链接: [04_multi_dimensional_concept_matrix.md](./04_multi_dimensional_concept_matrix.md)

### docs\04_thinking\04_thinking_representation_methods.md

- ⚠️ 损坏链接: [04_multi_dimensional_concept_matrix.md](./04_multi_dimensional_concept_matrix.md)

### docs\04_thinking\README.md

- ⚠️ 损坏链接: [concept/](../concept/)
- ⚠️ 损坏链接: [knowledge/](../knowledge/)
- ⚠️ 损坏链接: [多维度概念矩阵](04_multi_dimensional_concept_matrix.md)

### docs\05_guides\05_async_programming_usage_guide.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.85.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.85.0' → 建议更新为 1.96.0+

### docs\05_guides\05_cfg_select_macro_guide.md

- ⚠️ 旧版本声明: '> **稳定版本**: Rust 1.95.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **适用版本**: 1.95.0' → 建议更新为 1.96.0+

### docs\05_guides\05_inline_assembly_guide.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.0' → 建议更新为 1.96.0+

### docs\05_guides\05_kani_practical_guide.md

- ⚠️ 损坏链接: [形式化操作语义与 Rust 的形式化模型](../../concept/04_formal/09_operational_semantics.md)
- ⚠️ 旧版本声明: '**对应 Rust 版本**: 1.80.0' → 建议更新为 1.96.0+

### docs\05_guides\05_performance_tuning_guide.md

- ⚠️ 损坏链接: [05_performance_testing_report.md](./05_performance_testing_report.md)
- ⚠️ 损坏链接: [05_performance_testing_report.md](./05_performance_testing_report.md)

### docs\05_guides\05_testing_coverage_guide.md

- ⚠️ 损坏链接: [05_performance_testing_report.md](./05_performance_testing_report.md)

### docs\05_guides\05_verus_practical_guide.md

- ⚠️ 损坏链接: [形式化操作语义与 Rust 的形式化模型](../../concept/04_formal/09_operational_semantics.md)
- ⚠️ 旧版本声明: '**对应 Rust 版本**: 1.80.0' → 建议更新为 1.96.0+

### docs\05_guides\06_rust_2024_edition_migration_guide.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.85.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '**对应 Rust 版本**: 1.85.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.85.0' → 建议更新为 1.96.0+

### docs\05_guides\workflow\01_workflow_theory.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\06_toolchain\06_14_rust_1_95_nightly_preview.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.95.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.95.0' → 建议更新为 1.96.0+

### docs\06_toolchain\06_20_rustdoc_196_improvements.md

- ⚠️ 损坏链接: [`from_str()`](Self::from_str)
- ⚠️ 损坏链接: [`new()`](Self::new)
- ⚠️ 损坏链接: [`process()`](Self::process)
- ⚠️ 损坏链接: [`validate()`](Self::validate)
- ⚠️ 损坏链接: [deprecated(since = "2.0.0",note = "请使用 [`new_api()`](Self::new_api)

### docs\06_toolchain\06_jump_tables_guide.md

- ⚠️ 旧版本声明: '> **稳定版本**: Rust 1.93.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **适用版本**: 1.93.0' → 建议更新为 1.96.0+

### docs\07_project\07_completion_status.md

- ⚠️ 损坏链接: [07_project 目录](./README.md)
- ⚠️ 损坏链接: [README](./README.md)

### docs\07_project\07_documentation_cross_reference_guide.md

- ⚠️ 损坏链接: [07_project 目录](./README.md)
- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 损坏链接: [文档中心主索引](./README.md)

### docs\07_project\07_extension_deepening_plan_2026.md

- ⚠️ 损坏链接: [07_project 目录](./README.md)
- ⚠️ 损坏链接: [README](./README.md)

### docs\07_project\07_knowledge_structure_framework.md

- ⚠️ 损坏链接: [07_project 目录](./README.md)

### docs\07_project\07_module_knowledge_structure_guide.md

- ⚠️ 损坏链接: [07_project 目录](./README.md)
- ⚠️ 损坏链接: [多维概念矩阵](../04_thinking/04_multi_dimensional_concept_matrix.md)

### docs\07_project\07_project_architecture_guide.md

- ⚠️ 损坏链接: [07_project 目录](./README.md)

### docs\README.md

- ⚠️ 损坏链接: [00_meta/](00_meta/)
- ⚠️ 损坏链接: [01_learning/](01_learning/)
- ⚠️ 损坏链接: [01_learning/学习路径指南](01_learning/01_learning_path_guide_2025_10_24.md)
- ⚠️ 损坏链接: [02_reference/](02_reference/)
- ⚠️ 损坏链接: [02_reference/quick_reference/](02_reference/quick_reference/)
- ⚠️ 损坏链接: [03_guides/](03_guides/)
- ⚠️ 损坏链接: [03_guides/](03_guides/)
- ⚠️ 损坏链接: [03_practice/](03_practice/)
- ⚠️ 损坏链接: [03_practice/](03_practice/)
- ⚠️ 损坏链接: [05_guides/](05_guides/)
- ⚠️ 损坏链接: [05_guides/](05_guides/)
- ⚠️ 损坏链接: [06_toolchain/](06_toolchain/)

### docs\TRPL_3RD_ED_DIFF.md

- ⚠️ 损坏链接: [02_rust_vs_cpp.md](../concept/05_comparative/02_rust_vs_cpp.md)
- ⚠️ 损坏链接: [05_reference/](../concept/05_reference/)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.85.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.85.0' → 建议更新为 1.96.0+

### docs\content\10_content_crates_mapping.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [content 目录](./README.md)

### docs\content\academic\10_coq_formalization_guide.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\content\academic\10_tree_borrows_guide.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\content\academic\README.md

- ⚠️ 损坏链接: [Tree Borrows 权威指南](./10_tree_borrows_authoritative_guide.md)

### docs\content\ecosystem\README.md

- ⚠️ 损坏链接: [Content 总览](../README.md)

### docs\content\emerging\README.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.95' → 建议更新为 1.96.0+

### docs\content\production\README.md

- ⚠️ 损坏链接: [Content 总览](../README.md)

### docs\content\representations\10_knowledge_representation_matrix.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\content\scenarios\10_web_application_scenarios.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\research_notes\10_00_comprehensive_summary.md

- ⚠️ 损坏链接: [COMPREHENSIVE_ARGUMENTATION_GAP_ANALYSIS_AND_PLAN](software_design_theory/10_comprehensive_argumentation_gap_analysis_and_plan.md)
- ⚠️ 损坏链接: [FORMAL_METHODS_COMPLETENESS_CHECKLIST](formal_methods/10_formal_methods_completeness_checklist.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-20（109 天前，建议复审）

### docs\research_notes\10_00_organization_and_navigation.md

- ⚠️ 损坏链接: [04_compositional_engineering](software_design_theory/04_compositional_engineering/README.md#组合反例编译错误映射ce-t1t2t3)
- ⚠️ 损坏链接: [06_boundary_analysis](software_design_theory/03_execution_models/06_boundary_analysis.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_aeneas_integration_plan.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-03-10（91 天前，建议复审）

### docs\research_notes\10_application_trees.md

- ⚠️ 最后更新: 2026-03-10（91 天前，建议复审）

### docs\research_notes\10_argumentation_chain_and_flow.md

- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_argumentation_gap_index.md

- ⚠️ 损坏链接: [construction_capability](type_theory/10_construction_capability.md)
- ⚠️ 损坏链接: [coq_skeleton](coq_skeleton/README.md)
- ⚠️ 损坏链接: [formal_methods/00_completeness_gaps](formal_methods/00_completeness_gaps.md)
- ⚠️ 损坏链接: [software_design_theory](software_design_theory/README.md)
- ⚠️ 损坏链接: [type_theory/00_completeness_gaps](formal_methods/00_completeness_gaps.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_authoritative_alignment_guide.md

- ⚠️ 损坏链接: [Trait系统](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [借用检查](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [异步状态机](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [所有权模型](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [类型系统](type_theory/10_type_system_foundations.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_authoritative_alignment_status.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_best_practices.md

- ⚠️ 损坏链接: [.*\](.*)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [coq_skeleton](coq_skeleton/README.md)
- ⚠️ 损坏链接: [formal_methods](formal_methods/README.md)
- ⚠️ 损坏链接: [formal_methods](formal_methods/README.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [type_theory](type_theory/README.md)
- ⚠️ 损坏链接: [type_theory](type_theory/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_cargo_194_features.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_changelog.md

- ⚠️ 损坏链接: [00_completeness_gaps](formal_methods/00_completeness_gaps.md)
- ⚠️ 损坏链接: [01_design_patterns_formal/README §23 模式多维对比矩阵](software_design_theory/01_design_patterns_formal/README.md#23-模式多维对比矩阵)
- ⚠️ 损坏链接: [03_execution_models/README §执行模型多维对比矩阵](software_design_theory/03_execution_models/README.md#执行模型多维对比矩阵)
- ⚠️ 损坏链接: [04_compositional_engineering](software_design_theory/04_compositional_engineering/README.md)
- ⚠️ 损坏链接: [06_boundary_analysis](software_design_theory/03_execution_models/06_boundary_analysis.md)
- ⚠️ 损坏链接: [06_rust_idioms](software_design_theory/06_rust_idioms.md)
- ⚠️ 损坏链接: [07_anti_patterns](software_design_theory/07_anti_patterns.md)
- ⚠️ 损坏链接: [formal_methods/README §formal_methods 六篇并表](formal_methods/README.md#formal_methods-六篇并表)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [software_design_theory/](software_design_theory/README.md)
- ⚠️ 损坏链接: [type_theory/10_construction_capability.md](type_theory/10_construction_capability.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_classification.md

- ⚠️ 损坏链接: [07_anti_patterns](software_design_theory/07_anti_patterns.md)
- ⚠️ 损坏链接: [software_design_theory](software_design_theory/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_code_doc_formal_mapping.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_cognitive_argumentation_framework.md

- ⚠️ 最后更新: 2026-02-23（106 天前，建议复审）

### docs\research_notes\10_comprehensive_systematic_overview.md

- ⚠️ 损坏链接: [00_completeness_gaps](formal_methods/00_completeness_gaps.md)
- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 损坏链接: [software_design_theory](software_design_theory/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_comprehensive_systematic_review_and_100_percent_plan.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-20（109 天前，建议复审）

### docs\research_notes\10_comprehensive_task_orchestration_100_percent.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_comprehensive_task_orchestration_2026_03_01.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_concept_hierarchy_framework.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_concept_relationship_network.md

- ⚠️ 损坏链接: [10_async_state_machine.md](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [10_ownership_model.md](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [10_ownership_model.md](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [10_ownership_model.md](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [10_type_system_foundations.md](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [10_type_system_foundations.md](type_theory/10_type_system_foundations.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_const_eval_formalization.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_content_enhancement.md

- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_contributing.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_coq_isabelle_proof_scaffolding.md

- ⚠️ 最后更新: 2026-03-08（93 天前，建议复审）

### docs\research_notes\10_coq_of_rust_integration_plan.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\10_core_features_full_chain.md

- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [formal_methods/README §六篇并表](formal_methods/README.md#formal_methods-六篇并表)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [trait_system_formalization](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [trait_system_formalization](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\10_core_theorems_en_summary.md

- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\10_core_theorems_full_proofs.md

- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [formal_methods/README](formal_methods/README.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-20（109 天前，建议复审）

### docs\research_notes\10_cross_reference_index.md

- ⚠️ 损坏链接: [04_thinking/MULTI_DIMENSIONAL_CONCEPT_MATRIX](../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 损坏链接: [MATRIX](../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_design_mechanism_rationale.md

- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [trait_system_formalization](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [variance_theory](type_theory/10_variance_theory.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_distributed_architecture_decision_tree.md

- ⚠️ 最后更新: 2026-03-08（93 天前，建议复审）

### docs\research_notes\10_distributed_concept_mindmap.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_distributed_patterns_matrix.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_domain_analysis_framework.md

- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [variance_theory](type_theory/10_variance_theory.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_example.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\10_executable_semantics_roadmap.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_faq.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_faq_comprehensive.md

- ⚠️ 最后更新: 2026-02-24（105 天前，建议复审）

### docs\research_notes\10_feature_template.md

- ⚠️ 损坏链接: [01_formal_composition](software_design_theory/04_compositional_engineering/01_formal_composition.md)
- ⚠️ 损坏链接: [advanced_types](type_theory/10_advanced_types.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_formal_full_model_en_summary.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_formal_full_model_overview.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_formal_language_and_proofs.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_formal_methods_master_index.md

- ⚠️ 最后更新: 2026-02-21（108 天前，建议复审）

### docs\research_notes\10_formal_proof_critical_analysis_and_plan_2026_02.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_formal_proof_system_guide.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_formal_verification_guide.md

- ⚠️ 损坏链接: [formal_methods/README](formal_methods/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-01-26（134 天前，建议复审）

### docs\research_notes\10_getting_started.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-01-26（134 天前，建议复审）

### docs\research_notes\10_glossary.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_hierarchical_mapping_and_summary.md

- ⚠️ 损坏链接: [01_design_patterns_formal](software_design_theory/01_design_patterns_formal/README.md)
- ⚠️ 损坏链接: [02_workflow_safe_complete_models](software_design_theory/02_workflow_safe_complete_models/README.md)
- ⚠️ 损坏链接: [03_execution_models README §执行模型多维对比矩阵](software_design_theory/03_execution_models/README.md#执行模型多维对比矩阵)
- ⚠️ 损坏链接: [03_execution_models](software_design_theory/03_execution_models/README.md)
- ⚠️ 损坏链接: [04_boundary_matrix](software_design_theory/01_design_patterns_formal/04_boundary_matrix.md)
- ⚠️ 损坏链接: [04_compositional_engineering](software_design_theory/04_compositional_engineering/README.md)
- ⚠️ 损坏链接: [04_expressiveness_boundary](software_design_theory/02_workflow_safe_complete_models/04_expressiveness_boundary.md)
- ⚠️ 损坏链接: [05_boundary_system](software_design_theory/05_boundary_system/README.md)
- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 损坏链接: [README §23 模式多维对比矩阵](software_design_theory/01_design_patterns_formal/README.md#23-模式多维对比矩阵)
- ⚠️ 损坏链接: [README §六篇并表](formal_methods/README.md#formal_methods-六篇并表)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [formal_methods/README §六篇并表](formal_methods/README.md#formal_methods-六篇并表)
- ⚠️ 损坏链接: [formal_methods/README](formal_methods/README.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [trait_system_formalization](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [variance_theory](type_theory/10_variance_theory.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-20（109 天前，建议复审）

### docs\research_notes\10_incremental_update_flow.md

- ⚠️ 损坏链接: [formal_methods](formal_methods/README.md)
- ⚠️ 损坏链接: [type_theory](type_theory/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_international_formal_verification_index.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\10_l3_machine_proof_guide.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_language_semantics_expressiveness.md

- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 损坏链接: [advanced_types](type_theory/10_advanced_types.md)
- ⚠️ 损坏链接: [advanced_types](type_theory/10_advanced_types.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [trait_system_formalization](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [variance_theory](type_theory/10_variance_theory.md)
- ⚠️ 损坏链接: [variance_theory](type_theory/10_variance_theory.md)
- ⚠️ 损坏链接: [variance_theory](type_theory/10_variance_theory.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_macros_cheatsheet.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_maintenance_guide.md

- ⚠️ 损坏链接: [.*\](.*)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_practical_applications.md

- ⚠️ 损坏链接: [04_compositional_engineering](software_design_theory/04_compositional_engineering/README.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\10_progress_tracking.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_project_maintenance_guide.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_proof_index.md

- ⚠️ 损坏链接: [02_async](software_design_theory/03_execution_models/02_async.md)
- ⚠️ 损坏链接: [03_concurrent](software_design_theory/03_execution_models/03_concurrent.md)
- ⚠️ 损坏链接: [04_parallel](software_design_theory/03_execution_models/04_parallel.md)
- ⚠️ 损坏链接: [05_distributed](software_design_theory/03_execution_models/05_distributed.md)
- ⚠️ 损坏链接: [证明位置](formal_methods/00_completeness_gaps.md)
- ⚠️ 损坏链接: [证明位置](software_design_theory/03_execution_models/02_async.md)
- ⚠️ 损坏链接: [证明位置](software_design_theory/03_execution_models/02_async.md)
- ⚠️ 损坏链接: [证明位置](software_design_theory/03_execution_models/03_concurrent.md)
- ⚠️ 损坏链接: [证明位置](software_design_theory/03_execution_models/03_concurrent.md)
- ⚠️ 损坏链接: [证明位置](software_design_theory/03_execution_models/04_parallel.md)
- ⚠️ 损坏链接: [证明位置](software_design_theory/03_execution_models/04_parallel.md)
- ⚠️ 损坏链接: [证明位置](software_design_theory/03_execution_models/05_distributed.md)
- ⚠️ 损坏链接: [证明位置](software_design_theory/03_execution_models/05_distributed.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-20（109 天前，建议复审）

### docs\research_notes\10_proof_techniques_mindmap.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_quality_checklist.md

- ⚠️ 损坏链接: [FORMAL_METHODS_COMPLETENESS_CHECKLIST](formal_methods/10_formal_methods_completeness_checklist.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_quick_find.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_quick_reference.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-20（109 天前，建议复审）

### docs\research_notes\10_readme_100_percent_completion.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-20（109 天前，建议复审）

### docs\research_notes\10_research_methodology.md

- ⚠️ 损坏链接: [experiments/README](experiments/README.md)
- ⚠️ 损坏链接: [experiments/README](experiments/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\10_research_notes_organization.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_research_roadmap.md

- ⚠️ 损坏链接: [00_completeness_gaps](formal_methods/00_completeness_gaps.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_resources.md

- ⚠️ 损坏链接: [00_completeness_gaps](formal_methods/00_completeness_gaps.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [coq_skeleton](coq_skeleton/README.md)
- ⚠️ 损坏链接: [experiments/README](experiments/README.md)
- ⚠️ 损坏链接: [formal_methods](formal_methods/README.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [trait_system_formalization](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_rust_191_research_update_2025_11_15.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.91.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\10_rust_192_research_update_2025_12_11.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\10_rust_193_counterexamples_index.md

- ⚠️ 损坏链接: [advanced_types](type_theory/10_advanced_types.md)
- ⚠️ 损坏链接: [advanced_types](type_theory/10_advanced_types.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [formal_methods](formal_methods/README.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [trait_system_formalization](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [trait_system_formalization](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [type_theory](type_theory/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\10_rust_193_feature_matrix.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\10_rust_193_language_features_comprehensive_analysis.md

- ⚠️ 损坏链接: [advanced_types](type_theory/10_advanced_types.md)
- ⚠️ 损坏链接: [advanced_types](type_theory/10_advanced_types.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [trait_system_formalization](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [trait_system_formalization](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [variance_theory](type_theory/10_variance_theory.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-20（109 天前，建议复审）

### docs\research_notes\10_rust_194_195_feature_matrix.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_rust_194_comprehensive_analysis.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_rust_194_comprehensive_semantics_framework.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_rust_194_deep_semantic_analysis.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_rust_194_mind_representations.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_rust_194_research_update.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-03-06（95 天前，建议复审）

### docs\research_notes\10_rust_book_alignment.md

- ⚠️ 损坏链接: [10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [10_ownership_model.md §Def 4.1-4.5](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [10_ownership_model.md](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [10_send_sync_formalization.md](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [10_trait_system_formalization.md](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [10_type_system_foundations.md](type_theory/10_type_system_foundations.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_rust_formal_methods_cheatsheet.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_rustbelt_alignment.md

- ⚠️ 损坏链接: [coq_skeleton](coq_skeleton/README.md)
- ⚠️ 损坏链接: [coq_skeleton](coq_skeleton/README.md)
- ⚠️ 损坏链接: [coq_skeleton](coq_skeleton/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_rustsem_semantics.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-03-10（91 天前，建议复审）

### docs\research_notes\10_safe_decidable_mechanisms_overview.md

- ⚠️ 损坏链接: [06_boundary_analysis](software_design_theory/03_execution_models/06_boundary_analysis.md)
- ⚠️ 损坏链接: [SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN](formal_methods/10_safe_decidable_mechanisms_and_formal_methods_plan.md)
- ⚠️ 损坏链接: [SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN](formal_methods/10_safe_decidable_mechanisms_and_formal_methods_plan.md)
- ⚠️ 损坏链接: [SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN](formal_methods/10_safe_decidable_mechanisms_and_formal_methods_plan.md)
- ⚠️ 损坏链接: [SAFE_DECIDABLE_MECHANISMS_AND_FORMAL_METHODS_PLAN](formal_methods/10_safe_decidable_mechanisms_and_formal_methods_plan.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [formal_methods README §六篇并表](formal_methods/README.md#formal_methods-六篇并表)
- ⚠️ 损坏链接: [formal_methods README](formal_methods/README.md)
- ⚠️ 损坏链接: [formal_methods README](formal_methods/README.md)
- ⚠️ 损坏链接: [formal_methods](formal_methods/README.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [send_sync_formalization](formal_methods/10_send_sync_formalization.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [type_theory](type_theory/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_safe_unsafe_comprehensive_analysis.md

- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_statistics.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_system_integration.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_system_summary.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_task_checklist.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_template.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_theorems_and_proof_strategies.md

- ⚠️ 最后更新: 2026-02-23（106 天前，建议复审）

### docs\research_notes\10_theoretical_and_argumentation_system_architecture.md

- ⚠️ 损坏链接: [software_design_theory](software_design_theory/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_tools_guide.md

- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_tutorial_borrow_checker.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_tutorial_concurrency_models.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_tutorial_ownership_safety.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_tutorial_type_system.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_unified_systematic_framework.md

- ⚠️ 损坏链接: [04_compositional_engineering](software_design_theory/04_compositional_engineering/README.md)
- ⚠️ 损坏链接: [04_expressiveness_boundary](software_design_theory/02_workflow_safe_complete_models/04_expressiveness_boundary.md)
- ⚠️ 损坏链接: [06_boundary_analysis](software_design_theory/03_execution_models/06_boundary_analysis.md)
- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 损坏链接: [advanced_types](type_theory/10_advanced_types.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [async_state_machine](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [borrow_checker_proof](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [builder](software_design_theory/01_design_patterns_formal/01_creational/10_builder.md)
- ⚠️ 损坏链接: [composite](software_design_theory/01_design_patterns_formal/02_structural/10_composite.md)
- ⚠️ 损坏链接: [construction_capability](type_theory/10_construction_capability.md)
- ⚠️ 损坏链接: [construction_capability](type_theory/10_construction_capability.md)
- ⚠️ 损坏链接: [construction_capability](type_theory/10_construction_capability.md)
- ⚠️ 损坏链接: [construction_capability](type_theory/10_construction_capability.md)
- ⚠️ 损坏链接: [memento](software_design_theory/01_design_patterns_formal/03_behavioral/10_memento.md)
- ⚠️ 损坏链接: [observer](software_design_theory/01_design_patterns_formal/03_behavioral/10_observer.md)
- ⚠️ 损坏链接: [ownership_model](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [pin_self_referential](formal_methods/10_pin_self_referential.md)
- ⚠️ 损坏链接: [singleton](software_design_theory/01_design_patterns_formal/01_creational/10_singleton.md)
- ⚠️ 损坏链接: [software_design_theory](software_design_theory/README.md)
- ⚠️ 损坏链接: [trait_system_formalization](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [trait_system_formalization](type_theory/10_trait_system_formalization.md)
- ⚠️ 损坏链接: [type_system_foundations](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [variance_theory](type_theory/10_variance_theory.md)
- ⚠️ 损坏链接: [variance_theory](type_theory/10_variance_theory.md)
- ⚠️ 损坏链接: [variance_theory](type_theory/10_variance_theory.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_user_guide.md

- ⚠️ 损坏链接: [10_async_state_machine.md](formal_methods/10_async_state_machine.md)
- ⚠️ 损坏链接: [10_borrow_checker_proof.md](formal_methods/10_borrow_checker_proof.md)
- ⚠️ 损坏链接: [10_ownership_model.md](formal_methods/10_ownership_model.md)
- ⚠️ 损坏链接: [10_type_system_foundations.md](type_theory/10_type_system_foundations.md)
- ⚠️ 损坏链接: [software_design_theory/01_design_patterns_formal/README.md](software_design_theory/01_design_patterns_formal/README.md)
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\10_verification_tools_matrix.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_visualization_index.md

- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_workflow_concept_mindmap.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\10_writing_guide.md

- ⚠️ 损坏链接: [02_effectiveness_proofs](software_design_theory/04_compositional_engineering/02_effectiveness_proofs.md)
- ⚠️ 损坏链接: [state](software_design_theory/01_design_patterns_formal/03_behavioral/10_state.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\INDEX.md

- ⚠️ 损坏链接: [05_boundary_system 三维边界](software_design_theory/05_boundary_system/README.md)
- ⚠️ 损坏链接: [06_rust_idioms](software_design_theory/06_rust_idioms.md)
- ⚠️ 损坏链接: [07_anti_patterns 反模式](software_design_theory/07_anti_patterns.md)
- ⚠️ 损坏链接: [07_anti_patterns](software_design_theory/07_anti_patterns.md)
- ⚠️ 损坏链接: [23 安全 / 43 完全模型](software_design_theory/02_workflow_safe_complete_models/README.md)
- ⚠️ 损坏链接: [执行模型](software_design_theory/03_execution_models/README.md)
- ⚠️ 损坏链接: [组合工程](software_design_theory/04_compositional_engineering/README.md)
- ⚠️ 损坏链接: [设计模式形式化](software_design_theory/01_design_patterns_formal/README.md)
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\experiments\10_compiler_optimizations.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\experiments\10_concurrency_performance.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\experiments\10_macro_expansion_performance.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\experiments\10_memory_analysis.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\experiments\10_performance_benchmarks.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\experiments\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\00_completeness_gaps.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-20（109 天前，建议复审）

### docs\research_notes\formal_methods\10_async_concept_mindmap.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_async_runtime_decision_tree.md

- ⚠️ 最后更新: 2026-02-24（105 天前，建议复审）

### docs\research_notes\formal_methods\10_async_state_machine.md

- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_axiomatic_semantics.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_borrow_checker_proof.md

- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-27（102 天前，建议复审）

### docs\research_notes\formal_methods\10_case_studies.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_concurrency_concept_mindmap.md

- ⚠️ 最后更新: 2026-02-24（105 天前，建议复审）

### docs\research_notes\formal_methods\10_concurrency_safety_matrix.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_coq_formalization_guide.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_coq_formalization_matrix.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_design_pattern_concept_mindmap.md

- ⚠️ 最后更新: 2026-02-26（103 天前，建议复审）

### docs\research_notes\formal_methods\10_design_pattern_selection_decision_tree.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_error_handling_mindmap.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_error_type_selection_decision_tree.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_five_dimensional_concept_matrix.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_formal_foundations_index.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_formal_methods_comparison.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_formal_methods_completeness_checklist.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-20（109 天前，建议复审）

### docs\research_notes\formal_methods\10_implementation_progress_matrix.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_learning_progression_matrix.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_logical_foundations.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_macro_system_mindmap.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_memory_model_mindmap.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_operational_semantics.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_ownership_model.md

- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\formal_methods\10_ownership_transfer_decision_tree.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_paradigm_comparison_matrix.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_pin_self_referential.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_proof_completion_matrix.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-27（102 天前，建议复审）

### docs\research_notes\formal_methods\10_proof_strategies.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_proof_trees_additional.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_proof_trees_enhanced.md

- ⚠️ 最后更新: 2026-03-05（96 天前，建议复审）

### docs\research_notes\formal_methods\10_proof_trees_visualization.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_risk_assessment_matrix.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_safe_decidable_mechanisms_and_formal_methods_plan.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_send_sync_formalization.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_separation_logic.md

- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_variance_concept_mindmap.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\10_workflow_engines_matrix.md

- ⚠️ 旧版本声明: '> **版本**: Rust 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\formal_methods\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-20（109 天前，建议复审）

### docs\research_notes\formal_methods\lifetime_formalization.md

- ⚠️ 损坏链接: [MULTI_DIMENSIONAL_CONCEPT_MATRIX](../../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-27（102 天前，建议复审）

### docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\10_singleton.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\01_design_patterns_formal\01_creational\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\10_adapter.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\10_bridge.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\10_composite.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\10_decorator.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\10_facade.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\10_flyweight.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\10_proxy.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\01_design_patterns_formal\02_structural\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\10_chain_of_responsibility.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\01_design_patterns_formal\03_behavioral\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\01_design_patterns_formal\04_boundary_matrix.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\01_design_patterns_formal\README.md

- ⚠️ 损坏链接: [Abstract Factory](01_creational/10_abstract_factory.md)
- ⚠️ 损坏链接: [Adapter](02_structural/10_adapter.md)
- ⚠️ 损坏链接: [Bridge](02_structural/10_bridge.md)
- ⚠️ 损坏链接: [Builder](01_creational/10_builder.md)
- ⚠️ 损坏链接: [Chain](03_behavioral/10_chain_of_responsibility.md)
- ⚠️ 损坏链接: [Command](03_behavioral/10_command.md)
- ⚠️ 损坏链接: [Composite](02_structural/10_composite.md)
- ⚠️ 损坏链接: [Decorator](02_structural/10_decorator.md)
- ⚠️ 损坏链接: [Facade](02_structural/10_facade.md)
- ⚠️ 损坏链接: [Factory Method](01_creational/10_factory_method.md)
- ⚠️ 损坏链接: [Flyweight](02_structural/10_flyweight.md)
- ⚠️ 损坏链接: [Interpreter](03_behavioral/10_interpreter.md)
- ⚠️ 损坏链接: [Iterator](03_behavioral/10_iterator.md)
- ⚠️ 损坏链接: [Mediator](03_behavioral/10_mediator.md)
- ⚠️ 损坏链接: [Memento](03_behavioral/10_memento.md)
- ⚠️ 损坏链接: [Observer](03_behavioral/10_observer.md)
- ⚠️ 损坏链接: [Prototype](01_creational/10_prototype.md)
- ⚠️ 损坏链接: [Proxy](02_structural/10_proxy.md)
- ⚠️ 损坏链接: [Singleton](01_creational/10_singleton.md)
- ⚠️ 损坏链接: [State](03_behavioral/10_state.md)
- ⚠️ 损坏链接: [Strategy](03_behavioral/10_strategy.md)
- ⚠️ 损坏链接: [Template Method](03_behavioral/10_template_method.md)
- ⚠️ 损坏链接: [Visitor](03_behavioral/10_visitor.md)
- ⚠️ 损坏链接: [abstract_factory](01_creational/10_abstract_factory.md)
- ⚠️ 损坏链接: [adapter](02_structural/10_adapter.md)
- ⚠️ 损坏链接: [bridge](02_structural/10_bridge.md)
- ⚠️ 损坏链接: [builder](01_creational/10_builder.md)
- ⚠️ 损坏链接: [builder](01_creational/10_builder.md)
- ⚠️ 损坏链接: [chain_of_responsibility](03_behavioral/10_chain_of_responsibility.md)
- ⚠️ 损坏链接: [chain_of_responsibility](03_behavioral/10_chain_of_responsibility.md)
- ⚠️ 损坏链接: [command](03_behavioral/10_command.md)
- ⚠️ 损坏链接: [command](03_behavioral/10_command.md)
- ⚠️ 损坏链接: [command](03_behavioral/10_command.md)
- ⚠️ 损坏链接: [composite](02_structural/10_composite.md)
- ⚠️ 损坏链接: [composite](02_structural/10_composite.md)
- ⚠️ 损坏链接: [decorator](02_structural/10_decorator.md)
- ⚠️ 损坏链接: [decorator](02_structural/10_decorator.md)
- ⚠️ 损坏链接: [facade](02_structural/10_facade.md)
- ⚠️ 损坏链接: [factory_method](01_creational/10_factory_method.md)
- ⚠️ 损坏链接: [factory_method](01_creational/10_factory_method.md)
- ⚠️ 损坏链接: [flyweight](02_structural/10_flyweight.md)
- ⚠️ 损坏链接: [interpreter](03_behavioral/10_interpreter.md)
- ⚠️ 损坏链接: [iterator](03_behavioral/10_iterator.md)
- ⚠️ 损坏链接: [mediator](03_behavioral/10_mediator.md)
- ⚠️ 损坏链接: [memento](03_behavioral/10_memento.md)
- ⚠️ 损坏链接: [observer](03_behavioral/10_observer.md)
- ⚠️ 损坏链接: [observer](03_behavioral/10_observer.md)
- ⚠️ 损坏链接: [prototype](01_creational/10_prototype.md)
- ⚠️ 损坏链接: [proxy](02_structural/10_proxy.md)
- ⚠️ 损坏链接: [singleton](01_creational/10_singleton.md)
- ⚠️ 损坏链接: [state](03_behavioral/10_state.md)
- ⚠️ 损坏链接: [strategy](03_behavioral/10_strategy.md)
- ⚠️ 损坏链接: [strategy](03_behavioral/10_strategy.md)
- ⚠️ 损坏链接: [template_method](03_behavioral/10_template_method.md)
- ⚠️ 损坏链接: [visitor](03_behavioral/10_visitor.md)
- ⚠️ 损坏链接: [visitor](03_behavioral/10_visitor.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\02_workflow_safe_complete_models\02_complete_43_catalog.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\02_workflow_safe_complete_models\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\03_execution_models\01_synchronous.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\03_execution_models\02_async.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\03_execution_models\03_concurrent.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\03_execution_models\04_parallel.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\03_execution_models\05_distributed.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-27（102 天前，建议复审）

### docs\research_notes\software_design_theory\03_execution_models\06_boundary_analysis.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\03_execution_models\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\04_compositional_engineering\01_formal_composition.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\04_compositional_engineering\02_effectiveness_proofs.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\04_compositional_engineering\03_integration_theory.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\04_compositional_engineering\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\05_boundary_system\10_expressive_inexpressive_matrix.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\05_boundary_system\10_safe_unsafe_matrix.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\05_boundary_system\10_supported_unsupported_matrix.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\05_boundary_system\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\06_rust_idioms.md

- ⚠️ 损坏链接: [01_design_patterns_formal](01_design_patterns_formal/README.md)
- ⚠️ 损坏链接: [02_complete_43_catalog](02_workflow_safe_complete_models/02_complete_43_catalog.md)
- ⚠️ 损坏链接: [Builder](01_design_patterns_formal/01_creational/10_builder.md)
- ⚠️ 损坏链接: [builder](01_design_patterns_formal/01_creational/10_builder.md)
- ⚠️ 损坏链接: [builder](01_design_patterns_formal/01_creational/10_builder.md)
- ⚠️ 损坏链接: [state](01_design_patterns_formal/03_behavioral/10_state.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\07_anti_patterns.md

- ⚠️ 损坏链接: [01_design_patterns_formal](01_design_patterns_formal/README.md)
- ⚠️ 损坏链接: [safe_unsafe_matrix](05_boundary_system/10_safe_unsafe_matrix.md)
- ⚠️ 损坏链接: [safe_unsafe_matrix](05_boundary_system/10_safe_unsafe_matrix.md)
- ⚠️ 损坏链接: [safe_unsafe_matrix](05_boundary_system/10_safe_unsafe_matrix.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\07_crate_architectures\05_bevy_architecture.md

- ⚠️ 旧版本声明: '**对应 Rust 版本**: 1.85' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\07_crate_architectures\06_tokio_architecture.md

- ⚠️ 旧版本声明: '**对应 Rust 版本**: 1.85' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\07_crate_architectures\18_tracing_architecture.md

- ⚠️ 旧版本声明: '**对应 Rust 版本**: 1.85' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\07_crate_architectures\19_crossbeam_architecture.md

- ⚠️ 损坏链接: [形式化操作语义](../../../../concept/04_formal/09_operational_semantics.md)
- ⚠️ 旧版本声明: '**对应 Rust 版本**: 1.85' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\07_crate_architectures\20_ratatui_architecture.md

- ⚠️ 旧版本声明: '**对应 Rust 版本**: 1.85' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\07_crate_architectures\21_mio_architecture.md

- ⚠️ 旧版本声明: '**对应 Rust 版本**: 1.85' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\10_00_master_index.md

- ⚠️ 损坏链接: [01_design_patterns_formal/README](01_design_patterns_formal/README.md)
- ⚠️ 损坏链接: [01_design_patterns_formal](01_design_patterns_formal/README.md)
- ⚠️ 损坏链接: [02_workflow_safe_complete_models/README](02_workflow_safe_complete_models/README.md)
- ⚠️ 损坏链接: [03_execution_models/README](03_execution_models/README.md)
- ⚠️ 损坏链接: [03_execution_models](03_execution_models/README.md)
- ⚠️ 损坏链接: [04_compositional_engineering/README](04_compositional_engineering/README.md)
- ⚠️ 损坏链接: [04_compositional_engineering](04_compositional_engineering/README.md)
- ⚠️ 损坏链接: [05_boundary_system/README](05_boundary_system/README.md)
- ⚠️ 损坏链接: [05_boundary_system](05_boundary_system/README.md)
- ⚠️ 损坏链接: [expressive_inexpressive_matrix](05_boundary_system/10_expressive_inexpressive_matrix.md)
- ⚠️ 损坏链接: [safe_unsafe_matrix](05_boundary_system/10_safe_unsafe_matrix.md)
- ⚠️ 损坏链接: [safe_unsafe_matrix](05_boundary_system/10_safe_unsafe_matrix.md)
- ⚠️ 损坏链接: [supported_unsupported_matrix](05_boundary_system/10_supported_unsupported_matrix.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\software_design_theory\10_comprehensive_argumentation_gap_analysis_and_plan.md

- ⚠️ 损坏链接: [01_design_patterns_formal README](01_design_patterns_formal/README.md#反例错误码映射d14)
- ⚠️ 损坏链接: [01_design_patterns_formal README](01_design_patterns_formal/README.md#反例错误码映射d14)
- ⚠️ 损坏链接: [01_design_patterns_formal](01_design_patterns_formal/README.md)
- ⚠️ 损坏链接: [02_effectiveness_proofs](04_compositional_engineering/02_effectiveness_proofs.md#定理-ce-pat1模式组合-ce-保持)
- ⚠️ 损坏链接: [02_effectiveness_proofs](04_compositional_engineering/02_effectiveness_proofs.md#定理-ce-pat1模式组合-ce-保持)
- ⚠️ 损坏链接: [02_workflow README § 23/43 与工作流关系](02_workflow_safe_complete_models/README.md#2343-与工作流关系d34)
- ⚠️ 损坏链接: [02_workflow README](02_workflow_safe_complete_models/README.md#2343-与工作流关系d34)
- ⚠️ 损坏链接: [02_workflow_safe_complete_models](02_workflow_safe_complete_models/README.md)
- ⚠️ 损坏链接: [03_execution_models](03_execution_models/README.md)
- ⚠️ 损坏链接: [04_boundary_matrix](01_design_patterns_formal/04_boundary_matrix.md#模式组合约束-dagd15)
- ⚠️ 损坏链接: [04_boundary_matrix](01_design_patterns_formal/04_boundary_matrix.md#模式组合约束-dagd15)
- ⚠️ 损坏链接: [04_compositional_engineering](04_compositional_engineering/README.md)
- ⚠️ 损坏链接: [04_expressiveness_boundary § 工作流形式化](02_workflow_safe_complete_models/04_expressiveness_boundary.md#工作流形式化与引擎表达力d31d33)
- ⚠️ 损坏链接: [04_expressiveness_boundary](02_workflow_safe_complete_models/04_expressiveness_boundary.md#工作流形式化与引擎表达力d31d33)
- ⚠️ 损坏链接: [04_expressiveness_boundary](02_workflow_safe_complete_models/04_expressiveness_boundary.md#等价近似不可表达判定规则)
- ⚠️ 损坏链接: [04_expressiveness_boundary](02_workflow_safe_complete_models/04_expressiveness_boundary.md)
- ⚠️ 损坏链接: [05_distributed § CAP/BASE](03_execution_models/05_distributed.md#capbase-与-rust-衔接d23)
- ⚠️ 损坏链接: [05_distributed § 分布式专用模式形式化](03_execution_models/05_distributed.md#分布式专用模式形式化d21-扩展)
- ⚠️ 损坏链接: [05_distributed](03_execution_models/05_distributed.md#分布式专用模式形式化d21-扩展)
- ⚠️ 损坏链接: [05_distributed](03_execution_models/05_distributed.md)
- ⚠️ 损坏链接: [EB-DET1](02_workflow_safe_complete_models/04_expressiveness_boundary.md#等价近似不可表达判定规则)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\software_design_theory\README.md

- ⚠️ 损坏链接: [01_design_patterns_formal](01_design_patterns_formal/README.md)
- ⚠️ 损坏链接: [01_design_patterns_formal](01_design_patterns_formal/README.md)
- ⚠️ 损坏链接: [01_design_patterns_formal](01_design_patterns_formal/README.md)
- ⚠️ 损坏链接: [01_design_patterns_formal](01_design_patterns_formal/README.md)
- ⚠️ 损坏链接: [01_safe_23 常见陷阱](02_workflow_safe_complete_models/02_complete_43_catalog.md)
- ⚠️ 损坏链接: [01_safe_23_catalog](02_workflow_safe_complete_models/02_complete_43_catalog.md)
- ⚠️ 损坏链接: [01_safe_23_catalog](02_workflow_safe_complete_models/02_complete_43_catalog.md)
- ⚠️ 损坏链接: [02_effectiveness_proofs](04_compositional_engineering/02_effectiveness_proofs.md)
- ⚠️ 损坏链接: [02_workflow_safe_complete_models](02_workflow_safe_complete_models/README.md)
- ⚠️ 损坏链接: [02_workflow_safe_complete_models](02_workflow_safe_complete_models/README.md)
- ⚠️ 损坏链接: [03_execution_models README](03_execution_models/README.md)
- ⚠️ 损坏链接: [03_execution_models 可运行示例](03_execution_models/README.md#可运行示例层次推进)
- ⚠️ 损坏链接: [03_execution_models](03_execution_models/README.md)
- ⚠️ 损坏链接: [03_execution_models](03_execution_models/README.md)
- ⚠️ 损坏链接: [03_execution_models](03_execution_models/README.md)
- ⚠️ 损坏链接: [03_integration_theory](04_compositional_engineering/03_integration_theory.md)
- ⚠️ 损坏链接: [04_compositional_engineering](04_compositional_engineering/README.md)
- ⚠️ 损坏链接: [04_compositional_engineering](04_compositional_engineering/README.md)
- ⚠️ 损坏链接: [04_compositional_engineering](04_compositional_engineering/README.md)
- ⚠️ 损坏链接: [05_boundary_system](05_boundary_system/README.md)
- ⚠️ 损坏链接: [05_boundary_system](05_boundary_system/README.md)
- ⚠️ 损坏链接: [05_boundary_system](05_boundary_system/README.md)
- ⚠️ 损坏链接: [06_boundary_analysis](03_execution_models/06_boundary_analysis.md)
- ⚠️ 损坏链接: [06_boundary_analysis](03_execution_models/06_boundary_analysis.md)
- ⚠️ 损坏链接: [创建型模式对比](01_design_patterns_formal/README.md#创建型模式对比)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\research_notes\type_theory\10_advanced_types.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\type_theory\10_construction_capability.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\type_theory\10_lifetime_formalization.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\type_theory\10_trait_system_formalization.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-03-05（96 天前，建议复审）

### docs\research_notes\type_theory\10_type_system_foundations.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\research_notes\type_theory\10_variance_theory.md

- ⚠️ 损坏链接: [形式化工程系统 - 型变](../../rust-formal-engineering-system/01_theoretical_foundations/01_type_system/06_variance.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+

### docs\research_notes\type_theory\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\00_master_index.md

- ⚠️ 损坏链接: [docs/05_performance_testing_report.md](../05_guides/05_performance_testing_report.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\01_theoretical_foundations\01_type_system\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\01_theoretical_foundations\02_memory_safety\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\01_theoretical_foundations\02_ownership_system\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\01_theoretical_foundations\03_ownership_borrowing\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\01_theoretical_foundations\05_trait_system\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\01_theoretical_foundations\06_lifetime_management\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\01_theoretical_foundations\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\02_practical_applications\README.md

- ⚠️ 损坏链接: [memory/](memory/README.md)
- ⚠️ 损坏链接: [performance/](performance/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\02_practical_applications\memory\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\02_practical_applications\performance\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\02_programming_paradigms\01_synchronous\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\02_programming_paradigms\02_async\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\02_programming_paradigms\09_actor_model\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\02_programming_paradigms\11_benchmark_minimal_guide.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\02_programming_paradigms\README.md

- ⚠️ 损坏链接: [01_synchronous/](01_synchronous/README.md)
- ⚠️ 损坏链接: [02_async/](02_async/README.md)
- ⚠️ 损坏链接: [09_actor_model/](09_actor_model/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\03_compiler_theory\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\03_design_patterns\04_concurrent\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\03_design_patterns\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\05_software_engineering\07_testing\README.md

- ⚠️ 损坏链接: [../../../05_guides/05_performance_testing_report.md](../../../05_guides/05_performance_testing_report.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\05_software_engineering\README.md

- ⚠️ 损坏链接: [07_testing/](07_testing/README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\06_toolchain_ecosystem\01_compiler\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\06_toolchain_ecosystem\02_package_manager\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\06_toolchain_ecosystem\03_build_tools\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\06_toolchain_ecosystem\README.md

- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\09_research_agenda\04_research_methods\README.md

- ⚠️ 损坏链接: [返回研究议程索引](../README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.93.1' → 建议更新为 1.96.0+
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\10_quality_assurance\README.md

- ⚠️ 损坏链接: [**05_performance_testing_report.md**](../../05_guides/05_performance_testing_report.md)
- ⚠️ 损坏链接: [PERFORMANCE_TESTING_REPORT](../../05_guides/05_performance_testing_report.md)
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-formal-engineering-system\README.md

- ⚠️ 损坏链接: [多维概念矩阵](../04_thinking/04_multi_dimensional_concept_matrix.md)
- ⚠️ 最后更新: 2026-02-28（101 天前，建议复审）

### docs\rust-ownership-decidability\00-foundations\00-01-linear-logic-deep.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\00-foundations\00-01-linear-logic.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\00-foundations\00-02-affine-types.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\00-foundations\00-03-separation-logic-deep.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\00-foundations\00-03-separation-logic.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\00-foundations\00-04-theory-connections.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\01-core-concepts\01-01-ownership-rules-deep.md

- ⚠️ 损坏链接: [detailed-concepts/ownership-deep-dive.md](detailed-concepts/ownership-deep-dive.md)
- ⚠️ 最后更新: 2026-03-06（95 天前，建议复审）

### docs\rust-ownership-decidability\01-core-concepts\01-01-ownership-rules.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\01-core-concepts\01-02-borrowing-system-deep.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\01-core-concepts\01-02-borrowing-system.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\01-core-concepts\01-03-lifetimes-deep.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\01-core-concepts\01-03-lifetimes.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\01-core-concepts\01-04-runtime-vs-compile-time.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\01-core-concepts\01-05-interior-mutability-deep.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\01-core-concepts\01-05-interior-mutability.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\01-core-concepts\detailed-concepts\polonius-borrow-checker.md

- ⚠️ 损坏链接: [Parent README](../README.md)

### docs\rust-ownership-decidability\01-core-concepts\detailed-concepts\trait-system.md

- ⚠️ 损坏链接: [Parent README](../README.md)

### docs\rust-ownership-decidability\01-core-concepts\ownership-counterexamples.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\01-core-concepts\short-concepts\borrowing-concept-card.md

- ⚠️ 损坏链接: [Parent README](../README.md)

### docs\rust-ownership-decidability\01-core-concepts\short-concepts\lifetime-concept-card.md

- ⚠️ 损坏链接: [Parent README](../README.md)

### docs\rust-ownership-decidability\01-core-concepts\short-concepts\ownership-concept-card.md

- ⚠️ 损坏链接: [Parent README](../README.md)

### docs\rust-ownership-decidability\03-verification-tools\03-01-verification-overview-deep.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\03-verification-tools\03-01-verification-overview.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\03-verification-tools\03-02-creusot-deep-dive.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\03-verification-tools\03-03-miri-deep-dive.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\03-verification-tools\03-06-verus-guide.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\03-verification-tools\03-07-refinedrust-deep-dive.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\03-verification-tools\03-08-gillian-rust.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\04-decidability-analysis\04-01-type-inference.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\04-decidability-analysis\04-02-borrow-checking.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\05-comparative-study\05-01-linear-vs-affine.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\05-comparative-study\05-03-rust-vs-go.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [T Number](values []T)
- ⚠️ 损坏链接: [T comparable](a, b T)

### docs\rust-ownership-decidability\05-comparative-study\05-04-rust-vs-java.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\05-comparative-study\05-05-rust-vs-swift.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\07-references\README.md

- ⚠️ 最后更新: 2026-03-04（97 天前，建议复审）

### docs\rust-ownership-decidability\07-references\academic-papers.md

- ⚠️ 最后更新: 2026-03-04（97 天前，建议复审）

### docs\rust-ownership-decidability\07-references\books-resources.md

- ⚠️ 最后更新: 2026-03-04（97 天前，建议复审）

### docs\rust-ownership-decidability\07-references\online-courses.md

- ⚠️ 最后更新: 2026-03-04（97 天前，建议复审）

### docs\rust-ownership-decidability\07-references\tools-libraries.md

- ⚠️ 最后更新: 2026-03-04（97 天前，建议复审）

### docs\rust-ownership-decidability\08-advanced-topics\08-05-rust-195-features-formal.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\08-advanced-topics\README.md

- ⚠️ 损坏链接: [所有权可判定性总览](../README.md)

### docs\rust-ownership-decidability\10-research-frontiers\10-01-future-directions.md

- ⚠️ 最后更新: 2026-03-04（97 天前，建议复审）

### docs\rust-ownership-decidability\10-research-frontiers\10-02-type-system-extensions.md

- ⚠️ 最后更新: 2026-03-04（97 天前，建议复审）

### docs\rust-ownership-decidability\10-research-frontiers\10-03-verification-advancements.md

- ⚠️ 最后更新: 2026-03-04（97 天前，建议复审）

### docs\rust-ownership-decidability\10-research-frontiers\10-04-ownership-variations.md

- ⚠️ 最后更新: 2026-03-04（97 天前，建议复审）

### docs\rust-ownership-decidability\10-research-frontiers\10-05-ai-integration.md

- ⚠️ 最后更新: 2026-03-04（97 天前，建议复审）

### docs\rust-ownership-decidability\10-research-frontiers\10-06-formal-verification.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\10-research-frontiers\README.md

- ⚠️ 最后更新: 2026-03-04（97 天前，建议复审）

### docs\rust-ownership-decidability\10-research-frontiers\rust-1.93-features-analysis.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\100_PERCENT_COMPLETION_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\11-design-patterns\11-01-rust-design-patterns.md

- ⚠️ 损坏链接: [Parent README](../README.md)

### docs\rust-ownership-decidability\11-design-patterns\11-02-idiomatic-patterns.md

- ⚠️ 损坏链接: [Parent README](../README.md)

### docs\rust-ownership-decidability\11-design-patterns\11-03-type-state-pattern.md

- ⚠️ 损坏链接: [Parent README](../README.md)

### docs\rust-ownership-decidability\11-design-patterns\behavioral\command.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [behavioral 目录](./README.md)

### docs\rust-ownership-decidability\11-design-patterns\behavioral\observer.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [behavioral 目录](./README.md)

### docs\rust-ownership-decidability\11-design-patterns\behavioral\strategy.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [behavioral 目录](./README.md)

### docs\rust-ownership-decidability\11-design-patterns\creational\builder.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [creational 目录](./README.md)

### docs\rust-ownership-decidability\11-design-patterns\creational\factory.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [creational 目录](./README.md)

### docs\rust-ownership-decidability\11-design-patterns\rust-specific\newtype.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-specific 目录](./README.md)

### docs\rust-ownership-decidability\11-design-patterns\rust-specific\raii-guard.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-specific 目录](./README.md)

### docs\rust-ownership-decidability\11-design-patterns\structural\adapter.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [structural 目录](./README.md)

### docs\rust-ownership-decidability\11-design-patterns\structural\decorator.md

- ⚠️ 损坏链接: [B_behavior](ConcreteDecoratorA[A](ConcreteComponent)
- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [structural 目录](./README.md)
- ⚠️ 损坏链接: [{}]({})
- ⚠️ 损坏链接: [{}]({})

### docs\rust-ownership-decidability\11-design-patterns\structural\proxy.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [structural 目录](./README.md)

### docs\rust-ownership-decidability\13-architecture-patterns\clean-architecture.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\14-distributed-systems\13-01-distributed-patterns.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\14-distributed-systems\consensus-patterns.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\15-application-domains\data-engineering.md

- ⚠️ 损坏链接: [Parent README](../README.md)

### docs\rust-ownership-decidability\15-application-domains\systems-programming.md

- ⚠️ 损坏链接: [Parent README](../README.md)

### docs\rust-ownership-decidability\15-application-domains\web-development.md

- ⚠️ 损坏链接: [Parent README](../README.md)

### docs\rust-ownership-decidability\16-program-semantics\00-foundations\00a-lambda-calculus.md

- ⚠️ 最后更新: 2026-03-08（93 天前，建议复审）

### docs\rust-ownership-decidability\16-program-semantics\00-foundations\00b-type-theory-basics.md

- ⚠️ 最后更新: 2026-03-08（93 天前，建议复审）

### docs\rust-ownership-decidability\16-program-semantics\00-foundations\00c-operational-semantics.md

- ⚠️ 最后更新: 2026-03-08（93 天前，建议复审）

### docs\rust-ownership-decidability\16-program-semantics\09-workflow-ownership-analysis.md

- ⚠️ 损坏链接: [形式化操作语义](../../../concept/04_formal/09_operational_semantics.md)

### docs\rust-ownership-decidability\16-program-semantics\COMPLETION_STATUS_2026_03_08.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\16-program-semantics\COMPREHENSIVE_ANALYSIS_AND_ROADMAP.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\16-program-semantics\README.md

- ⚠️ 最后更新: 2026-03-07（94 天前，建议复审）

### docs\rust-ownership-decidability\16-program-semantics\TOPIC_COVERAGE_MATRIX.md

- ⚠️ 最后更新: 2026-03-07（94 天前，建议复审）

### docs\rust-ownership-decidability\16-program-semantics\rust-194-features\06-array-windows-semantics.md

- ⚠️ 旧版本声明: '> **稳定版本**: Rust 1.94' → 建议更新为 1.96.0+

### docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\04-exclusive-choice.md

- ⚠️ 最后更新: 2026-03-07（94 天前，建议复审）

### docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\05-simple-merge.md

- ⚠️ 最后更新: 2026-03-07（94 天前，建议复审）

### docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\06-multi-choice.md

- ⚠️ 最后更新: 2026-03-07（94 天前，建议复审）

### docs\rust-ownership-decidability\16-program-semantics\workflow-patterns\08-multi-merge.md

- ⚠️ 损坏链接: [i](Branch(i)

### docs\rust-ownership-decidability\AUDIT_REPORTS_INDEX.md

- ⚠️ 损坏链接: [AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md](./AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md)
- ⚠️ 损坏链接: [AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md](./AUTHORITY_ALIGNMENT_GAP_ANALYSIS.md)
- ⚠️ 损坏链接: [COMPLETION_ROADMAP_2026_Q1.md](./COMPLETION_ROADMAP_2026_Q1.md)
- ⚠️ 损坏链接: [COMPLETION_ROADMAP_2026_Q1.md](./COMPLETION_ROADMAP_2026_Q1.md)
- ⚠️ 损坏链接: [COMPLETION_ROADMAP_2026_Q1.md](./COMPLETION_ROADMAP_2026_Q1.md)
- ⚠️ 损坏链接: [COMPLETION_ROADMAP_2026_Q1.md](./COMPLETION_ROADMAP_2026_Q1.md)
- ⚠️ 损坏链接: [progress/2026-03-07_DESIGN_PATTERNS_COMPLETION_REPORT.md](progress/2026-03-07_DESIGN_PATTERNS_COMPLETION_REPORT.md)
- ⚠️ 损坏链接: [progress/](progress/README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\BATCH_4_COMPLETION_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\COMPARATIVE_ANALYSIS.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\COMPILATION_VERIFICATION_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\COMPLETE_KNOWLEDGE_MATRIX.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\COMPLETION_100_PERCENT_SUMMARY.md

- ⚠️ 损坏链接: [DOCUMENT_INDEX_MASTER.md](./DOCUMENT_INDEX_MASTER.md)
- ⚠️ 损坏链接: [README.md](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\COMPREHENSIVE_COMPLETION_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\COMPREHENSIVE_FAQ.md

- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)
- ⚠️ 损坏链接: [形式化理论](formal-foundations/README.md)
- ⚠️ 损坏链接: [案例分析](case-studies/README.md)
- ⚠️ 损坏链接: [高级实践工作坊](exercises/ADVANCED_OWNERSHIP_WORKSHOP.md)

### docs\rust-ownership-decidability\COMPREHENSIVE_KNOWLEDGE_SYNTHESIS.md

- ⚠️ 损坏链接: [MASTER_INDEX_AUTO.md](./MASTER_INDEX_AUTO.md)
- ⚠️ 损坏链接: [README.md](./README.md)
- ⚠️ 损坏链接: [case-studies/MODERN_CRATES_INDEX.md](case-studies/MODERN_CRATES_INDEX.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\CONCEPT_MAP.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\CONTENT_ASSOCIATION_ANALYSIS.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\CONTENT_TEMPLATE_L2.md

- ⚠️ 损坏链接: [所有权可判定性总览](./README.md)
- ⚠️ 旧版本声明: '**Rust 版本**: 1.94.0' → 建议更新为 1.96.0+
- ⚠️ 旧版本声明: '> **Rust 版本**: 1.94.0' → 建议更新为 1.96.0+

### docs\rust-ownership-decidability\CONTINUOUS_IMPROVEMENT_ACTION_PLAN.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\CROSS_REFERENCE_VERIFICATION_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [formal-foundations/models/](formal-foun... |
| MASTER_INDEX_AUTO.md | `formal-foundations/semantics/` | 54 | \| Semantics \| [formal-foundations/semantics/](formal-found... |
| MASTER_INDEX_AUTO.md | `formal-foundations/proofs/` | 55 | \| Proofs \| [formal-foundations/proofs/](formal-foundations... |
| MASTER_INDEX_AUTO.md | `coq-formalization/` | 56 | \| Coq Formalization \| [coq-formalization/](coq-formalizati... |
| MASTER_INDEX_AUTO.md | `formal-foundations/models/ownership-types.md` | 73 | - **Theory**: [ownership-types.md](formal-foundations/models... |
| MASTER_INDEX_AUTO.md | `formal-foundations/models/borrow-semantics.md` | 79 | - **Theory**: [borrow-semantics.md](formal-foundations/model... |
| MASTER_INDEX_AUTO.md | `formal-foundations/models/lifetime-logic.md` | 85 | - **Theory**: [lifetime-logic.md](formal-foundations/models/... |
| README.md | `CROSS_REFERENCE_VERIFICATION_REPORT.md` | 56 | \| `CROSS_REFERENCE_VERIFICATION_REPORT.md`... |
| README.md | `formal-foundations/README.md` | 65 | \| 形式化理论 \| 形式化基础 (待补充)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\CROSS_REFERENCE_VERIFICATION_SUMMARY.md

- ⚠️ 损坏链接: [MASTER_INDEX_AUTO.md](./MASTER_INDEX_AUTO.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\DESIGN_RATIONALE.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\ERROR_DIAGNOSTICS_GUIDE.md

- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)
- ⚠️ 损坏链接: [案例分析](case-studies/README.md)

### docs\rust-ownership-decidability\EXECUTIVE_SUMMARY_AND_RECOMMENDATIONS.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\FAQ_COMPREHENSIVE.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\FINAL_100_PERCENT_COMPLETION_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\FINAL_ASSOCIATION_COMPLETION_REPORT.md

- ⚠️ 损坏链接: [10_final_100_percent_completion_certification.md](FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\FINAL_COMPLETION_CERTIFICATE.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\FINAL_COMPLETION_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\FINAL_DOCUMENTATION.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\FINAL_EXECUTIVE_SUMMARY.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\FINAL_MASTER_INDEX.md

- ⚠️ 损坏链接: [README.md](./README.md)
- ⚠️ 损坏链接: [coq-formalization/README.md](coq-formalization/README.md)
- ⚠️ 损坏链接: [coq-formalization/README.md](coq-formalization/README.md)
- ⚠️ 损坏链接: [meta-model/01_abstract_syntax.md](meta-model/01_abstract_syntax.md)
- ⚠️ 损坏链接: [meta-model/02_semantic_domains.md](meta-model/02_semantic_domains.md)
- ⚠️ 损坏链接: [meta-model/03_judgments.md](meta-model/03_judgments.md)
- ⚠️ 损坏链接: [progress/10_progress_tracking.md](progress/PROGRESS_TRACKING.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)
- ⚠️ 损坏链接: [theorems/decidability_theorems.md](theorems/decidability_theorems.md)

### docs\rust-ownership-decidability\FINAL_ULTIMATE_COMPLETION_REPORT.md

- ⚠️ 损坏链接: [DOCUMENT_INDEX_MASTER.md](./DOCUMENT_INDEX_MASTER.md)
- ⚠️ 损坏链接: [ULTIMATE_COMPREHENSIVE_GUIDE.md](./ULTIMATE_COMPREHENSIVE_GUIDE.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)
- ⚠️ 最后更新: 2026-03-09（92 天前，建议复审）

### docs\rust-ownership-decidability\FINAL_VERIFICATION_100_PERCENT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\FOUNDATIONS_TO_PRACTICE_BRIDGE.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\FRAMEWORK_ANALYSIS_AND_GAP_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\FRAMEWORK_COMPLETION_SUMMARY.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\HISTORICAL_EVOLUTION.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\HORIZONTAL_CONNECTIONS.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\INITIAL_PHASE_COMPLETION_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\INTERACTIVE_LEARNING_GUIDE.md

- ⚠️ 损坏链接: [Coq形式化](./coq-formalization/README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)
- ⚠️ 损坏链接: [高级实践工作坊](exercises/ADVANCED_OWNERSHIP_WORKSHOP.md)

### docs\rust-ownership-decidability\MASTER_COMPREHENSIVE_ANALYSIS.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\NATURAL_LANGUAGE_ARGUMENTATION_INDEX.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\NATURAL_LANGUAGE_COMPLETION_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\OVERVIEW_AND_INTUITION.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\PROJECT_COMPREHENSIVE_AUDIT_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\PROJECT_STRUCTURE.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)
- ⚠️ 最后更新: 2026-03-05（96 天前，建议复审）

### docs\rust-ownership-decidability\QUICK_REFERENCE_CARD.md

- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)
- ⚠️ 损坏链接: [完整认证](FINAL_100_PERCENT_COMPLETION_CERTIFICATION.md)
- ⚠️ 损坏链接: [案例索引](case-studies/COMPLETE_DOMAIN_COVERAGE_INDEX.md)

### docs\rust-ownership-decidability\RESEARCH_TRACKING_SYSTEM.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\RUST_194_ALIGNMENT_PLAN.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\RUST_194_VS_193_COMPARISON.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\RUST_OWNERSHIP_DECIDABILITY_RESEARCH_PLAN.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\THEOREM_DEPENDENCY_GRAPH.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\THEOREM_INTUITIONS.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\THEOREM_TO_COMPILER_BRIDGE.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\THEORY_TO_PATTERN_BRIDGE.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\UNIFIED_THEORETICAL_FRAMEWORK.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\VISUAL_THINKING_GUIDE.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [rust-ownership-decidability 目录](./README.md)

### docs\rust-ownership-decidability\actor-specialty\ACTOR_MODEL_DEEP_DIVE.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\actor-specialty\COMPLETION_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [case-studies/actix-web-production.md](case-studies/actix-web-production.md)
- ⚠️ 损坏链接: [case-studies/actix-web-production.md](case-studies/actix-web-production.md)
- ⚠️ 损坏链接: [decision-trees/actor-framework-selection.md](decision-trees/actor-framework-selection.md)
- ⚠️ 损坏链接: [decision-trees/actor-framework-selection.md](decision-trees/actor-framework-selection.md)
- ⚠️ 损坏链接: [distributed/distributed-actors-formal.md](distributed/distributed-actors-formal.md)
- ⚠️ 损坏链接: [distributed/distributed-actors-formal.md](distributed/distributed-actors-formal.md)
- ⚠️ 损坏链接: [distributed/distributed-actors-formal.md](distributed/distributed-actors-formal.md)
- ⚠️ 损坏链接: [examples/chat-system-example.md](examples/chat-system-example.md)
- ⚠️ 损坏链接: [examples/chat-system-example.md](examples/chat-system-example.md)
- ⚠️ 损坏链接: [formal-proofs/actor-safety-theorems.md](formal-proofs/actor-safety-theorems.md)
- ⚠️ 损坏链接: [formal-proofs/actor-safety-theorems.md](formal-proofs/actor-safety-theorems.md)
- ⚠️ 损坏链接: [formal-proofs/actor-safety-theorems.md](formal-proofs/actor-safety-theorems.md)
- ⚠️ 损坏链接: [matrices/actor-framework-matrix.md](matrices/actor-framework-matrix.md)
- ⚠️ 损坏链接: [matrices/actor-framework-matrix.md](matrices/actor-framework-matrix.md)
- ⚠️ 损坏链接: [mindmaps/actor-model-mindmap.md](mindmaps/actor-model-mindmap.md)
- ⚠️ 损坏链接: [mindmaps/actor-model-mindmap.md](mindmaps/actor-model-mindmap.md)
- ⚠️ 损坏链接: [patterns/actor-design-patterns-expanded.md](patterns/actor-design-patterns-expanded.md)
- ⚠️ 损坏链接: [patterns/actor-design-patterns-expanded.md](patterns/actor-design-patterns-expanded.md)
- ⚠️ 损坏链接: [patterns/actor-design-patterns.md](patterns/actor-design-patterns.md)
- ⚠️ 损坏链接: [scenario-trees/actor-application-domains.md](scenario-trees/actor-application-domains.md)
- ⚠️ 损坏链接: [scenario-trees/actor-application-domains.md](scenario-trees/actor-application-domains.md)
- ⚠️ 损坏链接: [theory/actor-model-foundation.md](theory/actor-model-foundation.md)
- ⚠️ 损坏链接: [theory/actor-model-foundation.md](theory/actor-model-foundation.md)

### docs\rust-ownership-decidability\actor-specialty\case-studies\actix-web-production.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\actor-specialty\decision-trees\actor-framework-selection.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\actor-specialty\distributed\distributed-actors-formal.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\actor-specialty\examples\chat-system-example.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\actor-specialty\formal-proofs\actor-safety-theorems.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\actor-specialty\matrices\actor-framework-matrix.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\actor-specialty\mindmaps\actor-model-mindmap.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\actor-specialty\patterns\actor-design-patterns-expanded.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\actor-specialty\patterns\actor-design-patterns.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\actor-specialty\scenario-trees\actor-application-domains.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\actor-specialty\theory\actor-model-foundation.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\async-specialty\ASYNC_ECOSYSTEM_COMPLETE.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\async-specialty\COMPLETION_REPORT.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\async-specialty\README.md

- ⚠️ 损坏链接: [actor-specialty/README.md](../actor-specialty/README.md)

### docs\rust-ownership-decidability\audit_reports\CONTENT_QUALITY_AUDIT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [audit_reports 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\audit_reports\FINAL_COMPLETE_ANALYSIS_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [audit_reports 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\audit_reports\FINAL_COMPLETION_REPORT_V3.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [audit_reports 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\audit_reports\FORMALIZATION_FRAMEWORK.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [audit_reports 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\audit_reports\LIBRARY_ANALYSIS_COMPLETION_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [audit_reports 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\audit_reports\PHASE3_LIBRARY_ANALYSIS_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [audit_reports 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\case-studies\COMPLETE_DOMAIN_COVERAGE_INDEX.md

- ⚠️ 损坏链接: [AI/ML 开发指南](ml-ai/README.md)
- ⚠️ 损坏链接: [WASM 开发指南](wasm/README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)
- ⚠️ 损坏链接: [云原生指南](cloud/README.md)
- ⚠️ 损坏链接: [区块链开发指南](blockchain/README.md)
- ⚠️ 损坏链接: [安全工具指南](security/README.md)
- ⚠️ 损坏链接: [数据库系统实现指南](database/README.md)
- ⚠️ 损坏链接: [数据库系统实现指南](database/README.md)
- ⚠️ 损坏链接: [游戏开发指南](gamedev/README.md)
- ⚠️ 损坏链接: [音视频处理指南](media/README.md)
- ⚠️ 损坏链接: [音视频处理指南](media/README.md)

### docs\rust-ownership-decidability\case-studies\MODERN_CRATES_EXPANSION_REPORT.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\case-studies\MODERN_CRATES_FINAL_REPORT.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\case-studies\MODERN_CRATES_INDEX.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\case-studies\MODERN_CRATES_ROUND2_REPORT.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\case-studies\README.md

- ⚠️ 损坏链接: [所有权可判定性总览](../README.md)

### docs\rust-ownership-decidability\case-studies\bytemuck-formal-analysis.md

- ⚠️ 最后更新: 2026-03-10（91 天前，建议复审）

### docs\rust-ownership-decidability\case-studies\embassy-formal-analysis.md

- ⚠️ 最后更新: 2026-03-10（91 天前，建议复审）

### docs\rust-ownership-decidability\case-studies\littlefs2-formal-analysis.md

- ⚠️ 最后更新: 2026-03-10（91 天前，建议复审）

### docs\rust-ownership-decidability\case-studies\panic-probe-formal-analysis.md

- ⚠️ 最后更新: 2026-03-10（91 天前，建议复审）

### docs\rust-ownership-decidability\case-studies\zerocopy-formal-analysis.md

- ⚠️ 最后更新: 2026-03-10（91 天前，建议复审）

### docs\rust-ownership-decidability\comprehensive-analysis\COMPLETION_REPORT.md

- ⚠️ 损坏链接: [README.md](./README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\authoritative-sources\academic-papers.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\case-studies\embassy-embedded-analysis.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\case-studies\tokio-runtime-analysis.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\decision-trees\concurrency-model-selection.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\decision-trees\pattern-selection.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\design-patterns-comprehensive.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [comprehensive-analysis 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\extensions\advanced-ownership-patterns.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\extensions\performance-optimization.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\formal-framework\definitions.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\matrices\comprehensive-comparison-matrix.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\matrices\safety-analysis-matrix.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\mindmaps\borrowing-system-mindmap.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\mindmaps\ownership-system-mindmap.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\open-source-analysis.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [comprehensive-analysis 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\proofs\memory-safety-proof.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\scenario-trees\application-domain-tree.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\comprehensive-analysis\scenario-trees\real-time-systems-tree.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\exercises\09-01-practice-problems.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\exercises\ADVANCED_OWNERSHIP_WORKSHOP.md

- ⚠️ 损坏链接: [exercises 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\exercises\ownership-basics.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [exercises 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\formal-foundations\README.md

- ⚠️ 损坏链接: [`02-01-rustbelt.md`](models/02-01-rustbelt.md)
- ⚠️ 损坏链接: [`02-02-ownership-types.md`](models/02-02-ownership-types.md)
- ⚠️ 损坏链接: [`02-03-borrow-semantics.md`](models/02-03-borrow-semantics.md)
- ⚠️ 损坏链接: [`02-04-lifetime-logic.md`](models/02-04-lifetime-logic.md)
- ⚠️ 损坏链接: [`02-05-move-analysis.md`](models/02-05-move-analysis.md)
- ⚠️ 损坏链接: [`affine-logic-decidability.md`](proofs/affine-logic-decidability.md)
- ⚠️ 损坏链接: [`decidability-theorem.md`](proofs/decidability-theorem.md)
- ⚠️ 损坏链接: [`drop-elaboration-formal.md`](models/drop-elaboration-formal.md)
- ⚠️ 损坏链接: [`executable-semantics-comparison.md`](models/executable-semantics-comparison.md)
- ⚠️ 损坏链接: [`logical-relations.md`](semantics/logical-relations.md)
- ⚠️ 损坏链接: [`mechanized-proofs.md`](semantics/mechanized-proofs.md)
- ⚠️ 损坏链接: [`memory-model-semantics.md`](semantics/memory-model-semantics.md)
- ⚠️ 损坏链接: [`memory-safety-proof.md`](proofs/memory-safety-proof.md)
- ⚠️ 损坏链接: [`operational-semantics.md`](semantics/operational-semantics.md)
- ⚠️ 损坏链接: [`refinedrust-type-system.md`](models/refinedrust-type-system.md)
- ⚠️ 损坏链接: [`relaxed-memory-model.md`](models/relaxed-memory-model.md)
- ⚠️ 损坏链接: [`rustbelt-formalization.md`](proofs/rustbelt-formalization.md)
- ⚠️ 损坏链接: [`semantics-equivalence-proof.md`](semantics/semantics-equivalence-proof.md)
- ⚠️ 损坏链接: [`separation-logic-soundness.md`](proofs/separation-logic-soundness.md)
- ⚠️ 损坏链接: [`symbolic-borrow-checking.md`](models/symbolic-borrow-checking.md)
- ⚠️ 损坏链接: [`tree-borrows-comprehensive.md`](models/tree-borrows-comprehensive.md)
- ⚠️ 损坏链接: [`type-ownership-unified-theory.md`](proofs/type-ownership-unified-theory.md)
- ⚠️ 损坏链接: [`type-system-formalization.md`](semantics/type-system-formalization.md)
- ⚠️ 损坏链接: [所有权可判定性总览](../README.md)
- ⚠️ 最后更新: 2026-03-07（94 天前，建议复审）

### docs\rust-ownership-decidability\meta-model\01_abstract_syntax.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [meta-model 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)
- ⚠️ 最后更新: 2026-03-05（96 天前，建议复审）

### docs\rust-ownership-decidability\meta-model\02_semantic_domains.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [meta-model 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)
- ⚠️ 最后更新: 2026-03-05（96 天前，建议复审）

### docs\rust-ownership-decidability\meta-model\03_judgments.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [meta-model 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)
- ⚠️ 最后更新: 2026-03-05（96 天前，建议复审）

### docs\rust-ownership-decidability\meta-model\RUST_194_COMPREHENSIVE_GUIDE.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\meta-model\rust-194-alignment.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [meta-model 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\practical-examples\comprehensive-code-collection.md

- ⚠️ 损坏链接: [Parent README](../README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-05_initial_setup.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-06_FORMAL_ANALYSIS_PROGRESS.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-06_week1_progress.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-07_CONTENT_CREATION_BATCH_1.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-07_CONTENT_CREATION_BATCH_2.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-07_CONTENT_CREATION_BATCH_3.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-07_FINAL_COMPLETION_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-07_daily_update.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-08_weekend_sprint.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-09_50_PERCENT_MILESTONE.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-09_phase1_completion.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-10_MILESTONE_75_PERCENT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\2026-03-11_MILESTONE_90_PERCENT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\COMPREHENSIVE_STATUS_REPORT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\FINAL_100_PERCENT_COMPLETION_REPORT.md

- ⚠️ 损坏链接: [README](../README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\FINAL_COMPLETION_REPORT_40_PERCENT.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\progress\PROGRESS_TRACKING.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [progress 目录](./README.md)
- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\ref.md

- ⚠️ 损坏链接: [README](./README.md)

### docs\rust-ownership-decidability\theorems\README.md

- ⚠️ 最后更新: 2026-03-07（94 天前，建议复审）

### docs\rust-ownership-decidability\theorems\decidability_theorems.md

- ⚠️ 损坏链接: [上级目录](../README.md)
- ⚠️ 最后更新: 2026-03-05（96 天前，建议复审）

### docs\rust-ownership-decidability\visualizations\KNOWLEDGE_GRAPH_MINDMAP.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\visualizations\README.md

- ⚠️ 损坏链接: [决策树目录](./decision-trees/README.md)
- ⚠️ 损坏链接: [所有权可判定性总览](../README.md)
- ⚠️ 损坏链接: [矩阵目录](./matrices/README.md)

### docs\rust-ownership-decidability\visualizations\decision-tree.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\visualizations\decision-trees\type-selection-decision-tree.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [decision-trees 目录](./README.md)

### docs\rust-ownership-decidability\visualizations\matrices\rust-safety-mechanisms-matrix.md

- ⚠️ 损坏链接: [README](./README.md)
- ⚠️ 损坏链接: [matrices 目录](./README.md)

### docs\rust-ownership-decidability\visualizations\ownership-comprehensive-mindmap.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\visualizations\ownership-mindmap.md

- ⚠️ 损坏链接: [上级目录](../README.md)

### docs\rust-ownership-decidability\visualizations\scenario-tree.md

- ⚠️ 损坏链接: [上级目录](../README.md)

## 后续建议

1. **A类优先**: 速查表版本声明直接影响学习者体验
2. **链接修复**: 损坏的内部链接降低导航效率
3. **过期复审**: 超过 90 天未更新的文档需确认内容有效性
4. **C类评估**: 大型专项目录（如 rust-ownership-decidability/）需评估维护成本与价值
