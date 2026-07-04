# 知识体系质量仪表盘 (KB Quality Dashboard)

> 生成时间: 2026-07-04T12:59:36.952859+00:00
> 扫描文件数: 382

## 全局指标

| 指标 | 数值 | 目标 | 状态 |
|:---|:---|:---|:---|
| 总文件数 | 382 | 27 | ✅ |
| 总定理链 (⟹) | 1851 | ≥270 | ✅ |
| 总反命题 | 661 | ≥40 | ✅ |
| 总 Mermaid 图 | 540 | ≥50 | ✅ |
| 编译验证代码块 | 3474 | ≥150 | ✅ |
| 定理矩阵总行 | 17134 | — | — |
| 死链数量 | 0 | 0 | ✅ |
| 反向推理 (⟸) | 224 | ≥50 | ✅ |
| 模板化 ⟹ | 0 | 0 | ✅ |
| 前置概念覆盖率 | 322/322 | 100% | ✅ |
| 后置概念覆盖率 | 322/322 | 100% | ✅ |
| 双标签覆盖率 | 322/322 | >=95% | ✅ |
| 非法标签组合 | 0 | 0 | ✅ |

## 按层级分布

| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径 | ⟸/文件 | 模板化 | 前置覆盖 | 后置覆盖 | 双标签 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| L0 | 60 | 5.4 | 3.3 | 34/60 (56%) | 0.0 | 0 | 12/60 | 11/60 | 44/60 |
| L1 | 43 | 5.0 | 5.8 | 43/43 (100%) | 1.6 | 0 | 43/43 | 43/43 | 43/43 |
| L2 | 33 | 5.5 | 5.9 | 33/33 (100%) | 2.4 | 0 | 33/33 | 33/33 | 33/33 |
| L3 | 36 | 5.6 | 4.4 | 36/36 (100%) | 2.0 | 0 | 36/36 | 36/36 | 36/36 |
| L4 | 51 | 4.7 | 3.5 | 51/51 (100%) | 0.0 | 0 | 51/51 | 51/51 | 51/51 |
| L5 | 19 | 3.8 | 6.7 | 19/19 (100%) | 0.0 | 0 | 19/19 | 19/19 | 19/19 |
| L6 | 86 | 4.7 | 8.7 | 60/86 (69%) | 0.0 | 0 | 86/86 | 86/86 | 86/86 |
| L7 | 54 | 4.0 | 6.8 | 39/54 (72%) | 0.0 | 0 | 54/54 | 54/54 | 54/54 |

## 风险文件

| 文件 | 层级 | 未通过项 |
|:---|:---|:---|
| — | — | 所有文件通过质量门 |

## 文件详细统计

| 文件 | 层级 | 行数 | ⟹ | ⟸ | 模板 | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 | 前置 | 后置 | 受众 | 分级 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| concept\00_meta\03_bloom_taxonomy.md | L0 | 178 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\05_cross_reference_matrix.md | L0 | 14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| concept\00_meta\08_concept_audit_guide.md | L0 | 80 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\asp_marking_guide.md | L0 | 522 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\00_meta\audit_checklist.md | L0 | 442 | 1 | 0 | 0 | 2 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\authority_source_map.md | L0 | 188 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\bilingual_template.md | L0 | 164 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 进阶 | 研究者 | None |
| concept\00_meta\boundary_extension_tree.md | L0 | 350 | 1 | 0 | 0 | 1 | 3 | 1 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\career_landscape.md | L0 | 231 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 入门 → 进阶 | None |
| concept\00_meta\cognitive_dimension_matrix.md | L0 | 394 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\competency_graph.md | L0 | 408 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\comprehensive_rust_mapping.md | L0 | 233 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 → 进阶 | None |
| concept\00_meta\concept_consistency_audit_checklist.md | L0 | 13 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| concept\00_meta\concept_definition_decision_forest.md | L0 | 1117 | 3 | 0 | 0 | 1 | 10 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\concept_index.md | L0 | 785 | 4 | 0 | 0 | 2 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\cpp_rust_engineering_roadmap.md | L0 | 140 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| concept\00_meta\decidability_spectrum.md | L0 | 886 | 1 | 0 | 0 | 1 | 6 | 2 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\expressiveness_multiview.md | L0 | 769 | 0 | 0 | 0 | 1 | 7 | 7 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\fault_tree_analysis_collection.md | L0 | 769 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\foundations_gap_closure_index.md | L0 | 135 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| concept\00_meta\grading_system.md | L0 | 142 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\inter_layer_map.md | L0 | 626 | 12 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\inter_layer_topology.md | L0 | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ✅ | ❌ | ❌ | None | 专家级 |
| concept\00_meta\intra_layer_model_map.md | L0 | 335 | 11 | 0 | 0 | 1 | 5 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\kg_ontology_v2.md | L0 | 319 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | None |
| concept\00_meta\kg_tlo_alignment.md | L0 | 238 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| concept\00_meta\knowledge_mindmap.md | L0 | 296 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\knowledge_topology\01_concept_definition_atlas.md | L0 | 473 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\02_attribute_relationship_atlas.md | L0 | 450 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\03_scenario_decision_tree_atlas.md | L0 | 25 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\04_example_counterexample_atlas.md | L0 | 25 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\05_logical_reasoning_atlas.md | L0 | 25 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\06_inter_layer_mapping_atlas.md | L0 | 98 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\07_intra_layer_mapping_atlas.md | L0 | 314 | 244 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\08_concept_source_alignment_atlas.md | L0 | 50 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\09_reasoning_judgment_tree_atlas.md | L0 | 25 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\knowledge_topology\10_gap_and_action_plan.md | L0 | 82 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| concept\00_meta\learning_guide.md | L0 | 659 | 3 | 0 | 0 | 1 | 1 | 1 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\learning_mvp_path.md | L0 | 366 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ❌ | 初学者 | 综述级 |
| concept\00_meta\learning_mvp_path_en.md | L0 | 268 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| concept\00_meta\methodology.md | L0 | 530 | 1 | 0 | 0 | 2 | 5 | 1 | 6 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| concept\00_meta\navigation.md | L0 | 289 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\paradigm_transition_matrix.md | L0 | 314 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\pattern_semantic_space_index.md | L0 | 134 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| concept\00_meta\pl_foundations_roadmap.md | L0 | 129 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | None |
| concept\00_meta\placeholders\placeholder_generic.md | L0 | 22 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| concept\00_meta\problem_graph.md | L0 | 509 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\quality_dashboard_v2.md | L0 | 324 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\quick_reference.md | L0 | 817 | 1 | 0 | 0 | 1 | 0 | 25 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\rustbelt_predicate_map.md | L0 | 412 | 9 | 0 | 0 | 1 | 6 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\self_assessment.md | L0 | 2233 | 0 | 0 | 0 | 1 | 0 | 55 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\semantic_bridge_algorithms_patterns.md | L0 | 702 | 1 | 0 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\00_meta\semantic_expressiveness.md | L0 | 1127 | 1 | 0 | 0 | 1 | 2 | 1 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\semantic_space.md | L0 | 1325 | 10 | 0 | 0 | 2 | 5 | 9 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\sources.md | L0 | 488 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 研究者级 |
| concept\00_meta\template_deduplication_guide.md | L0 | 75 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 贡献者 | None |
| concept\00_meta\terminology_glossary.md | L0 | 463 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\theorem_inference_forest.md | L0 | 510 | 3 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\todos.md | L0 | 324 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\topic_authority_alignment_map.md | L0 | 16 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| concept\01_foundation\00_start.md | L1 | 142 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 初学者 | 初学者 |
| concept\01_foundation\01_ownership.md | L1 | 1810 | 12 | 2 | 0 | 3 | 7 | 43 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\02_borrowing.md | L1 | 1944 | 4 | 2 | 0 | 3 | 6 | 49 | 20 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\03_lifetimes.md | L1 | 1435 | 19 | 2 | 0 | 3 | 5 | 40 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\04_type_system.md | L1 | 2844 | 18 | 2 | 0 | 3 | 12 | 54 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\05_reference_semantics.md | L1 | 1429 | 3 | 2 | 0 | 4 | 7 | 35 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\06_zero_cost_abstractions.md | L1 | 835 | 3 | 2 | 0 | 3 | 2 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\07_control_flow.md | L1 | 1576 | 3 | 2 | 0 | 3 | 5 | 25 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\08_collections.md | L1 | 866 | 3 | 2 | 0 | 3 | 2 | 16 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\09_strings_and_text.md | L1 | 845 | 3 | 2 | 0 | 3 | 1 | 17 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\10_numerics.md | L1 | 1014 | 3 | 2 | 0 | 3 | 1 | 16 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\11_modules_and_paths.md | L1 | 889 | 3 | 2 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\12_attributes_and_macros.md | L1 | 914 | 3 | 2 | 0 | 3 | 1 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\13_panic_and_abort.md | L1 | 938 | 3 | 2 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\14_coercion_and_casting.md | L1 | 914 | 3 | 2 | 0 | 3 | 1 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\15_closure_basics.md | L1 | 888 | 3 | 2 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\16_testing_basics.md | L1 | 741 | 3 | 2 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\17_collections_advanced.md | L1 | 996 | 3 | 2 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\18_strings_and_encoding.md | L1 | 830 | 3 | 2 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\19_value_vs_reference_semantics.md | L1 | 197 | 4 | 0 | 0 | 1 | 0 | 3 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\20_variable_model.md | L1 | 626 | 4 | 2 | 0 | 2 | 0 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\21_effects_and_purity.md | L1 | 697 | 3 | 2 | 0 | 2 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\22_data_abstraction_spectrum.md | L1 | 753 | 3 | 2 | 0 | 2 | 0 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\23_move_semantics.md | L1 | 285 | 7 | 2 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\24_quiz_type_system.md | L1 | 545 | 7 | 2 | 0 | 1 | 0 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\25_quiz_error_handling.md | L1 | 658 | 7 | 2 | 0 | 1 | 0 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\26_quiz_modules_testing.md | L1 | 747 | 7 | 2 | 0 | 1 | 0 | 22 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\27_quiz_closures_iterators.md | L1 | 733 | 7 | 2 | 0 | 1 | 0 | 33 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\28_ownership_inventories_brown_book.md | L1 | 223 | 4 | 2 | 0 | 1 | 0 | 3 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\29_quiz_pl_foundations.md | L1 | 171 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\30_lifetimes_advanced.md | L1 | 1501 | 3 | 2 | 0 | 1 | 0 | 43 | 10 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\31_never_type.md | L1 | 553 | 3 | 2 | 0 | 1 | 0 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\32_error_handling_basics.md | L1 | 986 | 3 | 2 | 0 | 3 | 1 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\33_quiz_ownership_borrowing.md | L1 | 543 | 7 | 2 | 0 | 1 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\34_pl_prerequisites.md | L1 | 499 | 3 | 2 | 0 | 1 | 0 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\35_preludes.md | L1 | 221 | 4 | 2 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\36_keywords.md | L1 | 162 | 4 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\37_operators_and_symbols.md | L1 | 264 | 7 | 2 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\38_crates_and_source_files.md | L1 | 152 | 4 | 0 | 0 | 1 | 0 | 3 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\39_items.md | L1 | 127 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\40_patterns.md | L1 | 265 | 7 | 2 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\41_statements_and_expressions.md | L1 | 169 | 4 | 0 | 0 | 1 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\42_useful_development_tools.md | L1 | 92 | 4 | 0 | 0 | 1 | 1 | 0 | 0 | ✅ | ✅ | ✅ | 初学者 | 参考级 |
| concept\02_intermediate\01_traits.md | L2 | 2561 | 15 | 2 | 0 | 7 | 5 | 63 | 10 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\02_generics.md | L2 | 2679 | 16 | 2 | 0 | 7 | 6 | 64 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\03_memory_management.md | L2 | 2039 | 13 | 3 | 0 | 7 | 5 | 50 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\04_error_handling.md | L2 | 2530 | 9 | 3 | 0 | 7 | 8 | 53 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\05_assert_matches.md | L2 | 682 | 3 | 3 | 0 | 3 | 3 | 18 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\06_range_types.md | L2 | 627 | 3 | 3 | 0 | 3 | 2 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\07_closure_types.md | L2 | 747 | 3 | 3 | 0 | 3 | 3 | 15 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\08_interior_mutability.md | L2 | 836 | 3 | 3 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\09_serde_patterns.md | L2 | 901 | 3 | 3 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\10_module_system.md | L2 | 824 | 3 | 3 | 0 | 3 | 3 | 15 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\11_cow_and_borrowed.md | L2 | 761 | 3 | 3 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\12_smart_pointers.md | L2 | 857 | 3 | 3 | 0 | 3 | 2 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\13_dsl_and_embedding.md | L2 | 792 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\14_newtype_and_wrapper.md | L2 | 765 | 3 | 3 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\15_iterator_patterns.md | L2 | 1269 | 4 | 2 | 0 | 2 | 1 | 19 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\16_error_handling_deep_dive.md | L2 | 770 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\17_macro_patterns.md | L2 | 813 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\18_lifetimes_advanced.md | L2 | 898 | 3 | 3 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\19_advanced_traits.md | L2 | 866 | 3 | 3 | 0 | 3 | 1 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\20_type_system_advanced.md | L2 | 974 | 3 | 3 | 0 | 3 | 1 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\21_metaprogramming.md | L2 | 811 | 3 | 3 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\22_api_naming_conventions.md | L2 | 450 | 7 | 2 | 0 | 1 | 0 | 15 | 8 | ✅ | ✅ | ✅ | 进阶 | 中级 |
| concept\02_intermediate\23_quiz_traits_and_generics.md | L2 | 710 | 7 | 2 | 0 | 1 | 0 | 19 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\24_quiz_memory_management.md | L2 | 749 | 7 | 2 | 0 | 1 | 0 | 26 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\25_rtti_and_dynamic_typing.md | L2 | 265 | 7 | 2 | 0 | 1 | 0 | 5 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\26_c_preprocessor_vs_rust_macros.md | L2 | 258 | 7 | 2 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\27_exception_safety_rust_cpp.md | L2 | 263 | 9 | 2 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\28_construction_and_initialization.md | L2 | 274 | 7 | 2 | 0 | 1 | 0 | 5 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\29_friend_vs_module_privacy.md | L2 | 257 | 7 | 2 | 0 | 1 | 0 | 3 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\30_quiz_cpp_rust_foundations.md | L2 | 231 | 4 | 2 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\31_derive_traits.md | L2 | 274 | 7 | 2 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 参考级 |
| concept\02_intermediate\32_editions.md | L2 | 92 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| concept\02_intermediate\33_rust_release_process.md | L2 | 96 | 4 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| concept\03_advanced\00_before_formal.md | L3 | 174 | 4 | 0 | 0 | 1 | 1 | 0 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\03_advanced\01_concurrency.md | L3 | 1610 | 21 | 2 | 0 | 3 | 10 | 23 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\02_async.md | L3 | 3126 | 17 | 3 | 0 | 6 | 9 | 56 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\03_unsafe.md | L3 | 3427 | 14 | 2 | 0 | 4 | 10 | 63 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\04_macros.md | L3 | 2477 | 22 | 3 | 0 | 8 | 8 | 59 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\05_rust_ffi.md | L3 | 879 | 3 | 3 | 0 | 3 | 3 | 16 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\06_pin_unpin.md | L3 | 879 | 3 | 3 | 0 | 3 | 2 | 19 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\07_proc_macro.md | L3 | 899 | 3 | 3 | 0 | 3 | 2 | 10 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\08_nll_and_polonius.md | L3 | 831 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\09_ffi_advanced.md | L3 | 920 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\10_concurrency_patterns.md | L3 | 1139 | 3 | 3 | 0 | 3 | 1 | 22 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\11_atomics_and_memory_ordering.md | L3 | 1212 | 3 | 3 | 0 | 3 | 2 | 21 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\12_unsafe_rust_patterns.md | L3 | 34 | 3 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\13_inline_assembly.md | L3 | 817 | 7 | 2 | 0 | 1 | 0 | 25 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\14_custom_allocators.md | L3 | 864 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\15_zero_copy_parsing.md | L3 | 907 | 3 | 3 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\16_lock_free.md | L3 | 1189 | 3 | 3 | 0 | 3 | 1 | 20 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\17_type_erasure.md | L3 | 876 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\18_network_programming.md | L3 | 974 | 3 | 3 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\19_parallel_distributed_pattern_spectrum.md | L3 | 897 | 3 | 3 | 0 | 3 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\20_stream_processing_semantics.md | L3 | 846 | 3 | 3 | 0 | 2 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\21_quiz_concurrency_async.md | L3 | 746 | 7 | 2 | 0 | 1 | 0 | 19 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\22_quiz_unsafe.md | L3 | 652 | 7 | 2 | 0 | 1 | 0 | 21 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\23_quiz_macros.md | L3 | 712 | 7 | 2 | 0 | 1 | 0 | 23 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\24_async_closures.md | L3 | 571 | 3 | 2 | 0 | 1 | 0 | 20 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\25_async_advanced.md | L3 | 1671 | 4 | 3 | 0 | 1 | 1 | 40 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\26_async_patterns.md | L3 | 1142 | 3 | 3 | 0 | 3 | 1 | 20 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\27_linkage.md | L3 | 293 | 7 | 2 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\03_advanced\28_conditional_compilation.md | L3 | 281 | 7 | 2 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 中级 | 专家级 |
| concept\03_advanced\29_memory_model.md | L3 | 113 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\30_rust_runtime.md | L3 | 142 | 4 | 0 | 0 | 1 | 0 | 2 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\31_panic.md | L3 | 166 | 4 | 0 | 0 | 1 | 0 | 2 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\32_memory_allocation_and_lifetime.md | L3 | 99 | 4 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\33_variables.md | L3 | 131 | 4 | 0 | 0 | 1 | 0 | 3 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\34_visibility_and_privacy.md | L3 | 151 | 4 | 0 | 0 | 1 | 0 | 3 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\35_unsafe_reference.md | L3 | 103 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\04_formal\01_linear_logic.md | L4 | 1240 | 14 | 0 | 0 | 4 | 5 | 13 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\02_type_theory.md | L4 | 1481 | 27 | 0 | 0 | 4 | 5 | 27 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\03_ownership_formal.md | L4 | 1640 | 11 | 0 | 0 | 1 | 5 | 17 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\04_rustbelt.md | L4 | 1423 | 5 | 0 | 0 | 1 | 5 | 16 | 10 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\05_verification_toolchain.md | L4 | 1535 | 3 | 0 | 0 | 1 | 4 | 17 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\06_subtype_variance.md | L4 | 635 | 3 | 0 | 0 | 3 | 2 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\08_type_inference.md | L4 | 720 | 3 | 0 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\09_linear_logic_applications.md | L4 | 744 | 3 | 0 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\10_category_theory.md | L4 | 809 | 3 | 0 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\11_separation_logic.md | L4 | 838 | 3 | 0 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\12_denotational_semantics.md | L4 | 637 | 3 | 0 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\13_formal_methods.md | L4 | 743 | 3 | 0 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\14_lambda_calculus.md | L4 | 753 | 3 | 0 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\15_hoare_logic.md | L4 | 908 | 3 | 0 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\16_aerospace_certification_formal_methods.md | L4 | 1089 | 3 | 0 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\17_operational_semantics.md | L4 | 1076 | 3 | 0 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\18_evaluation_strategies.md | L4 | 684 | 4 | 0 | 0 | 2 | 0 | 14 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\19_rustc_query_system.md | L4 | 416 | 7 | 0 | 0 | 1 | 2 | 1 | 6 | ✅ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\04_formal\20_axiomatic_semantics.md | L4 | 952 | 3 | 0 | 0 | 3 | 0 | 13 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\21_type_semantics.md | L4 | 896 | 3 | 0 | 0 | 3 | 0 | 18 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\22_modern_verification_tools.md | L4 | 514 | 3 | 0 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\23_programming_language_foundations.md | L4 | 424 | 3 | 0 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\24_autoverus.md | L4 | 183 | 1 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\04_formal\25_quiz_formal_methods.md | L4 | 621 | 7 | 0 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\26_trait_solver_in_rustc.md | L4 | 314 | 7 | 0 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\04_formal\27_type_checking_and_inference.md | L4 | 313 | 7 | 0 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\04_formal\28_borrow_checking_decidability.md | L4 | 415 | 7 | 0 | 0 | 1 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\29_type_inference_complexity.md | L4 | 410 | 6 | 0 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\30_aeneas_symbolic_semantics.md | L4 | 446 | 6 | 0 | 0 | 1 | 1 | 4 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\31_miri.md | L4 | 304 | 4 | 0 | 0 | 2 | 1 | 2 | 6 | ✅ | ✅ | ✅ | 进阶 / 工程 / 形式化 | 综述级 |
| concept\04_formal\32_kani.md | L4 | 373 | 7 | 0 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 / 工程 / 形式化 | 综述级 |
| concept\04_formal\33_safety_tags_in_formal.md | L4 | 169 | 1 | 0 | 0 | 1 | 0 | 2 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\04_formal\34_borrow_sanitizer_in_formal.md | L4 | 169 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\04_formal\35_name_resolution_and_hir.md | L4 | 334 | 4 | 0 | 0 | 2 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\04_formal\36_tree_borrows_deep_dive.md | L4 | 160 | 1 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\04_formal\37_behavior_considered_undefined.md | L4 | 167 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 专家 | 研究级 |
| concept\04_formal\38_application_binary_interface.md | L4 | 169 | 4 | 0 | 0 | 1 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 研究级 |
| concept\04_formal\39_constant_evaluation.md | L4 | 145 | 4 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\40_names_and_resolution.md | L4 | 144 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\41_special_types_and_traits.md | L4 | 188 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\42_type_layout.md | L4 | 164 | 4 | 0 | 0 | 1 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\43_destructors.md | L4 | 182 | 4 | 0 | 0 | 1 | 0 | 3 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\44_notation.md | L4 | 120 | 4 | 0 | 0 | 1 | 1 | 0 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\45_lexical_structure.md | L4 | 120 | 4 | 0 | 0 | 1 | 0 | 2 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\46_items_reference.md | L4 | 118 | 4 | 0 | 0 | 1 | 0 | 2 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\47_attributes.md | L4 | 108 | 4 | 0 | 0 | 1 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\48_statements_and_expressions_reference.md | L4 | 108 | 4 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\49_patterns_reference.md | L4 | 104 | 4 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\50_type_system_reference.md | L4 | 127 | 4 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\51_names_reference.md | L4 | 107 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\04_formal\52_reference_appendices.md | L4 | 110 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| concept\05_comparative\01_rust_vs_cpp.md | L5 | 2127 | 9 | 0 | 0 | 2 | 10 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\05_comparative\02_rust_vs_go.md | L5 | 975 | 3 | 0 | 0 | 3 | 6 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\03_paradigm_matrix.md | L5 | 957 | 6 | 0 | 0 | 5 | 8 | 7 | 16 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\04_safety_boundaries.md | L5 | 1004 | 8 | 0 | 0 | 1 | 7 | 9 | 9 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\05_comparative\05_execution_model_isomorphism.md | L5 | 995 | 3 | 0 | 0 | 1 | 5 | 13 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\05_comparative\06_rust_vs_java.md | L5 | 608 | 3 | 0 | 0 | 3 | 3 | 7 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\07_rust_vs_python.md | L5 | 686 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\08_rust_vs_javascript.md | L5 | 684 | 3 | 0 | 0 | 3 | 2 | 5 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\09_rust_vs_swift.md | L5 | 725 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\10_rust_vs_zig.md | L5 | 764 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\11_rust_vs_kotlin.md | L5 | 805 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\12_rust_vs_scala.md | L5 | 766 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\13_rust_vs_csharp.md | L5 | 822 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\14_rust_vs_elixir.md | L5 | 817 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\15_rust_vs_typescript.md | L5 | 917 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\16_cpp_rust_surface_features.md | L5 | 234 | 4 | 0 | 0 | 0 | 0 | 2 | 6 | ✅ | ✅ | ✅ | 进阶 | 研究级 |
| concept\05_comparative\17_quiz_rust_vs_systems.md | L5 | 729 | 4 | 0 | 0 | 0 | 0 | 14 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\18_cpp_abi_object_model.md | L5 | 839 | 3 | 0 | 0 | 3 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\19_rust_vs_ruby.md | L5 | 733 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\01_toolchain.md | L6 | 1888 | 13 | 0 | 0 | 2 | 9 | 15 | 14 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\02_patterns.md | L6 | 1871 | 11 | 0 | 0 | 2 | 5 | 34 | 14 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\03_core_crates.md | L6 | 1342 | 8 | 0 | 0 | 2 | 6 | 17 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\04_application_domains.md | L6 | 1526 | 8 | 0 | 0 | 2 | 6 | 12 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\05_system_design_principles.md | L6 | 742 | 6 | 0 | 0 | 1 | 6 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\06_blockchain.md | L6 | 919 | 5 | 0 | 0 | 0 | 3 | 14 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\07_game_ecs.md | L6 | 1363 | 3 | 0 | 0 | 0 | 7 | 23 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\08_wasi.md | L6 | 652 | 6 | 0 | 0 | 5 | 2 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\09_cargo_script.md | L6 | 697 | 4 | 0 | 0 | 1 | 2 | 10 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\10_public_private_deps.md | L6 | 631 | 6 | 0 | 0 | 1 | 2 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\11_webassembly.md | L6 | 641 | 6 | 0 | 0 | 3 | 3 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\12_testing_strategies.md | L6 | 701 | 6 | 0 | 0 | 3 | 2 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\13_logging_observability.md | L6 | 680 | 6 | 0 | 0 | 3 | 3 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\14_documentation.md | L6 | 676 | 4 | 0 | 0 | 3 | 2 | 7 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\15_performance_optimization.md | L6 | 747 | 6 | 0 | 0 | 3 | 1 | 10 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\16_testing.md | L6 | 738 | 4 | 0 | 0 | 3 | 2 | 8 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\17_cross_compilation.md | L6 | 671 | 6 | 0 | 0 | 3 | 1 | 5 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\18_distributed_systems.md | L6 | 771 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\19_security_practices.md | L6 | 1090 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\20_licensing_and_compliance.md | L6 | 701 | 6 | 0 | 0 | 3 | 1 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\21_game_development.md | L6 | 698 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\22_embedded_systems.md | L6 | 950 | 6 | 0 | 0 | 3 | 1 | 10 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\23_database_access.md | L6 | 819 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\24_cloud_native.md | L6 | 791 | 4 | 0 | 0 | 3 | 1 | 8 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\25_cli_development.md | L6 | 788 | 6 | 0 | 0 | 3 | 1 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\26_game_development.md | L6 | 721 | 6 | 0 | 0 | 3 | 1 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\27_web_frameworks.md | L6 | 1004 | 6 | 0 | 0 | 4 | 3 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\28_devops_and_ci_cd.md | L6 | 874 | 6 | 0 | 0 | 3 | 2 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | L6 | 1033 | 3 | 0 | 0 | 0 | 0 | 26 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\30_system_composability.md | L6 | 802 | 3 | 0 | 0 | 0 | 4 | 23 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\31_microservice_patterns.md | L6 | 972 | 6 | 0 | 0 | 2 | 6 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\32_event_driven_architecture.md | L6 | 1050 | 6 | 0 | 0 | 2 | 4 | 15 | 8 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\33_cqrs_event_sourcing.md | L6 | 1461 | 6 | 0 | 0 | 3 | 1 | 18 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\34_idioms_spectrum.md | L6 | 1393 | 6 | 0 | 0 | 1 | 5 | 35 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\35_architecture_patterns.md | L6 | 1206 | 6 | 0 | 0 | 3 | 0 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\36_stream_processing_ecosystem.md | L6 | 569 | 6 | 0 | 0 | 1 | 0 | 10 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\37_database_systems.md | L6 | 543 | 6 | 0 | 0 | 1 | 0 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\38_network_protocols.md | L6 | 420 | 6 | 0 | 0 | 1 | 0 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\39_os_kernel.md | L6 | 415 | 6 | 0 | 0 | 1 | 0 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\40_reactive_programming.md | L6 | 1080 | 6 | 0 | 0 | 3 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\41_workflow_theory.md | L6 | 1391 | 6 | 0 | 0 | 3 | 0 | 17 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\42_api_design_patterns.md | L6 | 1298 | 6 | 0 | 0 | 3 | 0 | 19 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\43_security_cryptography.md | L6 | 928 | 6 | 0 | 0 | 3 | 0 | 16 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\44_formal_ecosystem_tower.md | L6 | 600 | 3 | 0 | 0 | 0 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\45_compiler_internals.md | L6 | 842 | 6 | 0 | 0 | 3 | 0 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\46_machine_learning_ecosystem.md | L6 | 943 | 6 | 0 | 0 | 3 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\47_compiler_infrastructure.md | L6 | 366 | 4 | 0 | 0 | 2 | 0 | 1 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\06_ecosystem\48_data_engineering.md | L6 | 940 | 6 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\49_game_engine_internals.md | L6 | 1133 | 6 | 0 | 0 | 3 | 0 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\50_distributed_consensus.md | L6 | 825 | 6 | 0 | 0 | 3 | 0 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\51_quantum_computing_rust.md | L6 | 906 | 4 | 0 | 0 | 3 | 0 | 9 | 12 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| concept\06_ecosystem\52_robotics.md | L6 | 1007 | 6 | 0 | 0 | 3 | 0 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\53_embedded_graphics.md | L6 | 1045 | 6 | 0 | 0 | 3 | 1 | 3 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\54_webassembly_advanced.md | L6 | 877 | 6 | 0 | 0 | 2 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\55_rust_for_data_science.md | L6 | 612 | 6 | 0 | 0 | 3 | 0 | 8 | 12 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| concept\06_ecosystem\56_c_to_rust_translation.md | L6 | 455 | 6 | 0 | 0 | 1 | 0 | 2 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\57_quiz_toolchain.md | L6 | 563 | 3 | 0 | 0 | 0 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\58_platform_rust_integration.md | L6 | 316 | 3 | 0 | 0 | 0 | 0 | 4 | 8 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\06_ecosystem\59_cargo_build_scripts.md | L6 | 523 | 3 | 0 | 0 | 2 | 2 | 14 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| concept\06_ecosystem\60_cargo_dependency_resolution.md | L6 | 520 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\61_cargo_source_replacement.md | L6 | 298 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\62_cargo_registries_and_publishing.md | L6 | 302 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\63_cargo_authentication_and_cache.md | L6 | 297 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\64_cargo_manifest_reference.md | L6 | 328 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 参考级 |
| concept\06_ecosystem\65_cargo_profiles_and_lints.md | L6 | 311 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\66_cargo_subcommands_and_plugins.md | L6 | 254 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\67_llvm_backend_and_codegen.md | L6 | 303 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\06_ecosystem\68_rustc_driver_and_stable_mir.md | L6 | 268 | 3 | 0 | 0 | 0 | 0 | 2 | 6 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\06_ecosystem\69_compiler_diagnostics_and_ui_tests.md | L6 | 293 | 3 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\06_ecosystem\70_rustc_bootstrap.md | L6 | 252 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\06_ecosystem\71_compiler_testing.md | L6 | 284 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| concept\06_ecosystem\72_cargo_security_cves.md | L6 | 478 | 4 | 0 | 0 | 3 | 1 | 0 | 8 | ✅ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| concept\06_ecosystem\73_pattern_composition_algebra.md | L6 | 726 | 6 | 0 | 0 | 3 | 0 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\74_formal_verification_tools.md | L6 | 942 | 6 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\75_industrial_case_studies.md | L6 | 357 | 6 | 0 | 0 | 1 | 0 | 2 | 12 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\06_ecosystem\76_cargo_196_features.md | L6 | 264 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| concept\06_ecosystem\77_rustdoc_196_changes.md | L6 | 236 | 3 | 0 | 0 | 0 | 0 | 3 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| concept\06_ecosystem\78_cargo_workspaces.md | L6 | 271 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| concept\06_ecosystem\79_development_tools.md | L6 | 192 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 初学者 | 研究级 |
| concept\06_ecosystem\80_cargo_getting_started.md | L6 | 88 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 参考级 |
| concept\06_ecosystem\81_cargo_workflow.md | L6 | 97 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\06_ecosystem\82_cargo_guide_practices.md | L6 | 91 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\06_ecosystem\83_cargo_configuration.md | L6 | 90 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\06_ecosystem\84_cargo_commands_reference.md | L6 | 82 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\06_ecosystem\85_cargo_manifest_targets.md | L6 | 100 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\06_ecosystem\86_cargo_registry_internals.md | L6 | 97 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 参考级 |
| concept\07_future\01_ai_integration.md | L7 | 1009 | 5 | 0 | 0 | 2 | 2 | 9 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\02_formal_methods.md | L7 | 1663 | 9 | 0 | 0 | 1 | 9 | 9 | 3 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\03_evolution.md | L7 | 2179 | 8 | 0 | 0 | 1 | 6 | 19 | 3 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\04_effects_system.md | L7 | 1768 | 6 | 0 | 0 | 1 | 4 | 26 | 12 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\05_rust_version_tracking.md | L7 | 2583 | 6 | 0 | 0 | 1 | 3 | 9 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\07_mcdc_coverage_preview.md | L7 | 563 | 4 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\08_safety_tags_preview.md | L7 | 650 | 4 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\09_parallel_frontend_preview.md | L7 | 667 | 6 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\10_derive_coerce_pointee_preview.md | L7 | 592 | 4 | 0 | 0 | 3 | 3 | 7 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\11_const_trait_impl_preview.md | L7 | 626 | 6 | 0 | 0 | 3 | 2 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\12_return_type_notation_preview.md | L7 | 505 | 3 | 0 | 0 | 3 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\13_unsafe_fields_preview.md | L7 | 619 | 6 | 0 | 0 | 3 | 3 | 6 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\14_lifetime_capture_preview.md | L7 | 150 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\15_pin_ergonomics_preview.md | L7 | 312 | 3 | 0 | 0 | 2 | 2 | 8 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\16_type_alias_impl_trait_preview.md | L7 | 146 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\17_const_trait_preview.md | L7 | 143 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\18_async_drop_preview.md | L7 | 758 | 6 | 0 | 0 | 3 | 2 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\19_rust_edition_preview.md | L7 | 67 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究级 |
| concept\07_future\20_borrowsanitizer_preview.md | L7 | 660 | 4 | 0 | 0 | 3 | 3 | 7 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\21_rust_in_ai.md | L7 | 778 | 6 | 0 | 0 | 3 | 1 | 7 | 12 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\22_gen_blocks_preview.md | L7 | 743 | 7 | 0 | 0 | 4 | 3 | 6 | 14 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\23_rust_edition_guide.md | L7 | 17 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| concept\07_future\24_roadmap.md | L7 | 1067 | 6 | 0 | 0 | 3 | 2 | 17 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\25_open_enums_preview.md | L7 | 799 | 4 | 0 | 0 | 3 | 3 | 13 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\26_specialization_preview.md | L7 | 743 | 4 | 0 | 0 | 3 | 2 | 7 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\27_compile_time_execution.md | L7 | 739 | 4 | 0 | 0 | 3 | 1 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\28_rust_for_webassembly.md | L7 | 947 | 4 | 0 | 0 | 3 | 2 | 11 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\29_ebpf_rust.md | L7 | 992 | 6 | 0 | 0 | 1 | 3 | 15 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\30_stable_abi_preview.md | L7 | 148 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\31_safety_tags_preview.md | L7 | 155 | 0 | 0 | 0 | 1 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\07_future\32_inline_const_pattern_preview.md | L7 | 148 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\33_autoverus_preview.md | L7 | 171 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| concept\07_future\34_must_not_suspend_preview.md | L7 | 144 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\35_ferrocene_preview.md | L7 | 653 | 6 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\37_rpitit_preview.md | L7 | 149 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\38_cranelift_backend_preview.md | L7 | 766 | 6 | 0 | 0 | 3 | 3 | 9 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\39_arbitrary_self_types_preview.md | L7 | 350 | 6 | 0 | 0 | 2 | 0 | 7 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\40_ergonomic_ref_counting_preview.md | L7 | 287 | 3 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\41_rust_specification_preview.md | L7 | 643 | 6 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\42_field_projections_preview.md | L7 | 392 | 4 | 0 | 0 | 2 | 0 | 8 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\43_rust_for_linux.md | L7 | 1018 | 4 | 0 | 0 | 3 | 2 | 9 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\44_edition_guide.md | L7 | 782 | 4 | 0 | 0 | 3 | 1 | 10 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\45_std_autodiff_preview.md | L7 | 326 | 6 | 0 | 0 | 2 | 0 | 5 | 12 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| concept\07_future\46_cargo_semver_checks_preview.md | L7 | 223 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\47_wasm_target_evolution.md | L7 | 142 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\48_aarch64_sve_sme_preview.md | L7 | 271 | 3 | 0 | 0 | 0 | 0 | 3 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\49_rust_in_space.md | L7 | 100 | 3 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\50_nightly_rust.md | L7 | 128 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 研究级 |
| concept\07_future\borrow_sanitizer.md | L7 | 315 | 3 | 0 | 0 | 1 | 1 | 1 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\rust_1_95_stabilized.md | L7 | 330 | 3 | 0 | 0 | 0 | 0 | 14 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\07_future\rust_1_96_stabilized.md | L7 | 318 | 3 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\07_future\rust_1_97_preview.md | L7 | 296 | 3 | 0 | 0 | 0 | 0 | 11 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| concept\07_future\rust_1_97_stabilized.md | L7 | 19 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 占位级 |
| concept\07_future\rust_1_98_preview.md | L7 | 578 | 3 | 0 | 0 | 0 | 0 | 6 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
