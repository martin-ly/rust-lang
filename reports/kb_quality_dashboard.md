# 知识体系质量仪表盘 (KB Quality Dashboard)

> 生成时间: 2026-07-09T19:55:16.500755+00:00
> 扫描文件数: 459

## 全局指标

| 指标 | 数值 | 目标 | 状态 |
|:---|:---|:---|:---|
| 总文件数 | 459 | 27 | ✅ |
| 总定理链 (⟹) | 2200 | ≥270 | ✅ |
| 总反命题 | 733 | ≥40 | ✅ |
| 总 Mermaid 图 | 609 | ≥50 | ✅ |
| 编译验证代码块 | 4569 | ≥150 | ✅ |
| 定理矩阵总行 | 19711 | — | — |
| 死链数量 | 0 | 0 | ✅ |
| 反向推理 (⟸) | 335 | ≥50 | ✅ |
| 模板化 ⟹ | 0 | 0 | ✅ |
| 前置概念覆盖率 | 396/396 | 100% | ✅ |
| 后置概念覆盖率 | 396/396 | 100% | ✅ |
| 双标签覆盖率 | 396/396 | >=95% | ✅ |
| 非法标签组合 | 0 | 0 | ✅ |

## 按层级分布

| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径 | ⟸/文件 | 模板化 | 前置覆盖 | 后置覆盖 | 双标签 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| L0 | 63 | 5.4 | 3.1 | 35/63 (55%) | 0.1 | 0 | 14/63 | 13/63 | 45/63 |
| L1 | 55 | 4.7 | 6.3 | 55/55 (100%) | 2.0 | 0 | 55/55 | 55/55 | 55/55 |
| L2 | 38 | 5.4 | 5.9 | 38/38 (100%) | 2.5 | 0 | 38/38 | 38/38 | 38/38 |
| L3 | 57 | 6.3 | 5.2 | 57/57 (100%) | 2.1 | 0 | 57/57 | 57/57 | 57/57 |
| L4 | 53 | 4.8 | 3.9 | 53/53 (100%) | 0.1 | 0 | 53/53 | 53/53 | 53/53 |
| L5 | 19 | 3.8 | 6.7 | 19/19 (100%) | 0.0 | 0 | 19/19 | 19/19 | 19/19 |
| L6 | 115 | 4.2 | 7.7 | 59/115 (51%) | 0.0 | 0 | 115/115 | 115/115 | 115/115 |
| L7 | 59 | 3.9 | 6.6 | 39/59 (66%) | 0.0 | 0 | 59/59 | 59/59 | 59/59 |

## 风险文件

| 文件 | 层级 | 未通过项 |
|:---|:---|:---|
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\19_value_vs_reference_semantics.md | L1 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\34_visibility_and_privacy.md | L3 | 过渡段落不足 (0 < 3); 反向推理不足 (⟸ 0 < 2) |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\21_type_semantics.md | L4 | 过渡段落不足 (0 < 3) |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_stabilized.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |

## 文件详细统计

| 文件 | 层级 | 行数 | ⟹ | ⟸ | 模板 | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 | 前置 | 后置 | 受众 | 分级 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| E:\_src\rust-lang\concept\00_meta\00_framework\03_bloom_taxonomy.md | L0 | 178 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\boundary_extension_tree.md | L0 | 350 | 1 | 0 | 0 | 1 | 3 | 1 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\cognitive_dimension_matrix.md | L0 | 394 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\competency_graph.md | L0 | 408 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\comprehensive_rust_mapping.md | L0 | 233 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 → 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\concept_definition_decision_forest.md | L0 | 1117 | 3 | 0 | 0 | 1 | 10 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\cpp_rust_engineering_roadmap.md | L0 | 206 | 0 | 0 | 0 | 0 | 2 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\decidability_spectrum.md | L0 | 886 | 1 | 0 | 0 | 1 | 6 | 2 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\expressiveness_multiview.md | L0 | 769 | 0 | 0 | 0 | 1 | 7 | 7 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\fault_tree_analysis_collection.md | L0 | 769 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\knowledge_mindmap.md | L0 | 296 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\methodology.md | L0 | 530 | 1 | 0 | 0 | 2 | 5 | 1 | 6 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\paradigm_transition_matrix.md | L0 | 314 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\pattern_semantic_space_index.md | L0 | 162 | 0 | 0 | 0 | 0 | 2 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\pl_foundations_roadmap.md | L0 | 144 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | None |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_bridge_algorithms_patterns.md | L0 | 702 | 1 | 0 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_expressiveness.md | L0 | 1127 | 1 | 0 | 0 | 1 | 2 | 1 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\semantic_space.md | L0 | 1324 | 10 | 0 | 0 | 2 | 5 | 9 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\theorem_inference_forest.md | L0 | 510 | 3 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\00_framework\todos.md | L0 | 343 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\01_terminology\bilingual_template.md | L0 | 164 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 初学者 | 进阶 | 研究者 | None |
| E:\_src\rust-lang\concept\00_meta\01_terminology\bilingual_template_v2.md | L0 | 321 | 0 | 2 | 0 | 5 | 1 | 5 | 0 | ✅ | ✅ | ✅ | 初学者 | 进阶 | 研究者 | None |
| E:\_src\rust-lang\concept\00_meta\01_terminology\terminology_glossary.md | L0 | 463 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\authority_source_map.md | L0 | 188 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\international_authority_index.md | L0 | 232 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 / 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\rustbelt_predicate_map.md | L0 | 412 | 9 | 0 | 0 | 1 | 6 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\sources.md | L0 | 488 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 研究者级 |
| E:\_src\rust-lang\concept\00_meta\02_sources\topic_authority_alignment_map.md | L0 | 352 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\03_audit\08_concept_audit_guide.md | L0 | 104 | 1 | 0 | 0 | 1 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\asp_marking_guide.md | L0 | 522 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\audit_checklist.md | L0 | 442 | 1 | 0 | 0 | 2 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\concept_consistency_audit_checklist.md | L0 | 13 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\03_audit\grading_system.md | L0 | 158 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\quality_dashboard_v2.md | L0 | 324 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\03_audit\template_deduplication_guide.md | L0 | 92 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 贡献者 | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\05_cross_reference_matrix.md | L0 | 14 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\career_landscape.md | L0 | 231 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 入门 → 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\concept_index.md | L0 | 785 | 4 | 0 | 0 | 2 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\foundations_gap_closure_index.md | L0 | 142 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\inter_layer_map.md | L0 | 626 | 12 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\inter_layer_topology.md | L0 | 15 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ✅ | ❌ | ❌ | None | 专家级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\intra_layer_model_map.md | L0 | 335 | 11 | 0 | 0 | 1 | 5 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\learning_guide.md | L0 | 658 | 3 | 0 | 0 | 1 | 1 | 1 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\learning_mvp_path.md | L0 | 366 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\learning_mvp_path_en.md | L0 | 268 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\04_navigation\navigation.md | L0 | 289 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\problem_graph.md | L0 | 509 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\quick_reference.md | L0 | 817 | 1 | 0 | 0 | 1 | 0 | 25 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\04_navigation\self_assessment.md | L0 | 2242 | 1 | 0 | 0 | 1 | 0 | 56 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\01_concept_definition_atlas.md | L0 | 473 | 1 | 1 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\02_attribute_relationship_atlas.md | L0 | 450 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\03_scenario_decision_tree_atlas.md | L0 | 142 | 0 | 0 | 0 | 0 | 3 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\04_example_counterexample_atlas.md | L0 | 131 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\05_logical_reasoning_atlas.md | L0 | 124 | 16 | 2 | 0 | 0 | 3 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\06_inter_layer_mapping_atlas.md | L0 | 116 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\07_intra_layer_mapping_atlas.md | L0 | 314 | 244 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\08_concept_source_alignment_atlas.md | L0 | 145 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\09_reasoning_judgment_tree_atlas.md | L0 | 154 | 0 | 0 | 0 | 0 | 5 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\10_gap_and_action_plan.md | L0 | 124 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | 元层 |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\kg_ontology_v2.md | L0 | 319 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 研究者 | None |
| E:\_src\rust-lang\concept\00_meta\knowledge_topology\kg_tlo_alignment.md | L0 | 238 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\placeholders\placeholder_generic.md | L0 | 22 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\00_meta\trpl_3rd_ed_mapping.md | L0 | 9 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | None | None |
| E:\_src\rust-lang\concept\01_foundation\00_start\00_start.md | L1 | 276 | 4 | 2 | 0 | 1 | 1 | 1 | 6 | ✅ | ✅ | ✅ | 初学者 | 初学者 |
| E:\_src\rust-lang\concept\01_foundation\00_start\06_zero_cost_abstractions.md | L1 | 835 | 3 | 2 | 0 | 3 | 2 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\15_closure_basics.md | L1 | 888 | 3 | 2 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\21_effects_and_purity.md | L1 | 693 | 3 | 2 | 0 | 2 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\34_pl_prerequisites.md | L1 | 503 | 3 | 2 | 0 | 1 | 0 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\36_keywords.md | L1 | 165 | 4 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\37_operators_and_symbols.md | L1 | 267 | 7 | 2 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\00_start\47_std_io_and_process.md | L1 | 450 | 4 | 4 | 0 | 4 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\00_ownership_borrow_lifetime_knowledge_map.md | L1 | 384 | 3 | 2 | 0 | 1 | 5 | 0 | 5 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\01_ownership.md | L1 | 1896 | 12 | 2 | 0 | 3 | 7 | 46 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\02_borrowing.md | L1 | 2041 | 4 | 2 | 0 | 3 | 6 | 53 | 20 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\03_lifetimes.md | L1 | 1482 | 19 | 2 | 0 | 3 | 5 | 40 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\23_move_semantics.md | L1 | 282 | 7 | 2 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\28_ownership_inventories_brown_book.md | L1 | 225 | 4 | 2 | 0 | 1 | 0 | 3 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\01_ownership_borrow_lifetime\30_lifetimes_advanced.md | L1 | 1569 | 3 | 2 | 0 | 1 | 0 | 46 | 10 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\04_type_system.md | L1 | 3279 | 18 | 2 | 0 | 3 | 12 | 63 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\10_numerics.md | L1 | 1047 | 3 | 2 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\14_coercion_and_casting.md | L1 | 912 | 3 | 2 | 0 | 3 | 1 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\22_data_abstraction_spectrum.md | L1 | 749 | 3 | 2 | 0 | 2 | 0 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\02_type_system\31_never_type.md | L1 | 553 | 3 | 2 | 0 | 1 | 0 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\05_reference_semantics.md | L1 | 1429 | 3 | 2 | 0 | 4 | 7 | 35 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\19_value_vs_reference_semantics.md | L1 | 202 | 4 | 0 | 0 | 1 | 0 | 3 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\03_values_and_references\20_variable_model.md | L1 | 621 | 4 | 2 | 0 | 2 | 0 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\07_control_flow.md | L1 | 1609 | 3 | 2 | 0 | 3 | 5 | 25 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\40_patterns.md | L1 | 265 | 7 | 2 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\04_control_flow\41_statements_and_expressions.md | L1 | 173 | 4 | 0 | 0 | 1 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\08_collections.md | L1 | 866 | 3 | 2 | 0 | 3 | 2 | 16 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\05_collections\17_collections_advanced.md | L1 | 996 | 3 | 2 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\09_strings_and_text.md | L1 | 845 | 3 | 2 | 0 | 3 | 1 | 17 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\18_strings_and_encoding.md | L1 | 830 | 3 | 2 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\06_strings_and_text\46_formatting_and_display.md | L1 | 419 | 4 | 3 | 0 | 4 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\11_modules_and_paths.md | L1 | 889 | 3 | 2 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\12_functions.md | L1 | 302 | 4 | 2 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\13_use_declarations.md | L1 | 225 | 4 | 2 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\14_structs.md | L1 | 233 | 4 | 2 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\15_enumerations.md | L1 | 235 | 4 | 2 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\16_implementations.md | L1 | 229 | 4 | 2 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\35_preludes.md | L1 | 230 | 4 | 2 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\38_crates_and_source_files.md | L1 | 271 | 4 | 2 | 0 | 1 | 1 | 4 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\39_items.md | L1 | 301 | 4 | 2 | 0 | 1 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\43_type_aliases.md | L1 | 407 | 4 | 3 | 0 | 4 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\44_static_items.md | L1 | 396 | 4 | 3 | 0 | 4 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\07_modules_and_items\45_const_items_and_const_fn.md | L1 | 417 | 4 | 3 | 0 | 4 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 基础级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\13_panic_and_abort.md | L1 | 938 | 3 | 2 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\32_error_handling_basics.md | L1 | 986 | 3 | 2 | 0 | 3 | 1 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\08_error_handling\33_error_handling_control_flow.md | L1 | 269 | 3 | 3 | 0 | 1 | 1 | 9 | 7 | ✅ | ✅ | ✅ | 初学者 | 入门实践级 |
| E:\_src\rust-lang\concept\01_foundation\09_macros_basics\12_attributes_and_macros.md | L1 | 914 | 3 | 2 | 0 | 3 | 1 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\16_testing_basics.md | L1 | 741 | 3 | 2 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\10_testing_basics\42_useful_development_tools.md | L1 | 227 | 4 | 2 | 0 | 1 | 2 | 0 | 6 | ✅ | ✅ | ✅ | 初学者 | 参考级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\24_quiz_type_system.md | L1 | 539 | 7 | 2 | 0 | 1 | 0 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\25_quiz_error_handling.md | L1 | 652 | 7 | 2 | 0 | 1 | 0 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\26_quiz_modules_testing.md | L1 | 741 | 7 | 2 | 0 | 1 | 0 | 22 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\27_quiz_closures_iterators.md | L1 | 727 | 7 | 2 | 0 | 1 | 0 | 33 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\29_quiz_pl_foundations.md | L1 | 171 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\01_foundation\11_quizzes\33_quiz_ownership_borrowing.md | L1 | 537 | 7 | 2 | 0 | 1 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\01_traits.md | L2 | 3080 | 15 | 2 | 0 | 7 | 5 | 75 | 10 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\09_serde_patterns.md | L2 | 901 | 3 | 3 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\18_lifetimes_advanced.md | L2 | 898 | 3 | 3 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\19_advanced_traits.md | L2 | 957 | 3 | 3 | 0 | 3 | 1 | 21 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\28_construction_and_initialization.md | L2 | 272 | 7 | 2 | 0 | 1 | 0 | 5 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\31_derive_traits.md | L2 | 268 | 7 | 2 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 初学者 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\32_editions.md | L2 | 194 | 4 | 0 | 0 | 1 | 1 | 3 | 0 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\33_rust_release_process.md | L2 | 152 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\00_traits\39_dispatch_mechanisms.md | L2 | 2031 | 7 | 2 | 0 | 1 | 0 | 40 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\02_generics.md | L2 | 3246 | 16 | 2 | 0 | 7 | 6 | 74 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\23_quiz_traits_and_generics.md | L2 | 700 | 7 | 2 | 0 | 1 | 0 | 19 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\01_generics\39_type_level_programming.md | L2 | 660 | 7 | 2 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\03_memory_management.md | L2 | 2176 | 13 | 3 | 0 | 7 | 5 | 57 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\08_interior_mutability.md | L2 | 872 | 3 | 3 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\11_cow_and_borrowed.md | L2 | 764 | 3 | 3 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\12_smart_pointers.md | L2 | 900 | 3 | 3 | 0 | 3 | 2 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\02_memory_management\24_quiz_memory_management.md | L2 | 746 | 7 | 2 | 0 | 1 | 0 | 26 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\04_error_handling.md | L2 | 2714 | 9 | 3 | 0 | 7 | 8 | 61 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\16_error_handling_deep_dive.md | L2 | 774 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\03_error_handling\27_exception_safety_rust_cpp.md | L2 | 266 | 9 | 2 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\06_range_types.md | L2 | 627 | 3 | 3 | 0 | 3 | 2 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\07_closure_types.md | L2 | 789 | 3 | 3 | 0 | 3 | 3 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\14_newtype_and_wrapper.md | L2 | 765 | 3 | 3 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\20_type_system_advanced.md | L2 | 1254 | 3 | 3 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\25_rtti_and_dynamic_typing.md | L2 | 265 | 7 | 2 | 0 | 1 | 0 | 5 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\35_unions.md | L2 | 423 | 4 | 3 | 0 | 4 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\04_types_and_conversions\37_type_conversions.md | L2 | 451 | 4 | 4 | 0 | 4 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\10_module_system.md | L2 | 824 | 3 | 3 | 0 | 3 | 3 | 15 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\22_api_naming_conventions.md | L2 | 452 | 7 | 2 | 0 | 1 | 0 | 15 | 8 | ✅ | ✅ | ✅ | 进阶 | 中级 |
| E:\_src\rust-lang\concept\02_intermediate\05_modules_and_visibility\29_friend_vs_module_privacy.md | L2 | 259 | 7 | 2 | 0 | 1 | 0 | 3 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\05_assert_matches.md | L2 | 694 | 3 | 3 | 0 | 3 | 3 | 18 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\13_dsl_and_embedding.md | L2 | 833 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\17_macro_patterns.md | L2 | 818 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\21_metaprogramming.md | L2 | 871 | 3 | 3 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\26_c_preprocessor_vs_rust_macros.md | L2 | 261 | 7 | 2 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\02_intermediate\06_macros_and_metaprogramming\36_attributes_by_category.md | L2 | 466 | 4 | 4 | 0 | 4 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\02_intermediate\07_iterators_and_closures\15_iterator_patterns.md | L2 | 1345 | 4 | 2 | 0 | 2 | 1 | 22 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\02_intermediate\09_quizzes\30_quiz_cpp_rust_foundations.md | L2 | 225 | 4 | 2 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\01_concurrency.md | L3 | 2104 | 21 | 2 | 0 | 3 | 13 | 27 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\10_concurrency_patterns.md | L3 | 2298 | 3 | 3 | 0 | 3 | 4 | 34 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\11_atomics_and_memory_ordering.md | L3 | 1347 | 3 | 3 | 0 | 3 | 2 | 21 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\16_lock_free.md | L3 | 1217 | 3 | 3 | 0 | 3 | 1 | 20 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\19_parallel_distributed_pattern_spectrum.md | L3 | 1047 | 3 | 3 | 0 | 3 | 0 | 18 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\21_quiz_concurrency_async.md | L3 | 737 | 7 | 2 | 0 | 1 | 0 | 19 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\00_concurrency\22_cross_platform_concurrency.md | L3 | 172 | 6 | 2 | 0 | 1 | 0 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\02_async.md | L3 | 3441 | 17 | 3 | 0 | 6 | 9 | 63 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\06_pin_unpin.md | L3 | 879 | 3 | 3 | 0 | 3 | 2 | 19 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\24_async_closures.md | L3 | 566 | 3 | 2 | 0 | 1 | 0 | 20 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\25_async_advanced.md | L3 | 1707 | 4 | 3 | 0 | 1 | 1 | 40 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\26_async_patterns.md | L3 | 1215 | 3 | 3 | 0 | 3 | 1 | 22 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\01_async\39_future_and_executor_mechanisms.md | L3 | 1046 | 7 | 2 | 0 | 1 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\01_process_model_and_lifecycle.md | L3 | 413 | 8 | 2 | 0 | 1 | 1 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\02_advanced_process_management.md | L3 | 307 | 8 | 2 | 0 | 1 | 1 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\03_async_process_management.md | L3 | 380 | 8 | 2 | 0 | 1 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\04_cross_platform_process_management.md | L3 | 308 | 8 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\05_ipc_mechanisms.md | L3 | 274 | 8 | 2 | 0 | 1 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\06_process_monitoring_and_diagnostics.md | L3 | 272 | 8 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\07_process_security_and_sandboxing.md | L3 | 236 | 8 | 2 | 0 | 1 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\08_process_performance_engineering.md | L3 | 212 | 8 | 2 | 0 | 1 | 1 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\09_process_testing_and_benchmarking.md | L3 | 241 | 8 | 2 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_process_ipc\10_modern_process_libraries.md | L3 | 229 | 8 | 2 | 0 | 1 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\00_before_formal.md | L3 | 175 | 4 | 0 | 0 | 1 | 1 | 0 | 0 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\03_unsafe.md | L3 | 3427 | 14 | 2 | 0 | 4 | 10 | 63 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\08_nll_and_polonius.md | L3 | 831 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\12_unsafe_rust_patterns.md | L3 | 33 | 3 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\22_quiz_unsafe.md | L3 | 646 | 7 | 2 | 0 | 1 | 0 | 21 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\29_memory_model.md | L3 | 255 | 4 | 2 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\30_rust_runtime.md | L3 | 278 | 4 | 2 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\31_panic.md | L3 | 167 | 4 | 0 | 0 | 1 | 0 | 2 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\02_unsafe\35_unsafe_reference.md | L3 | 232 | 4 | 2 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\04_macros.md | L3 | 2477 | 22 | 3 | 0 | 8 | 8 | 59 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\07_proc_macro.md | L3 | 1087 | 3 | 3 | 0 | 3 | 2 | 14 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\23_quiz_macros.md | L3 | 706 | 7 | 2 | 0 | 1 | 0 | 23 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\28_conditional_compilation.md | L3 | 279 | 7 | 2 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 中级 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\29_proc_macro_code_generation_optimization.md | L3 | 343 | 7 | 2 | 0 | 1 | 0 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\30_macro_debugging_and_diagnostics.md | L3 | 298 | 7 | 2 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\31_production_grade_macro_development.md | L3 | 344 | 7 | 2 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\32_macro_glossary.md | L3 | 662 | 8 | 2 | 0 | 1 | 0 | 27 | 6 | ✅ | ✅ | ✅ | 研究者 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\33_macro_faq.md | L3 | 782 | 8 | 2 | 0 | 1 | 0 | 35 | 6 | ✅ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\34_syn_quote_reference.md | L3 | 976 | 8 | 2 | 0 | 1 | 0 | 31 | 6 | ✅ | ✅ | ✅ | 专家 | 参考级 |
| E:\_src\rust-lang\concept\03_advanced\03_proc_macros\35_macro_hygiene.md | L3 | 1029 | 8 | 2 | 0 | 1 | 0 | 35 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\05_rust_ffi.md | L3 | 929 | 3 | 3 | 0 | 3 | 3 | 17 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\09_ffi_advanced.md | L3 | 920 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\04_ffi\27_linkage.md | L3 | 291 | 7 | 2 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\05_inline_assembly\13_inline_assembly.md | L3 | 817 | 7 | 2 | 0 | 1 | 0 | 25 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\14_custom_allocators.md | L3 | 864 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\15_zero_copy_parsing.md | L3 | 907 | 3 | 3 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\17_type_erasure.md | L3 | 876 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\18_network_programming.md | L3 | 1075 | 3 | 3 | 0 | 3 | 2 | 16 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\20_stream_processing_semantics.md | L3 | 847 | 3 | 3 | 0 | 2 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\32_memory_allocation_and_lifetime.md | L3 | 176 | 4 | 0 | 0 | 1 | 0 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\33_variables.md | L3 | 182 | 4 | 0 | 0 | 1 | 0 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\34_visibility_and_privacy.md | L3 | 204 | 4 | 0 | 0 | 1 | 1 | 6 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\06_low_level_patterns\36_ownership_performance_optimization.md | L3 | 180 | 4 | 0 | 0 | 1 | 0 | 8 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\03_advanced\07_unsafe_internals\37_unsafe_collections_internals.md | L3 | 489 | 4 | 4 | 0 | 4 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\02_type_theory.md | L4 | 1747 | 27 | 0 | 0 | 4 | 5 | 27 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\06_subtype_variance.md | L4 | 637 | 3 | 0 | 0 | 3 | 2 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\08_type_inference.md | L4 | 761 | 3 | 0 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\10_category_theory.md | L4 | 811 | 3 | 0 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\14_lambda_calculus.md | L4 | 755 | 3 | 0 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\21_type_semantics.md | L4 | 901 | 3 | 0 | 0 | 3 | 0 | 18 | 0 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\27_type_checking_and_inference.md | L4 | 317 | 7 | 0 | 0 | 1 | 0 | 7 | 6 | ✅ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\29_type_inference_complexity.md | L4 | 414 | 6 | 0 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\00_type_theory\50_type_system_reference.md | L4 | 424 | 4 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\01_linear_logic.md | L4 | 1241 | 14 | 0 | 0 | 4 | 5 | 13 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\03_ownership_formal.md | L4 | 1640 | 11 | 0 | 0 | 1 | 5 | 17 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\09_linear_logic_applications.md | L4 | 747 | 3 | 0 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\28_borrow_checking_decidability.md | L4 | 409 | 7 | 0 | 0 | 1 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\36_tree_borrows_deep_dive.md | L4 | 172 | 1 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\01_ownership_logic\37_behavior_considered_undefined.md | L4 | 176 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 专家 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\04_rustbelt.md | L4 | 1423 | 5 | 0 | 0 | 1 | 5 | 16 | 10 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\11_separation_logic.md | L4 | 839 | 3 | 0 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\33_safety_tags_in_formal.md | L4 | 177 | 1 | 0 | 0 | 1 | 0 | 2 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\02_separation_logic\34_borrow_sanitizer_in_formal.md | L4 | 177 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\12_denotational_semantics.md | L4 | 638 | 3 | 0 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\15_hoare_logic.md | L4 | 909 | 3 | 0 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\17_operational_semantics.md | L4 | 1077 | 3 | 0 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\18_evaluation_strategies.md | L4 | 680 | 4 | 0 | 0 | 2 | 0 | 14 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\20_axiomatic_semantics.md | L4 | 962 | 3 | 0 | 0 | 3 | 0 | 13 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\30_aeneas_symbolic_semantics.md | L4 | 453 | 6 | 0 | 0 | 1 | 1 | 4 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\03_operational_semantics\39_constant_evaluation.md | L4 | 196 | 4 | 0 | 0 | 1 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\05_verification_toolchain.md | L4 | 1535 | 3 | 0 | 0 | 1 | 4 | 17 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\13_formal_methods.md | L4 | 758 | 3 | 0 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\16_aerospace_certification_formal_methods.md | L4 | 1089 | 3 | 0 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\22_modern_verification_tools.md | L4 | 531 | 3 | 0 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\23_programming_language_foundations.md | L4 | 431 | 3 | 0 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\24_autoverus.md | L4 | 195 | 1 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\25_quiz_formal_methods.md | L4 | 621 | 7 | 0 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\31_miri.md | L4 | 315 | 4 | 0 | 0 | 2 | 1 | 2 | 6 | ✅ | ✅ | ✅ | 进阶 / 工程 / 形式化 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\04_model_checking\32_kani.md | L4 | 388 | 7 | 0 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 / 工程 / 形式化 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\19_rustc_query_system.md | L4 | 591 | 7 | 0 | 0 | 1 | 3 | 3 | 6 | ✅ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\20_mir_codegen_llvm_primer.md | L4 | 368 | 8 | 3 | 0 | 1 | 1 | 1 | 6 | ✅ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\26_trait_solver_in_rustc.md | L4 | 450 | 10 | 3 | 0 | 1 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\35_name_resolution_and_hir.md | L4 | 332 | 4 | 0 | 0 | 2 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\38_application_binary_interface.md | L4 | 176 | 4 | 0 | 0 | 1 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 专家 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\40_names_and_resolution.md | L4 | 220 | 4 | 0 | 0 | 1 | 0 | 2 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\41_special_types_and_traits.md | L4 | 195 | 4 | 0 | 0 | 1 | 0 | 0 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\42_type_layout.md | L4 | 171 | 4 | 0 | 0 | 1 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\43_destructors.md | L4 | 189 | 4 | 0 | 0 | 1 | 0 | 3 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\45_lexical_structure.md | L4 | 262 | 4 | 0 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\46_items_reference.md | L4 | 254 | 4 | 0 | 0 | 1 | 0 | 9 | 6 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\47_attributes.md | L4 | 180 | 4 | 0 | 0 | 1 | 0 | 5 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\48_statements_and_expressions_reference.md | L4 | 165 | 4 | 0 | 0 | 1 | 0 | 5 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\49_patterns_reference.md | L4 | 164 | 4 | 0 | 0 | 1 | 0 | 4 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\51_names_reference.md | L4 | 164 | 4 | 0 | 0 | 1 | 0 | 2 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\52_reference_appendices.md | L4 | 166 | 4 | 0 | 0 | 1 | 0 | 1 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\04_formal\05_rustc_internals\53_generics_compiler_behavior.md | L4 | 176 | 4 | 0 | 0 | 1 | 0 | 5 | 0 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\04_formal\06_notation\44_notation.md | L4 | 150 | 4 | 0 | 0 | 1 | 1 | 0 | 0 | ✅ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\03_paradigm_matrix.md | L5 | 1214 | 6 | 0 | 0 | 5 | 8 | 11 | 16 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\05_execution_model_isomorphism.md | L5 | 995 | 3 | 0 | 0 | 1 | 5 | 13 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\00_paradigms\16_cpp_rust_surface_features.md | L5 | 230 | 4 | 0 | 0 | 0 | 0 | 2 | 6 | ✅ | ✅ | ✅ | 进阶 | 研究级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\01_rust_vs_cpp.md | L5 | 2127 | 9 | 0 | 0 | 2 | 10 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\02_rust_vs_go.md | L5 | 975 | 3 | 0 | 0 | 3 | 6 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\09_rust_vs_swift.md | L5 | 725 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\10_rust_vs_zig.md | L5 | 764 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\18_cpp_abi_object_model.md | L5 | 839 | 3 | 0 | 0 | 3 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\01_systems_languages\19_rust_vs_ruby.md | L5 | 733 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\06_rust_vs_java.md | L5 | 608 | 3 | 0 | 0 | 3 | 3 | 7 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\07_rust_vs_python.md | L5 | 686 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\08_rust_vs_javascript.md | L5 | 684 | 3 | 0 | 0 | 3 | 2 | 5 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\11_rust_vs_kotlin.md | L5 | 805 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\12_rust_vs_scala.md | L5 | 766 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\13_rust_vs_csharp.md | L5 | 822 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\14_rust_vs_elixir.md | L5 | 817 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\02_managed_languages\15_rust_vs_typescript.md | L5 | 917 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\04_safety_boundaries.md | L5 | 1004 | 8 | 0 | 0 | 1 | 7 | 9 | 9 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\05_comparative\03_domain_comparisons\17_quiz_rust_vs_systems.md | L5 | 725 | 4 | 0 | 0 | 0 | 0 | 14 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\01_toolchain.md | L6 | 1888 | 13 | 0 | 0 | 2 | 9 | 15 | 14 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\13_logging_observability.md | L6 | 720 | 6 | 0 | 0 | 3 | 3 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\28_devops_and_ci_cd.md | L6 | 896 | 6 | 0 | 0 | 3 | 2 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\45_compiler_internals.md | L6 | 842 | 6 | 0 | 0 | 3 | 0 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\47_compiler_infrastructure.md | L6 | 366 | 4 | 0 | 0 | 2 | 0 | 1 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\57_quiz_toolchain.md | L6 | 560 | 3 | 0 | 0 | 0 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\58_platform_rust_integration.md | L6 | 313 | 3 | 0 | 0 | 0 | 0 | 4 | 8 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\67_llvm_backend_and_codegen.md | L6 | 300 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\68_rustc_driver_and_stable_mir.md | L6 | 265 | 3 | 0 | 0 | 0 | 0 | 2 | 6 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\69_compiler_diagnostics_and_ui_tests.md | L6 | 290 | 3 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\70_rustc_bootstrap.md | L6 | 249 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\71_compiler_testing.md | L6 | 281 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 专家 / 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\77_rustdoc_196_changes.md | L6 | 236 | 3 | 0 | 0 | 0 | 0 | 3 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\00_toolchain\79_development_tools.md | L6 | 192 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 初学者 | 研究级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\09_cargo_script.md | L6 | 737 | 4 | 0 | 0 | 1 | 2 | 12 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\10_public_private_deps.md | L6 | 243 | 4 | 0 | 0 | 1 | 1 | 1 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\11_resolver_v3_public_feature_unification.md | L6 | 178 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 实践级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\59_cargo_build_scripts.md | L6 | 520 | 3 | 0 | 0 | 2 | 2 | 14 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\60_cargo_dependency_resolution.md | L6 | 517 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\61_cargo_source_replacement.md | L6 | 295 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\62_cargo_registries_and_publishing.md | L6 | 299 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\63_cargo_authentication_and_cache.md | L6 | 294 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\64_cargo_manifest_reference.md | L6 | 325 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\65_cargo_profiles_and_lints.md | L6 | 308 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\66_cargo_subcommands_and_plugins.md | L6 | 251 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\72_cargo_security_cves.md | L6 | 476 | 4 | 0 | 0 | 3 | 1 | 0 | 8 | ✅ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\76_cargo_196_features.md | L6 | 264 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\78_cargo_workspaces.md | L6 | 268 | 3 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 中级 → 高级 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\80_cargo_getting_started.md | L6 | 169 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\81_cargo_workflow.md | L6 | 170 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\82_cargo_guide_practices.md | L6 | 166 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\83_cargo_configuration.md | L6 | 180 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\84_cargo_commands_reference.md | L6 | 168 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\85_cargo_manifest_targets.md | L6 | 170 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\86_cargo_registry_internals.md | L6 | 160 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 专家 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\01_cargo\87_build_std.md | L6 | 284 | 3 | 0 | 0 | 0 | 2 | 3 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\02_core_crates\03_core_crates.md | L6 | 1342 | 8 | 0 | 0 | 2 | 6 | 17 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\02_patterns.md | L6 | 3075 | 11 | 0 | 0 | 2 | 5 | 45 | 14 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\05_system_design_principles.md | L6 | 742 | 6 | 0 | 0 | 1 | 6 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\30_system_composability.md | L6 | 802 | 3 | 0 | 0 | 0 | 4 | 23 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\31_microservice_patterns.md | L6 | 1008 | 6 | 0 | 0 | 2 | 6 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\32_event_driven_architecture.md | L6 | 1038 | 6 | 0 | 0 | 2 | 4 | 15 | 8 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\33_cqrs_event_sourcing.md | L6 | 1461 | 6 | 0 | 0 | 3 | 1 | 18 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\34_idioms_spectrum.md | L6 | 1411 | 6 | 0 | 0 | 1 | 5 | 35 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\35_architecture_patterns.md | L6 | 1276 | 6 | 0 | 0 | 3 | 0 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\36_pattern_implementation_comparison.md | L6 | 789 | 4 | 0 | 0 | 0 | 0 | 16 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\37_pattern_selection_best_practices.md | L6 | 751 | 4 | 0 | 0 | 0 | 0 | 11 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\38_formal_design_pattern_theory.md | L6 | 997 | 4 | 0 | 0 | 0 | 0 | 16 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\39_frontier_research_and_innovative_patterns.md | L6 | 978 | 4 | 0 | 0 | 0 | 0 | 17 | 6 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\41_workflow_theory.md | L6 | 1409 | 6 | 0 | 0 | 3 | 0 | 17 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\42_api_design_patterns.md | L6 | 1298 | 6 | 0 | 0 | 3 | 0 | 19 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\73_pattern_composition_algebra.md | L6 | 726 | 6 | 0 | 0 | 3 | 0 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\82_engineering_and_production_patterns.md | L6 | 315 | 3 | 0 | 0 | 0 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\84_design_patterns_glossary.md | L6 | 257 | 4 | 0 | 0 | 0 | 0 | 4 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\03_design_patterns\85_design_patterns_faq.md | L6 | 486 | 4 | 0 | 0 | 0 | 0 | 4 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\18_distributed_systems.md | L6 | 814 | 6 | 0 | 0 | 3 | 1 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\24_cloud_native.md | L6 | 791 | 4 | 0 | 0 | 3 | 1 | 8 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\27_web_frameworks.md | L6 | 1004 | 6 | 0 | 0 | 4 | 3 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\38_network_protocols.md | L6 | 526 | 6 | 0 | 0 | 1 | 0 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\39_high_performance_network_service_architecture.md | L6 | 2057 | 3 | 0 | 0 | 0 | 0 | 19 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\40_reactive_programming.md | L6 | 1080 | 6 | 0 | 0 | 3 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\41_http_client_development.md | L6 | 186 | 0 | 0 | 0 | 0 | 0 | 8 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\42_glommio_and_thread_per_core.md | L6 | 224 | 3 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\04_web_and_networking\43_websocket_realtime_communication.md | L6 | 723 | 4 | 0 | 0 | 0 | 0 | 10 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\08_wasi.md | L6 | 672 | 6 | 0 | 0 | 5 | 2 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\17_cross_compilation.md | L6 | 671 | 6 | 0 | 0 | 3 | 1 | 5 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\22_embedded_systems.md | L6 | 973 | 6 | 0 | 0 | 3 | 1 | 10 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\25_cli_development.md | L6 | 788 | 6 | 0 | 0 | 3 | 1 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\39_os_kernel.md | L6 | 490 | 6 | 0 | 0 | 1 | 0 | 10 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\52_robotics.md | L6 | 1012 | 6 | 0 | 0 | 3 | 0 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\53_embedded_graphics.md | L6 | 1166 | 6 | 0 | 0 | 3 | 1 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\56_c_to_rust_translation.md | L6 | 455 | 6 | 0 | 0 | 1 | 0 | 2 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\05_systems_and_embedded\57_embedded_hal_1_0_migration.md | L6 | 237 | 3 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 / 工程 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\04_application_domains.md | L6 | 1526 | 8 | 0 | 0 | 2 | 6 | 12 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\23_database_access.md | L6 | 819 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\36_stream_processing_ecosystem.md | L6 | 569 | 6 | 0 | 0 | 1 | 0 | 10 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\37_database_systems.md | L6 | 543 | 6 | 0 | 0 | 1 | 0 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\48_data_engineering.md | L6 | 940 | 6 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\50_distributed_consensus.md | L6 | 863 | 6 | 0 | 0 | 3 | 0 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\06_data_and_distributed\55_rust_for_data_science.md | L6 | 612 | 6 | 0 | 0 | 3 | 0 | 8 | 12 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\19_security_practices.md | L6 | 1090 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\07_security_and_cryptography\43_security_cryptography.md | L6 | 931 | 6 | 0 | 0 | 3 | 0 | 16 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\44_formal_ecosystem_tower.md | L6 | 600 | 3 | 0 | 0 | 0 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\08_formal_verification\74_formal_verification_tools.md | L6 | 942 | 6 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_networking\01_advanced_network_protocols.md | L6 | 281 | 3 | 0 | 0 | 0 | 2 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_networking\02_network_security.md | L6 | 321 | 3 | 0 | 0 | 0 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_networking\03_custom_protocol_implementation.md | L6 | 185 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_networking\04_network_programming_quick_start.md | L6 | 262 | 3 | 0 | 0 | 0 | 2 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 | 指南级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_networking\05_formal_network_protocol_theory.md | L6 | 559 | 3 | 0 | 0 | 0 | 0 | 14 | 6 | ❌ | ✅ | ✅ | 研究者 / 专家 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_networking\06_networking_basics.md | L6 | 859 | 4 | 0 | 0 | 0 | 0 | 15 | 6 | ❌ | ✅ | ✅ | 初学者 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\12_testing_strategies.md | L6 | 748 | 6 | 0 | 0 | 3 | 2 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\14_documentation.md | L6 | 676 | 4 | 0 | 0 | 3 | 2 | 7 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\16_testing.md | L6 | 762 | 4 | 0 | 0 | 3 | 2 | 8 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\09_testing_and_quality\17_benchmarking.md | L6 | 158 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 进阶 | 指南级 |
| E:\_src\rust-lang\concept\06_ecosystem\10_performance\15_performance_optimization.md | L6 | 1154 | 6 | 0 | 0 | 3 | 1 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\06_blockchain.md | L6 | 921 | 5 | 0 | 0 | 0 | 3 | 14 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\07_game_ecs.md | L6 | 1362 | 3 | 0 | 0 | 0 | 7 | 23 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\11_webassembly.md | L6 | 674 | 6 | 0 | 0 | 3 | 3 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\20_licensing_and_compliance.md | L6 | 701 | 6 | 0 | 0 | 3 | 1 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\21_game_development.md | L6 | 698 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\26_game_development.md | L6 | 721 | 6 | 0 | 0 | 3 | 1 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\29_algorithms_competitive_programming.md | L6 | 1257 | 3 | 0 | 0 | 0 | 0 | 29 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\46_machine_learning_ecosystem.md | L6 | 943 | 6 | 0 | 0 | 3 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\49_game_engine_internals.md | L6 | 1133 | 6 | 0 | 0 | 3 | 0 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\51_quantum_computing_rust.md | L6 | 996 | 4 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\54_webassembly_advanced.md | L6 | 1145 | 6 | 0 | 0 | 2 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\59_wasm_glossary.md | L6 | 368 | 4 | 0 | 0 | 0 | 0 | 0 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\60_wasm_faq.md | L6 | 470 | 4 | 0 | 0 | 0 | 0 | 6 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\61_wasm_javascript_interop.md | L6 | 469 | 4 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\75_industrial_case_studies.md | L6 | 459 | 6 | 0 | 0 | 1 | 0 | 5 | 12 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\76_algorithm_engineering_practice.md | L6 | 1940 | 3 | 0 | 0 | 0 | 0 | 22 | 6 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\77_data_structures_in_rust.md | L6 | 273 | 3 | 0 | 0 | 0 | 1 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\78_algorithm_complexity_analysis.md | L6 | 181 | 0 | 0 | 0 | 0 | 0 | 4 | 0 | ❌ | ✅ | ✅ | 进阶 | 进阶 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\79_cutting_edge_algorithms.md | L6 | 235 | 3 | 0 | 0 | 0 | 0 | 3 | 6 | ❌ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\06_ecosystem\11_domain_applications\80_formal_algorithm_theory.md | L6 | 265 | 3 | 0 | 0 | 0 | 0 | 4 | 6 | ❌ | ✅ | ✅ | 专家 | 形式化级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\05_rust_version_tracking.md | L7 | 2584 | 6 | 0 | 0 | 1 | 3 | 9 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\50_nightly_rust.md | L7 | 233 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 初学者 | 研究级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_90_stabilized.md | L7 | 755 | 4 | 0 | 0 | 0 | 0 | 14 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_91_stabilized.md | L7 | 2543 | 3 | 0 | 0 | 0 | 0 | 81 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_92_stabilized.md | L7 | 2536 | 3 | 0 | 0 | 0 | 0 | 72 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_93_stabilized.md | L7 | 183 | 3 | 0 | 0 | 0 | 0 | 8 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_94_stabilized.md | L7 | 412 | 4 | 0 | 0 | 0 | 0 | 9 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_95_stabilized.md | L7 | 327 | 3 | 0 | 0 | 0 | 0 | 14 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_96_stabilized.md | L7 | 315 | 3 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_preview.md | L7 | 98 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_97_stabilized.md | L7 | 342 | 0 | 0 | 0 | 0 | 0 | 12 | 0 | ❌ | ✅ | ✅ | 进阶 | 参考级 |
| E:\_src\rust-lang\concept\07_future\00_version_tracking\rust_1_98_preview.md | L7 | 595 | 3 | 0 | 0 | 0 | 0 | 7 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\19_rust_edition_preview.md | L7 | 110 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 进阶 | 研究级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\23_rust_edition_guide.md | L7 | 17 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 研究者 | 研究级 |
| E:\_src\rust-lang\concept\07_future\01_edition_roadmap\44_edition_guide.md | L7 | 782 | 4 | 0 | 0 | 3 | 1 | 10 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\02_stabilized_features\borrow_sanitizer.md | L7 | 353 | 3 | 0 | 0 | 1 | 1 | 3 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\04_effects_system.md | L7 | 1768 | 6 | 0 | 0 | 1 | 4 | 26 | 12 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\07_mcdc_coverage_preview.md | L7 | 563 | 4 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\08_safety_tags_preview.md | L7 | 653 | 4 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\09_parallel_frontend_preview.md | L7 | 667 | 6 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\10_derive_coerce_pointee_preview.md | L7 | 636 | 4 | 0 | 0 | 3 | 3 | 8 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\11_const_trait_impl_preview.md | L7 | 654 | 6 | 0 | 0 | 3 | 2 | 7 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\12_return_type_notation_preview.md | L7 | 503 | 3 | 0 | 0 | 3 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\13_unsafe_fields_preview.md | L7 | 668 | 6 | 0 | 0 | 3 | 3 | 8 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\14_lifetime_capture_preview.md | L7 | 240 | 3 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\15_pin_ergonomics_preview.md | L7 | 312 | 3 | 0 | 0 | 2 | 2 | 8 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\16_type_alias_impl_trait_preview.md | L7 | 236 | 3 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\17_const_trait_preview.md | L7 | 234 | 3 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\18_async_drop_preview.md | L7 | 789 | 6 | 0 | 0 | 3 | 2 | 7 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\20_borrowsanitizer_preview.md | L7 | 664 | 4 | 0 | 0 | 3 | 3 | 7 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\22_gen_blocks_preview.md | L7 | 650 | 4 | 0 | 0 | 3 | 3 | 8 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\25_open_enums_preview.md | L7 | 799 | 4 | 0 | 0 | 3 | 3 | 13 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\26_specialization_preview.md | L7 | 772 | 4 | 0 | 0 | 3 | 2 | 8 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\27_compile_time_execution.md | L7 | 739 | 4 | 0 | 0 | 3 | 1 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\30_stable_abi_preview.md | L7 | 240 | 3 | 0 | 0 | 1 | 0 | 3 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\31_safety_tags_preview.md | L7 | 156 | 0 | 0 | 0 | 1 | 0 | 2 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\32_inline_const_pattern_preview.md | L7 | 251 | 3 | 0 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\33_autoverus_preview.md | L7 | 172 | 0 | 0 | 0 | 1 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 进阶 | 专家级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\34_must_not_suspend_preview.md | L7 | 231 | 3 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\35_ferrocene_preview.md | L7 | 653 | 6 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\37_rpitit_preview.md | L7 | 258 | 3 | 0 | 0 | 1 | 0 | 6 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\38_cranelift_backend_preview.md | L7 | 766 | 6 | 0 | 0 | 3 | 3 | 9 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\39_arbitrary_self_types_preview.md | L7 | 401 | 6 | 0 | 0 | 2 | 0 | 9 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\40_ergonomic_ref_counting_preview.md | L7 | 287 | 3 | 0 | 0 | 0 | 0 | 5 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\41_rust_specification_preview.md | L7 | 645 | 6 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\42_field_projections_preview.md | L7 | 392 | 4 | 0 | 0 | 2 | 0 | 8 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\45_std_autodiff_preview.md | L7 | 325 | 6 | 0 | 0 | 2 | 0 | 5 | 12 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\46_cargo_semver_checks_preview.md | L7 | 220 | 3 | 0 | 0 | 0 | 0 | 1 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\47_wasm_target_evolution.md | L7 | 242 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\48_aarch64_sve_sme_preview.md | L7 | 268 | 3 | 0 | 0 | 0 | 0 | 3 | 6 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\03_preview_features\49_rust_in_space.md | L7 | 231 | 3 | 0 | 0 | 1 | 0 | 2 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\01_ai_integration.md | L7 | 1007 | 5 | 0 | 0 | 2 | 2 | 9 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\02_formal_methods.md | L7 | 1663 | 9 | 0 | 0 | 1 | 9 | 9 | 3 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\03_evolution.md | L7 | 2179 | 8 | 0 | 0 | 1 | 6 | 19 | 3 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\21_rust_in_ai.md | L7 | 778 | 6 | 0 | 0 | 3 | 1 | 7 | 12 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\28_rust_for_webassembly.md | L7 | 947 | 4 | 0 | 0 | 3 | 2 | 11 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\29_ebpf_rust.md | L7 | 992 | 6 | 0 | 0 | 1 | 3 | 15 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\04_research_and_experimental\43_rust_for_linux.md | L7 | 1066 | 4 | 0 | 0 | 3 | 2 | 11 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| E:\_src\rust-lang\concept\07_future\05_roadmaps\24_roadmap.md | L7 | 1067 | 6 | 0 | 0 | 3 | 2 | 17 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
