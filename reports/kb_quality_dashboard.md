# 知识体系质量仪表盘 (KB Quality Dashboard)

> 生成时间: 2026-06-08T01:37:06.499642+00:00
> 扫描文件数: 267

## 全局指标

| 指标 | 数值 | 目标 | 状态 |
|:---|:---|:---|:---|
| 总文件数 | 267 | 27 | ✅ |
| 总定理链 (⟹) | 1176 | ≥270 | ✅ |
| 总反命题 | 596 | ≥40 | ✅ |
| 总 Mermaid 图 | 535 | ≥50 | ✅ |
| 编译验证代码块 | 2934 | ≥150 | ✅ |
| 定理矩阵总行 | 13309 | — | — |
| 死链数量 | 0 | 0 | ✅ |
| 反向推理 (⟸) | 175 | ≥50 | ✅ |
| 模板化 ⟹ | 0 | 0 | ✅ |
| 前置概念覆盖率 | 227/228 | 100% | ⚠️ |
| 后置概念覆盖率 | 214/228 | 100% | ⚠️ |

## 按层级分布

| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径 | ⟸/文件 | 模板化 | 前置覆盖 | 后置覆盖 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| L0 | 39 | 2.3 | 5.5 | 36/39 (92%) | 0.0 | 0 | 7/39 | 6/39 |
| L1 | 31 | 3.8 | 6.3 | 26/31 (83%) | 1.7 | 0 | 31/31 | 26/31 |
| L2 | 24 | 4.5 | 5.8 | 22/24 (91%) | 2.6 | 0 | 24/24 | 22/24 |
| L3 | 25 | 5.0 | 4.9 | 21/25 (84%) | 2.4 | 0 | 24/25 | 21/25 |
| L4 | 22 | 5.0 | 5.5 | 21/22 (95%) | 0.0 | 0 | 22/22 | 21/22 |
| L5 | 18 | 3.6 | 6.4 | 17/18 (94%) | 0.0 | 0 | 18/18 | 17/18 |
| L6 | 60 | 5.8 | 10.9 | 59/60 (98%) | 0.0 | 0 | 60/60 | 59/60 |
| L7 | 48 | 4.4 | 7.4 | 44/48 (91%) | 0.0 | 0 | 48/48 | 48/48 |

## 风险文件

| 文件 | 层级 | 未通过项 |
|:---|:---|:---|
| concept\01_foundation\23_quiz_ownership_borrowing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\24_quiz_type_system.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\25_quiz_error_handling.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\26_quiz_modules_testing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\27_quiz_closures_iterators.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\23_quiz_traits_and_generics.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\24_quiz_memory_management.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\00_before_formal.md | L3 | 缺失认知路径; 缺失反命题; 缺失前置概念; 缺失后置概念 |
| concept\03_advanced\21_quiz_concurrency_async.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\22_quiz_unsafe.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\23_quiz_macros.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\04_formal\24_quiz_formal_methods.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念 |
| concept\05_comparative\17_quiz_rust_vs_systems.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失后置概念 |
| concept\06_ecosystem\57_quiz_toolchain.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失后置概念 |
| concept\07_future\01_ai_integration.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (2 < 3) |
| concept\07_future\15_pin_ergonomics_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |

## 文件详细统计

| 文件 | 层级 | 行数 | ⟹ | ⟸ | 模板 | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 | 前置 | 后置 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| concept\00_meta\03_bloom_taxonomy.md | L0 | 140 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\05_cross_reference_matrix.md | L0 | 80 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\08_concept_audit_guide.md | L0 | 69 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\asp_marking_guide.md | L0 | 467 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ✅ | ✅ |
| concept\00_meta\audit_checklist.md | L0 | 345 | 1 | 0 | 0 | 2 | 1 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\authority_source_map.md | L0 | 145 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\boundary_extension_tree.md | L0 | 300 | 1 | 0 | 0 | 1 | 3 | 1 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\career_landscape.md | L0 | 188 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ |
| concept\00_meta\cognitive_dimension_matrix.md | L0 | 343 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\competency_graph.md | L0 | 366 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\comprehensive_rust_mapping.md | L0 | 190 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ |
| concept\00_meta\concept_definition_decision_forest.md | L0 | 1076 | 3 | 0 | 0 | 1 | 10 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\concept_index.md | L0 | 724 | 4 | 0 | 0 | 2 | 0 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\decidability_spectrum.md | L0 | 843 | 1 | 0 | 0 | 1 | 6 | 2 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\expressiveness_multiview.md | L0 | 720 | 0 | 0 | 0 | 1 | 7 | 7 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\fault_tree_analysis_collection.md | L0 | 727 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\grading_system.md | L0 | 106 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ |
| concept\00_meta\inter_layer_map.md | L0 | 588 | 12 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\inter_layer_topology.md | L0 | 363 | 8 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ✅ | ✅ |
| concept\00_meta\intra_layer_model_map.md | L0 | 297 | 11 | 0 | 0 | 1 | 5 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\kg_ontology.md | L0 | 369 | 4 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\knowledge_mindmap.md | L0 | 258 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\learning_guide.md | L0 | 620 | 3 | 0 | 0 | 1 | 1 | 1 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\LEARNING_MVP_PATH.md | L0 | 241 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ❌ |
| concept\00_meta\methodology.md | L0 | 499 | 1 | 0 | 0 | 2 | 5 | 1 | 6 | ✅ | ✅ | ✅ |
| concept\00_meta\navigation.md | L0 | 254 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\paradigm_transition_matrix.md | L0 | 272 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\problem_graph.md | L0 | 456 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\quality_dashboard_v2.md | L0 | 285 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\quick_reference.md | L0 | 780 | 1 | 0 | 0 | 1 | 0 | 25 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\rustbelt_predicate_map.md | L0 | 373 | 9 | 0 | 0 | 1 | 6 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\self_assessment.md | L0 | 2172 | 0 | 0 | 0 | 1 | 0 | 55 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\semantic_bridge_algorithms_patterns.md | L0 | 338 | 1 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ |
| concept\00_meta\semantic_expressiveness.md | L0 | 1089 | 1 | 0 | 0 | 1 | 2 | 1 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\semantic_space.md | L0 | 1279 | 10 | 0 | 0 | 2 | 5 | 9 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\sources.md | L0 | 447 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\terminology_glossary.md | L0 | 491 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\theorem_inference_forest.md | L0 | 469 | 3 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\00_meta\todos.md | L0 | 281 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ |
| concept\01_foundation\00_pl_prerequisites.md | L1 | 434 | 3 | 2 | 0 | 1 | 0 | 12 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\01_ownership.md | L1 | 1731 | 12 | 2 | 0 | 3 | 7 | 42 | 16 | ✅ | ✅ | ✅ |
| concept\01_foundation\02_borrowing.md | L1 | 1797 | 4 | 2 | 0 | 3 | 6 | 44 | 20 | ✅ | ✅ | ✅ |
| concept\01_foundation\03_lifetimes.md | L1 | 1377 | 19 | 2 | 0 | 3 | 5 | 40 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\03_lifetimes_advanced.md | L1 | 1344 | 3 | 2 | 0 | 1 | 0 | 39 | 10 | ✅ | ✅ | ✅ |
| concept\01_foundation\04_type_system.md | L1 | 2503 | 18 | 2 | 0 | 3 | 12 | 45 | 16 | ✅ | ✅ | ✅ |
| concept\01_foundation\05_never_type.md | L1 | 442 | 3 | 2 | 0 | 1 | 0 | 14 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\05_reference_semantics.md | L1 | 1374 | 3 | 2 | 0 | 4 | 7 | 35 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\06_zero_cost_abstractions.md | L1 | 680 | 3 | 2 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\07_control_flow.md | L1 | 757 | 3 | 2 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\08_collections.md | L1 | 704 | 3 | 2 | 0 | 3 | 2 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\09_strings_and_text.md | L1 | 644 | 3 | 2 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\10_error_handling_basics.md | L1 | 769 | 3 | 2 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\10_numerics.md | L1 | 713 | 3 | 2 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\11_modules_and_paths.md | L1 | 739 | 3 | 2 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\11_numeric_types.md | L1 | 588 | 3 | 2 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\12_attributes_and_macros.md | L1 | 749 | 3 | 2 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\13_panic_and_abort.md | L1 | 747 | 3 | 2 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\14_coercion_and_casting.md | L1 | 762 | 3 | 2 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\15_closure_basics.md | L1 | 747 | 3 | 2 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\16_testing_basics.md | L1 | 669 | 3 | 2 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\17_collections_advanced.md | L1 | 899 | 3 | 2 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\18_strings_and_encoding.md | L1 | 720 | 3 | 2 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\20_variable_model.md | L1 | 525 | 3 | 2 | 0 | 3 | 0 | 12 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\21_effects_and_purity.md | L1 | 570 | 3 | 2 | 0 | 3 | 0 | 17 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\22_data_abstraction_spectrum.md | L1 | 607 | 3 | 2 | 0 | 3 | 0 | 14 | 6 | ✅ | ✅ | ✅ |
| concept\01_foundation\23_quiz_ownership_borrowing.md | L1 | 438 | 0 | 0 | 0 | 0 | 0 | 17 | 0 | ❌ | ✅ | ❌ |
| concept\01_foundation\24_quiz_type_system.md | L1 | 460 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ❌ |
| concept\01_foundation\25_quiz_error_handling.md | L1 | 573 | 0 | 0 | 0 | 0 | 0 | 18 | 0 | ❌ | ✅ | ❌ |
| concept\01_foundation\26_quiz_modules_testing.md | L1 | 662 | 0 | 0 | 0 | 0 | 0 | 22 | 0 | ❌ | ✅ | ❌ |
| concept\01_foundation\27_quiz_closures_iterators.md | L1 | 648 | 0 | 0 | 0 | 0 | 0 | 33 | 0 | ❌ | ✅ | ❌ |
| concept\02_intermediate\01_traits.md | L2 | 2127 | 15 | 2 | 0 | 7 | 5 | 50 | 10 | ✅ | ✅ | ✅ |
| concept\02_intermediate\02_generics.md | L2 | 2510 | 16 | 2 | 0 | 7 | 6 | 57 | 8 | ✅ | ✅ | ✅ |
| concept\02_intermediate\03_memory_management.md | L2 | 1899 | 13 | 3 | 0 | 7 | 5 | 46 | 7 | ✅ | ✅ | ✅ |
| concept\02_intermediate\04_error_handling.md | L2 | 2376 | 9 | 3 | 0 | 7 | 8 | 50 | 7 | ✅ | ✅ | ✅ |
| concept\02_intermediate\05_assert_matches.md | L2 | 608 | 3 | 3 | 0 | 3 | 3 | 17 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\06_range_types.md | L2 | 559 | 3 | 3 | 0 | 3 | 2 | 12 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\07_closure_types.md | L2 | 585 | 3 | 3 | 0 | 3 | 3 | 9 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\08_interior_mutability.md | L2 | 691 | 3 | 3 | 0 | 3 | 2 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\09_serde_patterns.md | L2 | 838 | 3 | 3 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\10_module_system.md | L2 | 679 | 3 | 3 | 0 | 3 | 3 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\11_cow_and_borrowed.md | L2 | 699 | 3 | 3 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\12_smart_pointers.md | L2 | 724 | 3 | 3 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\13_dsl_and_embedding.md | L2 | 721 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\14_newtype_and_wrapper.md | L2 | 698 | 3 | 3 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\15_error_handling_deep_dive.md | L2 | 708 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\15_iterator_patterns.md | L2 | 668 | 4 | 2 | 0 | 2 | 0 | 11 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\16_iterator_patterns.md | L2 | 734 | 4 | 2 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\17_macro_patterns.md | L2 | 750 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\18_lifetimes_advanced.md | L2 | 704 | 3 | 3 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\19_advanced_traits.md | L2 | 704 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\20_type_system_advanced.md | L2 | 828 | 3 | 3 | 0 | 3 | 1 | 15 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\21_metaprogramming.md | L2 | 747 | 3 | 3 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ |
| concept\02_intermediate\23_quiz_traits_and_generics.md | L2 | 621 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ❌ |
| concept\02_intermediate\24_quiz_memory_management.md | L2 | 655 | 0 | 0 | 0 | 0 | 0 | 26 | 0 | ❌ | ✅ | ❌ |
| concept\03_advanced\00_before_formal.md | L3 | 105 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ |
| concept\03_advanced\01_concurrency.md | L3 | 1394 | 21 | 2 | 0 | 3 | 10 | 19 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\02_async.md | L3 | 2941 | 17 | 3 | 0 | 6 | 9 | 52 | 3 | ✅ | ✅ | ✅ |
| concept\03_advanced\02_async_advanced.md | L3 | 1405 | 4 | 3 | 0 | 1 | 1 | 30 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\02_async_patterns.md | L3 | 865 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\03_unsafe.md | L3 | 2882 | 14 | 2 | 0 | 4 | 10 | 45 | 3 | ✅ | ✅ | ✅ |
| concept\03_advanced\04_macros.md | L3 | 2273 | 22 | 3 | 0 | 8 | 8 | 51 | 8 | ✅ | ✅ | ✅ |
| concept\03_advanced\05_rust_ffi.md | L3 | 660 | 3 | 3 | 0 | 3 | 3 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\06_pin_unpin.md | L3 | 698 | 3 | 3 | 0 | 3 | 2 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\07_proc_macro.md | L3 | 753 | 3 | 3 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\08_nll_and_polonius.md | L3 | 690 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\09_ffi_advanced.md | L3 | 858 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\10_concurrency_patterns.md | L3 | 810 | 3 | 3 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\11_atomics_and_memory_ordering.md | L3 | 870 | 3 | 3 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\12_unsafe_rust_patterns.md | L3 | 886 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\14_custom_allocators.md | L3 | 801 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\15_zero_copy_parsing.md | L3 | 773 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\16_lock_free.md | L3 | 807 | 3 | 3 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\17_type_erasure.md | L3 | 793 | 3 | 3 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\18_network_programming.md | L3 | 905 | 3 | 3 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\19_parallel_distributed_pattern_spectrum.md | L3 | 831 | 3 | 3 | 0 | 3 | 0 | 17 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\20_stream_processing_semantics.md | L3 | 781 | 3 | 3 | 0 | 2 | 0 | 8 | 6 | ✅ | ✅ | ✅ |
| concept\03_advanced\21_quiz_concurrency_async.md | L3 | 661 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ❌ |
| concept\03_advanced\22_quiz_unsafe.md | L3 | 567 | 0 | 0 | 0 | 0 | 0 | 21 | 0 | ❌ | ✅ | ❌ |
| concept\03_advanced\23_quiz_macros.md | L3 | 626 | 0 | 0 | 0 | 0 | 0 | 23 | 0 | ❌ | ✅ | ❌ |
| concept\04_formal\01_linear_logic.md | L4 | 1114 | 14 | 0 | 0 | 4 | 5 | 13 | 3 | ✅ | ✅ | ✅ |
| concept\04_formal\02_type_theory.md | L4 | 1148 | 27 | 0 | 0 | 4 | 5 | 15 | 3 | ✅ | ✅ | ✅ |
| concept\04_formal\03_ownership_formal.md | L4 | 1472 | 12 | 0 | 0 | 1 | 5 | 10 | 3 | ✅ | ✅ | ✅ |
| concept\04_formal\04_rustbelt.md | L4 | 1299 | 5 | 0 | 0 | 1 | 5 | 16 | 10 | ✅ | ✅ | ✅ |
| concept\04_formal\05_verification_toolchain.md | L4 | 1411 | 3 | 0 | 0 | 1 | 4 | 17 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\06_subtype_variance.md | L4 | 572 | 3 | 0 | 0 | 3 | 2 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\08_type_inference.md | L4 | 638 | 3 | 0 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\09_linear_logic_applications.md | L4 | 682 | 3 | 0 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\10_category_theory.md | L4 | 652 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\11_separation_logic.md | L4 | 693 | 3 | 0 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\12_denotational_semantics.md | L4 | 552 | 3 | 0 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\13_formal_methods.md | L4 | 645 | 3 | 0 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\14_lambda_calculus.md | L4 | 598 | 3 | 0 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\15_hoare_logic.md | L4 | 744 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\16_aerospace_certification_formal_methods.md | L4 | 1025 | 3 | 0 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\17_operational_semantics.md | L4 | 944 | 3 | 0 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\18_evaluation_strategies.md | L4 | 534 | 3 | 0 | 0 | 3 | 0 | 14 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\20_axiomatic_semantics.md | L4 | 892 | 3 | 0 | 0 | 3 | 0 | 13 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\21_type_semantics.md | L4 | 823 | 3 | 0 | 0 | 3 | 0 | 18 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\22_modern_verification_tools.md | L4 | 451 | 3 | 0 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\23_programming_language_foundations.md | L4 | 333 | 3 | 0 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ |
| concept\04_formal\24_quiz_formal_methods.md | L4 | 540 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ❌ |
| concept\05_comparative\01_rust_vs_cpp.md | L5 | 2072 | 9 | 0 | 0 | 2 | 10 | 12 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\02_cpp_abi_object_model.md | L5 | 728 | 3 | 0 | 0 | 3 | 0 | 17 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\02_rust_vs_go.md | L5 | 918 | 3 | 0 | 0 | 3 | 6 | 11 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\03_paradigm_matrix.md | L5 | 916 | 6 | 0 | 0 | 5 | 8 | 7 | 16 | ✅ | ✅ | ✅ |
| concept\05_comparative\04_safety_boundaries.md | L5 | 963 | 8 | 0 | 0 | 1 | 7 | 9 | 9 | ✅ | ✅ | ✅ |
| concept\05_comparative\05_execution_model_isomorphism.md | L5 | 921 | 3 | 0 | 0 | 1 | 5 | 13 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\06_rust_vs_java.md | L5 | 546 | 3 | 0 | 0 | 3 | 3 | 7 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\07_rust_vs_python.md | L5 | 622 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\08_rust_vs_javascript.md | L5 | 613 | 3 | 0 | 0 | 3 | 2 | 5 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\08_rust_vs_ruby.md | L5 | 671 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\09_rust_vs_swift.md | L5 | 664 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\10_rust_vs_zig.md | L5 | 701 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\11_rust_vs_kotlin.md | L5 | 733 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\12_rust_vs_scala.md | L5 | 703 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\13_rust_vs_csharp.md | L5 | 750 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\14_rust_vs_elixir.md | L5 | 756 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\15_rust_vs_typescript.md | L5 | 856 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ |
| concept\05_comparative\17_quiz_rust_vs_systems.md | L5 | 662 | 0 | 0 | 0 | 0 | 0 | 15 | 0 | ❌ | ✅ | ❌ |
| concept\06_ecosystem\01_toolchain.md | L6 | 1634 | 13 | 0 | 0 | 2 | 9 | 15 | 14 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\02_patterns.md | L6 | 1715 | 7 | 0 | 0 | 2 | 5 | 28 | 14 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\03_core_crates.md | L6 | 1237 | 8 | 0 | 0 | 2 | 6 | 17 | 3 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\03_idioms_spectrum.md | L6 | 1354 | 6 | 0 | 0 | 1 | 5 | 35 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\04_application_domains.md | L6 | 1490 | 8 | 0 | 0 | 2 | 6 | 12 | 3 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\05_formal_ecosystem_tower.md | L6 | 542 | 3 | 0 | 0 | 0 | 2 | 6 | 6 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\05_system_design_principles.md | L6 | 676 | 6 | 0 | 0 | 1 | 6 | 8 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\06_blockchain.md | L6 | 857 | 5 | 0 | 0 | 0 | 3 | 14 | 6 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\07_game_ecs.md | L6 | 1297 | 3 | 0 | 0 | 0 | 7 | 23 | 6 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\08_wasi.md | L6 | 590 | 6 | 0 | 0 | 5 | 2 | 11 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\09_cargo_script.md | L6 | 632 | 4 | 0 | 0 | 1 | 2 | 11 | 8 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\10_public_private_deps.md | L6 | 564 | 6 | 0 | 0 | 1 | 2 | 12 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\11_webassembly.md | L6 | 530 | 6 | 0 | 0 | 3 | 3 | 6 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\12_testing_strategies.md | L6 | 628 | 6 | 0 | 0 | 3 | 2 | 9 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\13_logging_observability.md | L6 | 615 | 6 | 0 | 0 | 3 | 3 | 9 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\14_documentation.md | L6 | 607 | 4 | 0 | 0 | 3 | 2 | 7 | 8 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\15_performance_optimization.md | L6 | 685 | 6 | 0 | 0 | 3 | 1 | 10 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\16_testing.md | L6 | 673 | 4 | 0 | 0 | 3 | 2 | 8 | 8 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\17_cross_compilation.md | L6 | 600 | 6 | 0 | 0 | 3 | 1 | 5 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\18_distributed_systems.md | L6 | 708 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\19_security_practices.md | L6 | 855 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\20_licensing_and_compliance.md | L6 | 638 | 6 | 0 | 0 | 3 | 1 | 6 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\21_game_development.md | L6 | 636 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\22_embedded_systems.md | L6 | 848 | 6 | 0 | 0 | 3 | 1 | 10 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\23_database_access.md | L6 | 757 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\24_cloud_native.md | L6 | 675 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\25_cli_development.md | L6 | 722 | 6 | 0 | 0 | 3 | 1 | 9 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\26_game_development.md | L6 | 659 | 6 | 0 | 0 | 3 | 1 | 7 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\27_web_frameworks.md | L6 | 942 | 6 | 0 | 0 | 4 | 3 | 11 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\28_devops_and_ci_cd.md | L6 | 816 | 6 | 0 | 0 | 3 | 2 | 7 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | L6 | 975 | 3 | 0 | 0 | 0 | 0 | 26 | 6 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\30_system_composability.md | L6 | 743 | 3 | 0 | 0 | 0 | 4 | 23 | 6 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\31_microservice_patterns.md | L6 | 908 | 6 | 0 | 0 | 2 | 6 | 15 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\32_event_driven_architecture.md | L6 | 932 | 6 | 0 | 0 | 2 | 4 | 15 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\33_cqrs_event_sourcing.md | L6 | 1398 | 6 | 0 | 0 | 3 | 1 | 18 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\35_architecture_patterns.md | L6 | 1148 | 6 | 0 | 0 | 3 | 0 | 13 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\35_pattern_composition_algebra.md | L6 | 668 | 6 | 0 | 0 | 3 | 0 | 15 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\36_stream_processing_ecosystem.md | L6 | 512 | 6 | 0 | 0 | 1 | 0 | 10 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\37_database_systems.md | L6 | 483 | 6 | 0 | 0 | 1 | 0 | 9 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\38_network_protocols.md | L6 | 362 | 6 | 0 | 0 | 1 | 0 | 7 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\39_os_kernel.md | L6 | 418 | 6 | 0 | 0 | 1 | 0 | 8 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\40_reactive_programming.md | L6 | 1017 | 6 | 0 | 0 | 3 | 0 | 14 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\41_workflow_theory.md | L6 | 1332 | 6 | 0 | 0 | 3 | 0 | 17 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\42_api_design_patterns.md | L6 | 1233 | 6 | 0 | 0 | 3 | 0 | 19 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\43_security_cryptography.md | L6 | 875 | 6 | 0 | 0 | 3 | 0 | 16 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\45_compiler_internals.md | L6 | 832 | 6 | 0 | 0 | 3 | 0 | 10 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\46_machine_learning_ecosystem.md | L6 | 872 | 6 | 0 | 0 | 3 | 0 | 14 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\47_compiler_infrastructure.md | L6 | 312 | 6 | 0 | 0 | 2 | 0 | 1 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\47_formal_verification_tools.md | L6 | 839 | 6 | 0 | 0 | 3 | 0 | 11 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\48_data_engineering.md | L6 | 879 | 6 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\48_industrial_case_studies.md | L6 | 355 | 6 | 0 | 0 | 1 | 0 | 4 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\49_game_engine_internals.md | L6 | 1070 | 6 | 0 | 0 | 3 | 0 | 13 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\50_distributed_consensus.md | L6 | 762 | 6 | 0 | 0 | 3 | 0 | 6 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\51_quantum_computing_rust.md | L6 | 853 | 6 | 0 | 0 | 3 | 0 | 11 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\52_robotics.md | L6 | 935 | 6 | 0 | 0 | 3 | 0 | 15 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\53_embedded_graphics.md | L6 | 1031 | 6 | 0 | 0 | 3 | 1 | 5 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\54_webassembly_advanced.md | L6 | 873 | 6 | 0 | 0 | 2 | 0 | 14 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\55_rust_for_data_science.md | L6 | 581 | 6 | 0 | 0 | 3 | 0 | 10 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\56_c_to_rust_translation.md | L6 | 392 | 6 | 0 | 0 | 1 | 0 | 2 | 12 | ✅ | ✅ | ✅ |
| concept\06_ecosystem\57_quiz_toolchain.md | L6 | 509 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ❌ |
| concept\07_future\01_ai_integration.md | L7 | 929 | 2 | 0 | 0 | 2 | 2 | 9 | 2 | ✅ | ✅ | ✅ |
| concept\07_future\02_formal_methods.md | L7 | 1538 | 9 | 0 | 0 | 1 | 9 | 9 | 3 | ✅ | ✅ | ✅ |
| concept\07_future\03_evolution.md | L7 | 1403 | 8 | 0 | 0 | 1 | 6 | 19 | 3 | ✅ | ✅ | ✅ |
| concept\07_future\04_effects_system.md | L7 | 1689 | 6 | 0 | 0 | 1 | 4 | 26 | 12 | ✅ | ✅ | ✅ |
| concept\07_future\05_rust_version_tracking.md | L7 | 1327 | 6 | 0 | 0 | 1 | 3 | 6 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\07_mcdc_coverage_preview.md | L7 | 495 | 4 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\08_safety_tags_preview.md | L7 | 543 | 4 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\09_parallel_frontend_preview.md | L7 | 592 | 6 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\10_derive_coerce_pointee_preview.md | L7 | 517 | 4 | 0 | 0 | 3 | 3 | 7 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\11_const_trait_impl_preview.md | L7 | 552 | 6 | 0 | 0 | 3 | 2 | 6 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\11_stable_abi_preview.md | L7 | 84 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ |
| concept\07_future\12_inline_const_pattern_preview.md | L7 | 84 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ |
| concept\07_future\12_return_type_notation_preview.md | L7 | 511 | 4 | 0 | 0 | 3 | 2 | 5 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\13_must_not_suspend_preview.md | L7 | 80 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ |
| concept\07_future\13_unsafe_fields_preview.md | L7 | 550 | 6 | 0 | 0 | 3 | 3 | 6 | 12 | ✅ | ✅ | ✅ |
| concept\07_future\14_ferrocene_preview.md | L7 | 514 | 6 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\14_lifetime_capture_preview.md | L7 | 78 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ |
| concept\07_future\15_gen_blocks_preview.md | L7 | 522 | 4 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\15_pin_ergonomics_preview.md | L7 | 224 | 0 | 0 | 0 | 2 | 2 | 8 | 0 | ❌ | ✅ | ✅ |
| concept\07_future\15_rpitit_preview.md | L7 | 73 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ |
| concept\07_future\16_cranelift_backend_preview.md | L7 | 586 | 6 | 0 | 0 | 3 | 3 | 9 | 12 | ✅ | ✅ | ✅ |
| concept\07_future\16_type_alias_impl_trait_preview.md | L7 | 61 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ |
| concept\07_future\17_arbitrary_self_types_preview.md | L7 | 282 | 6 | 0 | 0 | 2 | 0 | 7 | 12 | ✅ | ✅ | ✅ |
| concept\07_future\17_const_trait_preview.md | L7 | 80 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ |
| concept\07_future\17_ergonomic_ref_counting_preview.md | L7 | 174 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ |
| concept\07_future\17_rust_specification_preview.md | L7 | 572 | 6 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\18_async_drop_preview.md | L7 | 628 | 6 | 0 | 0 | 3 | 2 | 6 | 12 | ✅ | ✅ | ✅ |
| concept\07_future\18_field_projections_preview.md | L7 | 318 | 6 | 0 | 0 | 2 | 0 | 8 | 12 | ✅ | ✅ | ✅ |
| concept\07_future\19_rust_edition_preview.md | L7 | 80 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ |
| concept\07_future\19_rust_for_linux.md | L7 | 716 | 4 | 0 | 0 | 3 | 1 | 6 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\20_borrowsanitizer_preview.md | L7 | 586 | 4 | 0 | 0 | 3 | 3 | 7 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\21_rust_in_ai.md | L7 | 679 | 6 | 0 | 0 | 3 | 1 | 7 | 12 | ✅ | ✅ | ✅ |
| concept\07_future\22_edition_guide.md | L7 | 638 | 6 | 0 | 0 | 3 | 1 | 10 | 12 | ✅ | ✅ | ✅ |
| concept\07_future\22_gen_blocks_preview.md | L7 | 80 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ |
| concept\07_future\22_std_autodiff_preview.md | L7 | 263 | 6 | 0 | 0 | 2 | 0 | 5 | 12 | ✅ | ✅ | ✅ |
| concept\07_future\23_rust_edition_guide.md | L7 | 567 | 4 | 0 | 0 | 3 | 1 | 6 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\24_cargo_semver_checks_preview.md | L7 | 138 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ |
| concept\07_future\24_roadmap.md | L7 | 998 | 6 | 0 | 0 | 3 | 2 | 17 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\24_wasm_target_evolution.md | L7 | 70 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ |
| concept\07_future\25_aarch64_sve_sme_preview.md | L7 | 187 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ |
| concept\07_future\25_open_enums_preview.md | L7 | 730 | 4 | 0 | 0 | 3 | 3 | 13 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\26_rust_in_space.md | L7 | 82 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ |
| concept\07_future\26_specialization_preview.md | L7 | 667 | 4 | 0 | 0 | 3 | 2 | 7 | 12 | ✅ | ✅ | ✅ |
| concept\07_future\27_compile_time_execution.md | L7 | 672 | 4 | 0 | 0 | 3 | 1 | 6 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\28_rust_for_webassembly.md | L7 | 869 | 4 | 0 | 0 | 3 | 2 | 11 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\29_ebpf_rust.md | L7 | 928 | 6 | 0 | 0 | 1 | 3 | 15 | 8 | ✅ | ✅ | ✅ |
| concept\07_future\archive\01_ai_integration_original.md | L7 | 1229 | 8 | 0 | 0 | 1 | 6 | 3 | 3 | ✅ | ✅ | ✅ |
| concept\07_future\rust_1_97_preview.md | L7 | 486 | 6 | 0 | 0 | 1 | 0 | 7 | 12 | ✅ | ✅ | ✅ |
