# 知识体系质量仪表盘 (KB Quality Dashboard)

> 生成时间: 2026-06-09T23:16:17.315582+00:00
> 扫描文件数: 270

## 全局指标

| 指标 | 数值 | 目标 | 状态 |
|:---|:---|:---|:---|
| 总文件数 | 270 | 27 | ✅ |
| 总定理链 (⟹) | 1172 | ≥270 | ✅ |
| 总反命题 | 597 | ≥40 | ✅ |
| 总 Mermaid 图 | 537 | ≥50 | ✅ |
| 编译验证代码块 | 3203 | ≥150 | ✅ |
| 定理矩阵总行 | 13633 | — | — |
| 死链数量 | 0 | 0 | ✅ |
| 反向推理 (⟸) | 175 | ≥50 | ✅ |
| 模板化 ⟹ | 0 | 0 | ✅ |
| 前置概念覆盖率 | 229/231 | 100% | ⚠️ |
| 后置概念覆盖率 | 216/231 | 100% | ⚠️ |
| 双标签覆盖率 | 230/231 | >=95% | ✅ |
| 非法标签组合 | 0 | 0 | ✅ |

## 按层级分布

| 层级 | 文件数 | 平均 ⟹/文件 | 平均过渡段/文件 | 认知路径 | ⟸/文件 | 模板化 | 前置覆盖 | 后置覆盖 | 双标签 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| L0 | 39 | 2.3 | 5.5 | 36/39 (92%) | 0.0 | 0 | 7/39 | 6/39 | 39/39 |
| L1 | 32 | 3.7 | 6.1 | 26/32 (81%) | 1.6 | 0 | 31/32 | 26/32 | 32/32 |
| L2 | 24 | 4.5 | 5.8 | 22/24 (91%) | 2.6 | 0 | 24/24 | 22/24 | 24/24 |
| L3 | 26 | 4.8 | 4.7 | 21/26 (80%) | 2.3 | 0 | 25/26 | 22/26 | 26/26 |
| L4 | 22 | 5.0 | 5.5 | 21/22 (95%) | 0.0 | 0 | 22/22 | 21/22 | 22/22 |
| L5 | 18 | 3.6 | 6.4 | 17/18 (94%) | 0.0 | 0 | 18/18 | 17/18 | 18/18 |
| L6 | 60 | 5.8 | 10.8 | 59/60 (98%) | 0.0 | 0 | 60/60 | 59/60 | 60/60 |
| L7 | 49 | 4.2 | 6.9 | 44/49 (89%) | 0.0 | 0 | 49/49 | 49/49 | 48/49 |

## 风险文件

| 文件 | 层级 | 未通过项 |
|:---|:---|:---|
| concept\01_foundation\00_start.md | L1 | 缺失认知路径; 缺失反命题; 缺失前置概念; 缺失后置概念 |
| concept\01_foundation\23_quiz_ownership_borrowing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\24_quiz_type_system.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\25_quiz_error_handling.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\26_quiz_modules_testing.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\01_foundation\27_quiz_closures_iterators.md | L1 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\23_quiz_traits_and_generics.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\02_intermediate\24_quiz_memory_management.md | L2 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\00_before_formal.md | L3 | 缺失认知路径; 缺失反命题; 缺失前置概念; 缺失后置概念 |
| concept\03_advanced\13_inline_assembly.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\21_quiz_concurrency_async.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\22_quiz_unsafe.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\03_advanced\23_quiz_macros.md | L3 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念; 反向推理不足 (⟸ 0 < 2) |
| concept\04_formal\24_quiz_formal_methods.md | L4 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失反命题; 缺失后置概念 |
| concept\05_comparative\17_quiz_rust_vs_systems.md | L5 | 缺失认知路径; 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失后置概念 |
| concept\06_ecosystem\57_quiz_toolchain.md | L6 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3); 缺失后置概念 |
| concept\07_future\01_ai_integration.md | L7 | 过渡段落不足 (2 < 3); 定理链不足 (2 < 3) |
| concept\07_future\15_pin_ergonomics_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\17_ergonomic_ref_counting_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\24_cargo_semver_checks_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\25_aarch64_sve_sme_preview.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |
| concept\07_future\archive\01_ai_integration_original.md | L7 | 缺失内容分级标签 |
| concept\07_future\borrow_sanitizer.md | L7 | 过渡段落不足 (0 < 3); 定理链不足 (0 < 3) |

## 文件详细统计

| 文件 | 层级 | 行数 | ⟹ | ⟸ | 模板 | 反命题 | Mermaid | 代码块 | 过渡段 | 认知路径 | 前置 | 后置 | 受众 | 分级 |
|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|:---|
| concept\00_meta\03_bloom_taxonomy.md | L0 | 176 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\05_cross_reference_matrix.md | L0 | 115 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\08_concept_audit_guide.md | L0 | 104 | 1 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\asp_marking_guide.md | L0 | 506 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\00_meta\audit_checklist.md | L0 | 384 | 1 | 0 | 0 | 2 | 1 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\authority_source_map.md | L0 | 184 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\boundary_extension_tree.md | L0 | 348 | 1 | 0 | 0 | 1 | 3 | 1 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\career_landscape.md | L0 | 228 | 0 | 0 | 0 | 1 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 入门 → 进阶 | 元层 |
| concept\00_meta\cognitive_dimension_matrix.md | L0 | 383 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\competency_graph.md | L0 | 406 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\comprehensive_rust_mapping.md | L0 | 230 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ✅ | ✅ | 初学者 → 进阶 | 元层 |
| concept\00_meta\concept_definition_decision_forest.md | L0 | 1116 | 3 | 0 | 0 | 1 | 10 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\concept_index.md | L0 | 764 | 4 | 0 | 0 | 2 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\decidability_spectrum.md | L0 | 883 | 1 | 0 | 0 | 1 | 6 | 2 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\expressiveness_multiview.md | L0 | 760 | 0 | 0 | 0 | 1 | 7 | 7 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\fault_tree_analysis_collection.md | L0 | 767 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\grading_system.md | L0 | 142 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\inter_layer_map.md | L0 | 628 | 12 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\inter_layer_topology.md | L0 | 403 | 8 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\00_meta\intra_layer_model_map.md | L0 | 337 | 11 | 0 | 0 | 1 | 5 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\kg_ontology.md | L0 | 409 | 4 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\knowledge_mindmap.md | L0 | 297 | 1 | 0 | 0 | 1 | 2 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\learning_guide.md | L0 | 658 | 3 | 0 | 0 | 1 | 1 | 1 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\LEARNING_MVP_PATH.md | L0 | 285 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ✅ | ❌ | 初学者 | 综述级 |
| concept\00_meta\methodology.md | L0 | 537 | 1 | 0 | 0 | 2 | 5 | 1 | 6 | ✅ | ✅ | ✅ | 研究者 | 综述级 |
| concept\00_meta\navigation.md | L0 | 290 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\paradigm_transition_matrix.md | L0 | 310 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\problem_graph.md | L0 | 494 | 1 | 0 | 0 | 1 | 7 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\quality_dashboard_v2.md | L0 | 324 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\00_meta\quick_reference.md | L0 | 818 | 1 | 0 | 0 | 1 | 0 | 25 | 6 | ✅ | ❌ | ❌ | 进阶 | 综述级 |
| concept\00_meta\rustbelt_predicate_map.md | L0 | 411 | 9 | 0 | 0 | 1 | 6 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\self_assessment.md | L0 | 2210 | 0 | 0 | 0 | 1 | 0 | 55 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\semantic_bridge_algorithms_patterns.md | L0 | 378 | 1 | 0 | 0 | 1 | 0 | 4 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\00_meta\semantic_expressiveness.md | L0 | 1127 | 1 | 0 | 0 | 1 | 2 | 1 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\semantic_space.md | L0 | 1319 | 10 | 0 | 0 | 2 | 5 | 9 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\sources.md | L0 | 487 | 1 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 进阶 | 研究者级 |
| concept\00_meta\terminology_glossary.md | L0 | 585 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 初学者 | 综述级 |
| concept\00_meta\theorem_inference_forest.md | L0 | 509 | 3 | 0 | 0 | 1 | 3 | 0 | 6 | ✅ | ❌ | ❌ | 研究者 | 综述级 |
| concept\00_meta\todos.md | L0 | 321 | 1 | 0 | 0 | 1 | 0 | 0 | 6 | ✅ | ❌ | ❌ | 专家 | 综述级 |
| concept\01_foundation\00_pl_prerequisites.md | L1 | 493 | 3 | 2 | 0 | 1 | 0 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\00_start.md | L1 | 114 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | ❌ | ❌ | ❌ | 初学者 | 初学者 |
| concept\01_foundation\01_ownership.md | L1 | 1743 | 12 | 2 | 0 | 3 | 7 | 42 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\02_borrowing.md | L1 | 1797 | 4 | 2 | 0 | 3 | 6 | 44 | 20 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\03_lifetimes.md | L1 | 1375 | 19 | 2 | 0 | 3 | 5 | 40 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\03_lifetimes_advanced.md | L1 | 1495 | 3 | 2 | 0 | 1 | 0 | 43 | 10 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\04_type_system.md | L1 | 2666 | 18 | 2 | 0 | 3 | 12 | 52 | 16 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\05_never_type.md | L1 | 507 | 3 | 2 | 0 | 1 | 0 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\05_reference_semantics.md | L1 | 1433 | 3 | 2 | 0 | 4 | 7 | 35 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\06_zero_cost_abstractions.md | L1 | 832 | 3 | 2 | 0 | 3 | 2 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\07_control_flow.md | L1 | 942 | 3 | 2 | 0 | 3 | 1 | 19 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\08_collections.md | L1 | 855 | 3 | 2 | 0 | 3 | 2 | 16 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\09_strings_and_text.md | L1 | 844 | 3 | 2 | 0 | 3 | 1 | 17 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\10_error_handling_basics.md | L1 | 976 | 3 | 2 | 0 | 3 | 1 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\10_numerics.md | L1 | 857 | 3 | 2 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\11_modules_and_paths.md | L1 | 888 | 3 | 2 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\11_numeric_types.md | L1 | 651 | 3 | 2 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\12_attributes_and_macros.md | L1 | 913 | 3 | 2 | 0 | 3 | 1 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\13_panic_and_abort.md | L1 | 877 | 3 | 2 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\14_coercion_and_casting.md | L1 | 913 | 3 | 2 | 0 | 3 | 1 | 15 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\15_closure_basics.md | L1 | 888 | 3 | 2 | 0 | 3 | 1 | 18 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\16_testing_basics.md | L1 | 734 | 3 | 2 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\17_collections_advanced.md | L1 | 996 | 3 | 2 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\18_strings_and_encoding.md | L1 | 830 | 3 | 2 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\20_variable_model.md | L1 | 597 | 3 | 2 | 0 | 3 | 0 | 12 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\21_effects_and_purity.md | L1 | 662 | 3 | 2 | 0 | 3 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\22_data_abstraction_spectrum.md | L1 | 712 | 3 | 2 | 0 | 3 | 0 | 14 | 6 | ✅ | ✅ | ✅ | 初学者 | 综述级 |
| concept\01_foundation\23_quiz_ownership_borrowing.md | L1 | 483 | 0 | 0 | 0 | 0 | 0 | 17 | 0 | ❌ | ✅ | ❌ | 初学者 | 综述级 |
| concept\01_foundation\24_quiz_type_system.md | L1 | 496 | 0 | 0 | 0 | 0 | 0 | 14 | 0 | ❌ | ✅ | ❌ | 初学者 | 综述级 |
| concept\01_foundation\25_quiz_error_handling.md | L1 | 609 | 0 | 0 | 0 | 0 | 0 | 18 | 0 | ❌ | ✅ | ❌ | 初学者 | 综述级 |
| concept\01_foundation\26_quiz_modules_testing.md | L1 | 698 | 0 | 0 | 0 | 0 | 0 | 22 | 0 | ❌ | ✅ | ❌ | 初学者 | 综述级 |
| concept\01_foundation\27_quiz_closures_iterators.md | L1 | 684 | 0 | 0 | 0 | 0 | 0 | 33 | 0 | ❌ | ✅ | ❌ | 初学者 | 综述级 |
| concept\02_intermediate\01_traits.md | L2 | 2300 | 15 | 2 | 0 | 7 | 5 | 58 | 10 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\02_generics.md | L2 | 2685 | 16 | 2 | 0 | 7 | 6 | 64 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\03_memory_management.md | L2 | 2054 | 13 | 3 | 0 | 7 | 5 | 50 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\04_error_handling.md | L2 | 2520 | 9 | 3 | 0 | 7 | 8 | 53 | 7 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\05_assert_matches.md | L2 | 682 | 3 | 3 | 0 | 3 | 3 | 18 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\06_range_types.md | L2 | 627 | 3 | 3 | 0 | 3 | 2 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\07_closure_types.md | L2 | 750 | 3 | 3 | 0 | 3 | 3 | 15 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\08_interior_mutability.md | L2 | 839 | 3 | 3 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\09_serde_patterns.md | L2 | 904 | 3 | 3 | 0 | 3 | 2 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\10_module_system.md | L2 | 836 | 3 | 3 | 0 | 3 | 3 | 15 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\11_cow_and_borrowed.md | L2 | 765 | 3 | 3 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\12_smart_pointers.md | L2 | 870 | 3 | 3 | 0 | 3 | 2 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\13_dsl_and_embedding.md | L2 | 781 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\14_newtype_and_wrapper.md | L2 | 758 | 3 | 3 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\15_error_handling_deep_dive.md | L2 | 774 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\15_iterator_patterns.md | L2 | 728 | 4 | 2 | 0 | 2 | 0 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\16_iterator_patterns.md | L2 | 794 | 4 | 2 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\17_macro_patterns.md | L2 | 816 | 3 | 3 | 0 | 3 | 1 | 9 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\18_lifetimes_advanced.md | L2 | 899 | 3 | 3 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\19_advanced_traits.md | L2 | 869 | 3 | 3 | 0 | 3 | 1 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\20_type_system_advanced.md | L2 | 945 | 3 | 3 | 0 | 3 | 1 | 16 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\21_metaprogramming.md | L2 | 807 | 3 | 3 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\02_intermediate\23_quiz_traits_and_generics.md | L2 | 661 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ❌ | 进阶 | 综述级 |
| concept\02_intermediate\24_quiz_memory_management.md | L2 | 700 | 0 | 0 | 0 | 0 | 0 | 26 | 0 | ❌ | ✅ | ❌ | 进阶 | 综述级 |
| concept\03_advanced\00_before_formal.md | L3 | 142 | 0 | 0 | 0 | 0 | 1 | 0 | 0 | ❌ | ❌ | ❌ | 进阶 | 综述级 |
| concept\03_advanced\01_concurrency.md | L3 | 1617 | 21 | 2 | 0 | 3 | 10 | 23 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\02_async.md | L3 | 3145 | 17 | 3 | 0 | 6 | 9 | 56 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\02_async_advanced.md | L3 | 1691 | 4 | 3 | 0 | 1 | 1 | 40 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\02_async_patterns.md | L3 | 1145 | 3 | 3 | 0 | 3 | 1 | 20 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\03_unsafe.md | L3 | 3064 | 14 | 2 | 0 | 4 | 10 | 50 | 3 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\04_macros.md | L3 | 2491 | 22 | 3 | 0 | 8 | 8 | 59 | 8 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\05_rust_ffi.md | L3 | 880 | 3 | 3 | 0 | 3 | 3 | 16 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\06_pin_unpin.md | L3 | 884 | 3 | 3 | 0 | 3 | 2 | 19 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\07_proc_macro.md | L3 | 900 | 3 | 3 | 0 | 3 | 2 | 10 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\08_nll_and_polonius.md | L3 | 830 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\09_ffi_advanced.md | L3 | 924 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\10_concurrency_patterns.md | L3 | 1142 | 3 | 3 | 0 | 3 | 1 | 22 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\11_atomics_and_memory_ordering.md | L3 | 1215 | 3 | 3 | 0 | 3 | 2 | 21 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\12_unsafe_rust_patterns.md | L3 | 1027 | 3 | 3 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\13_inline_assembly.md | L3 | 765 | 0 | 0 | 0 | 0 | 0 | 25 | 0 | ❌ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\14_custom_allocators.md | L3 | 867 | 3 | 3 | 0 | 3 | 1 | 12 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\15_zero_copy_parsing.md | L3 | 910 | 3 | 3 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\16_lock_free.md | L3 | 1195 | 3 | 3 | 0 | 3 | 1 | 20 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\17_type_erasure.md | L3 | 859 | 3 | 3 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\18_network_programming.md | L3 | 972 | 3 | 3 | 0 | 3 | 2 | 11 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\19_parallel_distributed_pattern_spectrum.md | L3 | 891 | 3 | 3 | 0 | 3 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\20_stream_processing_semantics.md | L3 | 841 | 3 | 3 | 0 | 2 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\03_advanced\21_quiz_concurrency_async.md | L3 | 697 | 0 | 0 | 0 | 0 | 0 | 19 | 0 | ❌ | ✅ | ❌ | 专家 | 专家级 |
| concept\03_advanced\22_quiz_unsafe.md | L3 | 603 | 0 | 0 | 0 | 0 | 0 | 21 | 0 | ❌ | ✅ | ❌ | 专家 | 专家级 |
| concept\03_advanced\23_quiz_macros.md | L3 | 662 | 0 | 0 | 0 | 0 | 0 | 23 | 0 | ❌ | ✅ | ❌ | 专家 | 专家级 |
| concept\04_formal\01_linear_logic.md | L4 | 1243 | 14 | 0 | 0 | 4 | 5 | 13 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\02_type_theory.md | L4 | 1489 | 27 | 0 | 0 | 4 | 5 | 27 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\03_ownership_formal.md | L4 | 1738 | 12 | 0 | 0 | 1 | 5 | 17 | 3 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\04_rustbelt.md | L4 | 1431 | 5 | 0 | 0 | 1 | 5 | 16 | 10 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\05_verification_toolchain.md | L4 | 1540 | 3 | 0 | 0 | 1 | 4 | 17 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\06_subtype_variance.md | L4 | 632 | 3 | 0 | 0 | 3 | 2 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\08_type_inference.md | L4 | 696 | 3 | 0 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\09_linear_logic_applications.md | L4 | 740 | 3 | 0 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\10_category_theory.md | L4 | 806 | 3 | 0 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\11_separation_logic.md | L4 | 837 | 3 | 0 | 0 | 3 | 1 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\12_denotational_semantics.md | L4 | 630 | 3 | 0 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\13_formal_methods.md | L4 | 737 | 3 | 0 | 0 | 3 | 1 | 7 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\14_lambda_calculus.md | L4 | 758 | 3 | 0 | 0 | 3 | 1 | 11 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\15_hoare_logic.md | L4 | 908 | 3 | 0 | 0 | 3 | 2 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\16_aerospace_certification_formal_methods.md | L4 | 1091 | 3 | 0 | 0 | 1 | 1 | 5 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\17_operational_semantics.md | L4 | 1084 | 3 | 0 | 0 | 3 | 1 | 13 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\18_evaluation_strategies.md | L4 | 594 | 3 | 0 | 0 | 3 | 0 | 14 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\20_axiomatic_semantics.md | L4 | 952 | 3 | 0 | 0 | 3 | 0 | 13 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\21_type_semantics.md | L4 | 883 | 3 | 0 | 0 | 3 | 0 | 18 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\22_modern_verification_tools.md | L4 | 511 | 3 | 0 | 0 | 1 | 0 | 8 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\23_programming_language_foundations.md | L4 | 393 | 3 | 0 | 0 | 1 | 0 | 10 | 6 | ✅ | ✅ | ✅ | 研究者 | 专家级 |
| concept\04_formal\24_quiz_formal_methods.md | L4 | 576 | 0 | 0 | 0 | 0 | 0 | 10 | 0 | ❌ | ✅ | ❌ | 研究者 | 专家级 |
| concept\05_comparative\01_rust_vs_cpp.md | L5 | 2132 | 9 | 0 | 0 | 2 | 10 | 12 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\05_comparative\02_cpp_abi_object_model.md | L5 | 788 | 3 | 0 | 0 | 3 | 0 | 17 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\05_comparative\02_rust_vs_go.md | L5 | 978 | 3 | 0 | 0 | 3 | 6 | 11 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\03_paradigm_matrix.md | L5 | 976 | 6 | 0 | 0 | 5 | 8 | 7 | 16 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\04_safety_boundaries.md | L5 | 1024 | 8 | 0 | 0 | 1 | 7 | 9 | 9 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\05_comparative\05_execution_model_isomorphism.md | L5 | 987 | 3 | 0 | 0 | 1 | 5 | 13 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\05_comparative\06_rust_vs_java.md | L5 | 612 | 3 | 0 | 0 | 3 | 3 | 7 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\07_rust_vs_python.md | L5 | 688 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\08_rust_vs_javascript.md | L5 | 679 | 3 | 0 | 0 | 3 | 2 | 5 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\08_rust_vs_ruby.md | L5 | 734 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\09_rust_vs_swift.md | L5 | 730 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\10_rust_vs_zig.md | L5 | 767 | 3 | 0 | 0 | 3 | 1 | 8 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\11_rust_vs_kotlin.md | L5 | 799 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\12_rust_vs_scala.md | L5 | 769 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\13_rust_vs_csharp.md | L5 | 816 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\14_rust_vs_elixir.md | L5 | 822 | 3 | 0 | 0 | 3 | 1 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\15_rust_vs_typescript.md | L5 | 922 | 3 | 0 | 0 | 3 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\05_comparative\17_quiz_rust_vs_systems.md | L5 | 698 | 0 | 0 | 0 | 0 | 0 | 15 | 0 | ❌ | ✅ | ❌ | 进阶 | 综述级 |
| concept\06_ecosystem\01_toolchain.md | L6 | 1780 | 13 | 0 | 0 | 2 | 9 | 15 | 14 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\02_patterns.md | L6 | 1870 | 7 | 0 | 0 | 2 | 5 | 31 | 14 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\03_core_crates.md | L6 | 1364 | 8 | 0 | 0 | 2 | 6 | 17 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\03_idioms_spectrum.md | L6 | 1423 | 6 | 0 | 0 | 1 | 5 | 35 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\04_application_domains.md | L6 | 1553 | 8 | 0 | 0 | 2 | 6 | 12 | 3 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\05_formal_ecosystem_tower.md | L6 | 606 | 3 | 0 | 0 | 0 | 2 | 6 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\05_system_design_principles.md | L6 | 745 | 6 | 0 | 0 | 1 | 6 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\06_blockchain.md | L6 | 920 | 5 | 0 | 0 | 0 | 3 | 14 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\07_game_ecs.md | L6 | 1360 | 3 | 0 | 0 | 0 | 7 | 23 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\08_wasi.md | L6 | 653 | 6 | 0 | 0 | 5 | 2 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\09_cargo_script.md | L6 | 700 | 4 | 0 | 0 | 1 | 2 | 11 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\10_public_private_deps.md | L6 | 632 | 6 | 0 | 0 | 1 | 2 | 12 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\11_webassembly.md | L6 | 600 | 6 | 0 | 0 | 3 | 3 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\12_testing_strategies.md | L6 | 697 | 6 | 0 | 0 | 3 | 2 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\13_logging_observability.md | L6 | 684 | 6 | 0 | 0 | 3 | 3 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\14_documentation.md | L6 | 676 | 4 | 0 | 0 | 3 | 2 | 7 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\15_performance_optimization.md | L6 | 754 | 6 | 0 | 0 | 3 | 1 | 10 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\16_testing.md | L6 | 742 | 4 | 0 | 0 | 3 | 2 | 8 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\17_cross_compilation.md | L6 | 669 | 6 | 0 | 0 | 3 | 1 | 5 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\18_distributed_systems.md | L6 | 777 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\19_security_practices.md | L6 | 924 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\20_licensing_and_compliance.md | L6 | 706 | 6 | 0 | 0 | 3 | 1 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\21_game_development.md | L6 | 704 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\22_embedded_systems.md | L6 | 954 | 6 | 0 | 0 | 3 | 1 | 10 | 8 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\23_database_access.md | L6 | 825 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\24_cloud_native.md | L6 | 743 | 6 | 0 | 0 | 3 | 1 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\25_cli_development.md | L6 | 790 | 6 | 0 | 0 | 3 | 1 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\26_game_development.md | L6 | 727 | 6 | 0 | 0 | 3 | 1 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\27_web_frameworks.md | L6 | 1011 | 6 | 0 | 0 | 4 | 3 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\28_devops_and_ci_cd.md | L6 | 884 | 6 | 0 | 0 | 3 | 2 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\29_algorithms_competitive_programming.md | L6 | 1038 | 3 | 0 | 0 | 0 | 0 | 26 | 6 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\30_system_composability.md | L6 | 806 | 3 | 0 | 0 | 0 | 4 | 23 | 6 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\31_microservice_patterns.md | L6 | 977 | 6 | 0 | 0 | 2 | 6 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\32_event_driven_architecture.md | L6 | 1001 | 6 | 0 | 0 | 2 | 4 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\33_cqrs_event_sourcing.md | L6 | 1466 | 6 | 0 | 0 | 3 | 1 | 18 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\35_architecture_patterns.md | L6 | 1216 | 6 | 0 | 0 | 3 | 0 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\35_pattern_composition_algebra.md | L6 | 731 | 6 | 0 | 0 | 3 | 0 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\36_stream_processing_ecosystem.md | L6 | 574 | 6 | 0 | 0 | 1 | 0 | 10 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\37_database_systems.md | L6 | 546 | 6 | 0 | 0 | 1 | 0 | 9 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\38_network_protocols.md | L6 | 424 | 6 | 0 | 0 | 1 | 0 | 7 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\39_os_kernel.md | L6 | 480 | 6 | 0 | 0 | 1 | 0 | 8 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\40_reactive_programming.md | L6 | 1085 | 6 | 0 | 0 | 3 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\41_workflow_theory.md | L6 | 1400 | 6 | 0 | 0 | 3 | 0 | 17 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\42_api_design_patterns.md | L6 | 1301 | 6 | 0 | 0 | 3 | 0 | 19 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\43_security_cryptography.md | L6 | 943 | 6 | 0 | 0 | 3 | 0 | 16 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\45_compiler_internals.md | L6 | 900 | 6 | 0 | 0 | 3 | 0 | 10 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\46_machine_learning_ecosystem.md | L6 | 940 | 6 | 0 | 0 | 3 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\47_compiler_infrastructure.md | L6 | 376 | 6 | 0 | 0 | 2 | 0 | 1 | 12 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\06_ecosystem\47_formal_verification_tools.md | L6 | 908 | 6 | 0 | 0 | 3 | 0 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\48_data_engineering.md | L6 | 947 | 6 | 0 | 0 | 3 | 0 | 12 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\48_industrial_case_studies.md | L6 | 417 | 6 | 0 | 0 | 1 | 0 | 4 | 12 | ✅ | ✅ | ✅ | 专家 | 专家级 |
| concept\06_ecosystem\49_game_engine_internals.md | L6 | 1138 | 6 | 0 | 0 | 3 | 0 | 13 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\50_distributed_consensus.md | L6 | 830 | 6 | 0 | 0 | 3 | 0 | 6 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\51_quantum_computing_rust.md | L6 | 921 | 6 | 0 | 0 | 3 | 0 | 11 | 12 | ✅ | ✅ | ✅ | 进阶 | 实验级 |
| concept\06_ecosystem\52_robotics.md | L6 | 1003 | 6 | 0 | 0 | 3 | 0 | 15 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\53_embedded_graphics.md | L6 | 1100 | 6 | 0 | 0 | 3 | 1 | 5 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\54_webassembly_advanced.md | L6 | 942 | 6 | 0 | 0 | 2 | 0 | 14 | 12 | ✅ | ✅ | ✅ | 进阶 | 专家级 |
| concept\06_ecosystem\55_rust_for_data_science.md | L6 | 651 | 6 | 0 | 0 | 3 | 0 | 10 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\56_c_to_rust_translation.md | L6 | 462 | 6 | 0 | 0 | 1 | 0 | 2 | 12 | ✅ | ✅ | ✅ | 进阶 | 综述级 |
| concept\06_ecosystem\57_quiz_toolchain.md | L6 | 547 | 0 | 0 | 0 | 0 | 0 | 7 | 0 | ❌ | ✅ | ❌ | 进阶 | 综述级 |
| concept\07_future\01_ai_integration.md | L7 | 993 | 2 | 0 | 0 | 2 | 2 | 9 | 2 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\02_formal_methods.md | L7 | 1671 | 9 | 0 | 0 | 1 | 9 | 9 | 3 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\03_evolution.md | L7 | 1468 | 8 | 0 | 0 | 1 | 6 | 19 | 3 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\04_effects_system.md | L7 | 1752 | 6 | 0 | 0 | 1 | 4 | 26 | 12 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\05_rust_version_tracking.md | L7 | 1465 | 6 | 0 | 0 | 1 | 3 | 8 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\07_mcdc_coverage_preview.md | L7 | 565 | 4 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\08_safety_tags_preview.md | L7 | 613 | 4 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\09_parallel_frontend_preview.md | L7 | 663 | 6 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\10_derive_coerce_pointee_preview.md | L7 | 587 | 4 | 0 | 0 | 3 | 3 | 7 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\11_const_trait_impl_preview.md | L7 | 622 | 6 | 0 | 0 | 3 | 2 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\11_stable_abi_preview.md | L7 | 148 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\12_inline_const_pattern_preview.md | L7 | 148 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\12_return_type_notation_preview.md | L7 | 581 | 4 | 0 | 0 | 3 | 2 | 5 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\13_must_not_suspend_preview.md | L7 | 144 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\13_unsafe_fields_preview.md | L7 | 620 | 6 | 0 | 0 | 3 | 3 | 6 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\14_ferrocene_preview.md | L7 | 584 | 6 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\14_lifetime_capture_preview.md | L7 | 142 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\15_gen_blocks_preview.md | L7 | 593 | 4 | 0 | 0 | 3 | 3 | 5 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\15_pin_ergonomics_preview.md | L7 | 296 | 0 | 0 | 0 | 2 | 2 | 8 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\15_rpitit_preview.md | L7 | 150 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\16_cranelift_backend_preview.md | L7 | 768 | 6 | 0 | 0 | 3 | 3 | 9 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\16_type_alias_impl_trait_preview.md | L7 | 146 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\17_arbitrary_self_types_preview.md | L7 | 352 | 6 | 0 | 0 | 2 | 0 | 7 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\17_const_trait_preview.md | L7 | 144 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\17_ergonomic_ref_counting_preview.md | L7 | 238 | 0 | 0 | 0 | 0 | 0 | 5 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\17_rust_specification_preview.md | L7 | 644 | 6 | 0 | 0 | 3 | 3 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\18_async_drop_preview.md | L7 | 760 | 6 | 0 | 0 | 3 | 2 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\18_field_projections_preview.md | L7 | 384 | 4 | 0 | 0 | 2 | 0 | 8 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\19_rust_edition_preview.md | L7 | 144 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\19_rust_for_linux.md | L7 | 785 | 4 | 0 | 0 | 3 | 1 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\20_borrowsanitizer_preview.md | L7 | 657 | 4 | 0 | 0 | 3 | 3 | 7 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\21_rust_in_ai.md | L7 | 747 | 6 | 0 | 0 | 3 | 1 | 7 | 12 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\22_edition_guide.md | L7 | 780 | 4 | 0 | 0 | 3 | 1 | 10 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\22_gen_blocks_preview.md | L7 | 144 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\22_std_autodiff_preview.md | L7 | 327 | 6 | 0 | 0 | 2 | 0 | 5 | 12 | ✅ | ✅ | ✅ | 研究者 | 实验级 |
| concept\07_future\23_rust_edition_guide.md | L7 | 636 | 4 | 0 | 0 | 3 | 1 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\24_cargo_semver_checks_preview.md | L7 | 205 | 0 | 0 | 0 | 0 | 0 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\24_roadmap.md | L7 | 1069 | 6 | 0 | 0 | 3 | 2 | 17 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\24_wasm_target_evolution.md | L7 | 133 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\25_aarch64_sve_sme_preview.md | L7 | 254 | 0 | 0 | 0 | 0 | 0 | 3 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\25_open_enums_preview.md | L7 | 800 | 4 | 0 | 0 | 3 | 3 | 13 | 8 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\26_rust_in_space.md | L7 | 145 | 3 | 0 | 0 | 1 | 0 | 1 | 6 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\26_specialization_preview.md | L7 | 744 | 4 | 0 | 0 | 3 | 2 | 7 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\27_compile_time_execution.md | L7 | 741 | 4 | 0 | 0 | 3 | 1 | 6 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\28_rust_for_webassembly.md | L7 | 938 | 4 | 0 | 0 | 3 | 2 | 11 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\29_ebpf_rust.md | L7 | 991 | 6 | 0 | 0 | 1 | 3 | 15 | 8 | ✅ | ✅ | ✅ | 专家 | 综述级 |
| concept\07_future\archive\01_ai_integration_original.md | L7 | 1265 | 8 | 0 | 0 | 1 | 6 | 3 | 3 | ✅ | ✅ | ✅ | 归档 | None |
| concept\07_future\borrow_sanitizer.md | L7 | 296 | 0 | 0 | 0 | 1 | 1 | 1 | 0 | ❌ | ✅ | ✅ | 专家 | 实验级 |
| concept\07_future\rust_1_97_preview.md | L7 | 723 | 6 | 0 | 0 | 1 | 0 | 15 | 12 | ✅ | ✅ | ✅ | 专家 | 实验级 |
