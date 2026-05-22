# 概念一致性审计报告 (Concept Consistency Report)

> 生成时间: 2026-05-22T09:14:50.470086
> 扫描文件数: 105
> 提取概念定义数: 469
> 跨文件引用数: 165

## 目录

- [概念一致性审计报告 (Concept Consistency Report)](#概念一致性审计报告-concept-consistency-report)
  - [目录](#目录)
  - [一、执行摘要](#一执行摘要)
  - [二、Send / Sync 一致性检查](#二send--sync-一致性检查)
  - [三、所有权三规则一致性检查](#三所有权三规则一致性检查)
  - [四、生命周期省略规则一致性检查](#四生命周期省略规则一致性检查)
  - [五、unsafe 语义一致性检查](#五unsafe-语义一致性检查)
  - [六、跨文件段落引用有效性检查](#六跨文件段落引用有效性检查)
  - [七、附录：概念定义统计](#七附录概念定义统计)
    - [7.1 按概念分类统计](#71-按概念分类统计)
    - [7.2 按文件统计](#72-按文件统计)

---

## 一、执行摘要

| 检查项 | 状态 | 详情 |
|:---|:---|:---|
| Send / Sync 一致性 | ✅ 通过 | 检测到 0 项 |
| 所有权三规则一致性 | ✅ 通过 | 检测到 0 项 |
| 生命周期省略规则一致性 | ✅ 通过 | 检测到 0 项 |
| unsafe 语义一致性 | ✅ 通过 | 检测到 0 项 |
| 跨文件段落引用有效性 | ✅ 全部有效 | 共 165 个引用 |
| **总计** | **0 错误 / 0 警告 / 0 提示** | — |

## 二、Send / Sync 一致性检查

> ✅ 未检测到一致性问题。

## 三、所有权三规则一致性检查

> ✅ 未检测到一致性问题。

## 四、生命周期省略规则一致性检查

> ✅ 未检测到一致性问题。

## 五、unsafe 语义一致性检查

> ✅ 未检测到一致性问题。

## 六、跨文件段落引用有效性检查

> ✅ 所有跨文件段落引用均有效。

## 七、附录：概念定义统计

### 7.1 按概念分类统计

| 概念 | 提取次数 | 涉及文件数 |
|:---|:---|:---|
| unsafe-UB | 126 | 35 |
| 所有权-Move语义 | 79 | 26 |
| Send+Sync | 52 | 25 |
| unsafe-契约 | 39 | 17 |
| 所有权-作用域绑定 | 32 | 14 |
| 所有权-唯一所有权 | 31 | 15 |
| unsafe-不变式 | 27 | 3 |
| unsafe-语义 | 18 | 12 |
| 生命周期-定义 | 14 | 7 |
| Send | 12 | 5 |
| Sync | 11 | 7 |
| 所有权-Copy例外 | 9 | 5 |
| 生命周期-Rule3 | 8 | 1 |
| 生命周期-Rule2 | 6 | 1 |
| 生命周期-Rule1 | 5 | 1 |

### 7.2 按文件统计

| 文件 | 概念定义数 | 跨文件引用数 | 章节数 |
|:---|:---|:---|:---|
| concept\00_meta\audit_checklist.md | 1 | 0 | 9 |
| concept\00_meta\authority_source_map.md | 1 | 0 | 0 |
| concept\00_meta\boundary_extension_tree.md | 1 | 0 | 5 |
| concept\00_meta\concept_index.md | 8 | 4 | 19 |
| concept\00_meta\decidability_spectrum.md | 4 | 0 | 16 |
| concept\00_meta\expressiveness_multiview.md | 4 | 0 | 20 |
| concept\00_meta\inter_layer_map.md | 11 | 2 | 14 |
| concept\00_meta\inter_layer_topology.md | 4 | 0 | 3 |
| concept\00_meta\intra_layer_model_map.md | 1 | 0 | 9 |
| concept\00_meta\knowledge_mindmap.md | 2 | 0 | 0 |
| concept\00_meta\learning_guide.md | 8 | 0 | 13 |
| concept\00_meta\methodology.md | 0 | 0 | 20 |
| concept\00_meta\navigation.md | 2 | 0 | 0 |
| concept\00_meta\quick_reference.md | 5 | 1 | 0 |
| concept\00_meta\self_assessment.md | 11 | 1 | 0 |
| concept\00_meta\semantic_expressiveness.md | 6 | 42 | 56 |
| concept\00_meta\semantic_space.md | 14 | 19 | 30 |
| concept\00_meta\sources.md | 1 | 0 | 14 |
| concept\00_meta\theorem_inference_forest.md | 8 | 0 | 14 |
| concept\00_meta\todos.md | 0 | 0 | 3 |
| concept\01_foundation\01_ownership.md | 43 | 2 | 25 |
| concept\01_foundation\02_borrowing.md | 4 | 2 | 31 |
| concept\01_foundation\03_lifetimes.md | 27 | 5 | 50 |
| concept\01_foundation\04_type_system.md | 3 | 3 | 43 |
| concept\01_foundation\05_reference_semantics.md | 0 | 0 | 8 |
| concept\01_foundation\06_zero_cost_abstractions.md | 0 | 0 | 8 |
| concept\01_foundation\07_control_flow.md | 0 | 0 | 8 |
| concept\01_foundation\08_collections.md | 0 | 0 | 8 |
| concept\01_foundation\09_strings_and_text.md | 0 | 0 | 8 |
| concept\02_intermediate\01_traits.md | 7 | 1 | 29 |
| concept\02_intermediate\02_generics.md | 3 | 5 | 41 |
| concept\02_intermediate\03_memory_management.md | 18 | 1 | 36 |
| concept\02_intermediate\04_error_handling.md | 1 | 3 | 49 |
| concept\02_intermediate\05_assert_matches.md | 0 | 0 | 10 |
| concept\02_intermediate\06_range_types.md | 0 | 0 | 11 |
| concept\02_intermediate\07_closure_types.md | 3 | 0 | 8 |
| concept\02_intermediate\08_interior_mutability.md | 1 | 0 | 8 |
| concept\02_intermediate\09_serde_patterns.md | 0 | 0 | 8 |
| concept\02_intermediate\10_module_system.md | 0 | 0 | 8 |
| concept\02_intermediate\11_cow_and_borrowed.md | 0 | 0 | 8 |
| concept\02_intermediate\12_smart_pointers.md | 2 | 0 | 8 |
| concept\02_intermediate\13_dsl_and_embedding.md | 0 | 0 | 8 |
| concept\03_advanced\01_concurrency.md | 37 | 10 | 22 |
| concept\03_advanced\02_async.md | 11 | 9 | 36 |
| concept\03_advanced\03_unsafe.md | 100 | 2 | 28 |
| concept\03_advanced\04_macros.md | 0 | 1 | 30 |
| concept\03_advanced\05_rust_ffi.md | 1 | 0 | 8 |
| concept\03_advanced\06_pin_unpin.md | 1 | 0 | 8 |
| concept\03_advanced\07_proc_macro.md | 0 | 0 | 8 |
| concept\03_advanced\08_nll_and_polonius.md | 0 | 0 | 8 |
| concept\04_formal\01_linear_logic.md | 10 | 2 | 25 |
| concept\04_formal\02_type_theory.md | 3 | 17 | 20 |
| concept\04_formal\03_ownership_formal.md | 5 | 10 | 25 |
| concept\04_formal\04_rustbelt.md | 4 | 4 | 28 |
| concept\04_formal\05_verification_toolchain.md | 1 | 1 | 14 |
| concept\04_formal\06_subtype_variance.md | 0 | 0 | 8 |
| concept\04_formal\07_separation_logic.md | 0 | 0 | 8 |
| concept\04_formal\08_type_inference.md | 0 | 0 | 8 |
| concept\04_formal\09_operational_semantics.md | 2 | 0 | 8 |
| concept\05_comparative\01_rust_vs_cpp.md | 11 | 1 | 41 |
| concept\05_comparative\02_rust_vs_go.md | 2 | 0 | 27 |
| concept\05_comparative\03_paradigm_matrix.md | 0 | 0 | 15 |
| concept\05_comparative\04_safety_boundaries.md | 18 | 13 | 19 |
| concept\05_comparative\05_execution_model_isomorphism.md | 4 | 0 | 17 |
| concept\05_comparative\06_rust_vs_java.md | 1 | 0 | 8 |
| concept\05_comparative\07_rust_vs_python.md | 2 | 0 | 8 |
| concept\05_comparative\08_rust_vs_javascript.md | 0 | 0 | 8 |
| concept\06_ecosystem\01_toolchain.md | 2 | 0 | 36 |
| concept\06_ecosystem\02_patterns.md | 4 | 0 | 18 |
| concept\06_ecosystem\03_core_crates.md | 1 | 0 | 28 |
| concept\06_ecosystem\03_idioms_spectrum.md | 7 | 0 | 33 |
| concept\06_ecosystem\04_application_domains.md | 0 | 0 | 35 |
| concept\06_ecosystem\05_formal_ecosystem_tower.md | 0 | 0 | 4 |
| concept\06_ecosystem\05_system_design_principles.md | 5 | 0 | 11 |
| concept\06_ecosystem\06_blockchain.md | 5 | 0 | 18 |
| concept\06_ecosystem\07_game_ecs.md | 1 | 0 | 29 |
| concept\06_ecosystem\08_wasi.md | 3 | 0 | 8 |
| concept\06_ecosystem\09_cargo_script.md | 0 | 0 | 9 |
| concept\06_ecosystem\10_public_private_deps.md | 1 | 0 | 10 |
| concept\06_ecosystem\11_webassembly.md | 0 | 0 | 8 |
| concept\06_ecosystem\12_testing_strategies.md | 1 | 0 | 8 |
| concept\06_ecosystem\13_logging_observability.md | 0 | 0 | 8 |
| concept\06_ecosystem\14_documentation.md | 0 | 0 | 8 |
| concept\06_ecosystem\15_performance_optimization.md | 1 | 0 | 8 |
| concept\06_ecosystem\16_testing.md | 1 | 0 | 8 |
| concept\07_future\01_ai_integration.md | 5 | 0 | 32 |
| concept\07_future\02_formal_methods.md | 1 | 0 | 43 |
| concept\07_future\03_evolution.md | 1 | 0 | 31 |
| concept\07_future\04_effects_system.md | 4 | 3 | 12 |
| concept\07_future\05_rust_version_tracking.md | 1 | 1 | 20 |
| concept\07_future\07_mcdc_coverage_preview.md | 0 | 0 | 7 |
| concept\07_future\08_safety_tags_preview.md | 1 | 0 | 10 |
| concept\07_future\09_parallel_frontend_preview.md | 0 | 0 | 8 |
| concept\07_future\10_derive_coerce_pointee_preview.md | 0 | 0 | 8 |
| concept\07_future\11_const_trait_impl_preview.md | 0 | 0 | 8 |
| concept\07_future\12_return_type_notation_preview.md | 0 | 0 | 8 |
| concept\07_future\13_unsafe_fields_preview.md | 6 | 0 | 8 |
| concept\07_future\14_ferrocene_preview.md | 0 | 0 | 8 |
| concept\07_future\15_gen_blocks_preview.md | 0 | 0 | 8 |
| concept\07_future\16_cranelift_backend_preview.md | 0 | 0 | 8 |
| concept\07_future\17_rust_specification_preview.md | 0 | 0 | 8 |
| concept\07_future\18_async_drop_preview.md | 0 | 0 | 8 |
| concept\07_future\19_specialization_preview.md | 0 | 0 | 8 |
| concept\07_future\borrowsanitizer_preview.md | 1 | 0 | 8 |
| concept\07_future\open_enums_preview.md | 0 | 0 | 15 |

---

> 本报告由 `scripts/concept_consistency_auditor.py` 自动生成。
